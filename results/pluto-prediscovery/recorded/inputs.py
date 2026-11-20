"""Prepare public queries and assemble the original scripts' outputs."""
import csv
import hashlib
import io
import json
from pathlib import Path
import sys
import urllib.parse
import urllib.request


def dump(value):
    print(json.dumps(value, indent=2))


def exposures(ra, dec):
    request = urllib.request.Request(
        "https://api.starglass.cfa.harvard.edu/public/dasch/dr7/queryexps",
        data=json.dumps({"ra_deg": float(ra), "dec_deg": float(dec)}).encode(),
        headers={"Content-Type": "application/json", "Accept": "application/json",
                 "User-Agent": "curl/8"},
    )
    with urllib.request.urlopen(request, timeout=300) as response:
        return list(csv.DictReader(io.StringIO("\n".join(json.load(response)))))


def selected_plates(path):
    rows = json.loads(Path(path).read_text())
    return dict.fromkeys(
        f"{row['series']}{int(row['platenum']):05d}" for row in rows
        if row["wcssource"] != "logbook"
        and float(row["limMagApass"] or row["limMagAtlas"] or 0) >= 15.9
    )


def fixed(folder, tag, plates):
    stem = "fixedpos" + ("_" + tag if tag else "")
    return [
        row
        for plate in Path(plates).read_text().splitlines()
        for row in json.loads((Path(folder) / f"{stem}_{plate}.json").read_text())
    ]


def ma733(source, dest):
    source, dest = Path(source), Path(dest)
    result = {
        name: json.loads((source / f"{name}.json").read_text())["733"]
        for name in ("measure", "archpos")
    }
    result["pipeline"] = json.loads((source / "pipeline_ma733.json").read_text())
    result["robust"] = json.loads((source / "robust.json").read_text())["733"]
    (dest / "ma00733.json").write_text(json.dumps(result, indent=2) + "\n")


def february_gaia(folder, measured_field):
    from astropy import units as u
    from astropy.coordinates import SkyCoord
    import numpy as np

    path = Path(folder) / "gaia-epoch.csv"
    measured_field = Path(measured_field)
    if measured_field.exists():
        path.write_bytes(measured_field.read_bytes())
    elif not path.exists():
        query = """
            SELECT source_id,ra,dec,pmra,pmdec,phot_g_mean_mag,bp_rp
            FROM gaiadr3.gaia_source
            WHERE 1=CONTAINS(POINT('ICRS',ra,dec),CIRCLE('ICRS',84.96155,16.13350,0.3565))
            AND phot_g_mean_mag<21 ORDER BY source_id
        """
        params = urllib.parse.urlencode({"REQUEST": "doQuery", "LANG": "ADQL",
                                         "FORMAT": "csv", "QUERY": query})
        endpoint = "https://gea.esac.esa.int/tap-server/tap/sync"
        with urllib.request.urlopen(f"{endpoint}?{params}", timeout=100) as response:
            path.write_bytes(response.read())
    data = path.read_bytes()
    stars = list(csv.DictReader(io.StringIO(data.decode())))
    ra = np.array([float(row["ra"]) for row in stars])
    dec = np.array([float(row["dec"]) for row in stars])
    dt = 1909.14 - 2016
    ra += dt * np.array([float(row["pmra"] or 0) for row in stars]) / 3.6e6 / np.cos(np.deg2rad(dec))
    dec += dt * np.array([float(row["pmdec"] or 0) for row in stars]) / 3.6e6
    prediction = SkyCoord(84.96155257 * u.deg, 16.13350142 * u.deg)
    separations = prediction.separation(SkyCoord(ra * u.deg, dec * u.deg)).arcsec
    nearest = int(separations.argmin())
    return {"plate": "B2247a", "gaia_dr3_source_id": stars[nearest]["source_id"],
            "separation_arcsec": float(separations[nearest]),
            "G": float(stars[nearest]["phot_g_mean_mag"]),
            "gaia_csv_sha256": hashlib.sha256(data).hexdigest()}


def february(folder):
    folder = Path(folder)
    for group in ("historic", "feb", "fixed"):
        for plate, row in json.loads((folder / f"{group}-open.json").read_text()).items():
            if plate != "chance":
                (folder / f"{plate}.json").write_text(json.dumps(row, indent=2) + "\n")


def weak(folder):
    folder = Path(folder)
    windows = (folder / "forced-windows.txt").read_text().splitlines()
    stack = (folder / "stack-clock.txt").read_text().splitlines()
    for plate in ("731", "733"):
        start = next(i for i, line in enumerate(stack) if line.startswith(plate))
        result = {
            "forced_windows": [line for line in windows if line.startswith(plate)],
            "faint_asteroid_stack": stack[start:start + 2],
        }
        (folder / f"ma00{plate}-summary.json").write_text(json.dumps(result, indent=2) + "\n")


def sbdb():
    fields = "spkid,pdes,class,H,q,e,a,i,om,w,ma,epoch"
    rows = []
    for constraint in (
        {"AND": ["H|LE|17.3"]},
        {"AND": ["H|GT|17.3"], "OR": ["class|EQ|" + c for c in ("MCA", "ATE", "APO", "AMO")]},
    ):
        query = urllib.parse.urlencode({
            "fields": fields, "sb-kind": "a", "sb-cdata": json.dumps(constraint),
            "full-prec": "true",
        })
        with urllib.request.urlopen(
            "https://ssd-api.jpl.nasa.gov/sbdb_query.api?" + query, timeout=300
        ) as response:
            rows.extend(json.load(response)["data"])
    return {"fields": fields.split(","), "data": rows}


def sample(path, count=20):
    """Choose sbvalidate's seeded per-class sample before integrating it."""
    import numpy as np

    orbit = json.loads(Path(path).read_text())
    index = {field: i for i, field in enumerate(orbit["fields"])}
    rows = orbit["data"]
    classes = np.array([row[index["class"]] for row in rows])
    neo = np.isin(classes, ("ATE", "APO", "AMO", "IEO"))
    h = np.array([float(row[index["H"]] or 99) for row in rows])
    q = np.array([float(row[index["q"]]) for row in rows])
    with np.errstate(invalid="ignore", divide="ignore"):
        vmin = np.where(q > 1.1, h + 5 * np.log10(q * (q - 0.9837)), -99)
    selected = []
    for mask, chunks in ((~neo & (vmin <= 18), 64), (neo, 40)):
        keep = np.flatnonzero(mask)
        ordered = np.concatenate([keep[chunk::chunks] for chunk in range(chunks)])
        rng = np.random.default_rng(5)
        for cls in np.unique(classes[ordered]):
            eligible = ordered[classes[ordered] == cls]
            selected.extend(rng.choice(eligible, min(count, len(eligible)), replace=False))
    return {"fields": orbit["fields"], "data": [rows[i] for i in selected]}


if __name__ == "__main__":
    task, *args = sys.argv[1:]
    if task == "exposures":
        dump(exposures(*args))
    elif task == "json-lines":
        dump([json.loads(line) for line in Path(args[0]).read_text().splitlines()])
    elif task == "plates":
        for plate in selected_plates(*args):
            print(plate)
    elif task == "fixed":
        dump(fixed(*args))
    elif task == "ma733":
        ma733(*args)
    elif task == "february-gaia":
        dump(february_gaia(*args))
    elif task == "february":
        february(*args)
    elif task == "weak":
        weak(*args)
    elif task == "sbdb":
        dump(sbdb())
    elif task == "sample":
        dump(sample(args[0], int(args[1]) if len(args) > 1 else 20))
    else:
        raise SystemExit(f"unknown task: {task}")
