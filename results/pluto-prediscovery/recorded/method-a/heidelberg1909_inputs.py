"""Cache public inputs in the current (scratch) directory. Run with astropy and requests."""
import csv
import io
import sys
from pathlib import Path

import requests

GAVO = "https://dc.g-vo.org"
GAIA = "https://gea.esac.esa.int/tap-server/tap/sync"
HORIZONS = "https://ssd.jpl.nasa.gov/api/horizons.api"
SKYBOT = "https://ssp.imcce.fr/webservices/skybot/api/conesearch.php"
FIELDS = dict(pluto=(84.96155, 16.1335), k179=(82.8318, 19.1102),
              k168=(79.6243, 18.2293), k417=(82.8265, 15.2092))
PLATES = ("B2247a", "B2248b")
OTHER = "B4816a"  # deep later epoch, both cameras exist, use a
HIST = "B3383a"

def get(name, url, params, signature):
    path = Path(name)
    if not path.exists():
        result = requests.get(url, params=params, timeout=100)
        result.raise_for_status()
        if signature not in result.content[:3000] and signature not in result.content:
            raise ValueError(name, result.text[:350])
        path.write_bytes(result.content)
    return path

def tap(name, url, query):
    return get(name, url, dict(REQUEST="doQuery", LANG="ADQL", FORMAT="csv", QUERY=query),
               b",")

def track(body, day="1909-Feb-20"):
    tag = body.strip(";") + ("-1914" if "1914" in day else "")
    p = dict(format="text", COMMAND=f"'{body}'", CENTER="'024'", START_TIME=f"'{day} 10:00'",
             STOP_TIME=f"'{day} 23:59'", STEP_SIZE="'5 m'", QUANTITIES="'1,9,19,20,24'",
             ANG_FORMAT="DEG", CSV_FORMAT="YES", EXTRA_PREC="YES")
    return get(tag+".eph", HORIZONS, p, b"$$SOE")

def rows(path):
    return list(csv.DictReader(io.StringIO(path.read_text())))

def metadata():
    ids = ",".join(f"'{p}'" for p in (*PLATES, OTHER, HIST))
    return rows(tap("meta.csv", GAVO+"/tap/sync", f"SELECT * FROM lsw.plates WHERE plateID IN ({ids})"))

def coordinates(field):
    if field == "hist":
        line = next(x for x in track("999", "1914-Jan-23").read_text().splitlines()
                    if x.startswith(" 1914-Jan-23 19:00"))
        return tuple(map(float, line.split(",")[3:5]))
    return FIELDS[field]

def field_data(field):
    ra, dec = coordinates(field)
    radius = .23 if field in ("pluto", "hist") else .085
    cond = f"1=CONTAINS(POINT('ICRS',g.ra,g.dec),CIRCLE('ICRS',{ra},{dec},{radius*1.55}))"
    cols = "g.source_id,g.ra,g.dec,g.pmra,g.pmdec,g.phot_g_mean_mag,g.bp_rp"
    tap(field+".csv", GAIA, f"SELECT {cols} FROM gaiadr3.gaia_source AS g WHERE {cond} AND g.phot_g_mean_mag<21 ORDER BY g.source_id")
    if field in ("pluto", "hist"):
        tap(field+"-B.csv", GAIA, f"SELECT g.source_id,b.b_jkc_mag,b.b_jkc_flag,b.v_jkc_mag FROM gaiadr3.gaia_source AS g JOIN gaiadr3.synthetic_photometry_gspc AS b ON g.source_id=b.source_id WHERE {cond} ORDER BY g.source_id")
    for row in metadata():
        plate = row["plateID"]
        if (plate == HIST) != (field == "hist") or (plate == OTHER and field != "pluto"):
            continue
        get(plate+"-"+field+".fits", GAVO+"/lswscans/res/positions/dl/dlget",
            dict(ID=row["pub_did"], CIRCLE=f"{ra} {dec} {radius}"), b"SIMPLE  =")

def main():
    task = sys.argv[1]
    if task == "tracks":
        for body in ("999","179;","168;","417;"):
            track(body)
        for name, ra, dec, radius in (("field",82,15.85,3.4),("cone",84.96155,16.1335,.04)):
            get(name+"-024.skybot", SKYBOT, dict(RA=ra,DEC=dec,SR=radius,TIME="1909-02-20T20:20:00",
                **{"-observer":"024","-filter":"0","-mime":"text"}), b"# Num")
    elif task == "aux":
        get("ps1.csv","https://catalogs.mast.stsci.edu/api/v0.1/panstarrs/dr2/mean.csv",
            dict(ra=84.96155,dec=16.1335,radius=.012,
                 columns="[objID,raMean,decMean,nDetections,gMeanPSFMag,rMeanPSFMag,iMeanPSFMag]"),b"objID")
        for hm in ("18:40","19:10","19:40","20:10","20:40","21:10","21:40","21:55"):
            get("sweep-"+hm.replace(":","")+".skybot",SKYBOT,
                dict(RA=84.96155,DEC=16.1335,SR=.08,TIME="1909-02-20T"+hm+":00",
                     **{"-observer":"024","-filter":"0","-mime":"text"}),b"# Num")
        get("1923.eph",HORIZONS,dict(format="text",COMMAND="'999'",CENTER="'024'",
            START_TIME="'1923-Dec-29 19:45'",STOP_TIME="'1923-Dec-29 19:55'",
            STEP_SIZE="'5 m'",QUANTITIES="'1'",ANG_FORMAT="DEG",CSV_FORMAT="YES"),b"$$SOE")
    else:
        field_data(task)

if __name__ == "__main__":
    main()
