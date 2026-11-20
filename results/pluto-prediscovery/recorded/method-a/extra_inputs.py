"""Acquire Gaia DR3 and screen the preselected Heidelberg exposure."""
import csv
import io
import json
import sys
from pathlib import Path

import requests
from astropy.time import Time

from fetch import archive, geometry


def tap(url, query):
    response = requests.get(url, params=dict(REQUEST="doQuery", LANG="ADQL",
                            FORMAT="csv", QUERY=query), timeout=90)
    response.raise_for_status()
    return response.text


def gaia(folder, field, ra, dec):
    query = f"""SELECT source_id,ra,dec,pmra,pmdec,phot_g_mean_mag
        FROM gaiadr3.gaia_source WHERE 1=CONTAINS(POINT('ICRS',ra,dec),
        CIRCLE('ICRS',{ra},{dec},0.26)) AND phot_g_mean_mag<19.5 ORDER BY source_id"""
    path = folder / (field + "-gaia.csv")
    if not path.exists():
        path.write_bytes(tap("https://gea.esac.esa.int/tap-server/tap/sync", query).encode())


def extra(folder):
    for field in ["ma", "mc"]:
        p = json.loads(next(folder.glob(field + "*.json")).read_text())["cutout"]
        gaia(folder, field, p["center_ra_deg"], p["center_dec_deg"])
    query = "SELECT * FROM lsw.plates WHERE plateID='B342a'"
    record, = csv.DictReader(io.StringIO(tap("https://dc.g-vo.org/tap/sync", query)))
    start = Time(record["startTime"], scale="ut1")
    end = Time(record["endTime"], scale="ut1")
    midpoint = start + (end - start) / 2
    minutes = float(record["exposure"]) / 60
    site = dict(name="Heidelberg", lon=-8.724, lat=49.398, elevation=560)
    g = geometry(midpoint.isot, minutes, site)
    ra, dec = [round(x, 4) for x in g[1][:2]]
    p = dict(ID=record["pub_did"], CIRCLE=f"{ra} {dec} 0.175")
    r = requests.get("https://dc.g-vo.org/lswscans/res/positions/dl/dlget",
                     params=p, timeout=120)
    r.raise_for_status()
    if not r.content.startswith(b"SIMPLE"):
        raise ValueError(r.text[:500])
    (folder / "hd342a.fits").write_bytes(r.content)
    (folder / "hd342a.json").write_text(json.dumps(dict(midpoint=midpoint.isot,
        minutes=minutes, endpoint_midpoint_endpoint=g, cutout=p, location=site), indent=2)+"\n")
    gaia(folder, "hd", ra, dec)
    rows = archive("dasch/dr7/querycat", dict(refcat="apass", ra_deg=ra,
                   dec_deg=dec, radius_arcsec=1200))
    (folder / "hd-apass.csv").write_text("\n".join(rows)+"\n")


if __name__ == "__main__":
    extra(Path(sys.argv[1]))
