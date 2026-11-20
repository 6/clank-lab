"""Fetch the public DR7 cutouts, comparison stars and JPL observing geometry."""
import argparse
import base64
import gzip
import hashlib
import json
from pathlib import Path

from astropy.time import Time
import numpy as np
import requests

ARCHIVE = "https://api.starglass.cfa.harvard.edu/public/"
HORIZONS = "https://ssd.jpl.nasa.gov/api/horizons.api"


def archive(endpoint, payload=None):
    r = (requests.post(ARCHIVE + endpoint, json=payload, timeout=90) if payload
         else requests.get(ARCHIVE + endpoint, timeout=90))
    r.raise_for_status()
    return r.json()


def geometry(midpoint, minutes, site):
    jd = Time(midpoint.rstrip("Z"), format="isot", scale="ut1").jd
    times = jd + np.array([-0.5, 0, 0.5]) * minutes / 1440
    coords = f"{-site['lon']},{site['lat']},{site['elevation']/1000}"
    args = dict(format="json", COMMAND="'999'", CENTER="'coord@399'",
                COORD_TYPE="'GEODETIC'", SITE_COORD=f"'{coords}'",
                TLIST="'" + ",".join(f"{x:.9f}" for x in times) + "'",
                QUANTITIES="'1,9'", ANG_FORMAT="'DEG'", CSV_FORMAT="'YES'",
                EXTRA_PREC="'YES'", OBJ_DATA="'NO'")
    r = requests.get(HORIZONS, params=args, timeout=90)
    r.raise_for_status()
    result = r.json()["result"]
    rows = result.split("$$SOE")[1].split("$$EOE")[0].strip().splitlines()
    return [[float(x) for x in row.split(",")[3:6]] for row in rows]


def fetch(dest):
    dest.mkdir(exist_ok=True, parents=True)

    def save(name, data):
        (dest / name).write_bytes(data)

    for plate in ("mc06858", "ma00731", "ma00733"):
        meta = archive("plates/p/" + plate)
        exp = meta["exposures"][0]
        geom = geometry(exp["datetime"], exp["exposure"], meta["location"])
        center = ([85.8785, 16.017] if plate.startswith("ma")
                  else [round(x, 3) for x in geom[1][:2]])
        params = dict(plate_id=plate, solution_number=0,
                      center_ra_deg=center[0], center_dec_deg=center[1])
        fits_name = plate + ".fits"
        if not (dest / fits_name).exists():
            encoded = archive("dasch/dr7/cutout", params)
            save(fits_name, gzip.decompress(base64.b64decode(encoded)))
        for cat in ("apass", "atlas"):
            name = f"{plate[:2]}-{cat}.csv"
            if not (dest / name).exists():
                rows = archive("dasch/dr7/querycat", dict(refcat=cat, ra_deg=center[0],
                               dec_deg=center[1], radius_arcsec=1200))
                save(name, ("\n".join(rows) + "\n").encode())
        record = dict(midpoint=exp["datetime"], minutes=exp["exposure"],
                      location=meta["location"], endpoint_midpoint_endpoint=geom,
                      cutout=params)
        save(plate + ".json", (json.dumps(record, indent=2) + "\n").encode())


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("data", type=Path)
    folder = parser.parse_args().data
    fetch(folder)
    for p in sorted(folder.iterdir()):
        print(hashlib.sha256(p.read_bytes()).hexdigest(), p.name)
