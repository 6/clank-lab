"""Check the absolute-time predictions and deeper stationary catalogues at both sites."""
import argparse
import csv
import hashlib
import io
import json
import math
from pathlib import Path

from astropy.time import Time
import requests

from audit_ma731 import horizons


def check(fixed, clock):
    record = json.loads(clock.read_text())
    plate = json.loads((fixed / (record["plate"] + ".json")).read_text())
    exact = Time(record["measured_midpoint_UT1"], format="isot", scale="ut1")
    jpl = horizons("999", "coord@399", exact.jd, "1,36,37", plate["location"])
    ra, dec = plate["endpoint_midpoint_endpoint"][1][:2]
    params = dict(ra=ra, dec=dec, radius=.006, columns="[objID,raMean,decMean,gMeanPSFMag,rMeanPSFMag,nDetections]")
    params["nDetections.gte"] = 2
    response = requests.get("https://catalogs.mast.stsci.edu/api/v0.1/panstarrs/dr2/mean.csv",
                            params=params, timeout=60)
    response.raise_for_status()
    rows = []
    for star in csv.DictReader(io.StringIO(response.text)):
        dx = (float(star["raMean"]) - ra) * math.cos(math.radians(dec))
        dy = float(star["decMean"]) - dec
        distance = math.hypot(dx, dy) * 3600
        if distance <= 10:
            rows.append(dict(id=star["objID"], radius_as=distance,
                             g=star["gMeanPSFMag"], r=star["rMeanPSFMag"], n=int(star["nDetections"])))
    return dict(plate=record["plate"], jpl_UT1=jpl[0], jpl_ICRF_deg=jpl[3:5], jpl_uncertainty=jpl[5:-1],
                ps1_within_10_arcsec=sorted(rows, key=lambda row: row["radius_as"]),
                ps1_sha256=hashlib.sha256(response.content).hexdigest())


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("fixed", type=Path)
    ap.add_argument("clocks", type=Path, nargs=2)
    args = ap.parse_args()
    print(json.dumps([check(args.fixed, c) for c in args.clocks], indent=2))
