"""Measure the Heidelberg Bruce scans of Wolf's 23 January 1914 field."""
import argparse
import csv
import hashlib
import io
import json
from pathlib import Path

import requests
from astropy.time import Time

from extra_inputs import gaia, tap
from fetch import archive, geometry
from measure import Plate, experiment


def measure(folder, plate):
    folder.mkdir(exist_ok=True, parents=True)
    name = "hd" + plate.lower()
    query = f"SELECT * FROM lsw.plates WHERE plateID='{plate}'"
    row, = csv.DictReader(io.StringIO(tap("https://dc.g-vo.org/tap/sync", query)))
    start, end = [Time(row[k], scale="ut1") for k in ("startTime", "endTime")]
    mid = start + (end-start)/2
    duration = float(row["exposure"])/60
    site = dict(name="Heidelberg", lon=-8.724, lat=49.398, elevation=560)
    positions = geometry(mid.isot, duration, site)
    ra, dec = [round(x, 4) for x in positions[1][:2]]
    params = dict(ID=row["pub_did"], CIRCLE=f"{ra} {dec} 0.18")
    path = folder / (name+".fits")
    if not path.exists():
        response = requests.get("https://dc.g-vo.org/lswscans/res/positions/dl/dlget", params=params, timeout=120)
        response.raise_for_status()
        if not response.content.startswith(b"SIMPLE"):
            raise ValueError("Expected a FITS cutout")
        path.write_bytes(response.content)
    record = dict(midpoint=mid.isot, minutes=duration, endpoint_midpoint_endpoint=positions, cutout=params, location=site)
    (folder / (name+".json")).write_text(json.dumps(record, indent=2)+"\n")
    gaia(folder, "hd", ra, dec)
    apass = folder/"hd-apass.csv"
    if not apass.exists():
        rows = archive("dasch/dr7/querycat", dict(refcat="apass", ra_deg=ra, dec_deg=dec, radius_arcsec=1200))
        apass.write_text("\n".join(rows)+"\n")
    result = experiment([Plate(folder, name)], True)
    result.update(inputs={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(folder.iterdir()) if p.is_file()},
                  archive_id=plate, start=start.isot, end=end.isot)
    return result


if __name__ == "__main__":
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("data", type=Path)
    ap.add_argument("plate", choices=["B3383a","B3384b"])
    args=ap.parse_args()
    print(json.dumps(measure(args.data / args.plate, args.plate), indent=2, allow_nan=False))
