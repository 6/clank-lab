"""Build the original December field inputs with only the two asteroid-derived clocks changed."""
import argparse
from datetime import datetime, timedelta
import json
from pathlib import Path
import shutil

from fetch import geometry


def correct(raw, out, clocks):
    if raw.resolve() == out.resolve():
        raise ValueError("Give a separate output directory for corrected geometry")
    out.mkdir(parents=True, exist_ok=True)
    for name in ["ma00731.fits","ma00733.fits","ma-gaia.csv","ma-apass.csv"]:
        shutil.copyfile(raw/name, out/name)
    for clock in clocks:
        r = json.loads(clock.read_text())
        name = r["plate"]
        if r["asteroid"] != "179" or name not in ("ma00731","ma00733"):
            raise ValueError("Expected the primary clock trail")
        rec = json.loads((raw/(name+".json")).read_text())
        assert r["header_midpoint"] == rec["midpoint"]
        # The plate cannot support timing to seconds. Round its image midpoint
        # to the nearest minute before querying the planetary ephemeris.
        inferred = datetime.fromisoformat(r["measured_midpoint_UT1"])+timedelta(seconds=30)
        rec["midpoint"] = inferred.replace(second=0,microsecond=0).isoformat()+"Z"
        rec["endpoint_midpoint_endpoint"] = geometry(rec["midpoint"],rec["minutes"],rec["location"])
        (out/(name+".json")).write_text(json.dumps(rec,indent=2)+"\n")


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("raw",type=Path)
    ap.add_argument("corrected",type=Path)
    ap.add_argument("primary_clocks",type=Path,nargs=2)
    args = ap.parse_args()
    correct(args.raw,args.corrected,args.primary_clocks)
