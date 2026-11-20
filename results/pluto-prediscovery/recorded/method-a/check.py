"""Check either archived clock experiment against its public-input reference."""
import argparse
import hashlib
import json
import math
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def need(condition, message):
    if not condition:
        raise ValueError(message)


def check(observed):
    reference = None
    for name in ("corrected-pair.json","pair.json"):
        trial = json.loads((ROOT.parent.parent/"data"/"recorded"/name).read_text())
        if observed["inputs"] == trial["inputs"]:
            reference = trial
            break
    need(reference is not None, "public input hashes differ")
    need(reference["code"] == observed["code"] == hashlib.sha256((ROOT/"measure.py").read_bytes()).hexdigest(),
         "measurement code differs")
    need([p["name"] for p in observed["plates"]] == ["ma00731","ma00733"], "plate IDs")
    need(observed["joint_null"] == 0, "unexpected joint trigger")
    repaired = name == "corrected-pair.json"
    for p,ref in zip(observed["plates"],reference["plates"],strict=True):
        need(p["n_null"] == 200 and p["eligible"] == ref["eligible"], "translated track count")
        need(p["trigger"] is repaired and (p["score"]>p["null_threshold"]) == repaired, "target trigger")
        need(p["null_at_least"] == ref["null_at_least"], "target rank")
        need(p["recovery"] == ref["recovery"] and p["native"] == ref["native"], "recovery counts")
        keys = ["score","opposite_score","null_threshold"]
        if repaired:
            keys.append("inferred_B")
            need(p["opposite_score"] < p["null_threshold"], "stationary-site veto")
            need(abs(p["inferred_B"]-16.33) <= .45, "photometry")
            need(1.44*math.hypot(*p["free_offset_px"]) < 6, "centroid")
            # The unconstrained fit is less reproducible numerically than a forced score.
            need(math.dist(p["free_offset_px"],ref["free_offset_px"]) < .02, "free centroid replay")
        for k in keys:
            need(math.isclose(p[k],ref[k],rel_tol=1e-6,abs_tol=1e-5),k)
        depth = max(float(m) for m,n in p["recovery"].items() if n>=160)
        print(p["name"], "trigger" if repaired else "archive-clock miss", f"score {p['score']:.2f}, depth B={depth:g}")
    if repaired:
        # The two detector residual lengths bound the sky-vector error by the triangle inequality.
        need(sum(1.45*math.hypot(*r["free_offset_px"]) for r in observed["plates"]) < 8, "motion")


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("measurement",nargs="?",type=Path,default=ROOT.parent.parent/"data"/"recorded"/"corrected-pair.json")
    check(json.loads(ap.parse_args().measurement.read_text()))
