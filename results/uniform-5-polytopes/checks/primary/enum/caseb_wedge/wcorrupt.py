"""Deliberate corruptions: each must turn a CERTIFIED fan into not certified.

    python3 wcorrupt.py      # exit 0 iff the baselines certify and every corruption fails
"""
import sys
import time

from flint import arb

import wrun

CASES = [
    # (description, fan, keyword arguments of wrun.certify)
    ("baseline", "i:4,6,10", {}),
    ("drop the separation constraints |p - x| >= 1", "i:4,6,10", dict(drop=("separation",))),
    ("threshold 1.80 instead of 2cos(pi/17)", "i:4,6,10", dict(L2override=arb("1.80") ** 2)),
    ("threshold 1.91 (just below the float maximum 1.9215)", "i:4,6,10",
     dict(L2override=arb("1.91") ** 2)),
    ("baseline", "ii:5", {}),
    ("drop the fan-facet constraints", "ii:5", dict(drop=("facet",))),
    ("baseline", "iii:3,5", {}),
    ("threshold 1.80 (float maximum 1.884)", "iii:3,5", dict(L2override=arb("1.80") ** 2)),
]


def main():
    ok = True
    for desc, fid, kw in CASES:
        t0 = time.process_time()
        F = wrun.build(fid)
        res = wrun.certify(F, time_budget=300, **kw)
        good = (res["status"] == "CERTIFIED") == (desc == "baseline")
        ok &= good
        why = res["failures"][0]["kind"] if res["failures"] else ""
        print("%-9s %-55s %-10s %-9s %5.1fs %s" % (fid, desc, res["status"], "ok" if good else "WRONG",
                                                  time.process_time() - t0, why), flush=True)
    print("corruptions:", "all behave as required" if ok else "SOME CORRUPTION NOT DETECTED")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
