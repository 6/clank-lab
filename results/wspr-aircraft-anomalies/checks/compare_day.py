"""Compare one replayed day's counts with the recorded run (data/per_day.csv).

usage: compare_day.py units-DAY.npz per_day.csv
Exits 1 if a count differs by more than 1% (the WSPR mirror can gain late spots).
"""
import sys, csv
import numpy as np

U = np.load(sys.argv[1], allow_pickle=False); day = str(U["day"])
row = {r["day"]: r for r in csv.DictReader(open(sys.argv[2]))}[day]
have, cov = U["have"], U["have"] & U["cov"]
now = {"scored": int(have.sum()), "covered": int(cov.sum()),
       "crossed": int((cov & (U["dh"] <= 5)).sum()),
       "uncrossed": int((cov & (U["dh"] >= 25) & (U["da"] >= 5)).sum()),
       "placebo1_crossed": int((U["p1have"] & U["p1cov"] & (U["p1dh"] <= 5)).sum()),
       "placebo2_crossed": int((U["p2have"] & U["p2cov"] & (U["p2dh"] <= 5)).sum())}
bad = 0
for k, v in now.items():
    ref = int(row[k]); rel = abs(v - ref) / max(ref, 1)
    bad += rel > 0.01
    print(f"{day} {k:17s} recorded {ref:9d} replay {v:9d} ({100 * rel:.2f}%)")
sys.exit(1 if bad else 0)
