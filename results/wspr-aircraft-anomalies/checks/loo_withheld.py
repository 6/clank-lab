"""Leave one date out with its aircraft withheld everywhere (review round 56). Not part of the
frozen test; uses sens.py's estimator, resampling scheme and verdict unchanged.

usage: loo_withheld.py OUT.json PER_DATE_SUMS.csv units-DAY.npz ...

sens.py's deletion drops one date's sums but keeps that date's aircraft in its neighbors'
placebo labels. Here, deleting date X also removes X's fleet from the analysis: a remaining
date whose next (placebo 1) or previous (placebo 2) placebo fleet is X's uses its other
placebo's sums for both. The units files supply each date's placebo dates.
"""
import sys, os, json, csv
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import analyze as A
import sens

def main(out, sums_csv, paths):
    pl = {}
    for p in paths:
        D = np.load(p, allow_pickle=False)
        pl[str(D["day"])] = [str(x) for x in D["placebo_days"]]
    rows = list(csv.DictReader(open(sums_csv)))
    days = [r["day"] for r in rows]
    assert days == sorted(days) and set(days) == set(pl)
    keys = [(a, k, p) for a in ("real", "planted") for k in "WM" for p in sens.LABELS]
    base = {key: np.array([[float(r[f"{key[0]}_{key[1]}_{key[2] or 'real'}_sumd"]),
                            float(r[f"{key[0]}_{key[1]}_{key[2] or 'real'}_n"])] for r in rows]) for key in keys}
    n = len(days); res = {}
    for i, X in enumerate(days):
        keep = [j for j in range(n) if j != i]
        S = {key: v[keep].copy() for key, v in base.items()}
        swapped = []
        for jj, j in enumerate(keep):
            p1, p2 = pl[days[j]]
            for a in ("real", "planted"):
                for k in "WM":
                    if p1 == X:
                        S[(a, k, "p1")][jj] = S[(a, k, "p2")][jj]
                    if p2 == X:
                        S[(a, k, "p2")][jj] = S[(a, k, "p1")][jj]
            if X in (p1, p2):
                swapped.append(days[j])
        idx = np.random.default_rng(A.SEED).integers(0, n - 1, (A.NBOOT, n - 1))
        r = sens.summarize(S, idx)
        res[X] = dict(result=sens.jsonable(r), verdict=sens.verdict(r), placebo_replaced_on=swapped)
    W_hi = {d: v["result"]["real_W"]["hi"] for d, v in res.items()}
    M_hi = {d: v["result"]["real_M"]["hi"] for d, v in res.items()}
    P_lo = {d: min(v["result"]["planted_W"]["lo"], v["result"]["planted_M"]["lo"]) for d, v in res.items()}
    summary = dict(n_dates=n, verdicts=sorted(set(v["verdict"] for v in res.values())),
                   W_upper_max=[max(W_hi.values()), max(W_hi, key=W_hi.get)],
                   M_upper_max=[max(M_hi.values()), max(M_hi, key=M_hi.get)],
                   planted_lower_min=[min(P_lo.values()), min(P_lo, key=P_lo.get)])
    json.dump(dict(summary=summary, deletions=res), open(out, "w"), indent=1)
    print(json.dumps(summary))

if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2], sys.argv[3:])
