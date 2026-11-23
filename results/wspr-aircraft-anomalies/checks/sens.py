"""Sensitivity runs added after the frozen test (checks/README.md, "Sensitivity
runs"). Not part of the frozen test: the frozen verdict stays the one analyze.py
gives. Uses analyze.py's own designs and estimator unchanged.

usage: sens.py OUT_DIR units-DAY.npz ...
Writes OUT_DIR/sens.json and OUT_DIR/per_date_sums.csv and prints a summary.

Variants (primary flag and planted control each; verdict by analyze.verdict):
  frozen    the frozen analysis (must reproduce results.json's primary and planted)
  slotkey   designs match on the two-minute slot start (t // 120 * 120), not the
            exact spot time
  oddrop    spots whose time is not on an even minute are dropped from the units
  strict    controls need dh > 25 km and da > 5 km (strict), not >=
  all3      slotkey, oddrop and strict together
Dependence (on the frozen per-date sums):
  leave one date out: Delta and its day-bootstrap interval on the other 35 dates,
            and the verdict, for each date
  cyclic moving-block bootstrap over the date-sorted sample, block lengths 2, 3,
            4 and 6 dates (adjacent dates share ADS-B through the placebos)
"""
import sys, os, json
from multiprocessing import Pool
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import analyze as A

LABELS = ("", "p1", "p2")
VARS = {"frozen": dict(), "slotkey": dict(slot=True), "oddrop": dict(odd=True),
        "strict": dict(strict=True), "all3": dict(slot=True, odd=True, strict=True)}

def day_sums(args):
    """Per-date (sum d, n crossed with controls, n controls) for W and M, three label sets,
    flag 'primary' (real) and 'planted', under one variant."""
    path, opt = args
    D = dict(np.load(path, allow_pickle=False))
    # the odd-minute mask is taken from the reported times, before any slot keying (the first
    # version keyed first, so its "all3" kept every spot and equalled "slotkey"; review round 56)
    keep = (D["t"] % 120 == 0) if opt.get("odd") else np.ones(len(D["t"]), bool)
    if opt.get("slot"):
        D["t"] = D["t"] // 120 * 120
    out = {}
    for anom in ("real", "planted"):
        y = A.flags(D[anom], 0.75)
        for p in LABELS:
            have = D[p + "have"] & keep
            base = have & D[p + "cov"]
            crossed = base & (D[p + "dh"] <= 5.0)
            if opt.get("strict"):
                unc = base & (D[p + "dh"] > A.FAR_HIGH) & (D[p + "da"] > A.FAR_ANY)
            else:
                unc = base & (D[p + "dh"] >= A.FAR_HIGH) & (D[p + "da"] >= A.FAR_ANY)
            for k, fn in (("W", A.design_w), ("M", A.design_m)):
                d, nc = fn(D, crossed, unc.astype(float) if k == "W" else unc, y)
                out[(anom, k, p)] = (float(d.sum()), int(len(d)), int(nc))
    return str(D["day"]), out

def delta(S, idx):
    """S[label] = array (days, 2) of (sum d, n); idx = (draws, days) day indices."""
    with np.errstate(invalid="ignore", divide="ignore"):
        b = {p: S[p][idx, 0].sum(1) / S[p][idx, 1].sum(1) for p in LABELS}
    return b[""] - (b["p1"] + b["p2"]) / 2

def summarize(S, idx):
    """Point Delta and percentile 95% interval for each (anom, design)."""
    out = {}
    for anom in ("real", "planted"):
        for k in "WM":
            s = {p: S[(anom, k, p)] for p in LABELS}
            pt = {p: s[p][:, 0].sum() / s[p][:, 1].sum() for p in LABELS}
            lo, hi = np.nanpercentile(delta(s, idx), [2.5, 97.5])
            out[(anom, k)] = dict(E=float(pt[""] - (pt["p1"] + pt["p2"]) / 2), lo=float(lo), hi=float(hi),
                                  n_crossed=int(s[""][:, 1].sum()))
    return out

def verdict(r):
    res = {"primary": {k: {"delta": r[("real", k)]} for k in "WM"},
           "planted": {k: {"delta": r[("planted", k)]} for k in "WM"}}
    return A.verdict(res)

def jsonable(r):
    return {f"{a}_{k}": v for (a, k), v in r.items()}

def block_idx(n, L, draws, rng):
    """Cyclic moving-block bootstrap indices: ceil(n/L) blocks of L consecutive dates."""
    nb = -(-n // L)
    starts = rng.integers(0, n, (draws, nb))
    idx = (starts[:, :, None] + np.arange(L)[None, None, :]) % n
    return idx.reshape(draws, nb * L)[:, :n]

if __name__ == "__main__":
    outdir, paths = sys.argv[1], sorted(sys.argv[2:])
    jobs = int(os.environ.get("JOBS", "2"))
    os.makedirs(outdir, exist_ok=True)
    n = len(paths)
    iid = np.random.default_rng(A.SEED).integers(0, n, (A.NBOOT, n))   # analyze.py's draws
    res = {"variants": {}, "days": None}
    sums = {}
    with Pool(jobs) as pool:
        for name, opt in VARS.items():
            ck = os.path.join(outdir, f"ckpt-{name}.json")   # checkpoint per variant (resumable)
            if os.path.exists(ck):
                got = [(d, {tuple(k.split("|")): tuple(v) for k, v in o.items()}) for d, o in json.load(open(ck))]
            else:
                got = sorted(pool.map(day_sums, [(p, opt) for p in paths]))
                json.dump([(d, {"|".join(k): v for k, v in o.items()}) for d, o in got], open(ck + ".tmp", "w"))
                os.replace(ck + ".tmp", ck)
            days = [g[0] for g in got]
            res["days"] = days
            S = {key: np.array([[g[1][key][0], g[1][key][1]] for g in got]) for key in got[0][1]}
            C = {key: sum(g[1][key][2] for g in got) for key in got[0][1]}
            sums[name] = (S, C, got)
            r = summarize(S, iid)
            res["variants"][name] = dict(result=jsonable(r), verdict=verdict(r),
                                         controls={f"{a}_{k}_{p or 'real'}": C[(a, k, p)] for (a, k, p) in C})
            print(f"{name:8s}", " ".join(f"{a[:4]}-{k} {100*v['E']:+.2f} [{100*v['lo']:+.2f},{100*v['hi']:+.2f}] n={v['n_crossed']}"
                                        for (a, k), v in r.items()), "|", verdict(r), flush=True)
    # per-date sums of the frozen run
    S, C, got = sums["frozen"]
    with open(os.path.join(outdir, "per_date_sums.csv"), "w") as f:
        cols = [(a, k, p) for a in ("real", "planted") for k in "WM" for p in LABELS]
        f.write("day," + ",".join(f"{a}_{k}_{p or 'real'}_{q}" for (a, k, p) in cols for q in ("sumd", "n", "controls")) + "\n")
        for g in got:
            f.write(g[0] + "," + ",".join(f"{g[1][c][0]:.6f},{g[1][c][1]},{g[1][c][2]}" for c in cols) + "\n")
    # leave one date out (analyze.py's draw scheme on the remaining 35 dates)
    loo = {}
    for i, d in enumerate(res["days"]):
        keep = [j for j in range(n) if j != i]
        Si = {key: v[keep] for key, v in S.items()}
        idx = np.random.default_rng(A.SEED).integers(0, n - 1, (A.NBOOT, n - 1))
        r = summarize(Si, idx)
        loo[d] = dict(result=jsonable(r), verdict=verdict(r))
    res["leave_one_out"] = loo
    W_hi = {d: v["result"]["real_W"]["hi"] for d, v in loo.items()}
    M_hi = {d: v["result"]["real_M"]["hi"] for d, v in loo.items()}
    print("LOO W upper max", max(W_hi.values()) * 100, max(W_hi, key=W_hi.get),
          "| M upper max", max(M_hi.values()) * 100, max(M_hi, key=M_hi.get))
    print("LOO verdicts", sorted(set(v["verdict"] for v in loo.values())))
    # adjacent-date dependence: cyclic moving-block bootstrap
    blk = {}
    for L in (2, 3, 4, 6):
        idx = block_idx(n, L, A.NBOOT, np.random.default_rng(A.SEED + L))
        r = summarize(S, idx)
        blk[str(L)] = dict(result=jsonable(r), verdict=verdict(r))
        print(f"block {L}", " ".join(f"{a[:4]}-{k} [{100*v['lo']:+.2f},{100*v['hi']:+.2f}]" for (a, k), v in r.items()),
              "|", verdict(r), flush=True)
    res["block_bootstrap"] = blk
    json.dump(res, open(os.path.join(outdir, "sens.json"), "w"), indent=1, sort_keys=True)
