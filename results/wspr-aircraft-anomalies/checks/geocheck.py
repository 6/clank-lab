"""Cutoff-geometry check added after the frozen test (checks/README.md,
"Sensitivity runs"). Not part of the frozen test.

usage: geocheck.py UNITS.npz DATA_DIR SEED N_PER_CLASS OUT.jsonl

Reference: check.py's nearest(), which uses no candidate screen, no distance
cap before the comparison, no sign-change step and no along-track guard. It
takes every aircraft in the three raw ADS-B Exchange snapshots of the slot
(downloaded again; cached per snapshot here) at 1-s sampling over seconds
1-111. For real labels only, units are drawn at random in four classes of
covered, scored units:
  near5_h   high-track distance dh in [3, 7] km (the crossing cutoff)
  near25_h  dh in [23, 27] km (the control cutoff for high tracks)
  near5_a   any-airborne distance da in [3, 7] km (the control cutoff for any aircraft)
  control   primary controls (dh >= 25 and da >= 5) that some crossed unit uses
            in design W or M (the false-control risk the reader named)
Each unit is written with the pipeline's and the reference's distances and its
class under each (crossed / control / neither).
"""
import sys, os, json, random, functools, csv, io, gzip, glob
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import check as C
import analyze as A

C.raw_snap = functools.lru_cache(maxsize=16)(C.raw_snap)   # units run in time order

def cls(h, a):
    if h <= 5.0: return "crossed"
    if h >= 25.0 and a >= 5.0: return "control"
    return "neither"

def used_controls(D):
    """Indices of primary controls used by some crossed unit in W or M (real labels)."""
    base = D["have"] & D["cov"]
    crossed = base & (D["dh"] <= 5.0); unc = base & (D["dh"] >= 25.0) & (D["da"] >= 5.0)
    used = np.zeros(len(crossed), bool)
    # W: an uncrossed unit within +-30 min of a crossed unit on the same link
    link = np.rec.fromarrays([D["tx"], D["rx"], D["band"]]); _, lid = np.unique(link, return_inverse=True)
    o = np.lexsort((D["t"], lid)); key = lid[o].astype(np.int64) * 10**10 + (D["t"][o] - D["t"].min())
    lo = np.searchsorted(key, key - A.W_MIN, "left"); hi = np.searchsorted(key, key + A.W_MIN, "right")
    cc = np.concatenate([[0], np.cumsum(crossed[o])])
    used[o[unc[o] & (cc[hi] - cc[lo] > 0)]] = True
    # M: same slot and band, sharing a station, other link, length ratio in [0.8, 1.25]
    for side in ("tx", "rx"):
        key = np.rec.fromarrays([D["t"], D["band"], D[side]]); _, kid = np.unique(key, return_inverse=True)
        shared = np.isin(kid, kid[crossed]) & unc
        for j in np.nonzero(shared)[0]:
            ic = np.nonzero((kid == kid[j]) & crossed)[0]
            r = D["length"][j] / D["length"][ic]
            ok = (r >= A.M_LO) & (r <= A.M_HI) & ~((D["tx"][ic] == D["tx"][j]) & (D["rx"][ic] == D["rx"][j]))
            if ok.any(): used[j] = True
    return used

if __name__ == "__main__":
    units, data, seed, n, out = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), sys.argv[5]
    D = dict(np.load(units, allow_pickle=False)); day = str(D["day"])
    rng = random.Random(seed)
    base = D["have"] & D["cov"]
    pools = {"near5_h": base & (D["dh"] >= 3) & (D["dh"] <= 7), "near25_h": base & (D["dh"] >= 23) & (D["dh"] <= 27),
             "near5_a": base & (D["da"] >= 3) & (D["da"] <= 7), "control": used_controls(D)}
    pick = []
    for c, m in pools.items():
        idx = list(np.nonzero(m)[0]); pick += [(c, int(i)) for i in rng.sample(idx, min(n, len(idx)))]
    print(day, {c: int(m.sum()) for c, m in pools.items()}, flush=True)
    txl = {}
    for f in sorted(glob.glob(os.path.join(data, "wspr", day, "*.csv.gz"))):
        for r in csv.reader(io.TextIOWrapper(gzip.open(f), "utf-8")):
            txl[(r[2].upper(), "tx")] = r[3].upper(); txl[(r[4].upper(), "rx")] = r[5].upper()
    done = set()
    if os.path.exists(out):
        done = {(r["class"], r["unit"]) for r in map(json.loads, open(out)) if r["day"] == day}
    with open(out, "a") as f:
        for c, i in sorted(pick, key=lambda x: D["t"][x[1]]):   # time order: snapshots are reused
            if (c, i) in done: continue
            h, a = C.nearest(day, int(D["t"][i]), txl[(str(D["tx"][i]), "tx")], txl[(str(D["rx"][i]), "rx")])
            h, a = min(h, C.CAP), min(a, C.CAP)
            rec = dict(day=day, cls=c, unit=i, dh=float(D["dh"][i]), da=float(D["da"][i]), ref_dh=h, ref_da=a,
                       label=cls(D["dh"][i], D["da"][i]), ref_label=cls(h, a), length=float(D["length"][i]))
            rec["class"] = rec.pop("cls")
            f.write(json.dumps(rec) + "\n"); f.flush()
