"""Exact-arithmetic check of the SNR and frequency flags (review round finding on prep.py's
floating-point variance). Not part of the frozen test; it reuses prep.py's loading, cleaning
and window definition unchanged.

usage: exactflags.py DAY DATA_DIR UNITS.npz OUT.json

prep.py computes |z| > 0.75 from exact integer window sums converted to float64. Here the
same comparison is made in exact integer arithmetic:
    |z| > 0.75  <=>  16 (n v - S1)^2 (n - 1) > 9 n (n S2 - S1^2),
with no flag when n S2 - S1^2 = 0 (zero variance), for every unit's SNR and frequency score,
with the real SNR and with the planted SNR (the units file's plant mask). Python integers are
used wherever int64 could overflow. It reports, for each score, the number of units whose
exact flag differs from prep.py's stored flag, and the number of exact ties (|z| = 0.75).
"""
import sys, os, json
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import prep as P

def exact(W, v_int):
    trip = np.rec.fromarrays([W["tx"], W["rx"], W["band"]])
    _, tid = np.unique(trip, return_inverse=True)
    o = np.lexsort((W["t"], tid)); tid_s, t_s = tid[o], W["t"][o]
    key = tid_s.astype(np.int64) * 10**10 + (t_s - t_s.min())
    lo = np.searchsorted(key, key - 3 * 3600, "left"); hi = np.searchsorted(key, key + 3 * 3600, "right")
    n = (hi - lo).astype(np.int64)
    v = v_int[o].astype(object)            # Python integers: exact, no overflow
    c1 = np.concatenate([[0], np.cumsum(v)]).astype(object)
    c2 = np.concatenate([[0], np.cumsum(v * v)]).astype(object)
    s1 = c1[hi] - c1[lo]; s2 = c2[hi] - c2[lo]
    no = n.astype(object)
    a = no * v - s1
    b = no * s2 - s1 * s1
    lhs = 16 * a * a * (no - 1); rhs = 9 * no * b
    flag = np.array([(bb > 0) and (l > r) for l, r, bb in zip(lhs, rhs, b)], bool)
    tie = np.array([(bb > 0) and (l == r) for l, r, bb in zip(lhs, rhs, b)], bool)
    back = np.empty_like(o); back[o] = np.arange(len(o))
    return flag[back], tie[back], n[back]

def main(day, data, units, out):
    W, _ = P.clean(P.load_wspr(day, data))
    d = int(P.dt.datetime.fromisoformat(day).replace(tzinfo=P.dt.timezone.utc).timestamp())
    rel = W["t"] - d
    blk = np.full(len(rel), -1)
    for H in P.BLOCK_HOURS:
        m = (rel >= H * 3600) & (rel < H * 3600 + 3600)
        blk[m] = H * 100 + (rel[m] - H * 3600) // 120
    lat_t, lon_t = np.array([P.loc_latlon(l) for l in W["txl"]]).T
    lat_r, lon_r = np.array([P.loc_latlon(l) for l in W["rxl"]]).T
    A, B = P.xyz(lat_t, lon_t), P.xyz(lat_r, lon_r)
    length = np.arctan2(np.linalg.norm(np.cross(A, B), axis=1), np.einsum("ij,ij->i", A, B)) * P.RE
    snr = np.rint(W["snr"]).astype(np.int64); assert np.array_equal(snr, W["snr"])
    f = W["f"].astype(np.int64)
    trip = np.rec.fromarrays([W["tx"], W["rx"], W["band"]]); _, tid = np.unique(trip, return_inverse=True)
    o = np.lexsort((W["t"], tid)); tid_s = tid[o]
    first = np.r_[True, tid_s[1:] != tid_s[:-1]]
    ref_s = f[o][np.maximum.accumulate(np.where(first, np.arange(len(f)), 0))]
    ref = np.empty_like(f); ref[o] = ref_s
    fs, ts, n = exact(W, snr)
    ff, tf, _ = exact(W, f - ref)
    unit = (blk >= 0) & (length >= 100.0) & (n >= 5)
    ui = np.nonzero(unit)[0]
    U = dict(np.load(units, allow_pickle=False))
    assert len(ui) == len(U["t"]) and np.array_equal(W["t"][ui], U["t"]), "units do not line up"
    plant = np.zeros(len(W["t"]), bool); plant[ui] = U["plant"]
    fp, tp, _ = exact(W, snr + P.PLANT_DB * plant)
    r = dict(day=day, units=int(len(ui)), max_abs_freq_offset=int(np.abs(f - ref).max()))
    for name, ex, tie, col, arr in (("snr_real", fs, ts, 1, "real"), ("freq_real", ff, tf, 2, "real"),
                                    ("snr_planted", fp, tp, 1, "planted"), ("freq_planted", ff, tf, 2, "planted")):
        stored = np.abs(U[arr][:, col]) > 0.75
        r[name] = dict(differ=int((stored != ex[ui]).sum()), ties=int(tie[ui].sum()),
                       flagged_exact=int(ex[ui].sum()), flagged_stored=int(stored.sum()))
    json.dump(r, open(out, "w"), indent=1)
    print(json.dumps(r))

if __name__ == "__main__":
    main(*sys.argv[1:5])
