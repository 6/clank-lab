"""Frozen analysis (protocol-frozen.txt sections 5-7).

usage: analyze.py OUT_DIR units-DAY.npz ...
Writes OUT_DIR/results.json and prints the summary table and the verdict.
"""
import sys, os, json
import numpy as np

FAR_HIGH, FAR_ANY, U_BOUND, NBOOT, SEED = 25.0, 5.0, 0.02, 10000, 20261121
W_MIN, M_LO, M_HI = 1800, 0.8, 1.25

def load(paths):
    return [dict(np.load(p, allow_pickle=False)) for p in paths]

def flags(z, thr, which="any"):
    s, f, d = np.abs(z[:, 1]) > thr, np.abs(z[:, 2]) > thr, z[:, 3] > 0
    return {"any": s | f | d, "snr": s, "freq": f, "drift": d}[which].astype(float)

def design_w(D, crossed, unc, y):
    """Same link (tx, rx, band), uncrossed slots within +-30 min."""
    link = np.rec.fromarrays([D["tx"], D["rx"], D["band"]])
    _, lid = np.unique(link, return_inverse=True)
    o = np.lexsort((D["t"], lid)); key = lid[o].astype(np.int64) * 10**10 + (D["t"][o] - D["t"].min())
    lo = np.searchsorted(key, key - W_MIN, "left"); hi = np.searchsorted(key, key + W_MIN, "right")
    cu = np.concatenate([[0.0], np.cumsum(unc[o])]); cy = np.concatenate([[0.0], np.cumsum(unc[o] * y[o])])
    nc = cu[hi] - cu[lo]; sy = cy[hi] - cy[lo]
    c = crossed[o] & (nc > 0)
    return y[o][c] - sy[c] / nc[c], int(nc[c].sum())

def design_m(D, crossed, unc, y):
    """Same slot and band, sharing tx or rx, path length within [0.8, 1.25], uncrossed, other link."""
    groups = {}
    for i in np.nonzero(unc)[0]:
        for side in ("tx", "rx"):
            groups.setdefault((side, D["t"][i], D["band"][i], D[side][i]), []).append(i)
    d, ncon = [], 0
    # only crossed units sharing a (slot, band, station) group with some uncrossed unit can match
    cand_i = np.zeros(len(crossed), bool)
    for side in ("tx", "rx"):
        key = np.rec.fromarrays([D["t"], D["band"], D[side]])
        _, kid = np.unique(key, return_inverse=True)
        cand_i |= np.isin(kid, kid[unc])
    for i in np.nonzero(crossed & cand_i)[0]:
        cand = set(groups.get(("tx", D["t"][i], D["band"][i], D["tx"][i]), [])) | \
               set(groups.get(("rx", D["t"][i], D["band"][i], D["rx"][i]), []))
        c = [j for j in cand if not (D["tx"][j] == D["tx"][i] and D["rx"][j] == D["rx"][i])
             and M_LO <= D["length"][j] / D["length"][i] <= M_HI]
        if c:
            d.append(y[i] - y[c].mean()); ncon += len(c)
    return np.array(d), ncon

def unit_sets(D, p, rc, cross_set, cover, band):
    have, dh, da, cov = D[p + "have"], D[p + "dh"], D[p + "da"], D[p + "cov"]
    base = have & (cov if cover else True)
    dist = dh if cross_set == "high" else da
    if band is None:
        crossed = base & (dist <= rc)
    else:
        crossed = base & (dist >= band[0]) & (dist < band[1])
    unc = base & (dh >= FAR_HIGH) & (da >= FAR_ANY)
    return crossed, unc

def ci(bs):
    lo, hi = np.nanpercentile(bs, [2.5, 97.5])
    return float(lo), float(hi)

def run(days, anom="real", thr=0.75, which="any", rc=5.0, cross_set="high", cover=True, band=None, value="flag"):
    """Excess E for the real labels and both placebos, and the primary statistic
    Delta = E_real - (E_p1 + E_p2) / 2, per design, with day-bootstrap intervals."""
    sums = {(k, p): np.zeros((len(days), 2)) for k in "WM" for p in ("", "p1", "p2")}
    ncon = {(k, p): 0 for k in "WM" for p in ("", "p1", "p2")}
    for di, D in enumerate(days):
        z = D[anom]
        y = flags(z, thr, which) if value == "flag" else np.abs(z[:, 1])
        for p in ("", "p1", "p2"):
            crossed, unc = unit_sets(D, p, rc, cross_set, cover, band)
            for k, fn in (("W", design_w), ("M", design_m)):
                d, nc = fn(D, crossed, unc.astype(float) if k == "W" else unc, y)
                sums[(k, p)][di] = (d.sum(), len(d)); ncon[(k, p)] += nc
    rng = np.random.default_rng(SEED)
    idx = rng.integers(0, len(days), (NBOOT, len(days)))
    out = {}
    with np.errstate(invalid="ignore", divide="ignore"):
        for k in "WM":
            r = {}
            boots = {}
            for p, name in (("", "real"), ("p1", "placebo1"), ("p2", "placebo2")):
                S = sums[(k, p)]
                E = S[:, 0].sum() / S[:, 1].sum() if S[:, 1].sum() else float("nan")
                boots[p] = S[idx, 0].sum(1) / S[idx, 1].sum(1)
                lo, hi = ci(boots[p])
                r[name] = dict(E=float(E), lo=lo, hi=hi, n_crossed=int(S[:, 1].sum()), n_controls=ncon[(k, p)],
                               days_with_units=int((S[:, 1] > 0).sum()))
            Ep = (r["placebo1"]["E"] + r["placebo2"]["E"]) / 2
            lo, hi = ci(boots[""] - (boots["p1"] + boots["p2"]) / 2)
            r["delta"] = dict(E=r["real"]["E"] - Ep, lo=lo, hi=hi)
            out[k] = r
    return out

def base_rates(days):
    """Anomaly rate among primary crossed and uncrossed units (operating point)."""
    a = {"crossed": [0, 0], "uncrossed": [0, 0]}
    for D in days:
        base = D["have"] & D["cov"]; y = flags(D["real"], 0.75)
        for k, m in (("crossed", base & (D["dh"] <= 5.0)), ("uncrossed", base & (D["dh"] >= FAR_HIGH) & (D["da"] >= FAR_ANY))):
            a[k][0] += int(m.sum()); a[k][1] += float(y[m].sum())
    return {k: dict(units=v[0], anomaly_rate=v[1] / v[0] if v[0] else None) for k, v in a.items()}

VARIANTS = {
    "primary": {},
    "planted": {"anom": "planted"},
    "threshold_1.0sd": {"thr": 1.0},
    "snr_only": {"which": "snr"}, "freq_only": {"which": "freq"}, "drift_only": {"which": "drift"},
    "radius_1nmi": {"rc": 1.852},
    "any_airborne": {"cross_set": "any"},
    "no_coverage_mask": {"cover": False},
    "abs_z_snr": {"value": "absz"},
    "dose_0_2": {"band": (0.0, 2.0)}, "dose_2_5": {"band": (2.0, 5.0)}, "dose_5_10": {"band": (5.0, 10.0)},
    "dose_10_25": {"band": (10.0, 25.0)},
}

def verdict(res):
    P, L = res["primary"], res["planted"]
    if not (L["W"]["delta"]["lo"] > 0 and L["M"]["delta"]["lo"] > 0):
        return "INCONCLUSIVE (planted control not recovered)"
    if P["W"]["delta"]["lo"] > 0 and P["M"]["delta"]["lo"] > 0:
        small = max(P["W"]["delta"]["hi"], P["M"]["delta"]["hi"]) < U_BOUND
        return "POSITIVE" + (" (excess under 2 per 100)" if small else "")
    if P["W"]["delta"]["hi"] < U_BOUND and P["M"]["delta"]["hi"] < U_BOUND:
        return "NEGATIVE (excess under 2 per 100 crossed link-slots in both designs)"
    return "INCONCLUSIVE"

if __name__ == "__main__":
    outdir, paths = sys.argv[1], sorted(sys.argv[2:])
    days = load(paths)
    res = {name: run(days, **kw) for name, kw in VARIANTS.items()}
    res["operating_point"] = base_rates(days)
    res["verdict"] = verdict(res)
    res["days"] = [str(D["day"]) for D in days]
    os.makedirs(outdir, exist_ok=True)
    json.dump(res, open(os.path.join(outdir, "results.json"), "w"), indent=1, sort_keys=True)
    print(f"{'variant':16s} {'des':3s} {'set':8s} {'E/100':>7s} {'95% CI':>17s} {'crossed':>8s} {'controls':>9s}")
    for name in VARIANTS:
        for k in "WM":
            for p in ("real", "placebo1", "placebo2", "delta"):
                r = res[name][k][p]
                extra = f" {r['n_crossed']:8d} {r['n_controls']:9d}" if p != "delta" else ""
                print(f"{name:16s} {k:3s} {p:8s} {100*r['E']:7.2f} [{100*r['lo']:6.2f},{100*r['hi']:6.2f}]{extra}")
    print("operating point", res["operating_point"])
    print("VERDICT:", res["verdict"])
