"""Build the scored test units of one sample day.

usage: prep.py DAY PLACEBO_DAY_1 PLACEBO_DAY_2 DATA_DIR OUT.npz

For every valid WSPR spot in the 240 test slots of DAY (one-hour blocks
starting 00, 03, ..., 21 UTC, slots :00..:58), compute
  * the published GDTAAA anomaly flags (protocol-frozen.txt, section 3), on the real
    SNR and on the planted-control SNR;
  * crossing labels (section 4) from DAY's ADS-B snapshots (real) and from
    each placebo day's snapshots at the same UTC times (placebo 1, placebo 2).
"""
import sys, os, gzip, csv, io, re, glob, datetime as dt
import numpy as np

RE = 6371.0
BLOCK_HOURS = (0, 3, 6, 9, 12, 15, 18, 21)
R_CROSS, D_MAX = 5.0, 30.0   # km (distances are capped at D_MAX)
FL_PRIMARY = 20000.0                          # ft
COVER_FRAC = 0.25                             # of a block's 61 snapshots
PLANT_P, PLANT_DB, PLANT_SEED = 0.10, 6, 20261121
LOC = re.compile(r"^[A-R]{2}[0-9]{2}[A-X]{2}$")

# ---------------------------------------------------------------- WSPR ----
def load_wspr(day, data):
    cols = {k: [] for k in ("t", "band", "tx", "txl", "rx", "rxl", "f", "snr", "drift")}
    epoch = {}
    for f in sorted(glob.glob(os.path.join(data, "wspr", day, "*.csv.gz"))):
        r = csv.reader(io.TextIOWrapper(gzip.open(f), "utf-8")); head = next(r)
        assert head[:9] == ["time", "band", "tx_sign", "tx_loc", "rx_sign", "rx_loc", "frequency", "snr", "drift"], head
        for row in r:
            s = row[0]
            if s not in epoch:
                epoch[s] = int(dt.datetime.fromisoformat(s).replace(tzinfo=dt.timezone.utc).timestamp())
            cols["t"].append(epoch[s]); cols["band"].append(int(row[1]))
            cols["tx"].append(row[2].upper()); cols["txl"].append(row[3].upper())
            cols["rx"].append(row[4].upper()); cols["rxl"].append(row[5].upper())
            cols["f"].append(int(row[6])); cols["snr"].append(float(row[7])); cols["drift"].append(int(row[8]))
    return dict(t=np.array(cols["t"], np.int64), band=np.array(cols["band"]), tx=np.array(cols["tx"]),
                rx=np.array(cols["rx"]), txl=np.array(cols["txl"]), rxl=np.array(cols["rxl"]),
                f=np.array(cols["f"], np.int64), snr=np.array(cols["snr"]), drift=np.array(cols["drift"], np.int64))

def take(W, m):
    return {k: v[m] for k, v in W.items()}

def clean(W):
    n0 = len(W["t"])
    # exact duplicates
    key = np.rec.fromarrays([W["t"], W["band"], W["tx"], W["rx"], W["txl"], W["rxl"], W["f"], W["snr"], W["drift"]])
    _, first = np.unique(key, return_index=True)
    W = take(W, np.sort(first))
    # station filters: 6-character locators, no '/', no telemetry pseudo-calls, no mobile stations
    ok = np.array([bool(LOC.match(a)) and bool(LOC.match(b)) for a, b in zip(W["txl"], W["rxl"])])
    ok &= np.array(["/" not in a and "/" not in b and a[:1] not in "01Q" for a, b in zip(W["tx"], W["rx"])])
    locs = {}
    for c, l in zip(np.concatenate([W["tx"], W["rx"]]), np.concatenate([W["txl"], W["rxl"]])):
        locs.setdefault(c, set()).add(l)
    mobile = {c for c, s in locs.items() if len(s) > 1}
    ok &= np.array([a not in mobile and b not in mobile for a, b in zip(W["tx"], W["rx"])])
    W = take(W, ok)
    # ambiguous link-slots (several differing spots for one tx, rx, band, slot): drop all
    k2 = np.rec.fromarrays([W["t"], W["band"], W["tx"], W["rx"]])
    u, inv, cnt = np.unique(k2, return_inverse=True, return_counts=True)
    W = take(W, cnt[inv] == 1)
    return W, dict(rows=n0, kept=len(W["t"]), mobile_calls=len(mobile))

def loc_latlon(l):
    lon = (ord(l[0]) - 65) * 20 - 180 + int(l[2]) * 2 + (ord(l[4]) - 65) * (5 / 60) + 2.5 / 60
    lat = (ord(l[1]) - 65) * 10 - 90 + int(l[3]) + (ord(l[5]) - 65) * (2.5 / 60) + 1.25 / 60
    return lat, lon

def xyz(lat, lon):
    la, lo = np.radians(lat), np.radians(lon)
    return np.stack([np.cos(la) * np.cos(lo), np.cos(la) * np.sin(lo), np.sin(la)], -1)

def anomalies(W, snr):
    """GDTAAA flags for every spot of W given an SNR column (protocol-frozen.txt section 3)."""
    trip = np.rec.fromarrays([W["tx"], W["rx"], W["band"]])
    _, tid = np.unique(trip, return_inverse=True)
    o = np.lexsort((W["t"], tid)); tid_s, t_s = tid[o], W["t"][o]
    key = tid_s.astype(np.int64) * 10**10 + (t_s - t_s.min())
    lo = np.searchsorted(key, key - 3 * 3600, "left"); hi = np.searchsorted(key, key + 3 * 3600, "right")
    n = (hi - lo).astype(np.float64)
    def zscore(v):
        # exact integer window sums (SNR and frequency are integers): a float running sum loses
        # the small windows' variance after a triple with large values (bug found by check.py)
        vi = np.rint(v).astype(np.int64); assert np.array_equal(vi, v)
        c1 = np.concatenate([[0], np.cumsum(vi)]); c2 = np.concatenate([[0], np.cumsum(vi * vi)])
        s1 = (c1[hi] - c1[lo]).astype(np.float64); s2 = (c2[hi] - c2[lo]).astype(np.float64)
        with np.errstate(invalid="ignore", divide="ignore"):
            var = (s2 - s1 * s1 / n) / (n - 1)
            sd = np.sqrt(np.where(var > 1e-9, var, 0.0))
            z = np.where(sd > 0, (v - s1 / n) / sd, 0.0)
        return z
    v = snr[o]
    f = W["f"][o].astype(np.float64)
    # reference each triple's frequencies to its first value (precision of the running sums)
    first = np.r_[True, tid_s[1:] != tid_s[:-1]]; ref = f[np.maximum.accumulate(np.where(first, np.arange(len(f)), 0))]
    zs, zf = zscore(v), zscore(f - ref)
    nz = (W["drift"][o] != 0).astype(np.float64)
    cz = np.concatenate([[0.0], np.cumsum(nz)]); frac_nz = (cz[hi] - cz[lo]) / n
    back = np.empty_like(o); back[o] = np.arange(len(o))
    res = np.stack([n, zs, zf, ((nz > 0) & (frac_nz < 0.5)).astype(np.float64)], 1)
    return res[back]   # columns: n_window, z_snr, z_freq, drift_anomaly

# ---------------------------------------------------------------- ADS-B ----
def load_snap(adir, hhmm):
    f = os.path.join(adir, hhmm + ".npz")
    if not os.path.exists(f):
        return None
    z = np.load(f)
    return z["hex"], z["num"]

def tracks(snaps, t0):
    """Union of aircraft over the slot's three snapshots -> knot arrays."""
    idx = {}
    for s in snaps:
        for h in s[0]:
            idx.setdefault(h, len(idx))
    A = len(idx); TP = np.full((A, 3), np.nan); LAT = np.full((A, 3), np.nan); LON = np.full((A, 3), np.nan)
    GS = np.full((A, 3), np.nan); TRK = np.full((A, 3), np.nan); ALT = np.full((A, 3), np.nan)
    for k, (hx, num) in enumerate(snaps):
        ii = np.array([idx[h] for h in hx], dtype=np.int64)
        TP[ii, k] = num[:, 0] - t0; LAT[ii, k] = num[:, 1]; LON[ii, k] = num[:, 2]
        ALT[ii, k] = num[:, 3]; GS[ii, k] = num[:, 4]; TRK[ii, k] = num[:, 5]
    # the same stale report seen in two snapshots counts once
    for k in (1, 2):
        for j in range(k):
            dup = np.abs(TP[:, k] - TP[:, j]) < 1e-3
            TP[dup, k] = np.nan
    alt_any_high = np.nanmax(np.where(np.isnan(ALT), -np.inf, ALT), 1) >= FL_PRIMARY
    ground_only = np.all((ALT == -1) | np.isnan(TP), 1)
    return TP, xyz(LAT, LON), GS, TRK, alt_any_high, ~ground_only

def positions(TP, P, GS, TRK, taus):
    """Positions (len(taus), A, 3) by interpolation between knots, else dead reckoning <= 60 s."""
    A = TP.shape[0]; out = np.full((len(taus), A, 3), np.nan)
    for j, tau in enumerate(taus):
        d = TP - tau
        before = np.where(d <= 0, d, -np.inf); after = np.where(d >= 0, d, np.inf)
        kb = np.argmax(before, 1); ka = np.argmin(after, 1)
        hb = np.isfinite(before[np.arange(A), kb]); ha = np.isfinite(after[np.arange(A), ka])
        both = hb & ha
        tb, ta = TP[np.arange(A), kb], TP[np.arange(A), ka]
        w = np.where(both & (ta > tb), (tau - tb) / np.where(ta > tb, ta - tb, 1), 0.0)
        p = (1 - w)[:, None] * P[np.arange(A), kb] + w[:, None] * P[np.arange(A), ka]
        with np.errstate(invalid="ignore"):
            p /= np.linalg.norm(p, axis=1, keepdims=True)
        out[j, both] = p[both]
        one = ~both & (hb | ha)
        k = np.where(hb, kb, ka); dtk = tau - TP[np.arange(A), k]
        p0 = P[np.arange(A), k]; gs = GS[np.arange(A), k]; trk = np.radians(TRK[np.arange(A), k])
        dr = one & np.isfinite(gs) & np.isfinite(trk) & (np.abs(dtk) <= 60)
        st = one & ~dr & (np.abs(dtk) <= 15)
        lat = np.arcsin(np.clip(p0[:, 2], -1, 1)); lon = np.arctan2(p0[:, 1], p0[:, 0])
        north = np.stack([-np.sin(lat) * np.cos(lon), -np.sin(lat) * np.sin(lon), np.cos(lat)], 1)
        east = np.stack([-np.sin(lon), np.cos(lon), np.zeros_like(lon)], 1)
        u = np.cos(trk)[:, None] * north + np.sin(trk)[:, None] * east
        delta = np.nan_to_num(gs * 1.852 / 3600 * dtk / RE)
        q = np.cos(delta)[:, None] * p0 + np.sin(delta)[:, None] * np.nan_to_num(u)
        out[j, dr] = q[dr]; out[j, st] = p0[st]
    return out

def coverage(snaps):
    cnt = np.zeros((180, 360), np.int32)
    for hx, num in snaps:
        c = np.unique((np.floor(num[:, 1]) + 90).clip(0, 179).astype(int) * 360 + (np.floor(num[:, 2]) + 180).astype(int) % 360)
        cnt.flat[c] += 1
    return cnt >= COVER_FRAC * len(snaps)

def path_covered(a, b, theta, cov):
    n = max(2, int(np.ceil(theta * RE / 10)) + 1)
    s = np.linspace(0, 1, n)[:, None]
    pts = (np.sin((1 - s) * theta) * a + np.sin(s * theta) * b) / np.sin(theta)
    lat = np.degrees(np.arcsin(np.clip(pts[:, 2], -1, 1))); lon = np.degrees(np.arctan2(pts[:, 1], pts[:, 0]))
    return bool(cov[(np.floor(lat) + 90).clip(0, 179).astype(int), (np.floor(lon) + 180).astype(int) % 360].all())

def link_min_dist(A, B, Pt, high, airborne):
    """For links A->B (L,3) and aircraft positions Pt (T, M, 3), the minimum distance (km, capped
    at D_MAX) to the minor arc over the samples, for high-flying and for all airborne aircraft."""
    L = len(A); dh = np.full(L, D_MAX); da = np.full(L, D_MAX)
    N = np.cross(A, B); sth = np.linalg.norm(N, axis=1); N /= sth[:, None]
    theta = np.arctan2(sth, np.einsum("ij,ij->i", A, B))
    valid = np.isfinite(Pt[..., 0])
    # prefilter position: the mid sample, else any defined sample
    Pm = Pt[len(Pt) // 2].copy()
    for j in range(len(Pt)):
        m = ~np.isfinite(Pm[:, 0]) & valid[j]; Pm[m] = Pt[j, m]
    keep = np.isfinite(Pm[:, 0]) & airborne
    ai = np.nonzero(keep)[0]; Pm = Pm[ai]
    marg = (D_MAX + 60.0) / RE
    for c0 in range(0, L, 400):
        sl = slice(c0, min(L, c0 + 400))
        S = N[sl] @ Pm.T
        AL = np.arctan2(np.einsum("lk,mk->lm", np.cross(N[sl], A[sl]), Pm), A[sl] @ Pm.T)
        li, mj = np.nonzero((np.abs(S) < np.sin(marg)) & (AL > -marg) & (AL < theta[sl, None] + marg))
        if len(li) == 0:
            continue
        li = li + c0; m = ai[mj]
        n_, a_, th = N[li], A[li], theta[li]
        best = np.full(len(li), np.inf); prev_s = prev_al = None
        for j in range(len(Pt)):
            p = Pt[j, m]; ok = np.isfinite(p[:, 0]); p = np.nan_to_num(p)
            s = np.einsum("ik,ik->i", n_, p)
            al = np.arctan2(np.einsum("ik,ik->i", np.cross(n_, a_), p), np.einsum("ik,ik->i", a_, p))
            inarc = (al >= 0) & (al <= th)
            ang_a = np.arccos(np.clip(np.einsum("ik,ik->i", a_, p), -1, 1))
            ang_b = np.arccos(np.clip(np.einsum("ik,ik->i", B[li], p), -1, 1))
            d = np.where(inarc, np.arcsin(np.abs(np.clip(s, -1, 1))), np.minimum(ang_a, ang_b)) * RE
            best = np.where(ok, np.minimum(best, d), best)
            if prev_s is not None:
                okp = ok & prev_ok
                with np.errstate(invalid="ignore", divide="ignore"):
                    w = prev_s / (prev_s - s)
                alx = prev_al + w * (al - prev_al)
                cross = okp & (np.sign(s) != np.sign(prev_s)) & (alx >= 0) & (alx <= th) & (np.abs(al - prev_al) < 0.1)
                best = np.where(cross, 0.0, best)
            prev_s, prev_al, prev_ok = s, al, ok
        best = np.minimum(best, D_MAX)
        np.minimum.at(da, li, best)
        h = high[m]
        np.minimum.at(dh, li[h], best[h])
    return dh, da, theta

def label_day(U, adir, shift=0):
    """Labels for the test units U (dict with t, A, B) from the snapshots in adir; shift is
    (test day - ADS-B day) in seconds, so placebo snapshots are put on the test day's clock."""
    n = len(U["t"]); dh = np.full(n, np.nan); da = np.full(n, np.nan); cov = np.zeros(n, bool)
    have = np.zeros(n, bool); d0 = None
    for H in BLOCK_HOURS:
        hh = [f"{H + m // 60:02d}{m % 60:02d}" for m in range(61)]
        snaps = [load_snap(adir, x) for x in hh]
        present = [s for s in snaps if s is not None]
        if not present:
            continue
        cmask = coverage(present); pc_cache = {}
        for k in range(30):
            three = snaps[2 * k: 2 * k + 3]
            if any(s is None for s in three):
                continue
            sel = np.nonzero(U["slot_block"] == H * 100 + k)[0]
            if len(sel) == 0:
                continue
            t0 = U["t"][sel[0]]
            TP, P, GS, TRK, high, airborne = tracks(three, float(t0) - shift)
            taus = 1.0 + 5.0 * np.arange(23)
            Pt = positions(TP, P, GS, TRK, taus)
            h_, a_, th = link_min_dist(U["A"][sel], U["B"][sel], Pt, high, airborne)
            dh[sel], da[sel], have[sel] = h_, a_, True
            for i, s in enumerate(sel):
                key = (U["txl"][s], U["rxl"][s])
                if key not in pc_cache:
                    pc_cache[key] = path_covered(U["A"][s], U["B"][s], th[i], cmask)
                cov[s] = pc_cache[key]
    return dh, da, cov, have

def main(day, pday1, pday2, data, out):
    W, stats = clean(load_wspr(day, data))
    d = dt.datetime.fromisoformat(day).replace(tzinfo=dt.timezone.utc).timestamp()
    rel = W["t"] - int(d)
    blk = np.full(len(rel), -1)
    for H in BLOCK_HOURS:
        m = (rel >= H * 3600) & (rel < H * 3600 + 3600)
        blk[m] = H * 100 + (rel[m] - H * 3600) // 120
    lat_t, lon_t = np.array([loc_latlon(l) for l in W["txl"]]).T
    lat_r, lon_r = np.array([loc_latlon(l) for l in W["rxl"]]).T
    A, B = xyz(lat_t, lon_t), xyz(lat_r, lon_r)
    length = np.arctan2(np.linalg.norm(np.cross(A, B), axis=1), np.einsum("ij,ij->i", A, B)) * RE
    real = anomalies(W, W["snr"])
    unit = (blk >= 0) & (length >= 100.0) & (real[:, 0] >= 5)
    ui = np.nonzero(unit)[0]
    U = dict(t=W["t"][ui], slot_block=blk[ui], A=A[ui], B=B[ui], txl=W["txl"][ui], rxl=W["rxl"][ui])
    adir = lambda x: os.path.join(data, "adsb", x)
    lab = {}
    ep = lambda x: int(dt.datetime.fromisoformat(x).replace(tzinfo=dt.timezone.utc).timestamp())
    for p, dd in (("", day), ("p1", pday1), ("p2", pday2)):
        dh, da, cov, have = label_day(U, adir(dd), ep(day) - ep(dd))
        lab.update({p + "dh": dh, p + "da": da, p + "cov": cov, p + "have": have})
    # planted control: +6 dB on 10% of the real-label crossed units, then the rule is recomputed
    rng = np.random.default_rng(PLANT_SEED + int(day.replace("-", "")))
    crossed = lab["have"] & (lab["dh"] <= R_CROSS)
    plant = np.zeros(len(W["t"]), bool); plant[ui[crossed & (rng.random(len(ui)) < PLANT_P)]] = True
    planted = anomalies(W, W["snr"] + PLANT_DB * plant)
    np.savez_compressed(out, day=day, placebo_days=np.array([pday1, pday2]), t=W["t"][ui], slot_block=blk[ui],
        tx=W["tx"][ui], rx=W["rx"][ui], band=W["band"][ui], length=length[ui],
        real=real[ui], planted=planted[ui], plant=plant[ui], **lab,
        stats=np.array([stats["rows"], stats["kept"], stats["mobile_calls"], len(ui)]))
    print(day, "placebos", pday1, pday2, stats, "units", len(ui),
          "labelled", [int(lab[p + "have"].sum()) for p in ("", "p1", "p2")])

if __name__ == "__main__":
    main(*sys.argv[1:6])
