"""Independent spot check of prep.py's units (imports nothing from the pipeline).

usage: check.py UNITS.npz DATA_DIR N_UNITS SEED [corrupt-label|corrupt-anomaly]

For N random scored units: recomputes the GDTAAA flags from the raw WSPR CSVs
in plain Python, and the nearest high (>= FL200) and any-airborne aircraft
distances from the RAW ADS-B Exchange snapshots (downloaded again), with
haversine/cross-track formulas and 1-s sampling. Exits 1 on any mismatch.
"""
import sys, os, gzip, csv, io, json, math, glob, random, urllib.request, datetime as dt
import numpy as np

R = 6371.0
CAP = 30.0
def hav(la1, lo1, la2, lo2):
    p1, p2 = math.radians(la1), math.radians(la2); dp = p2 - p1; dl = math.radians(lo2 - lo1)
    a = math.sin(dp / 2) ** 2 + math.cos(p1) * math.cos(p2) * math.sin(dl / 2) ** 2
    return 2 * R * math.asin(min(1.0, math.sqrt(a)))
def bearing(la1, lo1, la2, lo2):
    p1, p2 = math.radians(la1), math.radians(la2); dl = math.radians(lo2 - lo1)
    return math.atan2(math.sin(dl) * math.cos(p2), math.cos(p1) * math.sin(p2) - math.sin(p1) * math.cos(p2) * math.cos(dl))
def arc_dist(la1, lo1, la2, lo2, la, lo):
    d13 = hav(la1, lo1, la, lo) / R; L = hav(la1, lo1, la2, lo2)
    xt = math.asin(max(-1, min(1, math.sin(d13) * math.sin(bearing(la1, lo1, la, lo) - bearing(la1, lo1, la2, lo2)))))
    at = math.acos(max(-1, min(1, math.cos(d13) / math.cos(xt)))) * R
    if math.cos(bearing(la1, lo1, la, lo) - bearing(la1, lo1, la2, lo2)) < 0: at = -at
    if 0 <= at <= L: return abs(xt) * R
    return min(hav(la1, lo1, la, lo), hav(la2, lo2, la, lo))
def locll(l):
    l = l.upper()
    return ((ord(l[1]) - 65) * 10 - 90 + int(l[3]) + (ord(l[5]) - 65) * 2.5 / 60 + 1.25 / 60,
            (ord(l[0]) - 65) * 20 - 180 + int(l[2]) * 2 + (ord(l[4]) - 65) * 5 / 60 + 2.5 / 60)

def raw_snap(day, ts):
    t = dt.datetime.fromtimestamp(ts, dt.timezone.utc)
    url = f"https://samples.adsbexchange.com/readsb-hist/{day.replace('-', '/')}/{t:%H%M%S}Z.json.gz"
    b = urllib.request.urlopen(urllib.request.Request(url, headers={"User-Agent": "check"}), timeout=120).read()
    a = json.loads(gzip.decompress(b) if b[:2] == b"\x1f\x8b" else b)
    out = {}
    for x in a["aircraft"]:
        if "lat" in x and x.get("seen_pos") is not None and x["seen_pos"] <= 60:
            out[x["hex"]] = (a["now"] - x["seen_pos"], x["lat"], x["lon"], x.get("alt_baro"), x.get("gs"), x.get("track"))
    return out

def nearest(day, t0, txl, rxl):
    la1, lo1 = locll(txl); la2, lo2 = locll(rxl)
    snaps = [raw_snap(day, t0 + 60 * k) for k in range(3)]
    hexes = set().union(*snaps); best_h = best_a = 100.0
    for h in hexes:
        kn = sorted({s[h][:3] for s in snaps if h in s})
        alts = [s[h][3] for s in snaps if h in s]
        if all(a == "ground" for a in alts): continue
        high = any(isinstance(a, (int, float)) and a >= 20000 for a in alts)
        last = [s[h] for s in snaps if h in s][-1]
        for sec in range(1, 112):
            tau = t0 + sec
            pos = None
            for (ta, a1, b1), (tb, a2, b2) in zip(kn, kn[1:]):
                if ta <= tau <= tb and tb > ta:
                    w = (tau - ta) / (tb - ta); dlon = (b2 - b1 + 540) % 360 - 180
                    pos = (a1 + w * (a2 - a1), b1 + w * dlon); break
            if pos is None:
                ta, a1, b1 = min(kn, key=lambda k: abs(k[0] - tau)); dtk = tau - ta
                src = [s[h] for s in snaps if h in s and abs(s[h][0] - ta) < 1e-3][0]
                gs, trk = src[4], src[5]
                if isinstance(gs, (int, float)) and isinstance(trk, (int, float)) and abs(dtk) <= 60:
                    d = gs * 1.852 / 3600 * dtk / R; th = math.radians(trk); p = math.radians(a1)
                    p2 = math.asin(math.sin(p) * math.cos(d) + math.cos(p) * math.sin(d) * math.cos(th))
                    l2 = math.radians(b1) + math.atan2(math.sin(th) * math.sin(d) * math.cos(p), math.cos(d) - math.sin(p) * math.sin(p2))
                    pos = (math.degrees(p2), math.degrees(l2))
                elif abs(dtk) <= 15:
                    pos = (a1, b1)
            if pos is None: continue
            dd = arc_dist(la1, lo1, la2, lo2, *pos)
            best_a = min(best_a, dd)
            if high: best_h = min(best_h, dd)
    return best_h, best_a

def wspr_flags(day, data, t, tx, rx, band):
    rows = []
    for f in sorted(glob.glob(os.path.join(data, "wspr", day, "*.csv.gz"))):
        rows.extend(csv.reader(io.TextIOWrapper(gzip.open(f), "utf-8")))
    rows = [r for r in rows if r[0] != "time"]
    seen = set(); uniq = []
    for r in rows:
        k = (r[0], r[1], r[2].upper(), r[4].upper(), r[3].upper(), r[5].upper(), r[6], r[7], r[8])
        if k not in seen: seen.add(k); uniq.append(k)
    locs = {}
    for k in uniq:
        locs.setdefault(k[2], set()).add(k[4]); locs.setdefault(k[3], set()).add(k[5])
    import re
    ok6 = re.compile(r"^[A-R]{2}[0-9]{2}[A-X]{2}$")
    good = [k for k in uniq if ok6.match(k[4]) and ok6.match(k[5]) and "/" not in k[2] + k[3]
            and k[2][:1] not in "01Q" and len(locs[k[2]]) == 1 and len(locs[k[3]]) == 1]
    cnt = {}
    for k in good: cnt[(k[0], k[1], k[2], k[3])] = cnt.get((k[0], k[1], k[2], k[3]), 0) + 1
    good = [k for k in good if cnt[(k[0], k[1], k[2], k[3])] == 1]
    ep = lambda s: dt.datetime.fromisoformat(s).replace(tzinfo=dt.timezone.utc).timestamp()
    res = []
    for (tt, txx, rxx, bb) in zip(t, tx, rx, band):
        trip = [k for k in good if k[2] == txx and k[3] == rxx and int(k[1]) == bb]
        win = [k for k in trip if abs(ep(k[0]) - tt) <= 3 * 3600]
        me = [k for k in trip if ep(k[0]) == tt][0]
        def z(i):
            v = [float(k[i]) for k in win]; m = sum(v) / len(v)
            sd = math.sqrt(sum((x - m) ** 2 for x in v) / (len(v) - 1)) if len(v) > 1 else 0
            return (float(me[i]) - m) / sd if sd > 1e-4 else 0.0
        fr = sum(int(k[8]) != 0 for k in win) / len(win)
        res.append((len(win), z(7), z(6), float(int(me[8]) != 0 and fr < 0.5)))
    return res

if __name__ == "__main__":
    units, data, n, seed = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
    mode = sys.argv[5] if len(sys.argv) > 5 else ""
    U = dict(np.load(units)); day = str(U["day"])
    rng = random.Random(seed)
    idx = [i for i in range(len(U["t"])) if U["have"][i]]
    # half the sample from crossed-or-near units, half from uncrossed ones, so both labels are checked
    near = [i for i in idx if U["dh"][i] <= 5]; far = [i for i in idx if U["dh"][i] >= 25 and U["da"][i] >= 5]
    pick = rng.sample(near, n // 2) + rng.sample(far, min(len(far), n - n // 2))
    if mode == "corrupt-label": U["dh"][pick[0]] = 30.0
    if mode == "corrupt-anomaly": U["real"][pick[0], 1] += 3.0
    txl = {}
    for f in sorted(glob.glob(os.path.join(data, "wspr", day, "*.csv.gz"))):
        for r in csv.reader(io.TextIOWrapper(gzip.open(f), "utf-8")):
            txl[(r[2].upper(), "tx")] = r[3].upper(); txl[(r[4].upper(), "rx")] = r[5].upper()
    flags = wspr_flags(day, data, [int(U["t"][i]) for i in pick], [str(U["tx"][i]) for i in pick],
                       [str(U["rx"][i]) for i in pick], [int(U["band"][i]) for i in pick])
    bad = 0
    for i, fl in zip(pick, flags):
        h, a = nearest(day, int(U["t"][i]), txl[(str(U["tx"][i]), "tx")], txl[(str(U["rx"][i]), "rx")])
        h, a = min(h, CAP), min(a, CAP)   # prep.py caps distances at 30 km
        ok_lab = (abs(h - U["dh"][i]) <= 1.5 or min(h, U["dh"][i]) >= CAP - 0.5) and (abs(a - U["da"][i]) <= 1.5 or min(a, U["da"][i]) >= CAP - 0.5)
        ok_an = fl[0] == U["real"][i, 0] and all(abs(fl[j] - U["real"][i, j]) < 1e-6 for j in (1, 2, 3))
        bad += not (ok_lab and ok_an)
        print(f"unit {i}: dh {U['dh'][i]:6.2f}/{h:6.2f} da {U['da'][i]:6.2f}/{a:6.2f} n {int(U['real'][i,0])}/{fl[0]} "
              f"zs {U['real'][i,1]:+.4f}/{fl[1]:+.4f} zf {U['real'][i,2]:+.4f}/{fl[2]:+.4f} dr {U['real'][i,3]:.0f}/{fl[3]:.0f} "
              + ("OK" if ok_lab and ok_an else "MISMATCH"))
    print("checked", len(pick), "mismatches", bad)
    sys.exit(1 if bad else 0)
