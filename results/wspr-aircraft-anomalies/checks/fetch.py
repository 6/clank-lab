"""Download and reduce the public inputs for one sample day.

usage: fetch.py DAY DATA_DIR      (DAY like 2024-01-01)

WSPR: wspr.live hourly CSVs for [DAY-1 21:00, DAY+1 01:00) UTC, kept gzipped.
ADS-B: ADS-B Exchange readsb-hist snapshots HH:MM:00Z for the four test
blocks (00, 03, ..., 21 UTC; minutes 0..60), each reduced to an .npz of
hex, position time (now - seen_pos), lat, lon, alt_baro, gs, track; the raw
file's SHA-256 goes in a manifest and the raw file is discarded.
"""
import sys, os, gzip, json, hashlib, time, urllib.request, urllib.parse, datetime as dt
import numpy as np

BLOCK_HOURS = (0, 3, 6, 9, 12, 15, 18, 21)
UA = {"User-Agent": "wspr-adsb-test/1.0", "Accept-Encoding": "gzip"}

def get(url, tries=6):
    for k in range(tries):
        try:
            with urllib.request.urlopen(urllib.request.Request(url, headers=UA), timeout=120) as r:
                return r.read()
        except urllib.error.HTTPError as e:
            if e.code == 404:
                return None
            err = e
        except Exception as e:
            err = e
        time.sleep(2 * 2 ** k)
    raise RuntimeError(f"failed {url}: {err}")

def gunzip(b):
    return gzip.decompress(b) if b[:2] == b"\x1f\x8b" else b

def fetch_wspr(day, out):
    d0 = dt.datetime.fromisoformat(day) - dt.timedelta(hours=3)
    man = []
    for h in range(28):
        a = d0 + dt.timedelta(hours=h); b = a + dt.timedelta(hours=1)
        f = os.path.join(out, a.strftime("%Y%m%d%H") + ".csv.gz")
        if not os.path.exists(f):
            q = ("SELECT time,band,tx_sign,tx_loc,rx_sign,rx_loc,frequency,snr,drift,power "
                 f"FROM wspr.rx WHERE time >= '{a:%Y-%m-%d %H:%M:%S}' AND time < '{b:%Y-%m-%d %H:%M:%S}' "
                 "ORDER BY time,tx_sign,rx_sign,band,frequency,snr,drift FORMAT CSVWithNames")
            raw = get("https://db1.wspr.live/?enable_http_compression=1&query=" + urllib.parse.quote(q))
            body = gunzip(raw)
            if not body.startswith(b'"time"'):
                raise RuntimeError(f"bad WSPR reply for {a}: {body[:200]!r}")
            with gzip.open(f + ".tmp", "wb", compresslevel=6) as g:
                g.write(body)
            os.replace(f + ".tmp", f)
            time.sleep(0.5)
        body = gzip.open(f).read()
        man.append((os.path.basename(f), hashlib.sha256(body).hexdigest(), body.count(b"\n") - 1))
    return man

def reduce_snapshot(raw):
    a = json.loads(gunzip(raw))
    now = float(a["now"]); rows = []
    for x in a["aircraft"]:
        if "lat" not in x or "lon" not in x:
            continue
        sp = x.get("seen_pos", 0.0)
        if sp is None or sp > 60:
            continue
        al = x.get("alt_baro")
        alt = -1.0 if al == "ground" else (float(al) if isinstance(al, (int, float)) else np.nan)
        rows.append((x["hex"], now - float(sp), float(x["lat"]), float(x["lon"]), alt,
                     float(x["gs"]) if isinstance(x.get("gs"), (int, float)) else np.nan,
                     float(x["track"]) if isinstance(x.get("track"), (int, float)) else np.nan))
    hexes = np.array([r[0] for r in rows], dtype="U8")
    num = np.array([r[1:] for r in rows], dtype=np.float64).reshape(-1, 6)
    return now, hexes, num

def fetch_adsb(day, out):
    d = dt.datetime.fromisoformat(day); man = []
    for H in BLOCK_HOURS:
        for m in range(61):
            t = d + dt.timedelta(hours=H, minutes=m)
            f = os.path.join(out, t.strftime("%H%M") + ".npz")
            if os.path.exists(f):
                man.append(tuple(open(f + ".sha256").read().split()))
                continue
            url = f"https://samples.adsbexchange.com/readsb-hist/{d:%Y/%m/%d}/{t:%H%M}00Z.json.gz"
            raw = get(url)
            if raw is None:
                man.append((t.strftime("%H%M"), "MISSING")); continue
            body = gunzip(raw)
            now, hexes, num = reduce_snapshot(body)
            np.savez(f + ".tmp.npz", now=now, hex=hexes, num=num)
            os.replace(f + ".tmp.npz", f)
            h = hashlib.sha256(body).hexdigest()
            open(f + ".sha256", "w").write(f"{t:%H%M} {h}\n")
            man.append((t.strftime("%H%M"), h))
    return man

if __name__ == "__main__":
    day, data = sys.argv[1], sys.argv[2]
    w = os.path.join(data, "wspr", day); a = os.path.join(data, "adsb", day)
    os.makedirs(w, exist_ok=True); os.makedirs(a, exist_ok=True)
    mw = fetch_wspr(day, w); ma = fetch_adsb(day, a)
    with open(os.path.join(data, f"manifest-{day}.txt"), "w") as g:
        for r in mw: g.write("wspr " + " ".join(map(str, r)) + "\n")
        for r in ma: g.write("adsb " + " ".join(map(str, r)) + "\n")
    print(day, "wspr rows", sum(r[2] for r in mw), "adsb files", sum(1 for r in ma if r[1] != "MISSING"),
          "missing", sum(1 for r in ma if r[1] == "MISSING"))
