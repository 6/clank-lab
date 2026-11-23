"""Profile of each sample day's design-W cases (real labels), to see what sets one day apart.
Not part of the frozen test; uses analyze.py's design W unchanged.

usage: dayprofile.py OUT.json units-DAY.npz ...
For each day: the number of cases, distinct links, the share of cases on the five links with
the most cases, the standard deviation of the per-case difference d and the standard error
of the day's excess (per 100), the crossed and control flag rates (per 100), the median path
length (km), and the station appearing in the most cases with its count.
"""
import sys, os, json
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import analyze as A

def profile(path):
    D = dict(np.load(path, allow_pickle=False))
    y = A.flags(D["real"], 0.75)
    base = D["have"] & D["cov"]
    crossed = base & (D["dh"] <= 5.0)
    unc = (base & (D["dh"] >= A.FAR_HIGH) & (D["da"] >= A.FAR_ANY)).astype(float)
    d, _ = A.design_w(D, crossed, unc, y)
    # the same ordering and case selection as design_w, to recover each case's link
    link = np.rec.fromarrays([D["tx"], D["rx"], D["band"]])
    _, lid = np.unique(link, return_inverse=True)
    o = np.lexsort((D["t"], lid))
    key = lid[o].astype(np.int64) * 10**10 + (D["t"][o] - D["t"].min())
    lo = np.searchsorted(key, key - A.W_MIN, "left"); hi = np.searchsorted(key, key + A.W_MIN, "right")
    cu = np.concatenate([[0.0], np.cumsum(unc[o])])
    c = crossed[o] & ((cu[hi] - cu[lo]) > 0)
    L, yc, ln = lid[o][c], y[o][c], D["length"][o][c]
    assert len(L) == len(d)
    _, cnt = np.unique(L, return_counts=True)
    st, sc = np.unique(np.concatenate([D["tx"][o][c], D["rx"][o][c]]), return_counts=True)
    return str(D["day"]), dict(
        cases=int(len(d)), links=int(len(cnt)),
        top5_share=round(float(np.sort(cnt)[::-1][:5].sum()) / len(d), 3),
        sd=round(float(d.std()), 3), se_per100=round(100 * float(d.std()) / len(d) ** 0.5, 2),
        crossed_flag_per100=round(100 * float(yc.mean()), 1),
        control_flag_per100=round(100 * float((yc - d).mean()), 1),
        median_length_km=round(float(np.median(ln))),
        top_station=str(st[np.argmax(sc)]), top_station_cases=int(sc.max()))

if __name__ == "__main__":
    out = dict(profile(p) for p in sorted(sys.argv[2:]))
    json.dump(out, open(sys.argv[1], "w"), indent=1, sort_keys=True)
    for day, v in sorted(out.items()):
        print(day, json.dumps(v))
