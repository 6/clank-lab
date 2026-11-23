"""Offline quick check: synthetic tests of the anomaly rule and the crossing
geometry, and the verdict recomputed from data/results.json with two corruptions it must reject.
usage: selftest.py RESULTS.json"""
import sys, os, json, math
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import prep

def test_anomalies():
    # triple X: one huge-frequency triple first (the 2026-11-21 regression), then triple Y with a
    # tiny spread; Y's z values are checked against a direct two-pass computation
    t0 = 1_700_000_000; rows = []
    for k in range(40):
        rows.append((t0 + 120 * k, "AAA", "XXX", 14, 14_000_000 + (k % 2) * 150_000_000, -10 + k % 5, 0))
    fy = [14_097_050, 14_097_051, 14_097_050, 14_097_052, 14_097_050, 14_097_050, 14_097_051]
    sy = [-20, -18, -25, -19, -20, -21, -10]; dr = [0, 0, 1, 0, 0, 0, 0]
    for k in range(7):
        rows.append((t0 + 120 * k, "BBB", "YYY", 14, fy[k], sy[k], dr[k]))
    W = dict(t=np.array([r[0] for r in rows]), tx=np.array([r[1] for r in rows]), rx=np.array([r[2] for r in rows]),
             band=np.array([r[3] for r in rows]), f=np.array([r[4] for r in rows], np.int64),
             snr=np.array([r[5] for r in rows], float), drift=np.array([r[6] for r in rows], np.int64))
    res = prep.anomalies(W, W["snr"])[40:]
    for k in range(7):
        for col, v in ((1, sy), (2, fy)):
            m = sum(v) / 7; sd = math.sqrt(sum((x - m) ** 2 for x in v) / 6)
            assert abs(res[k, col] - (v[k] - m) / sd) < 1e-9, (k, col, res[k, col])
        assert res[k, 0] == 7 and res[k, 3] == float(dr[k] != 0)
    print("ok: anomaly rule matches a direct computation (with a large-valued triple first)")

def test_geometry():
    A = prep.xyz(np.array([0.0]), np.array([0.0])); B = prep.xyz(np.array([0.0]), np.array([10.0]))
    taus = 1.0 + 5.0 * np.arange(23)
    def run(lat0, dlat_per_s, lon):
        P = prep.xyz(np.array([[lat0 + dlat_per_s * t for t in (0, 60, 120)]]), np.full((1, 3), lon))
        TP = np.array([[0.0, 60.0, 120.0]]); GS = np.full((1, 3), np.nan); TRK = GS.copy()
        Pt = prep.positions(TP, P, GS, TRK, taus)
        dh, da, _ = prep.link_min_dist(A, B, Pt, np.array([True]), np.array([True]))
        return dh[0], da[0]
    km = 1 / 111.195
    h, a = run(-0.1, 0.2 / 120, 5.0); assert h == 0.0 and a == 0.0, (h, a)          # crosses mid-path
    h, _ = run(10 * km, 0.0, 5.0); assert abs(h - 10.0) < 0.05, h                    # parallel, 10 km off
    h, _ = run(-0.1, 0.2 / 120, 12.0); assert h == prep.D_MAX, h                     # 2 deg beyond the arc end
    print("ok: crossing geometry (through the arc 0 km, 10 km offset, beyond the end capped)")

def verdict(r, U=0.02):
    P, L = r["primary"], r["planted"]
    if not (L["W"]["delta"]["lo"] > 0 and L["M"]["delta"]["lo"] > 0): return "INCONCLUSIVE"
    if P["W"]["delta"]["lo"] > 0 and P["M"]["delta"]["lo"] > 0: return "POSITIVE"
    if P["W"]["delta"]["hi"] < U and P["M"]["delta"]["hi"] < U: return "NEGATIVE"
    return "INCONCLUSIVE"

def test_verdict(path):
    r = json.load(open(path)); v = verdict(r)
    assert r["verdict"].split()[0] == v, (r["verdict"], v)
    for k in "WM":
        d = r["primary"][k]
        assert abs(d["delta"]["E"] - (d["real"]["E"] - (d["placebo1"]["E"] + d["placebo2"]["E"]) / 2)) < 1e-12
    print("ok: verdict", v, "follows from results.json")
    bad = json.loads(json.dumps(r)); bad["primary"]["W"]["delta"]["hi"] = 0.025
    assert verdict(bad) != v or v != "NEGATIVE", "corruption 1 not rejected"
    bad = json.loads(json.dumps(r)); bad["planted"]["M"]["delta"]["lo"] = -0.001
    assert verdict(bad) == "INCONCLUSIVE", "corruption 2 not rejected"
    print("ok: corrupted bound (W upper 2.5 per 100) and failed planted control both change the verdict")

if __name__ == "__main__":
    test_anomalies(); test_geometry(); test_verdict(sys.argv[1])
