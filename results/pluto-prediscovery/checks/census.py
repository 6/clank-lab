"""Census of public archival plates covering Pluto's predicted position, 1880-01-01 to 1909-06-30.

Usage: python census.py WORKDIR

Archives: Harvard DASCH DR7 (exposure query), the Heidelberg plate archive (GAVO table lsw.plates) and
APPLAUSE DR4. Pluto's geocentric position and V come from JPL Horizons, daily; its B is taken as V + 0.87
(Pluto's resolved color, the redder assumed case; with the 1933-34 combined color 0.78
every margin rises by 0.09 mag, which census.json also reports). Pluto's track is sampled every 30 days while its solar elongation is
at least 30 degrees on the sample date; at each kept sample the DASCH query asks for exposures within 15 days
that cover the point, whatever the elongation on their own dates. Exposures in the windows of skipped samples are
not queried.
Each exposure is then placed against Pluto's position at its own date. The depth margin is DASCH's limiting
magnitude (APASS, else ATLAS) minus Pluto's B. Heidelberg gives no limits; its plates are listed with their
exposure times. Writes WORKDIR/census.json and WORKDIR/census-exposures.csv (one row per DASCH exposure covering
Pluto's position: plate, date, series, plate solution, coverage, limit, Pluto's B, margin and verdict). Takes under an hour, almost all of it waiting on the DASCH service.
"""
import csv
import io
import json
import sys
import time
from pathlib import Path

import numpy as np
import requests
from astropy.table import Table
from astropy.time import Time
from astropy.wcs import WCS

W = Path(sys.argv[1]); W.mkdir(parents=True, exist_ok=True)
START, STOP = "1880-01-01", "1909-06-30"


def get(url, **kw):
    for attempt in range(8):
        r = requests.post(url, timeout=600, **kw) if "json" in kw or "data" in kw else requests.get(url, timeout=600, **kw)
        if r.status_code not in (429, 500, 502, 503, 504):
            r.raise_for_status()
            return r
        time.sleep(20*2**min(attempt, 4))
    r.raise_for_status()


def cached(name, fn):
    p = W/name
    if not p.exists():
        p.write_bytes(fn())
    return p.read_bytes()


# Pluto's track
txt = json.loads(cached("pluto-track.json", lambda: get("https://ssd.jpl.nasa.gov/api/horizons.api", params=dict(
    format="json", COMMAND="'999'", OBJ_DATA="NO", MAKE_EPHEM="YES", EPHEM_TYPE="OBSERVER", CENTER="'500@399'",
    START_TIME=f"'{START}'", STOP_TIME=f"'{STOP}'", STEP_SIZE="'1 d'", QUANTITIES="'1,9,23'", CSV_FORMAT="YES",
    ANG_FORMAT="DEG", EXTRA_PREC="YES", CAL_FORMAT="JD")).content))["result"]
rows = [[x.strip() for x in l.split(",")] for l in txt.split("$$SOE")[1].split("$$EOE")[0].strip().splitlines()]
JD = np.array([float(r[0]) for r in rows]); RA = np.array([float(r[3]) for r in rows]); DE = np.array([float(r[4]) for r in rows])
V = np.array([float(r[5]) for r in rows]); EL = np.array([float(r[7]) for r in rows])


def pluto(j):
    # B is not rounded: margins and verdicts use the unrounded value; only printed and exported copies are rounded.
    return float(np.interp(j, JD, RA)), float(np.interp(j, JD, DE)), float(np.interp(j, JD, V))+0.87


# DASCH
(W/"dasch").mkdir(exist_ok=True)
dasch = {}
rank = dict(inside=2, edge=1, unknown=0)
for i in range(0, len(JD), 30):
    if EL[i] < 30:
        continue
    lo, hi = Time(JD[i]-15, format="jd").isot[:19]+"Z", Time(JD[i]+15, format="jd").isot[:19]+"Z"
    d = json.loads(cached(f"dasch/{lo[:10]}.json", lambda: get(
        "https://api.starglass.cfa.harvard.edu/public/dasch/dr7/queryexps",
        json=dict(ra_deg=float(RA[i]), dec_deg=float(DE[i]), midpoint_min=lo, midpoint_max=hi)).content))
    h = d[0].split(",")
    for line in d[1:]:
        r = dict(zip(h, line.split(",")))
        if not r.get("expdate"):
            continue
        j = Time(r["expdate"].rstrip("Z"), format="isot", scale="utc").jd
        pra, pde, pb = pluto(j)
        off = float(np.hypot((pra-RA[i])*np.cos(np.radians(DE[i])), pde-DE[i]))
        edge = float(r["edgedist"]) if r.get("edgedist") else None
        lim = next((float(r[k]) for k in ("limMagApass", "limMagAtlas") if r.get(k)), None)
        key = (r["series"], int(r["platenum"]), r["solnum"], r["expdate"])
        row = dict(archive="DASCH", plate=f"{r['series'].upper()} {int(r['platenum'])}", series=r["series"], solnum=r["solnum"], date=r["expdate"][:16],
                   jd=j, exptime_min=float(r["exptime"]) if r.get("exptime") else None, solved=r.get("wcssource") or None,
                   limit=lim, pluto_B=pb, margin=None if lim is None else lim-pb,
                   covers="unknown" if edge is None else ("inside" if edge > off else "edge"))
        if key not in dasch or rank[row["covers"]] > rank[dasch[key]["covers"]]:
            dasch[key] = row

# Heidelberg
q = ("SELECT plateID, dateObs, startTime, endTime, exposure, instId, pixelSize, wcs_refPixel, wcs_refValues, wcs_cdmatrix "
     f"FROM lsw.plates WHERE dateObs < {Time(STOP).mjd} AND centerAlpha BETWEEN 30 AND 110 AND centerDelta BETWEEN -10 AND 35")
lsw = list(csv.DictReader(io.StringIO(cached("lsw.csv", lambda: get(
    "https://dc.g-vo.org/tap/sync", data=dict(REQUEST="doQuery", LANG="ADQL", FORMAT="csv", MAXREC="100000", QUERY=q)).content).decode())))


def arr(s):
    return [float(x) for x in s.strip("[]{}").split(",")]


heid = []
for r in lsw:
    j = float(r["dateObs"])+2400000.5
    if not JD[0] <= j <= JD[-1]:
        continue
    pra, pde, pb = pluto(j)
    w = WCS(naxis=2); w.wcs.ctype = ["RA---TAN", "DEC--TAN"]; w.wcs.crpix = arr(r["wcs_refPixel"]); w.wcs.crval = arr(r["wcs_refValues"])
    cd = arr(r["wcs_cdmatrix"]); w.wcs.cd = [[cd[0], cd[1]], [cd[2], cd[3]]]
    nx, ny = [int(x) for x in arr(r["pixelSize"])]
    x, y = w.all_world2pix([[pra, pde]], 1)[0]
    margin = float(min(x, y, nx-x, ny-y))
    if margin < 0:
        continue
    heid.append(dict(archive="Heidelberg", plate=r["plateID"], date=r["startTime"][:16], jd=j,
                     exptime_min=round(float(r["exposure"] or 0)/60, 1), instrument=r["instId"].split(",")[-1].strip(),
                     pluto_B=pb, edge_px=round(margin)))

# APPLAUSE
aq = "SELECT plate_id, jd_mid, exptime, ra_icrs, dec_icrs FROM applause_dr4.exposure WHERE year_mid < 1909.5"
ap = Table.read(io.BytesIO(cached("applause.xml", lambda: get(  # this service answers in VOTable only
    "https://www.plate-archive.org/tap/sync", data=dict(REQUEST="doQuery", LANG="ADQL", QUERY=aq)).content)), format="votable")
near = []
for r in ap:
    if np.ma.is_masked(r["jd_mid"]) or np.ma.is_masked(r["ra_icrs"]):
        continue
    pra, pde, _ = pluto(float(r["jd_mid"]))
    a, b = np.radians([pra, pde]); c, d = np.radians([float(r["ra_icrs"]), float(r["dec_icrs"])])
    near.append(float(np.degrees(np.arccos(np.clip(np.sin(b)*np.sin(d)+np.cos(b)*np.cos(d)*np.cos(a-c), -1, 1)))))

# Exposure-level export: one row per exposure (series, plate number, midpoint), merged across samples and plate
# solutions with its best coverage label. Verdicts use unrounded margins; printed values are rounded to 0.001 mag.
exp = {}
for k, r in dasch.items():
    m = (k[0], k[1], k[3])
    if m not in exp or rank[r["covers"]] > rank[exp[m]["covers"]]:
        exp[m] = r


def verdict(r):
    if r["covers"] != "inside":
        return dict(edge="not tested (edge unresolved)", unknown="not tested (no edge distance)")[r["covers"]]
    if r["margin"] is None:
        return "not tested (no limit)"
    return "passes" if r["margin"] >= 0 else "short"


with open(W/"census-exposures.csv", "w", newline="") as f:
    cw = csv.writer(f, lineterminator="\n")
    cw.writerow(["plate", "date_utc", "series", "solnum", "coverage", "limit_B", "pluto_B", "margin", "verdict"])
    for r in sorted(exp.values(), key=lambda r: (r["jd"], r["plate"])):
        cw.writerow([r["plate"], r["date"], r["series"], r["solnum"], r["covers"],
                     "" if r["limit"] is None else f"{r['limit']:.3f}", f"{r['pluto_B']:.3f}",
                     "" if r["margin"] is None else f"{r['margin']:.3f}", verdict(r)])

cut = Time("1908-12-01").jd
out = dict(dasch_samples=len(list(range(0, len(JD), 30))), applause_exposures=len(ap),
           applause_nearest_deg=round(min(near), 1) if near else None, windows={})
for name, sel in (("1908-12-01 to 1909-06-30", lambda r: r["jd"] >= cut), ("before 1908-12-01", lambda r: r["jd"] < cut)):
    D = sorted([r for r in dasch.values() if sel(r) and r["covers"] == "inside"],
               key=lambda r: -(r["margin"] if r["margin"] is not None else -99))
    H = sorted([r for r in heid if sel(r)], key=lambda r: r["jd"])
    edge = sum(1 for r in dasch.values() if sel(r) and r["covers"] == "edge")
    unknown = sum(1 for r in dasch.values() if sel(r) and r["covers"] == "unknown")
    # The same exposure can come back under several plate solutions (solnum); merged, it keeps its best label.
    merged = {}
    for k, r in dasch.items():
        if sel(r):
            m = (k[0], k[1], k[3])
            merged[m] = max(merged.get(m, 0), dict(inside=2, edge=1, unknown=0)[r["covers"]])
    out.setdefault("merged_solutions", {})[name] = {lab: sum(v == n for v in merged.values()) for lab, n in (("inside", 2), ("edge", 1), ("unknown", 0))}
    # Sensitivity to the color: with B - V = 0.78 instead of 0.87 Pluto is 0.09 mag brighter, so every margin rises by 0.09.
    out.setdefault("margin_ge_0_with_BV_0.78", {})[name] = [r["plate"] for r in D if r["margin"] is not None and r["margin"] + 0.09 >= 0]
    out["windows"][name] = dict(dasch_exposures=len(D), dasch_at_edge=edge, dasch_edge_unknown=unknown,
                                dasch_with_limit=sum(r["limit"] is not None for r in D),
                                dasch_margin_ge_0=[r["plate"] for r in D if r["margin"] is not None and r["margin"] >= 0],
                                dasch_top=D[:15], heidelberg=H)
    print(f"== {name}: DASCH {len(D)} exposures with Pluto inside the plate, {edge} unresolved at the plate edge (edge distance <= Pluto's distance from the sample point) "
          f"and {unknown} with no edge distance ({out['windows'][name]['dasch_with_limit']} inside with a limit), "
          f"margin >= 0: {out['windows'][name]['dasch_margin_ge_0']}; Heidelberg {len(H)}: {[r['plate'] for r in H]}")
    print("   merged across plate solutions:", out["merged_solutions"][name], "; margin >= 0 with B-V 0.78:", out["margin_ge_0_with_BV_0.78"][name])
    for r in D[:6]:
        print("  ", r["plate"], r["date"], r["exptime_min"], r["limit"], round(r["pluto_B"], 3), None if r["margin"] is None else round(r["margin"], 3))
print("APPLAUSE exposures before 1909.5:", len(ap), "nearest to Pluto (deg):", out["applause_nearest_deg"])
json.dump(out, open(W/"census.json", "w"), indent=1)
