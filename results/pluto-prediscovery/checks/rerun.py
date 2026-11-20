"""Rerun the measurements of the three plates from public data.

Usage: python rerun.py WORKDIR

Downloads the public scans (Harvard DASCH DR7 mosaic of MA 731, about 0.6 GB; cutouts of the Heidelberg
Bruce plates B2247a, B2248b, B3383a and B4816a from the GAVO plate archive), JPL Horizons ephemerides,
Gaia DR3 and APASS DR9 stars and IMCCE SkyBoT cone searches, then:

  1. dates each exposure from asteroid trails on the same glass;
  2. measures each plate at Pluto's predicted position at that time;
  3. runs the controls: the archive-time position on MA 731, the joint random-offset test (the measurement
     replayed at 300,000 shifted positions), injections, comparably faint catalog stars, the nearest Gaia star,
     SkyBoT cone searches, the 1914 positive control and the 1923 fixed-site check, and writes the inputs of
     the blinded sheet (figure.py --blind draws it);
  4. compares the December and February positions with Pluto's predicted motion;
  5. compares every number with ../data/expected.json and exits nonzero if one falls outside its tolerance.

Results go to WORKDIR/results.json. One thread is enough; the run takes about ten minutes, most of it downloads
(under a minute of computing once the inputs are cached). Only the numbers in expected.json are checked.
"""
import json
import os
import sys
from pathlib import Path

import numpy as np
import requests

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import clock  # noqa: E402
import plates  # noqa: E402

DASCH = "https://api.starglass.cfa.harvard.edu/public"
GAVO = "https://dc.g-vo.org"
HORIZONS = "https://ssd.jpl.nasa.gov/api/horizons.api"
SKYBOT = "https://ssp.imcce.fr/webservices/skybot/api/conesearch.php"
TAUNTON = "'-71.0903,41.8997,0.003'"  # Harvard's Oak Ridge station as DASCH lists it (east longitude, lat, km)

W = Path(sys.argv[1]).resolve()
W.mkdir(parents=True, exist_ok=True)
os.chdir(W)


def download(path, url, params=None, method="get", payload=None, check=b"SIMPLE"):
    p = W/path
    if not p.exists():
        r = (requests.post(url, json=payload, timeout=600) if method == "post"
             else requests.get(url, params=params, timeout=600, stream=True))
        r.raise_for_status()
        with open(p.with_suffix(".part"), "wb") as f:
            for chunk in r.iter_content(1 << 20):
                f.write(chunk)
        head = p.with_suffix(".part").read_bytes()[:80]
        if check and not head.startswith(check):
            raise RuntimeError(f"{path}: unexpected content {head[:60]!r}")
        p.with_suffix(".part").rename(p)
    return p


def dasch(endpoint, payload=None):
    import time
    for attempt in range(8):
        r = (requests.post(f"{DASCH}/{endpoint}", json=payload, timeout=300) if payload is not None
             else requests.get(f"{DASCH}/{endpoint}", timeout=300))
        if r.status_code not in (429, 502, 503, 504):
            break
        time.sleep(15*2**attempt)
    r.raise_for_status()
    return r.json()


def horizons(body, center, times=None, start=None, stop=None, step="1m", site=None):
    """Topocentric astrometric ICRF RA, Dec (deg) and V. Times are UT."""
    p = dict(format="json", COMMAND=f"'{body}'", OBJ_DATA="NO", MAKE_EPHEM="YES", EPHEM_TYPE="OBSERVER",
             QUANTITIES="'1,9'", CSV_FORMAT="YES", ANG_FORMAT="DEG", EXTRA_PREC="YES", TIME_DIGITS="SECONDS")
    if site:
        p.update(CENTER="'coord@399'", COORD_TYPE="GEODETIC", SITE_COORD=site)
    else:
        p.update(CENTER=f"'{center}'")
    if times:
        p.update(TLIST=" ".join(f"'{t}'" for t in times), TLIST_TYPE="CAL")
    else:
        p.update(START_TIME=f"'{start}'", STOP_TIME=f"'{stop}'", STEP_SIZE=f"'{step}'")
    txt = requests.get(HORIZONS, params=p, timeout=300).json()["result"]
    rows = [r.split(",") for r in txt.split("$$SOE")[1].split("$$EOE")[0].strip().splitlines()]
    ra = np.array([float(r[3]) for r in rows]); de = np.array([float(r[4]) for r in rows])
    v = np.array([float(r[5]) if r[5].strip() not in ("n.a.", "") else np.nan for r in rows])
    return [r[0].strip() for r in rows], ra, de, v


def gavo_cutout(plate, ra, dec, radius):
    did = f"ivo://org.gavo.dc/~?lswscans/data/part1/Bruceplatten/FITS/{plate}.fits"
    return download(f"{plate}-{ra:.3f}-{dec:.3f}.fits", f"{GAVO}/lswscans/res/positions/dl/dlget",
                    params=dict(ID=did, CIRCLE=f"{ra} {dec} {radius}"))


def minutes(stamp, origin):
    """Minutes from origin 'YYYY-Mon-DD HH:MM' for Horizons stamps."""
    from datetime import datetime
    f = "%Y-%b-%d %H:%M:%S" if stamp.count(":") == 2 else "%Y-%b-%d %H:%M"
    return (datetime.strptime(stamp, f)-datetime.strptime(origin, "%Y-%b-%d %H:%M")).total_seconds()/60


def hhmmss(m, origin_hour):
    t = (origin_hour*60+m) % 1440
    return f"{int(t//60):02d}:{int(t % 60):02d}:{(t*60) % 60:04.1f}"


def ut_string(day, origin_hour, m):
    t = origin_hour*60+m; d = int(t//1440); t -= d*1440
    from datetime import datetime, timedelta
    base = datetime.strptime(day, "%Y-%m-%d")+timedelta(days=d, seconds=round(t*60, 1))
    return base.strftime("%Y-%m-%d %H:%M:%S")


def run_plate(label, scan, hdu, mid, open_, close_, epoch, bexp, inject=True):
    P = plates.Plate(label, str(scan), hdu, mid[0], mid[1], epoch, str(W))
    M, mf, trail = plates.measure(P, mid[0], mid[1], open_, close_, bexp)
    M.update(ra=mid[0], dec=mid[1])
    out = dict(astrometry=P.astrometry, measure={k: v for k, v in M.items() if k != "calib"})
    # a 2' stamp of the filtered scan in S/N units, on a sky grid (east = +xi), for the figure
    g = np.arange(-60, 60.01, 0.5); XI, ETA = np.meshgrid(g, g)
    X, Y = P.std2pix(XI.ravel(), ETA.ravel())
    from scipy import ndimage as ndi
    st = (ndi.map_coordinates(mf, [Y, X], order=1).reshape(XI.shape)-M["base"])/M["noise"]
    np.savez_compressed(W/f"stamp_{label}.npz", snr=st.astype(np.float32), step=0.5,
                        centroid=[M["offset_east"], M["offset_north"]])
    if inject:
        out["injection"] = plates.inject(P, mf, M["base"], M["noise"], M["sigma_px"], M["calib"], trail,
                                         Bs=tuple(round(bexp+d, 2) for d in (-0.5, -0.25, 0, 0.25, 0.5)))
        # astrometric and photometric errors of comparably faint, isolated catalog stars, measured the same way
        out["faint_stars"] = plates.faint_stars(P, mf, M, bexp)
        # the same stars held out: each measured with an astrometric solution and B calibration fitted without it
        out["heldout_faint_stars"] = plates.heldout(P, mf, M, bexp)
        # injections through the measurement itself (before filtering; centroid, position, S/N and B acceptance)
        out["injection_pipeline"] = plates.inject_pipeline(P, mf, M, trail, Bs=tuple(round(bexp+d, 2) for d in (-0.5, -0.25, 0, 0.25, 0.5)))
    return out, P, M, mf


def nearest_gaia(P, ra, dec):
    """The nearest Gaia DR3 star (G < 19.5) to (ra, dec), with Gaia positions moved to the plate epoch as in the
    measurement. Also the same distance with the unmoved DR3 (epoch 2016) positions, for comparison."""
    gra, gde, G = P.gaia
    d = np.hypot((gra-ra)*np.cos(np.radians(dec)), gde-dec)*3600
    k = int(np.argmin(d))
    from astropy.table import Table
    g = Table.read(W/f"gaia_{P.label}.fits")
    d0 = np.hypot((np.array(g["ra"], float)-ra)*np.cos(np.radians(dec)), np.array(g["dec"], float)-dec)*3600
    return dict(arcsec=float(d[k]), G=float(G[k]), arcsec_epoch2016=float(np.min(d0)),
                same_star_epoch2016=bool(int(np.argmin(d0)) == k))


def skybot(ra, dec, time, observer, radius_deg=0.04):
    r = requests.get(SKYBOT, params={"RA": ra, "DEC": dec, "SR": radius_deg, "TIME": time, "-observer": observer,
                                     "-filter": 0, "-mime": "text", "-output": "object"}, timeout=300)
    r.raise_for_status()
    rows = [l for l in r.text.splitlines() if l and not l.startswith("#")]
    return [l.split("|")[1].strip() for l in rows]


R = {}

# ---------------------------------------------------------------- Harvard MA 731
meta = dasch("plates/p/ma00731")
exp = meta["exposures"][0]
R["ma731_archive"] = dict(midpoint=exp["datetime"], minutes=exp["exposure"])
if not (W/"ma00731_mosaic.fits.fz").exists():
    m = dasch("dasch/dr7/mosaic_package", dict(plate_id="ma00731", binning=1))
    download("ma00731_mosaic.fits.fz", m["baseFitsUrl"])
MA = W/"ma00731_mosaic.fits.fz"
# clock: (179) Klytaemnestra, 1-minute JPL track over the local night, minutes after 21:00 UT Dec 20
st, ra, de, _ = horizons("179;", None, start="1908-12-20 21:00", stop="1908-12-21 13:00", site=TAUNTON)
T = np.array([minutes(s, "1908-Dec-20 21:00") for s in st])
c = clock.fit_trail(MA, 1, T, ra, de, 1908.973, str(W/"gaia_clock_ma731_179.fits"))
arch_mid = minutes("1908-Dec-21 " + exp["datetime"][11:19], "1908-Dec-20 21:00")
c.update(t_mid_ut=hhmmss(c["t_mid"], 21), correction_min=c["t_mid"]-arch_mid)
R["ma731_clock_179"] = c
# Horizons returns a time list in time order: open, midpoint, close
times = [ut_string("1908-12-20", 21, c["t_open"]), ut_string("1908-12-20", 21, c["t_mid"]), ut_string("1908-12-20", 21, c["t_close"])]
_, pra, pde, pv = horizons("999", None, times=times, site=TAUNTON)
R["ma731_pluto_prediction"] = dict(times=times, ra=pra.tolist(), dec=pde.tolist(), V=float(pv[1]))


def sep_arcsec(r1, d1, r2, d2):
    return float(np.hypot((r1-r2)*np.cos(np.radians((d1+d2)/2)), d1-d2)*3600)


def timing(clk, pra, pde):
    """How far Pluto's prediction moves per minute of clock error, and for the trail fit's own 1-sigma error.
    Also the distance from Pluto to the region the clock fit reads (a square of 700 px half-width)."""
    rate = sep_arcsec(pra[0], pde[0], pra[2], pde[2])/(clk["t_close"]-clk["t_open"])
    return dict(pluto_arcsec_per_min=rate, t_mid_err_min=clk["t_mid_err"], arcsec_for_1sigma=rate*clk["t_mid_err"])


R["ma731_timing"] = timing(c, pra, pde)
R["ma731_timing"]["clock_region_distance_from_pluto_deg"] = sep_arcsec(float(np.median(ra)), float(np.median(de)), pra[1], pde[1])/3600
out, P731, M731, mf731 = run_plate("ma731", MA, 1, (pra[1], pde[1]), (pra[0], pde[0]), (pra[2], pde[2]), 1908.973, 16.33)
R["ma731"] = out
R["ma731"]["nearest_gaia"] = nearest_gaia(P731, M731["free_centroid_ra"], M731["free_centroid_dec"])
# the archive-time position (a second hypothesis, reported as a control)
_, ara, ade, _ = horizons("999", None, times=["1908-12-21 " + exp["datetime"][11:19]], site=TAUNTON)
X, Y = P731.sky2pix(ara[0], ade[0])
from scipy import ndimage as nd  # noqa: E402
R["ma731_archive_time_snr"] = float((nd.map_coordinates(mf731, [Y, X], order=1)[0]-M731["base"])/M731["noise"])
# the same free search as at the trail-time prediction (brightest filtered pixel within 8 pixels, windowed centroid)
_fx, _fy = plates.free_centroid(P731, mf731, float(np.ravel(X)[0]), float(np.ravel(Y)[0]), M731["sigma_px"])
_fe, _fn = P731.pix2std(_fx, _fy); _pe, _pn = P731.pix2std(float(np.ravel(X)[0]), float(np.ravel(Y)[0]))
R["ma731_archive_time_free_search"] = dict(
    snr_at_centroid=float((nd.map_coordinates(mf731, [[_fy], [_fx]], order=1)[0]-M731["base"])/M731["noise"]),
    offset_arcsec=float(np.hypot(float(np.ravel(_fe)[0]-np.ravel(_pe)[0]), float(np.ravel(_fn)[0]-np.ravel(_pn)[0]))))
_cra, _cde = P731.pix2sky(_fx, _fy)
R["ma731_archive_time_free_search"]["nearest_gaia"] = nearest_gaia(P731, float(np.ravel(_cra)[0]), float(np.ravel(_cde)[0]))
R["ma731_archive_time_free_search"]["from_image_arcsec"] = float(np.hypot(
    (float(np.ravel(_cra)[0])-M731["free_centroid_ra"])*np.cos(np.radians(M731["free_centroid_dec"])),
    float(np.ravel(_cde)[0])-M731["free_centroid_dec"])*3600)
R["ma731_archive_time_free_search"]["prediction_from_image_arcsec"] = float(np.hypot(
    (float(ara[0])-M731["free_centroid_ra"])*np.cos(np.radians(M731["free_centroid_dec"])), float(ade[0])-M731["free_centroid_dec"])*3600)
R["ma731_skybot"] = skybot(M731["free_centroid_ra"], M731["free_centroid_dec"], times[1].replace(" ", "T"), "500")

# ---------------------------------------------------------------- Heidelberg, 20 February 1909
HD = dict(B2247a=("1909-02-20 18:50:10", "1909-02-20 20:20:11", "1909-02-20 21:50:12"),
          B2248b=("1909-02-20 18:50:22", "1909-02-20 20:20:23", "1909-02-20 21:50:24"))
ASTEROIDS = {"168": (79.6243, 18.2293), "417": (82.8265, 15.2092)}
tracks = {}
for a in ASTEROIDS:
    st, ra, de, _ = horizons(f"{a};", "024", start="1909-02-20 10:00", stop="1909-02-20 23:59")
    tracks[a] = (np.array([minutes(s, "1909-Feb-20 10:00") for s in st]), ra, de)
feb = {}
for plate, (t0, tm, t1) in HD.items():
    clocks = {}
    for a, (ara_, ade_) in ASTEROIDS.items():
        cut = gavo_cutout(plate, ara_, ade_, 0.3)
        T, ra, de = tracks[a]
        cc = clock.fit_trail(cut, 0, T, ra, de, 1909.14, str(W/f"gaia_clock_{plate}_{a}.fits"))
        arch = int(tm[11:13])*60+int(tm[14:16])+int(tm[17:19])/60-600  # minutes after 10:00 UT
        cc.update(t_mid_ut=hhmmss(cc["t_mid"], 10), minus_archive_min=cc["t_mid"]-arch)
        clocks[a] = cc
    R[f"{plate}_clocks"] = clocks
    _, pra, pde, pv = horizons("999", "024", times=[t0, tm, t1])
    R[f"{plate}_pluto_prediction"] = dict(times=[t0, tm, t1], ra=pra.tolist(), dec=pde.tolist(), V=float(pv[1]))
    R[f"{plate}_timing"] = timing(clocks["417"], pra, pde)
    R[f"{plate}_timing"]["clock_region_distance_from_pluto_deg"] = sep_arcsec(*ASTEROIDS["417"], pra[1], pde[1])/3600
    cut = gavo_cutout(plate, 84.96154, 16.13351, 0.7)
    out, P, M, mf = run_plate(plate.lower(), cut, 0, (pra[1], pde[1]), (pra[0], pde[0]), (pra[2], pde[2]), 1909.14, 16.40)
    out["nearest_gaia"] = nearest_gaia(P, M["free_centroid_ra"], M["free_centroid_dec"])
    R[plate] = out
    feb[plate] = (P, M, mf)
R["feb_skybot"] = skybot(84.96154, 16.13351, "1909-02-20T20:20:00", "024")

# ---------------------------------------------------------------- joint random-position control
# One random sky offset moves all three predictions together (keeping Pluto's motion). At every moved prediction
# the measurement's own statistic is replayed (plates.replay: brightest filtered pixel within 8 pixels, windowed
# centroid, S/N at the centroid, centroid distance from the prediction, Gaia veto within 3"). Index 0 is the real
# prediction, whose replayed values are the thresholds: an offset is a hit on a plate when its S/N is at least the
# real one and its distance at most the real one. The search rule instead accepts any S/N >= 4 in the window.
from scipy.spatial import cKDTree  # noqa: E402
from scipy.stats import chi2  # noqa: E402
J = dict(ma731=(P731, M731, mf731, 1908.973), b2247a=(*feb["B2247a"], 1909.14), b2248b=(*feb["B2248b"], 1909.14))
rng = np.random.default_rng(1909); off = rng.uniform(-1500, 1500, (300000, 2)); off = off[np.hypot(off[:, 0], off[:, 1]) > 60]
inside = np.ones(len(off), bool); obs = {}; srch = {}; R["replay_at_prediction"] = {}; dists = {}
crowd_ok = np.ones(len(off), bool); crowd_lit = np.ones(len(off), bool); R["gaia_within_60as_at_pluto"] = {}
R["crowding_tolerance"] = {}
for lab, (P, M, mf, ep) in J.items():
    px, py = P.T.std(M["ra"], M["dec"])
    xi = np.r_[px, px+off[:, 0]]; eta = np.r_[py, py+off[:, 1]]
    X, Y = P.std2pix(xi[1:], eta[1:]); inside &= (X > 60) & (Y > 60) & (X < P.nx-60) & (Y < P.ny-60)
    snr, dist, cat, dpx = plates.replay(P, mf, M, xi, eta, prefilter_snr=4.0)
    s0, d0 = float(snr[0]), float(dist[0]); dists[lab] = dist[1:]
    R["replay_at_prediction"][lab] = dict(snr=s0, offset_arcsec=d0, gaia_within_3as=bool(cat[0]), offset_px=float(dpx[0]))
    obs[lab] = (snr[1:] >= s0) & (dist[1:] <= d0); obs[lab+"_u"] = obs[lab] & ~cat[1:]
    srch[lab] = snr[1:] >= 4.0; srch[lab+"_u"] = srch[lab] & ~cat[1:]
    srch[lab+"_u3"] = srch[lab+"_u"] & (dist[1:] <= 3.0)  # cut chosen after seeing the search-rule counts
    # the outside review's alternative (2026-11-20): the final centroid also within 8 pixels of the prediction,
    # applied to the real measurement (index 0, which passes it) and to every shifted one alike
    assert dpx[0] <= 8.0
    srch[lab+"_8"] = srch[lab] & (dpx[1:] <= 8.0); srch[lab+"_u8"] = srch[lab+"_u"] & (dpx[1:] <= 8.0)
    gra, gde, G = P.gaia; gt = cKDTree(np.c_[P.T.std(gra, gde)])
    n0 = len(gt.query_ball_point([px, py], 60.0)); R["gaia_within_60as_at_pluto"][lab] = n0
    cnt = np.array([len(l) for l in gt.query_ball_point(np.c_[xi[1:], eta[1:]], 60.0)])
    tol = max(2, round(0.2*n0)); R["crowding_tolerance"][lab] = dict(n=n0, admitted=[n0-tol, n0+tol])
    crowd_ok &= np.abs(cnt-n0) <= tol
    crowd_lit &= np.abs(cnt-n0) <= 0.2*n0  # 20% taken literally (a non-integer bound)
    R["crowding_tolerance"][lab]["admitted_literal_20pct"] = [int(np.ceil(0.8*n0)), int(np.floor(1.2*n0))]
crowd_ok &= inside; crowd_lit &= inside


def tally(sel, keys, within):
    h = within.copy()
    for k in keys:
        h &= sel[k]
    k, n = int(h.sum()), int(within.sum())
    return dict(hits=k, trials=n, rate=k/n, upper95=float(chi2.ppf(0.95, 2*k+2)/2/n))


R["joint_null"] = {
    "observed values, ma731": tally(obs, ["ma731"], inside),
    "observed values, b2247a": tally(obs, ["b2247a"], inside),
    "observed values, b2248b": tally(obs, ["b2248b"], inside),
    "observed values, uncatalogued, ma731": tally(obs, ["ma731_u"], inside),
    "observed values, b2247a & b2248b": tally(obs, ["b2247a", "b2248b"], inside),
    "observed values, uncatalogued, b2247a & b2248b": tally(obs, ["b2247a_u", "b2248b_u"], inside),
    "observed values, all three plates": tally(obs, ["ma731", "b2247a", "b2248b"], inside),
    "observed values, uncatalogued, all three plates": tally(obs, ["ma731_u", "b2247a_u", "b2248b_u"], inside),
    "search rule, all three plates": tally(srch, ["ma731", "b2247a", "b2248b"], inside),
    "search rule, uncatalogued, all three plates": tally(srch, ["ma731_u", "b2247a_u", "b2248b_u"], inside),
    "after seeing the data: search rule, uncatalogued, centroid within 3 arcsec, all three plates":
        tally(srch, ["ma731_u3", "b2247a_u3", "b2248b_u3"], inside),
    "search rule with the final centroid within 8 pixels, all three plates": tally(srch, ["ma731_8", "b2247a_8", "b2248b_8"], inside),
    "search rule with the final centroid within 8 pixels, uncatalogued, all three plates":
        tally(srch, ["ma731_u8", "b2247a_u8", "b2248b_u8"], inside),
    "crowding-matched, observed values, all three plates": tally(obs, ["ma731", "b2247a", "b2248b"], crowd_ok),
    "crowding-matched, search rule, uncatalogued, all three plates": tally(srch, ["ma731_u", "b2247a_u", "b2248b_u"], crowd_ok),
    "crowding within 20% literally, observed values, all three plates": tally(obs, ["ma731", "b2247a", "b2248b"], crowd_lit),
}
# where the final centroids of the loose-rule, uncatalogued joint matches lie: median distance from the moved prediction
_h = inside & srch["ma731_u"] & srch["b2247a_u"] & srch["b2248b_u"]
R["joint_null"]["search rule, uncatalogued, all three plates"]["median_centroid_distance_arcsec"] = {
    lab: float(np.median(d[_h])) for lab, d in dists.items()}

# Blinded cut-outs: on each plate the image and 11 controls, each control centred so that an uncatalogued peak
# of similar S/N (within 1 of the image's) sits where the image sits relative to the prediction. The panel order
# is shuffled with a fixed seed; figure.py draws the sheet and the key is written separately.
from scipy import ndimage as ndi  # noqa: E402
rngb = np.random.default_rng(1908); blind = {}
for lab, (P, M, mf, ep) in J.items():
    pk = plates.peaks(P, mf, M["base"], M["noise"], M["sigma_px"])
    gra, gde, G = P.gaia; free = cKDTree(np.c_[P.T.std(gra, gde)]).query(np.c_[pk["xi"], pk["eta"]])[0] > 3.0
    px, py = P.T.std(M["ra"], M["dec"]); dxi, deta = M["offset_east"], M["offset_north"]
    far = np.hypot(pk["xi"]-px, pk["eta"]-py) > 120
    X, Y = P.std2pix(pk["xi"], pk["eta"]); edge = (X > 200) & (Y > 200) & (X < P.nx-200) & (Y < P.ny-200)
    cand = np.nonzero(free & far & edge & (np.abs(pk["snr"]-M["snr_at_centroid"]) <= 1.0))[0]
    pick = rngb.choice(cand, size=min(11, len(cand)), replace=False)
    centres = [(px, py)]+[(pk["xi"][i]-dxi, pk["eta"][i]-deta) for i in pick]
    order = rngb.permutation(len(centres))
    g = np.arange(-30, 30.01, 0.5); XI, ETA = np.meshgrid(g, g); stamps = []
    for j in order:
        cx, cy = centres[j]
        Xs, Ys = P.std2pix(cx+XI.ravel(), cy+ETA.ravel())
        stamps.append(((ndi.map_coordinates(mf, [Ys, Xs], order=1).reshape(XI.shape)-M["base"])/M["noise"]).astype(np.float32))
    np.savez_compressed(W/f"blind_{lab}.npz", snr=np.array(stamps), step=0.5)
    blind[lab] = dict(panels=len(centres), image_panel=int(np.nonzero(order == 0)[0][0])+1, candidates=int(len(cand)))
R["blind_cutouts"] = blind

# ---------------------------------------------------------------- motion, December to February
def offsets(M):
    return np.array([M["offset_east"], M["offset_north"]])


d0 = offsets(R["ma731"]["measure"])
R["motion_residual_arcsec"] = {p: float(np.hypot(*(offsets(R[p]["measure"])-d0))) for p in HD}

# ---------------------------------------------------------------- positive control, 23 January 1914
_, cra, cde, _ = horizons("999", "024", times=["1914-01-23 17:38:05", "1914-01-23 18:58:05", "1914-01-23 20:18:06"])
cut = gavo_cutout("B3383a", float(cra[1]), float(cde[1]), 0.7)
R["B3383a_1914_control"], *_ = run_plate("b3383a", cut, 0, (cra[1], cde[1]), (cra[0], cde[0]), (cra[2], cde[2]), 1914.06, 16.27)

# ---------------------------------------------------------------- fixed-site check, 29 December 1923
fra = np.mean([R[p]["measure"]["free_centroid_ra"] for p in HD]); fde = np.mean([R[p]["measure"]["free_centroid_dec"] for p in HD])
cut = gavo_cutout("B4816a", round(float(fra), 5), round(float(fde), 5), 0.7)
R["B4816a_1923_fixed_site"], *_ = run_plate("b4816a", cut, 0, (fra, fde), (fra, fde), (fra, fde), 1923.99, 16.40)

R["apass_source"] = plates.APASS_SOURCE  # live VizieR or the pinned cut, per plate
json.dump(R, open(W/"results.json", "w"), indent=1, default=float)

# ---------------------------------------------------------------- compare with the recorded values
E = json.load(open(HERE.parent/"data"/"expected.json"))


def get(path):
    x = R
    for k in path.split("/"):
        x = x[k]
    return x


bad = 0
for row in E["checks"]:
    v = get(row["path"])
    ok = ((row.get("min") is None or v >= row["min"]) and (row.get("max") is None or v <= row["max"])
          and ("equals" not in row or v == row["equals"]))
    bad += not ok
    print(f"{'ok  ' if ok else 'FAIL'} {row['what']}: {v if not isinstance(v, float) else round(v, 3)}")
for lab, how in plates.APASS_SOURCE.items():
    print(f"APASS source for {lab}: {how}")
print("all checks pass" if not bad else f"{bad} checks failed")
sys.exit(1 if bad else 0)
