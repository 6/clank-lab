"""The single Pan-STARRS z detection 0.9 arcsec from the MA 731 image: its catalogue records and its pixels.

Usage: python ps1_detection.py WORKDIR [OUT.pdf]

Reads from MAST the Pan-STARRS DR2 mean-object and detection records of object 127220858937860206, the z-band
detections within 3 arcmin on the two nights 2010-11-07 and 2010-11-08, and the PS1 image list at the position;
downloads the z warp of each night with its mask and the z stack with its mask (skycell 1699.009, about 135 MB);
then measures, at the detection's position:

  * the mask bits and finite pixels in each image;
  * a forced aperture flux over the finite pixels that carry no mask bit (radius 1.5 arcsec, local annulus
    4-6 arcsec), its nominal error (independent pixels) and an empirical error from the same aperture at 400 nearby
    places, calibrated to Jy on the
    same night's catalogued z detections (median ratio of aperture counts to the catalogue PSF flux), so that the
    detection's own flux, 0.90 mJy (z 16.51), can be compared with what each image shows there.

It writes WORKDIR/ps1_detection.json and, if OUT is given, a four-panel figure (15 arcsec square, north up,
east left): the preceding night's warp, the detection night's warp (undefined pixels orange), the pixels that warp's
mask flags as a cosmic ray (bit 256), and the stack. The circle has radius 1 arcsec.
"""
import json
import sys
import warnings
from pathlib import Path

import numpy as np
import requests

warnings.filterwarnings("ignore")
from astropy.io import fits  # noqa: E402
from astropy.wcs import WCS  # noqa: E402

MAST = "https://catalogs.mast.stsci.edu/api/v0.1/panstarrs/dr2"
IMG = "https://ps1images.stsci.edu"
OBJ, DET = 127220858937860206, 140762759360000513
CELL = "rings.v3.skycell/1699/009/rings.v3.skycell.1699.009"
IMAGES = {"warp 2010-11-07": "wrp.z.55507_65222", "warp 2010-11-08 (the detection)": "wrp.z.55508_62720",
          "stack": "stk.z.unconv"}
# Bit names from the PS1 detection-flag table (outerspace.stsci.edu, "PS1 Detection Flags", read 2026-11-20).
INFOFLAG = {0x1: "PSFMODEL", 0x800: "DEFECT (source is thought to be a defect)",
            0x2000: "CR_LIMIT (source has crNsigma above limit)", 0x200000: "AP_MAGS"}
W = Path(sys.argv[1]).resolve()
W.mkdir(parents=True, exist_ok=True)


def get(name, url, params=None):
    p = W/name
    if not p.exists():
        r = requests.get(url, params=params, timeout=600, stream=True)
        r.raise_for_status()
        with open(p.with_suffix(".part"), "wb") as f:
            for chunk in r.iter_content(1 << 20):
                f.write(chunk)
        p.with_suffix(".part").rename(p)
    return p


def table(name, endpoint, **params):
    import csv
    return list(csv.DictReader(open(get(name, f"{MAST}/{endpoint}.csv", params))))


R = {}
mean = table("ps1_mean.csv", "mean", objID=OBJ)[0]
det = table("ps1_detection.csv", "detection", objID=OBJ)
R["mean"] = {k: mean[k] for k in ("objID", "raMean", "decMean", "nDetections", "nStackDetections", "ng", "nr", "ni",
                                  "nz", "ny", "zMeanPSFMag", "raStack")}
assert len(det) == 1 and int(det[0]["detectID"]) == DET
d = det[0]
flag = int(d["infoFlag"])
R["detection"] = {k: d[k] for k in ("detectID", "obsTime", "filterID", "imageID", "ra", "dec", "psfFlux", "psfFluxErr",
                                    "psfMajorFWHM", "psfMinorFWHM", "extNSigma", "psfChiSq", "infoFlag", "infoFlag2",
                                    "infoFlag3", "expTime")}
R["detection"]["infoFlag_hex"] = hex(flag)
R["detection"]["infoFlag_bits"] = [INFOFLAG.get(b, hex(b)) for b in (1 << i for i in range(32)) if flag & b]
R["detection"]["z_mag"] = float(-2.5*np.log10(float(d["psfFlux"])/3631))
ra0, de0 = float(d["ra"]), float(d["dec"])

cone = table("ps1_cone_z.csv", "detection", ra=ra0, dec=de0, radius=0.05, filterID=4,
             **{"obsTime.min": 55500, "obsTime.max": 55515}, pagesize=5000,
             columns="objID,detectID,obsTime,imageID,ra,dec,psfFlux,infoFlag")
nights = sorted({c["obsTime"][:5] for c in cone})
R["z_exposures_within_3arcmin_2010_11_01_to_15"] = {
    n: dict(detections=sum(c["obsTime"].startswith(n) for c in cone),
            nearest_other_arcsec=float(min(np.hypot((float(c["ra"])-ra0)*np.cos(np.radians(de0)), float(c["dec"])-de0)*3600
                                           for c in cone if c["obsTime"].startswith(n) and int(c["objID"]) != OBJ)))
    for n in nights}
files = get("ps1_files.txt", f"{IMG}/cgi-bin/ps1filenames.py", dict(ra=ra0, dec=de0, type="warp,stack", filters="z"))
rows = [l.split() for l in open(files).read().splitlines()[1:]]
R["z_warp_epochs_mjd"] = sorted({float(r[5]) for r in rows if r[6] == "warp"})


def load(stem, half=800):
    """The image and mask within half px of the detection (0.25"/px), with the full image's WCS and the offset."""
    im = fits.open(get(f"{stem}.fits", f"{IMG}/{CELL}.{stem}.fits"))[1]
    mk = fits.open(get(f"{stem}.mask.fits", f"{IMG}/{CELL}.{stem}.mask.fits"))[1]
    w = WCS(im.header); x, y = (int(round(float(v))) for v in w.all_world2pix(ra0, de0, 0))
    y0, x0 = max(0, y-half), max(0, x-half)
    a = np.array(im.section[y0:y+half, x0:x+half], float)
    if im.header.get("BSOFTEN"):  # stacks are stored asinh-compressed
        a = im.header["BOFFSET"]+im.header["BSOFTEN"]*2*np.sinh(a/(2.5*np.log10(np.e)))
    return a, np.array(mk.section[y0:y+half, x0:x+half], np.int64), w, x0, y0


def aperture(a, x, y, m=None, r=6.0, r1=16.0, r2=24.0):
    """Sum within r px (0.25"/px) minus the annulus median over the usable pixels, the nominal noise (annulus robust
    scatter times the root of the pixel count, which assumes independent pixels), and the usable fraction. Usable
    pixels are finite and, when a mask m is given, carry no mask bit."""
    yy, xx = np.mgrid[-30:31, -30:31]; rr = np.hypot(xx-(x-round(x)), yy-(y-round(y)))
    sl = np.s_[int(round(y))-30:int(round(y))+31, int(round(x))-30:int(round(x))+31]; s = a[sl]
    good = np.isfinite(s) if m is None else np.isfinite(s) & (m[sl] == 0)
    ann = s[(rr >= r1) & (rr < r2) & good]; med = np.median(ann); sd = 1.4826*np.median(np.abs(ann-med))
    core = (rr < r) & good
    return float(np.sum(s[core]-med)), float(sd*np.sqrt(core.sum())), float(core.sum()/(rr < r).sum())


def empirical_noise(a, m, x, y, n=400, inner=40, outer=200, seed=8):
    """Robust scatter of the same aperture's sums at n random places inside outer px but outside inner px, each
    using only usable pixels and kept when at least 90% of its pixels are usable: a noise estimate that does not
    assume independent pixels."""
    rng = np.random.default_rng(seed); v = []
    while len(v) < n:
        dx, dy = rng.uniform(-outer, outer, 2)
        if np.hypot(dx, dy) < inner or not (31 < x+dx < a.shape[1]-32 and 31 < y+dy < a.shape[0]-32):
            continue
        f, _, fr = aperture(a, x+dx, y+dy, m)
        if fr >= 0.9:
            v.append(f)
    v = np.array(v)
    return float(1.4826*np.median(np.abs(v-np.median(v))))


night = {"warp 2010-11-07": "55507", "warp 2010-11-08 (the detection)": "55508"}
R["images"] = {}
cuts = {}
for lab, stem in IMAGES.items():
    a, m, w, x0, y0 = load(stem)
    x, y = (float(v) for v in w.all_world2pix(ra0, de0, 0)); x -= x0; y -= y0
    f, e, frac = aperture(a, x, y, m)
    _, _, ffin = aperture(a, x, y)
    ee = empirical_noise(a, m, x, y)
    # calibration: catalogued z detections of those nights within 3', unflagged as defects, 1-30 mJy
    ref = [c for c in cone if (lab == "stack" or c["obsTime"].startswith(night[lab])) and int(c["objID"]) != OBJ
           and 1e-3 < float(c["psfFlux"]) < 3e-2 and not int(c["infoFlag"]) & 0x800]
    rat = []
    for c in ref:
        cx, cy = (float(v) for v in w.all_world2pix(float(c["ra"]), float(c["dec"]), 0)); cx -= x0; cy -= y0
        if 40 < cx < a.shape[1]-40 and 40 < cy < a.shape[0]-40:
            cf, _, cfrac = aperture(a, cx, cy, m)
            if cfrac == 1.0 and cf > 0:
                rat.append(cf/float(c["psfFlux"]))
    k = float(np.median(rat)) if rat else np.nan
    xi, yi = int(round(x)), int(round(y)); core = m[yi-4:yi+5, xi-4:xi+5]
    bits = sorted({b for v in np.unique(core) for b in (1 << i for i in range(16)) if v & b})
    R["images"][lab] = dict(file=f"{CELL}.{stem}.fits", pixel=[x+x0, y+y0], finite_fraction_r1p5=ffin,
                            unmasked_fraction_r1p5=frac,
                            mask_bits_within_1arcsec=bits, forced_counts=f, forced_counts_err=e, forced_snr=f/e,
                            counts_per_jy=k, calibration_stars=len(rat), forced_mjy=1e3*f/k, forced_mjy_err=1e3*e/k,
                            detection_snr_expected=float(d["psfFlux"])*k/e,
                            empirical_err_mjy=1e3*ee/k, detection_snr_expected_empirical=float(d["psfFlux"])*k/ee)
    cuts[lab] = (a[yi-30:yi+31, xi-30:xi+31], m[yi-30:yi+31, xi-30:xi+31])
json.dump(R, open(W/"ps1_detection.json", "w"), indent=1, default=float)
for lab, v in R["images"].items():
    print(f"{lab}: finite {v['finite_fraction_r1p5']:.2f}, unmasked {v['unmasked_fraction_r1p5']:.2f}, "
          f"mask bits {v['mask_bits_within_1arcsec']}, forced {v['forced_mjy']:.3f} +- {v['forced_mjy_err']:.3f} mJy "
          f"(nominal; {v['empirical_err_mjy']:.3f} from nearby apertures); a steady 0.90 mJy source would give S/N "
          f"{v['detection_snr_expected']:.0f} nominal, {v['detection_snr_expected_empirical']:.0f} from nearby apertures")

if len(sys.argv) > 2:
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    cm = plt.get_cmap("gray_r").copy(); cm.set_bad("tab:orange")  # pixels the warp leaves undefined (NaN) are orange
    fig, ax = plt.subplots(1, 4, figsize=(8, 2.3))
    panels = [("warp 2010-11-07", 0), ("warp 2010-11-08 (the detection)", 0), ("warp 2010-11-08 (the detection)", 1),
              ("stack", 0)]
    titles = ["z, Nov 7, 2010", "z, Nov 8 (detection)", "Nov 8 mask (CR bit)", "z stack"]
    for a_, (lab, which), t in zip(ax, panels, titles):
        im, mk = cuts[lab]
        if which:
            show = (mk & 256) > 0; a_.imshow(show[::-1, :], cmap="gray_r", vmin=0, vmax=1)
        else:
            sd = 1.4826*np.nanmedian(np.abs(im-np.nanmedian(im)))
            a_.imshow(((im-np.nanmedian(im))/sd)[::-1, :], cmap=cm, vmin=-2, vmax=8)
        a_.add_patch(plt.Circle((30, 30), 4, fill=False, color="tab:blue", lw=0.8))
        a_.set_title(t, fontsize=8); a_.set_xticks([]); a_.set_yticks([])
    fig.tight_layout()
    fig.savefig(sys.argv[2])
