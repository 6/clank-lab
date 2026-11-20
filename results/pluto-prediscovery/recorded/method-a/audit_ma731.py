"""Check the MA 731 solution against local stars, archive timing and two JPL orbits."""
import argparse
import base64
import csv
import gzip
import hashlib
import json
from pathlib import Path

from astropy.io import fits
from astropy.time import Time
from astropy.wcs import WCS
from jplephem.spk import SPK
import numpy as np
import requests
from scipy.optimize import least_squares

from fetch import HORIZONS, archive
from measure import Plate, chip, gaussian, grid, offsets, read_rows


KERNEL_HASH = "a20a7139da04cbc462454634918e9a9ca69127044e2cc9d4f9c16e238d2deedc"


def horizons(body, center, jd, quantities, site=None):
    params = dict(format="json", COMMAND=f"'{body}'", CENTER=f"'{center}'",
                  TLIST=f"'{jd:.9f}'", QUANTITIES=f"'{quantities}'",
                  ANG_FORMAT="'DEG'", CSV_FORMAT="'YES'", EXTRA_PREC="'YES'",
                  OBJ_DATA="'NO'", TIME_DIGITS="'FRACSEC'")
    if site:
        coords = f"{-site['lon']},{site['lat']},{site['elevation']/1000}"
        params.update(COORD_TYPE="'GEODETIC'", SITE_COORD=f"'{coords}'")
    response = requests.get(HORIZONS, params=params, timeout=90)
    response.raise_for_status()
    table = response.json()["result"].split("$$SOE")[1].split("$$EOE")[0].strip()
    return [entry.strip() for entry in next(csv.reader([table]))]


def older_orbit(kernel, jd):
    if hashlib.sha256(kernel.read_bytes()).hexdigest() != KERNEL_HASH:
        raise ValueError("Expected JPL DE421 kernel")
    with SPK.open(kernel) as eph:
        earth = eph[0, 3].compute(jd) + eph[3, 399].compute(jd)
        delta = eph[0, 9].compute(jd) - earth
        for _ in range(4):
            light_days = np.linalg.norm(delta) / (299792.458 * 86400)
            delta = eph[0, 9].compute(jd - light_days) - earth
    return np.rad2deg([np.arctan2(delta[1], delta[0]),
                       np.arcsin(delta[2] / np.linalg.norm(delta))])


def east_north(a, b):
    a, b = np.asarray(a), np.asarray(b)
    return (b-a) * [3600*np.cos(np.deg2rad((a[1]+b[1])/2)), 3600]


def local_astrometry(p, folder, scale):
    ids = read_rows(folder / "ma-gaia.csv")
    rows = []
    masked = []
    window = grid(12)
    for i, (xy, mag) in enumerate(zip(p.xy, p.g)):
        radius = offsets(xy, p.target)
        if radius > 120 or not 10 < mag < 16:
            continue
        # The affine registration and PSF use only stars outside 125 pixels.
        near = p.tree.query_ball_point(xy, 13)
        if any(j != i and p.g[j] < mag+2 for j in near):
            continue
        q = window + np.rint(xy) - xy
        data = chip(p.img, xy, window)
        usable = np.isfinite(data)
        if usable.mean() < .9:
            masked.append(ids[i]["source_id"])
            continue
        data, q = data[usable], q[usable]
        def residual(par):
            dx, dy, amplitude, sky, sx, sy = par
            return amplitude*gaussian(q-[dx, dy], p.sig) + sky + q@[sx, sy] - data
        sky = np.median(data)
        fit = least_squares(residual, [0, 0, max(data.max()-sky, 1), sky, 0, 0],
                            bounds=([-8, -8, 0, -np.inf, -np.inf, -np.inf],
                                    [8, 8, np.inf, np.inf, np.inf, np.inf]))
        if not fit.success:
            raise ValueError("Centroid fit failed")
        rows.append(dict(source=ids[i]["source_id"], G=mag, radius_as=radius*scale,
                         residual_xy_px=fit.x[:2].tolist()))
    rows.sort(key=lambda r: r["radius_as"])
    residuals = np.array([r["residual_xy_px"] for r in rows]) * scale
    lengths = np.linalg.norm(residuals, axis=1)
    return dict(stars=rows, masked_stars=masked, median_xy_as=np.median(residuals, axis=0).tolist(),
                radial_rms_as=np.sqrt(np.mean(lengths**2)),
                radial_p90_as=np.quantile(lengths, .9), max_as=lengths.max())


def stamp_scatter(p, xy):
    q = p.delta + np.rint(xy) - xy
    data = chip(p.img, xy, p.delta)
    good = np.isfinite(data)
    q, data = q[good], data[good]
    terms = [np.ones(len(q)), q[:, 0], q[:, 1]]
    for i in p.tree.query_ball_point(xy, 1.65*p.radius):
        if p.g[i] < 18.7:
            terms.append(gaussian(q-(p.xy[i]-xy), p.sig))
    basis = np.column_stack(terms)
    residual = data - basis @ np.linalg.lstsq(basis, data, rcond=1e-6)[0]
    return np.median(np.abs(residual-np.median(residual)))


def main(folder, kernel, pair):
    p = Plate(folder, "ma00731")
    meta = archive("dasch/dr7/mosaic_package", dict(plate_id=p.name, binning=1))["metadata"]
    original = archive("plates/p/" + p.name)
    exposure, = meta["astrometry"]["exposures"]
    jd = Time(p.meta["midpoint"].rstrip("Z"), format="isot", scale="ut1").jd
    assert exposure["durMin"] == p.meta["minutes"]
    pl = horizons(999, "coord@399", jd, "1,9,14,19,20,24,36,37", original["location"])
    mid = np.array(pl[3:5], dtype=float)
    positions = np.array(p.meta["endpoint_midpoint_endpoint"])[:, :2]
    assert np.allclose(mid, positions[1], rtol=0, atol=1e-8)
    geo = horizons(9, "500@399", jd, "1,30")
    modern = np.array(geo[3:5], dtype=float)
    de421 = older_orbit(kernel, jd + float(geo[5])/86400)
    compare = east_north(modern, de421)
    shift = east_north(positions[0], positions[2])
    raw_wcs = gzip.decompress(base64.b64decode(meta["astrometry"]["b01HeaderGz"]))
    header = fits.Header.fromstring(raw_wcs, sep="\n")
    # DR7 stores TPV coefficients under TAN labels. Use the daschlab convention.
    header["CTYPE1"], header["CTYPE2"] = "RA---TPV", "DEC--TPV"
    native = WCS(header, naxis=2).all_world2pix([mid], 0)[0]
    native_size = np.array([header["NAXIS1"], header["NAXIS2"]])
    scale = float(np.sqrt(abs(np.linalg.det(p.wcs.pixel_scale_matrix)))*3600)
    local = local_astrometry(p, folder, scale)
    stamp = chip(p.img, p.target, p.delta)
    scatter = stamp_scatter(p, p.target)
    nearby = [stamp_scatter(p, p.target+[x,y])
              for x,y in grid(4)*28 if 28 <= np.hypot(x,y) <= 120]
    r, distance, phase = (float(pl[i]) for i in [9, 11, 13])
    colour_b = float(pl[5]) + .78
    geometry_b = 15.73 + 5*np.log10(r*distance/1520.7) + .0372*phase
    p.calibrate()
    measurement = p.response(p.target, p.trail)
    threshold = json.loads(pair.read_text())["plates"][0]["null_threshold"]
    standards = [a for (_,m,c), (_,a) in zip(p.refs[1::2], p.validation)
                 if abs(m-16.33) <= .25 and abs(c-.78) <= .25]
    q = p.delta + np.rint(p.target)-p.target
    assert np.isfinite(stamp).all()
    scores = {}
    for radius_as in [0, 1, 3, 6]:
        values = []
        for angle in np.arange(8)*np.pi/4:
            displacement = radius_as/scale*np.array([np.cos(angle), np.sin(angle)])
            tracks = np.array([gaussian(q-displacement-t*p.trail, p.sig)
                               for t in np.linspace(-.5, .5, 9)])
            values.append(p.injected((*measurement[:3], tracks), geometry_b))
        scores[str(radius_as)] = [min(values), max(values)]
    trail_peak = np.mean([gaussian(np.array([t*p.trail]), p.sig)[0]**(1/p.gamma)
                          for t in np.linspace(-.5, .5, 9)])**p.gamma
    return dict(logbook_exposure=exposure, site=original["location"], jacket_or_plate_markings=original["has_markings"],
                horizons=dict(UT=pl[0], ICRF_deg=mid.tolist(), V=float(pl[5]), subobserver_deg=pl[7:9],
                              r_AU=r, delta_AU=distance, phase_deg=phase, uncertainties=pl[14:20],
                              geocentric_barycenter_deg=modern.tolist(), tdb_minus_ut_s=float(geo[5]),
                              DE421_geocentric_barycenter_deg=de421.tolist(),
                              DE421_minus_modern_east_north_as=compare.tolist()),
                trail=dict(east_north_as=shift.tolist(), length_as=np.linalg.norm(shift),
                           pa_deg=np.degrees(np.arctan2(*shift))%360, pixels=np.linalg.norm(p.trail),
                           time_accuracy_minutes=exposure["dateAccDays"]*1440,
                           timing_shift_as=np.linalg.norm(shift)*exposure["dateAccDays"]*1440/exposure["durMin"],
                           isolated_trailed_to_point_peak=trail_peak),
                astrometry=local, image=dict(wcs_sha256=hashlib.sha256(raw_wcs).hexdigest(),
                    native_xy=native.tolist(), native_dimensions=native_size.tolist(),
                    native_edge_px=np.min(np.minimum(native, native_size-1-native)),
                    cutout_xy=p.target.tolist(), cutout_dimensions=list(p.img.shape[::-1]),
                    cutout_edge_px=np.min(np.minimum(p.target, np.array(p.img.shape[::-1])-1-p.target)),
                    scale_as_per_px=scale, stamp_finite=int(np.isfinite(stamp).sum()),
                    stamp_min_max=[stamp.min(), stamp.max()], cutout_min_max=[np.nanmin(p.img),np.nanmax(p.img)],
                    stamp_MAD=scatter, local_MAD_median=np.median(nearby),
                    local_MAD_at_most=int(np.sum(np.array(nearby)<=scatter)), local_stamps=len(nearby)),
                photometry=dict(B_V_model=colour_b, B_1933_opposition_model=geometry_b,
                    colourterm_apass=meta["photometry"]["medianColortermApass"],
                    colourterm_atlas=meta["photometry"]["medianColortermAtlas"],
                    calibration_median_B_minus_V=np.median([c for _,_,c in p.refs[::2]]),
                    colour_matched_stars=len(standards), triggered=int(np.sum(np.array(standards)>threshold)),
                    threshold=threshold, measured_score=measurement[0],
                    injected_score_range_by_offset_arcsec=scores))


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("data", type=Path)
    ap.add_argument("de421", type=Path)
    ap.add_argument("pair", type=Path, help="Measurement at the same midpoint")
    args = ap.parse_args()
    print(json.dumps(main(args.data, args.de421, args.pair), indent=2, allow_nan=False))
