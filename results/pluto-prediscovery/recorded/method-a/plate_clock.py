"""Infer MA exposure midpoints from bright, identified minor-planet trails."""
import argparse
import base64
import csv
import gzip
import hashlib
import json
from pathlib import Path

from astropy.time import Time
import numpy as np
import requests
from scipy.linalg import qr
from scipy.optimize import least_squares

from audit_ma731 import local_astrometry
from extra_inputs import gaia
from fetch import HORIZONS, archive
from measure import Plate, chip, gaussian, grid


def ephemeris(body, site, dates):
    coords = f"{-site['lon']},{site['lat']},{site['elevation']/1000}"
    params = dict(format="json", COMMAND=f"'{body}'", CENTER="'coord@399'",
                  COORD_TYPE="'GEODETIC'", SITE_COORD=f"'{coords}'", TIME_DIGITS="'FRACSEC'",
                  TLIST="'"+",".join(f"{t:.9f}" for t in dates)+"'",
                  QUANTITIES="'1,9,36'", ANG_FORMAT="'DEG'", CSV_FORMAT="'YES'",
                  EXTRA_PREC="'YES'", OBJ_DATA="'NO'")
    response = requests.get(HORIZONS, params=params, timeout=90)
    response.raise_for_status()
    table = response.json()["result"].split("$$SOE")[1].split("$$EOE")[0].strip()
    return [[float(v) if v.strip() != "n.a." else None for v in (r[3:6]+r[7:9])]
            for r in csv.reader(table.splitlines())]


def get_field(base, name, asteroid):
    folder = base / (asteroid+"-"+name)
    folder.mkdir(parents=True, exist_ok=True)
    original = archive("plates/p/"+name)
    exposure, = original["catalog_exposures"]
    date, duration = exposure["datetime"], exposure["exposure_length"]
    jd = Time(date.rstrip("Z"), scale="ut1").jd
    site = original["location"]
    clock_grid = np.arange(-12, 12.25, .25)
    # Include both ends of the full 181-minute trail for interpolation.
    hours = np.arange(-14, 14.25, .25)
    # Split the Horizons lists to respect its limit on individual input lines.
    coords = np.array([row for times in np.array_split(jd+hours/24, 4)
                       for row in ephemeris(asteroid+";", site, times)])
    geom = [np.interp([-duration/120, 0, duration/120], hours, coords[:,i]) for i in range(3)]
    center = np.round(coords[hours==0, :2][0], 3)
    patch = dict(plate_id=name, solution_number=0, center_ra_deg=center[0], center_dec_deg=center[1])
    if not (folder / (name+".fits")).exists():
        scan = archive("dasch/dr7/cutout", patch)
        (folder / (name+".fits")).write_bytes(gzip.decompress(base64.b64decode(scan)))
    gaia(folder, "ma", *center)
    if not (folder / "ma-apass.csv").exists():
        apass = archive("dasch/dr7/querycat", dict(refcat="apass", ra_deg=center[0],
                        dec_deg=center[1], radius_arcsec=1200))
        (folder / "ma-apass.csv").write_text("\n".join(apass)+"\n")
    record = dict(midpoint=date, minutes=duration, location=site,
                  endpoint_midpoint_endpoint=np.transpose(geom).tolist(), cutout=patch)
    (folder / (name+".json")).write_text(json.dumps(record, indent=2)+"\n")
    plate = Plate(folder, name)
    # Apply the same affine correction used by Plate.align to nearby sky
    # positions. Derive it from the resulting propagated catalogue positions.
    from measure import column, read_rows
    stars = read_rows(folder / "ma-gaia.csv")
    dec = column(stars, "dec")
    years = plate.year-2016
    ra = column(stars, "ra")+column(stars,"pmra")*years/(3.6e6*np.cos(np.deg2rad(dec)))
    dec += column(stars,"pmdec")*years/3.6e6
    raw = plate.wcs.all_world2pix(np.column_stack((ra, dec)), 0)
    mat = np.linalg.lstsq(np.column_stack((np.ones(len(raw)),raw)),plate.xy,rcond=None)[0]
    pixels = plate.wcs.all_world2pix(coords[:,:2], 0)
    pixels = np.column_stack((np.ones(len(pixels)),pixels))@mat
    def pos(hour):
        return np.array([np.interp(hour,hours,dim) for dim in pixels.T])
    return folder, plate, jd, duration, clock_grid, pos, coords[hours==0, 3:][0]


def stamp_model(p, xy, trail):
    # Enclose either end of the trail and the native PSF in a rectangular stamp.
    extent = np.ceil(abs(trail)*.7 + 3.5*max(p.sig[:2])+4).astype(int)
    yy, xx = np.mgrid[-extent[1]:extent[1]+1, -extent[0]:extent[0]+1]
    delta = np.column_stack((xx.ravel(), yy.ravel()))
    q = delta + np.rint(xy) - xy
    data = chip(p.img, xy, delta)
    good = np.isfinite(data)
    q, data = q[good], data[good]
    cols = [np.ones(len(q)), q[:,0], q[:,1]]
    for i in p.tree.query_ball_point(xy, np.linalg.norm(extent)+14):
        if p.g[i] < 18.7 and np.all(np.abs(p.xy[i]-xy) < extent+12):
            cols.append(gaussian(q-(p.xy[i]-xy),p.sig))
    design = np.column_stack(cols)
    basis, r, _ = qr(design, mode="economic", pivoting=True)
    basis = basis[:, abs(np.diag(r)) > 1e-6*np.linalg.norm(design, axis=0).max()]
    def project(v):
        return v-basis@(basis.T@v)
    sky_removed = project(data)
    times = (np.arange(25)+.5)/25-.5
    normal = np.array([-trail[1],trail[0]])/np.linalg.norm(trail)
    def model(par):
        dx, dy, length, side = par
        vec = length*trail+side*normal
        shape = project(np.mean([gaussian(q-[dx,dy]-t*vec,p.sig) for t in times],axis=0))
        amplitude = max(0,(shape@sky_removed)/(shape@shape))
        return amplitude, sky_removed-amplitude*shape
    return model, sky_removed


def clock(base, name, asteroid, test_hour=None):
    folder, p, jd, duration, hours, pos, err = get_field(base, name, asteroid)
    def trail(hour):
        return pos(hour+duration/120)-pos(hour-duration/120)
    # A blind physical clock uses only the bright asteroid. On the corroborating
    # asteroid use a single specified hour, never optimize over the day's path.
    def score(hour, side=0):
        vec = trail(hour)
        perp = np.array([-vec[1],vec[0]])/np.linalg.norm(vec)
        model, data = stamp_model(p,pos(hour)+side*perp,vec)
        amp, resid = model([0,0,1,0])
        return amp, 1-(resid@resid)/(data@data)
    if test_hour is None:
        feasible = [h for h in hours if np.all(pos(h)>85) and np.all(pos(h)<np.array(p.img.shape[::-1])-85)]
        scores = [(h,*score(h)) for h in feasible]
        hour, _, _ = max(scores, key=lambda x: x[2])
    else:
        hour = test_hour
        scores = [(hour,*score(hour))]
    first_hour = hour
    for iteration in range(3):
        vec = trail(hour)
        model, data = stamp_model(p, pos(hour), vec)
        sol = least_squares(lambda z:model(z)[1], [0,0,1,0],
                            bounds=([-12,-12,.2,-12],[12,12,2,12]))
        if not sol.success:
            raise ValueError("Asteroid fit failed")
        offset, factor, side = sol.x[:2], sol.x[2], sol.x[3]
        dt = offset@vec/(vec@vec)*duration/60
        if iteration < 2:
            hour += dt
    amp, resid = model(sol.x)
    point = least_squares(lambda v:model([*v,0,0])[1], [0,0], bounds=(-12,12))
    scale = np.sqrt(abs(np.linalg.det(p.wcs.pixel_scale_matrix)))*3600
    perpendicular = offset - vec*(offset@vec)/(vec@vec)
    local = local_astrometry(p, folder, scale)
    center = hour+dt
    return dict(asteroid=asteroid, plate=name, header_midpoint=p.meta["midpoint"],
                nominal_duration_min=duration, asteroid_horizons_3sigma_as=err.tolist(),
                seed_hour=first_hour, measured_midpoint_UT1=Time(jd+center/24,format="jd",scale="ut1").isot,
                clock_offset_min=center*60, midpoint_cross_as=np.linalg.norm(perpendicular)*scale,
                model_trail_as=np.linalg.norm(vec)*scale, observed_trail_as=np.hypot(factor*np.linalg.norm(vec),side)*scale,
                equivalent_duration_min=duration*np.hypot(factor, side/np.linalg.norm(vec)),
                trail_angle_residual_deg=np.rad2deg(np.arctan2(side,factor*np.linalg.norm(vec))),
                amp=amp, improvement_over_background=1-resid@resid/(data@data),
                improvement_over_point=1-resid@resid/(point.fun @ point.fun),
                nominal_score=score(0), seed_score=score(first_hour),
                cross_track_controls=[score(first_hour,d) for d in [-75,-50,50,75]],
                clock_search_count=len(scores), next_best_outside_one_duration=max(
                    (r[2] for r in scores if abs(r[0]-first_hour)*60>duration),default=None),
                registration=p.reg, local_median_xy_as=local["median_xy_as"],
                local_radial_p90_as=local["radial_p90_as"], local_star_count=len(local["stars"]),
                input_hashes={f.name:hashlib.sha256(f.read_bytes()).hexdigest() for f in sorted(folder.iterdir())})


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("scratch", type=Path)
    ap.add_argument("plate", choices=["ma00731","ma00733"])
    ap.add_argument("asteroid", choices=["179","1436","2891"])
    ap.add_argument("--test-hour", type=float, help="At a second asteroid, seed only at the specified clock offset")
    args = ap.parse_args()
    print(json.dumps(clock(args.scratch,args.plate,args.asteroid,args.test_hour),
                     indent=2, allow_nan=False))
