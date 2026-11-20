"""Retrieve independent centroid directions and compare differential photometry to field stars."""
import argparse
import json
from pathlib import Path

import numpy as np
from scipy.ndimage import map_coordinates

from audit_ma731 import east_north, local_astrometry
from measure import Plate, column, offsets, read_rows


def affine(p, rows):
    dt = p.year-2016.
    dec = column(rows,"dec")
    ra = column(rows,"ra")+dt*column(rows,"pmra")/(3.6e6*np.cos(np.deg2rad(dec)))
    dec = dec+dt*column(rows,"pmdec")/3.6e6
    raw = p.wcs.all_world2pix(np.column_stack((ra,dec)),0)
    return np.linalg.lstsq(np.column_stack((np.ones(len(raw)),raw)),p.xy,rcond=None)[0]


def picture(plates, matrices, path):
    from PIL import Image, ImageDraw, ImageFont
    scale = 4
    nx,ny = 131,85
    y,x = np.mgrid[:ny,:nx]
    origin = np.rint(np.mean([p.raw_target for p in plates],axis=0)).astype(int)-[nx//2,ny//2]
    coords = np.stack((np.ones(x.size), x.ravel()+origin[0], y.ravel()+origin[1]),axis=1)
    panels = Image.new("RGB",(nx*scale*2+16,ny*scale+64),"white")
    draw = ImageDraw.Draw(panels)
    font = ImageFont.load_default(size=18)
    for i,(p,mat) in enumerate(zip(plates,matrices)):
        points = coords@mat
        patch = map_coordinates(p.img,[points[:,1],points[:,0]],order=1).reshape(ny,nx)
        lo,hi = np.nanpercentile(patch,[5,99.5])
        im = Image.fromarray(np.nan_to_num(255*np.clip((patch[::-1]-lo)/(hi-lo),0,1)).astype(np.uint8))
        im = im.resize((nx*scale,ny*scale),Image.Resampling.NEAREST)
        left = i*(nx*scale+16)
        panels.paste(im,(left,32))
        draw.text((left+3,4),f"MA {int(p.name[2:])}   {p.meta['midpoint'][:16].replace('T',' ')} UT1",font=font,fill="black")
        for j,other in enumerate(plates):
            a,b = ((other.raw_target-origin+.5)*scale+[left,32]).tolist()
            b = 32+ny*scale-(b-32)
            # Short pointers leave the underlying cutout pixels visible.
            color = "#56dfef" if j==0 else "#ffbc5b"
            draw.line((a,b-44,a,b-31),fill=color,width=2)
            draw.line((a+31,b,a+44,b),fill=color,width=2)
    draw.text((3,ny*scale+38),"Cyan: Dec 21 prediction     Amber: Dec 22 prediction     North up, east left     Field width 189 arcsec",font=font,fill="black")
    panels.save(path)


def null_quantiles(plates):
    # Repeat the frozen neighbourhood matching to expose its amplitude distribution.
    ranked = []
    for x in range(-752, 753, 16):
        for y in range(-752, 753, 16):
            locations = [p.target + [x, y] for p in plates]
            if not all(p.inside(xy) and offsets(xy, p.raw_target) > 145 for p, xy in zip(plates, locations)):
                continue
            mismatch = sum(np.sum((np.log1p(p.features(xy)) - np.log1p(p.features(p.target)))**2)
                           for p, xy in zip(plates, locations))
            ranked.append((mismatch, x, y))
    chosen = sorted(ranked)[:200]
    return [np.quantile([p.response(p.target + [x, y], p.trail)[0] for _, x, y in chosen],
                        [.5, .9, .95, .99, 1], method="higher").tolist() for p in plates]


def diagnose(folder, pair, figure):
    plates = [Plate(folder,r["name"]) for r in pair["plates"]]
    rows = read_rows(folder/"ma-gaia.csv")
    matrices = [affine(p,rows) for p in plates]
    world,pred,valid = [],[],[]
    local = []
    for p,r,mat in zip(plates,pair["plates"],matrices):
        p.calibrate()
        xy = p.target+r["free_offset_px"]
        raw = (xy-mat[0])@np.linalg.inv(mat[1:])
        world.append(p.wcs.all_pix2world([raw],0)[0])
        pred.append(np.array(p.meta["endpoint_midpoint_endpoint"][1][:2]))
        local.append(local_astrometry(p,folder,1.44))
        vals = {}
        for (i,m,c),(_,amp) in zip(p.refs[1::2],p.validation):
            vals[rows[i]["source_id"]] = (m, 16.33-np.log(amp/p.peak(16.33))/(.4*np.log(10)*p.gamma) if amp>0 else None)
        valid.append(vals)
    shift = east_north(pred[0],pred[1])
    motion = east_north(world[0],world[1])
    bdiff = pair["plates"][1]["inferred_B"]-pair["plates"][0]["inferred_B"]
    stars = [k for k in sorted(valid[0].keys() & valid[1].keys()) if abs(valid[0][k][0]-16.33)<=.75]
    both = [valid[1][k][1]-valid[0][k][1] for k in stars if all(v[k][1] is not None for v in valid)]
    photometry = []
    for v in valid:
        matched = [v[k] for k in stars]
        errors = [inferred - actual for actual, inferred in matched if inferred is not None]
        photometry.append(dict(count=len(matched), positive=len(errors),
                               residual_q16_50_84=np.quantile(errors,[.16,.5,.84]).tolist()))
    if figure:
        picture(plates,matrices,figure)
    return dict(free_ICRF_deg=np.asarray(world).tolist(),expected_EN_as=shift.tolist(),measured_EN_as=motion.tolist(),
                vector_residual_as=float(np.linalg.norm(motion-shift)),local_astrometry=local,
                delta_B=bdiff,common_withheld_companions=len(stars),positive_amplitudes=len(both),
                median_delta_B=float(np.median(both)),quantiles_10_90=np.quantile(both,[.1,.9]).tolist(),
                as_discrepant=int(sum(abs(d)>=abs(bdiff) for d in both)),as_faint=int(sum(d>=bdiff for d in both)),
                stellar_differences_mag=both, per_night_photometry=photometry,
                null_score_q50_90_95_99_100_higher=null_quantiles(plates))


if __name__=="__main__":
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("fixed",type=Path)
    ap.add_argument("pair",type=Path)
    ap.add_argument("--figure",type=Path)
    a=ap.parse_args()
    print(json.dumps(diagnose(a.fixed,json.loads(a.pair.read_text()),a.figure),indent=2,allow_nan=False))
