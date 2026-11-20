"""Compare the two public cutouts with their full-resolution scanner mosaic rows."""
import argparse
import base64
import gzip
import hashlib
import json
from pathlib import Path

from astropy.io import fits
from astropy.wcs import WCS
import numpy as np
import requests
from scipy.ndimage import map_coordinates
from scipy.stats import spearmanr

from fetch import archive
from measure import Plate


def read_range(url, start, stop):
    response = requests.get(url,headers={"Range":f"bytes={start}-{stop-1}"},stream=True,timeout=45)
    with response:
        response.raise_for_status()
        if response.status_code != 206:
            raise ValueError("Archive did not provide partial content")
        data = response.content
    if len(data) != stop-start:
        raise ValueError("Short range response")
    return data


def native(fixed, scratch, name):
    p = Plate(fixed,name)
    package = archive("dasch/dr7/mosaic_package",dict(plate_id=name,binning=1))
    url = package["baseFitsUrl"]
    astro = package["metadata"]["astrometry"]
    if astro["rotationDelta"] not in (0,None):
        raise ValueError("Unexpected image rotation on this plate")
    head = fits.Header.fromstring(gzip.decompress(base64.b64decode(astro["b01HeaderGz"])).decode(),sep="\n")
    head["CTYPE1"],head["CTYPE2"] = "RA---TPV","DEC--TPV"
    wcs = WCS(head,naxis=2)
    y,x = np.mgrid[-30:31,-30:31]
    pos = np.rint(p.target).astype(int)
    cut = p.img[pos[1]+y,pos[0]+x]
    sky = p.wcs.all_pix2world(pos[0]+x,pos[1]+y,0)
    xn,yn = wcs.all_world2pix(*sky,0)
    xmin,ymin = int(xn.min())-2,int(yn.min())-2
    xmax,ymax = int(xn.max())+4,int(yn.max())+4
    scratch.mkdir(exist_ok=True,parents=True)
    path = scratch/(name+"-sparse.fz")
    # The two DR7 RICE files have one variable-length compressed byte array per detector row.
    prefix = read_range(url,0,2880*24)
    with open(path,"wb") as f:
        f.write(prefix)
        f.truncate(package["baseFitsSize"])
    with fits.open(path,disable_image_compression=True) as hdul:
        h = hdul[1].header
        offset = hdul[1].fileinfo()["datLoc"]
        assert h["ZTILE2"]==1 and h["NAXIS1"]==8 and h["TFORM1"].startswith("1PB")
        heap = offset+h.get("THEAP",h["NAXIS1"]*h["NAXIS2"])
    desc = read_range(url,offset+8*ymin,offset+8*ymax)
    sizes,starts = np.frombuffer(desc,dtype=">i4").reshape(-1,2).T.astype(np.int64)
    first,last = int(min(starts)),int(max(starts+sizes))
    data = read_range(url,heap+first,heap+last)
    with open(path,"r+b") as f:
        f.seek(offset+8*ymin)
        f.write(desc)
        f.seek(heap+first)
        f.write(data)
    with fits.open(path) as hdul:
        img = hdul[1].section[ymin:ymax,xmin:xmax].astype(float)
    patch = map_coordinates(img,[yn-ymin,xn-xmin],order=1)
    good = np.isfinite(cut) & (patch>0)
    core = (x*x+y*y <= (p.radius+2)**2)
    return dict(valid_pairs=int(good.sum()), compared_pixels=good.size, core_pixels=int(core.sum()),
                core_valid=int(good[core].sum()), plate=name,native_bounds_0based_halfopen=[xmin,xmax,ymin,ymax],
                scanner_patch_sha256=hashlib.sha256(img.astype(">f8").tobytes()).hexdigest(),
                compressed_bytes=len(data),native_extrema=[img.min(),img.max()],
                nearest_edge_px=float(min(xn[30,30],yn[30,30],head["NAXIS1"]-1-xn[30,30],head["NAXIS2"]-1-yn[30,30])),
                rank_correlation=float(spearmanr(cut[good],patch[good]).statistic),
                finite=int(np.isfinite(img).sum()),pixels=img.size)


if __name__=="__main__":
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("fixed",type=Path)
    ap.add_argument("scratch",type=Path)
    args = ap.parse_args()
    print(json.dumps([native(args.fixed,args.scratch,n) for n in ("ma00731","ma00733")],indent=2,allow_nan=False))
