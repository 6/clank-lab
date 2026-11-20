"""Forced photometry with local deblending, native stars and translated trails."""
import argparse
import csv
import hashlib
import json
from pathlib import Path

from astropy.io import fits
from astropy.wcs import WCS
import numpy as np
from scipy.ndimage import gaussian_filter
from scipy.optimize import least_squares, minimize
from scipy.spatial import cKDTree


def read_rows(path):
    with path.open() as stream:
        return list(csv.DictReader(stream))


def column(rows, key):
    return np.array([float(r[key] or 0) for r in rows])


def offsets(points, center):
    return np.linalg.norm(points - center, axis=-1)


def grid(radius):
    y, x = np.mgrid[-radius:radius+1, -radius:radius+1]
    return np.column_stack((x.ravel(), y.ravel()))


def chip(image, xy, delta):
    q = delta + np.rint(xy).astype(int)
    return image[q[:, 1], q[:, 0]]


def gaussian(q, sig):
    u = q[:, 0] / sig[0]
    v = (q[:, 1] - sig[2]*q[:, 0]) / sig[1]
    return np.exp(-0.5 * (u*u + v*v))


class Plate:
    def __init__(self, folder, name):
        self.name = name
        field = name[:2]
        self.meta = json.loads((folder / (name+".json")).read_text())
        img, header = fits.getdata(folder / (name+".fits"), header=True,
                                   do_not_scale_image_data=True)
        self.img = img.astype(float)
        if "BLANK" in header and img.dtype.kind in "iu":
            self.img[img == header["BLANK"]] = np.nan
        self.img = self.img * header.get("BSCALE", 1) + header.get("BZERO", 0)
        self.wcs = WCS(header)
        geom = np.array(self.meta["endpoint_midpoint_endpoint"])
        predicted = self.wcs.all_world2pix(geom[:, :2], 0)
        self.raw_target = predicted[1]
        self.trail = predicted[2] - predicted[0]
        self.year = float(self.meta["midpoint"][:4]) + 0.9
        rows = read_rows(folder / (field+"-gaia.csv"))
        ra, dec = column(rows,"ra"), column(rows,"dec")
        self.g = column(rows,"phot_g_mean_mag")
        self.modern = cKDTree(np.column_stack(self.wcs.all_world2pix(ra, dec, 0)))
        years = self.year - 2016.0
        self.xy = np.column_stack(self.wcs.all_world2pix(
            ra + column(rows,"pmra") * years / (3.6e6 * np.cos(np.deg2rad(dec))),
            dec + column(rows,"pmdec") * years / 3.6e6, 0))
        self.align()
        self.tree = cKDTree(self.xy)
        self.trees = [cKDTree(self.xy[mask]) for mask in
                      [self.g < 16, (self.g >= 16) & (self.g < 19)]]
        a = [r for r in read_rows(folder / (field+"-apass.csv"))
             if r["ref_text"].startswith("APASS_") and r["v_flag"] == "0"]
        # Match APASS at its catalogue epoch to the Gaia entry propagated there.
        epoch = column(a,"pos_epoch")
        dec0 = column(a,"dec_deg")
        ap = np.column_stack(self.wcs.all_world2pix(column(a,"ra_deg") + column(a,"pm_ra_masyr") *
            (2016-epoch)/(3.6e6*np.cos(np.deg2rad(dec0))),
            dec0 + column(a,"pm_dec_masyr")*(2016-epoch)/3.6e6, 0))
        dist, ids = self.modern.query(ap)
        self.refs = [(i,m,c) for i,m,c,d in zip(ids,column(a,"stdmag"),column(a,"color"),dist)
                     if d < 2.5 and self.inside(self.xy[i]) and
                     0.15 < c < 1.55 and 13.8 < m < 17.8]

    def inside(self, p):
        x,y = p
        return (45 < x < self.img.shape[1]-45 and 45 < y < self.img.shape[0]-45
                and offsets(p,self.raw_target) > 125)

    def align(self):
        bright = [p for p,m in zip(self.xy,self.g) if 10 < m < 14.5 and self.inside(p)]
        d = grid(23)
        patches = np.array([chip(self.img,p,d) for p in bright])
        patches -= np.nanmedian(patches,axis=1)[:,None]
        stack = np.nanmedian(patches/(1+np.nanstd(patches,axis=1)[:,None]),axis=0)
        peak = np.argmax(np.abs(stack))
        self.reg = dict(n=len(bright), stack_peak=float(stack[peak]))
        if abs(stack[peak]) < 2 or np.max(np.abs(d[peak])) > 16:
            raise ValueError("Incoherent off-track registration: "+str(self.reg))
        self.img *= np.sign(stack[peak])
        start = d[peak]
        valid = np.isfinite(self.img)
        sm = gaussian_filter(np.where(valid,self.img,0),2)
        if not valid.all():
            density = gaussian_filter(valid.astype(float),2)
            sm = np.divide(sm,density,out=np.full_like(sm,-np.inf),where=density>0)
        window = grid(7)
        obs = []
        for p in bright:
            q = p+start
            b = chip(sm,q,window)
            k = np.argmax(b)
            pos = np.rint(q)+window[k]
            obs.append(pos)
        bright, obs = np.array(bright),np.array(obs)
        def design(pts):
            return np.column_stack((np.ones(len(pts)),(pts-self.raw_target)/400))
        basis = design(bright)
        ok = np.ones(len(obs),dtype=bool)
        for _ in range(4):
            mat = np.linalg.lstsq(basis[ok], (obs-bright)[ok],rcond=None)[0]
            resid = offsets(obs,bright+basis@mat)
            ok = resid < max(2,2.7*np.median(resid[ok]))
        self.reg.update(used=int(ok.sum()),rms_px=float(np.sqrt(np.mean(resid[ok]**2))))
        self.target = self.raw_target+mat[0]
        self.xy += design(self.xy)@mat
        # Median normalized profiles, centered on the measured bright-star peaks.
        profiles = np.array([chip(self.img,p,d) for p in obs[ok]])
        profiles -= np.nanmedian(profiles,axis=1)[:,None]
        prof = np.nanmedian(profiles/np.maximum(1,np.nanmax(profiles,axis=1))[:,None],axis=0)
        def err(par):
            return par[3]*gaussian(d,par[:3])+par[4]-prof
        self.sig = least_squares(err,[4,4,0,1,0],bounds=([1,1,-1,0.3,-.3],
                                 [14,14,1,1.5,.3]),loss="soft_l1",f_scale=.04).x[:3]
        self.radius = int(np.clip(np.ceil(3*np.max(self.sig[:2])),12,32))
        self.delta = grid(self.radius)

    def response(self,p,trail,omit=None):
        # The template's least-squares coefficient after projecting away the
        # nuisance stars and tilted background is a linear functional of pixels.
        q = self.delta + np.rint(p)-p
        data = chip(self.img,p,self.delta)
        valid = np.isfinite(data)
        if valid.mean() < .90:
            raise ValueError("Insufficient valid pixels in fitted stamp")
        q, data = q[valid], data[valid]
        r = self.radius
        terms = [np.ones(len(q)),q[:,0]/r,q[:,1]/r]
        inds = self.tree.query_ball_point(p, 1.65*r)
        for i in inds:
            if self.g[i] < 18.7 and i != omit:
                terms.append(gaussian(q-(self.xy[i]-p),self.sig))
        nuisance = np.stack(terms,axis=1)
        tracks = np.array([gaussian(q-t*trail,self.sig) for t in np.linspace(-.5,.5,9)])
        template = tracks.mean(axis=0)
        # Retain the fit to the background for the nonlinear injection as well.
        co = np.linalg.lstsq(nuisance,np.column_stack((template,data)),rcond=1e-6)[0]
        resid = template - nuisance@co[:,0]
        weight = resid / (resid@resid)
        field = np.maximum(0,nuisance[:,3:]@co[3:,1])
        return float(weight@data),weight,field,tracks

    def features(self,p):
        return np.array([tree.query(p)[0] for tree in self.trees])

    def calibrate(self):
        stars = [(i,m,c,self.response(self.xy[i],np.zeros(2),i)[0]) for i,m,c in self.refs]
        # Keep alternating stars out of the fit. No image detection cut.
        fit = stars[::2]
        centers,amps = [],[]
        for m in np.arange(14,17.51,.5):
            sample = [s[3] for s in fit if abs(s[1]-m)<.35]
            if len(sample)>=3 and np.median(sample)>0:
                centers.append(m); amps.append(np.median(sample))
        if len(centers)<3:
            raise ValueError("Insufficient photometric standards")
        slope,intercept = np.polyfit(centers,np.log(amps),1)
        self.gamma = -slope/(.4*np.log(10))
        if not .15 < self.gamma < 3:
            raise ValueError("Invalid fitted characteristic curve")
        self.peak = lambda m: np.exp(intercept+slope*m)
        self.validation = [(m,a) for _,m,_,a in stars[1::2]]
        return dict(nfit=len(fit),response_bins=list(zip(centers,amps)),
                    exponent=self.gamma,nvalidation=len(self.validation))

    def injected(self,measurement,mag):
        a,w,field,tracks = measurement
        # Local power response fitted to stellar peaks. Superpose the trail and
        # stationary signal in equivalent exposure, then apply the response.
        g = self.gamma
        source = self.peak(mag)**(1/g) * np.mean(tracks**(1/g),axis=0)
        added = (field**(1/g)+source)**g-field
        return a+w@added


MAGS = [14.5,15,15.5,15.75,16,16.1,16.25,16.33,16.5,16.75,17]


def experiment(plates, open_track):
    results = [dict(name=p.name,registration=p.reg,psf=p.sig.tolist(),
                    target_xy=p.target.tolist(),trail_xy=p.trail.tolist(),
                    photometry=p.calibrate()) for p in plates]
    feasible = []
    for dx in range(-752,753,16):
        for dy in range(-752,753,16):
            off = np.array([dx,dy])
            if not all(p.inside(p.target+off) and offsets(p.target+off,p.raw_target)>145
                       for p in plates):
                continue
            distance = sum(np.sum((np.log1p(p.features(p.target+off))-
                                   np.log1p(p.features(p.target)))**2) for p in plates)
            feasible.append((distance,dx,dy))
    chosen = sorted(feasible)[:200]
    masks = []
    for p,r in zip(plates,results):
        measured = [p.response(p.target+[x,y],p.trail) for _,x,y in chosen]
        null = np.array([v[0] for v in measured])
        cut = np.quantile(null,.99,method="higher")
        rec = {str(m):int(sum(float(p.injected(v,m))>cut for v in measured)) for m in MAGS}
        native = {}
        for m in [15,15.5,16,16.33,16.75]:
            v = [a for b,a in p.validation if abs(b-m)<=.25]
            native[str(m)] = [int(np.sum(np.array(v)>cut)),len(v)]
        r.update(n_null=len(null), eligible=len(feasible),null_threshold=float(cut),
                 recovery=rec,native=native,neighbours_px=p.features(p.target).tolist(),
                 null_median=float(np.median(null)))
        masks.append(null>cut)
        if open_track:
            score = p.response(p.target,p.trail)[0]
            r.update(score=score,null_at_least=int(sum(null>=score)),
                     trigger=bool(score>cut))
            if score>cut:
                # Fit position independently on each stamp without a position penalty.
                # Search a fixed +/-12 px box and maximize the decrease in squared
                # residual. Holding the pixel window fixed avoids edge discontinuities.
                q = p.delta + np.rint(p.target)-p.target
                dat = chip(p.img,p.target,p.delta)
                valid = np.isfinite(dat)
                q, dat = q[valid], dat[valid]
                terms = [np.ones(len(q)),q[:,0],q[:,1]]
                for i in p.tree.query_ball_point(p.target,1.65*p.radius):
                    if p.g[i]<18.7:
                        terms.append(gaussian(q-(p.xy[i]-p.target),p.sig))
                design = np.stack(terms,axis=1)
                basis = np.linalg.svd(design,full_matrices=False)[0]
                y = dat-basis@(basis.T@dat)
                def loss(pos):
                    profile = np.mean([gaussian(q-pos-t*p.trail,p.sig)
                                       for t in np.linspace(-.5,.5,9)],axis=0)
                    profile -= basis@(basis.T@profile)
                    return -max(0,float(profile@y))**2/(profile@profile)
                seeds = np.arange(-12,13,3)
                best = min(([x,y0] for x in seeds for y0 in seeds),key=loss)
                free = minimize(loss,best,bounds=[(-12,12)]*2)
                r["free_offset_px"] = free.x.tolist()
                r["inferred_B"] = float(16.33-np.log(score/p.peak(16.33))/
                                        (.4*np.log(10)*p.gamma))
            if len(plates)==2:
                other = plates[1-plates.index(p)]
                # Both MA cutouts have identical WCS. Transfer sky coordinates
                # between plates before applying this plate's registration.
                opposite = p.target + other.raw_target - p.raw_target
                r["opposite_score"] = p.response(opposite,p.trail)[0]
    return dict(plates=results,joint_null=int(np.sum(np.logical_and.reduce(masks))))


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("folder",type=Path)
    ap.add_argument("group",choices=["historical","pair","bruce"])
    ap.add_argument("--open-track",action="store_true")
    args = ap.parse_args()
    names = dict(historical=["mc06858"],pair=["ma00731","ma00733"],bruce=["hd342a"])[args.group]
    result = experiment([Plate(args.folder,n) for n in names],args.open_track)
    inputs = {p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(args.folder.iterdir())
              if any(p.name.startswith(n) or p.name.startswith(n[:2]+"-") and
                     p.name.endswith(("gaia.csv","apass.csv")) for n in names)}
    result.update(inputs=inputs, code=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    print(json.dumps(result,indent=2,allow_nan=False))


if __name__ == "__main__":
    main()
