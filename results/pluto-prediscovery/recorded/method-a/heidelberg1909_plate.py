"""Local registration in native pixels, using the public FITS SIP solution as a seed."""
from pathlib import Path
import warnings
import numpy as np
import pandas as pd
from astropy.io import fits
from astropy.wcs import WCS, FITSFixedWarning
from scipy.ndimage import gaussian_filter, map_coordinates
from scipy.spatial import cKDTree


warnings.simplefilter("ignore", FITSFixedWarning)

def mad(a):
    return 1.4826*np.median(abs(a-np.median(a)))

def patch(image, xy, r):
    x,y = np.rint(xy).astype(int)
    return image[y-r:y+r+1,x-r:x+r+1]

def axes(r):
    y,x = np.mgrid[-r:r+1,-r:r+1]
    return x,y

def basis(xy):
    return np.column_stack((np.ones(len(xy)),xy/1000))

def track(body, t, historic=False):
    name = str(body)+("-1914" if historic else "")+".eph"
    txt = Path(name).read_text().split("$$SOE")[1].split("$$EOE")[0]
    lines = [s.split(",") for s in txt.strip().splitlines()]
    times = [int(s[0][-5:-3])+int(s[0][-2:])/60 for s in lines]
    data = np.array([[float(s[i]) for i in (-10,-9,-8,-6,-4,-2)] for s in lines])
    if np.min(t)<min(times) or np.max(t)>max(times):
        raise ValueError("time outside ephemeris")
    return np.array([np.interp(t,times,c) for c in data.T]).T

class Plate:
    def __init__(self, name, field):
        self.name = name
        with fits.open(name+"-"+field+".fits") as hdus:
            h = hdus[0]
            self.w = WCS(h.header)
            self.im = h.data.astype(float)
            self.year = float(h.header["DATE-OBS"][:4])+.14
        self.center = (np.array(self.im.shape[::-1])-1)/2
        table = pd.read_csv(field+".csv")
        if Path(field+"-B.csv").exists():
            table = table.merge(pd.read_csv(field+"-B.csv"), on="source_id",how="left")
        dt = self.year-2016
        table.ra += dt*table.pmra.fillna(0)/3.6e6/np.cos(np.deg2rad(table.dec))
        table.dec += dt*table.pmdec.fillna(0)/3.6e6
        raw = self.w.all_world2pix(table[["ra","dec"]].values,0,quiet=True)
        inside = np.all((raw>32)&(raw < 2*self.center-32),axis=1)
        self.tab = table[inside].reset_index(drop=True)
        self.raw = raw[inside]
        g = self.tab.phot_g_mean_mag.to_numpy()
        pool = (g>11)&(g<16.2)&(np.linalg.norm(self.raw-self.center,axis=1)>150)
        tree = cKDTree(self.raw[g<17])
        self.phot_hold = np.arange(len(g)) % 4 == 0
        if field in ("pluto","hist"): pool &= ~self.phot_hold
        sel = np.where(pool & (tree.query(self.raw,k=2)[0][:,1]>18))[0]
        sel = sel[np.argsort(g[sel])][:180]
        # Stack catalogue-centered windows before identifying individual images.
        stack_ids = [i for i in sel if np.linalg.norm(self.raw[i]-self.center)>200 and np.all(self.raw[i]>72) and np.all(self.raw[i]<2*self.center-72)]
        stack = np.array([patch(self.im,self.raw[i],70) for i in stack_ids])
        bg = np.median(stack,axis=(1,2))[:,None,None]
        norm = np.percentile(stack,99,axis=(1,2))[:,None,None]-bg
        template = gaussian_filter(np.median((stack-bg)/np.maximum(1,norm),axis=0),1.5)
        shift = np.array(np.unravel_index(template.argmax(), template.shape))[::-1]-70
        centers, idx = [], []
        for i in sel:
            pos = self.raw[i]+shift
            a = patch(self.im,pos,13)
            if a.shape != (27,27): continue
            x,y = axes(13)
            b = np.median(a)
            smooth = gaussian_filter(a,1.5)
            window = (x*x+y*y<=8**2)
            j,k = np.unravel_index(np.argmax(np.where(window,smooth,-np.inf)),a.shape)
            w = np.maximum(0,a-b)*np.exp(-((x-x[j,k])**2+(y-y[j,k])**2)/55)
            if smooth[j,k]-b < 2*mad(a): continue
            centers.append(np.rint(pos)+[np.sum(x*w)/w.sum(),np.sum(y*w)/w.sum()])
            idx.append(i)
        idx = np.array(idx)
        if len(idx)<9: raise ValueError("too few registration stars",name,field,len(idx),shift,len(sel))
        d = np.array(centers)-self.raw[idx]
        X = basis(self.raw[idx]-self.center)
        train = np.arange(len(idx))%4!=0
        use = train.copy()
        for _ in range(5):
            self.coef = np.linalg.lstsq(X[use],d[use],rcond=None)[0]
            residual = np.linalg.norm(X @ self.coef-d,axis=1)
            use = train & (residual<max(1.0,np.median(residual[use])+3*mad(residual[use])))
        self.xy = self.raw+basis(self.raw-self.center)@self.coef
        self.tree = cKDTree(self.xy)
        self.g = g
        self.ast = dict(ties=int(use.sum()), withheld=int(sum(~train)), seed=shift.tolist(),
                        center_shift=self.coef[0].tolist(), withheld_p50_p90_px=np.percentile(residual[~train],[50,90]).tolist())
        # Empirical PSF at catalogue positions in the local corrected frame.
        isolated = self.g<18
        sep = cKDTree(self.xy[isolated]).query(self.xy,k=2)[0][:,1]
        pool = np.where((self.g>13)&(self.g<16.4)&(sep>18)&(np.linalg.norm(self.xy-self.center,axis=1)>150))[0]
        if field in ("pluto","hist"): pool = pool[~self.phot_hold[pool]]
        shapes = []
        x,y = axes(15)
        for i in pool:
            p = self.xy[i]
            if np.any(p<17) or np.any(p>2*self.center-17): continue
            img = map_coordinates(self.im,[p[1]+y,p[0]+x],order=1)
            bg = np.median(img[x*x+y*y>12**2])
            amp = np.max(gaussian_filter(img,1)[12:19,12:19])-bg
            if amp>3*mad(img[x*x+y*y>12**2]):
                shapes.append((img-bg)/amp)
        if len(shapes)<4: raise ValueError("too few PSF stars",name,field,len(shapes))
        psf = gaussian_filter(np.median(shapes,axis=0),.6)
        psf -= np.median(psf[x*x+y*y>=13**2])
        self.psf = psf/psf.max()
        self.ast["profiles"] = len(shapes)
        self.ast["fwhm_area_diameter_px"] = 2*np.sqrt(np.sum(self.psf>.5)/np.pi)

    def pix(self, sky):
        raw = self.w.all_world2pix(np.atleast_2d(sky),0)
        return raw + basis(raw-self.center)@self.coef

    def sky(self, pixel):
        raw = pixel.copy()
        for _ in range(3):
            raw = pixel-(basis(np.atleast_2d(raw-self.center))@self.coef)[0]
        return self.w.all_pix2world([raw],0)[0]

    def profile(self, x, y, pos, trail):
        dx,dy = trail
        n = 1 if max(abs(dx),abs(dy))<.01 else max(5,int(np.hypot(dx,dy)/2)+1)
        steps = (np.arange(n)+.5)/n-.5
        return np.mean([map_coordinates(self.psf,[15+y-pos[1]-s*dy,15+x-pos[0]-s*dx],
                                        order=1,mode="constant") for s in steps],axis=0)

    def design(self, pos, trail, rad=13, omit=None):
        q = np.rint(pos).astype(int)
        x,y = axes(rad)
        x,y = (x+q[0]).ravel(),(y+q[1]).ravel()
        a = self.im[y,x]
        cols = [np.ones(len(x)),(x-q[0])/rad,(y-q[1])/rad]
        for i in self.tree.query_ball_point(pos,rad+8):
            if self.g[i]<19.5 and i!=omit:
                star = self.profile(x,y,self.xy[i],(0,0))
                if star.max()>.06: cols.append(star)
        nuisance = np.stack(cols,axis=1)
        src = self.profile(x,y,pos,trail)
        return a,x,y,nuisance,src

    def annulus(self,pos,inner,outer):
        a = patch(self.im,pos,outer)
        x,y = axes(outer)
        r2 = x*x+y*y
        return mad(a[(r2>=inner**2)&(r2<=outer**2)])

    def measure(self,pos,trail,omit=None):
        a,x,y,b,s = self.design(pos,trail,omit=omit)
        v = s-b @ np.linalg.lstsq(b,s,rcond=None)[0]
        return float((a@v)/(v@v))
