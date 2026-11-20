"""Run controls before --open. The two cameras share sky translations."""
import argparse
import json
from pathlib import Path

import numpy as np
import pandas as pd
from scipy.optimize import least_squares
from scipy.spatial import cKDTree
from heidelberg1909_plate import Plate, mad, track

FEB = ("B2247a","B2248b")
OTHER, HIST = "B4816a","B3383a"
GRADES = [14.5,15,15.5,16,16.25,16.33,16.4,16.5,16.75,17,17.25,17.5,17.7]
RNG = 19090220

def dump(path,value):
    Path(path).write_text(json.dumps(value,indent=2,allow_nan=False,default=lambda n:n.item())+"\n")

def fitted_hour(name):
    clocks = json.loads(Path(name+".clock").read_text())
    times = [v["mid_hour"] for v in clocks.values() if v.get("over_bg",0)>.25 and
             v["over_static"]>.15 and .65<v["length_ratio"]<1.35 and v["cross_px"]<3]
    if len(times)<2: raise ValueError("independent clock estimates required",name)
    return np.median(times)

class Measurement:
    def __init__(self,name):
        feb = name in FEB
        hist = name==HIST
        self.p = p = Plate(name,"hist" if hist else "pluto")
        t = fitted_hour(name if feb else FEB[0]) if not hist else 18+58/60+5.5/3600
        duration = (9601 if hist else 10802)/3600
        self.eph = track(999,[t-duration/2,t,t+duration/2],hist)
        pos = p.pix(self.eph[:,:2])
        self.pos = pos[1]
        self.path = pos[2]-pos[0] if name!=OTHER else np.zeros(2)
        self.expected = self.eph[1,2]+.78
        self.hour = t
        self.calibrate()
        self.trees = [cKDTree(p.xy[k]) for k in [p.g<16,(p.g>=16)&(p.g<19.5)]]
        self.noise = p.annulus(self.pos,87,110)
        self.neighbor = self.dist(self.pos)

    def dist(self,xy):
        return np.array([tree.query(xy)[0] for tree in self.trees]).T

    def calibrate(self):
        p = self.p
        tab = p.tab
        b = tab.b_jkc_mag.to_numpy()
        color = b-tab.v_jkc_mag.to_numpy()
        xy = (p.xy-self.pos)/600
        separate = cKDTree(p.xy[p.g<18]).query(p.xy,k=2)[0][:,1]>18
        use = (np.linalg.norm(p.xy-self.pos,axis=1)>120)&(np.linalg.norm(xy,axis=1)<1.24)
        use &= separate & (tab.b_jkc_flag==1) & (b>14.7)&(b<17.7)&(color>0)&(color<1.6)
        ids = np.flatnonzero(use)
        amp = np.array([p.measure(p.xy[i],[0,0],omit=i) for i in ids])
        train = ~p.phot_hold[ids]
        mat = np.c_[np.ones(len(ids)),b[ids]-16.4,color[ids]-.78,xy[ids]]
        init = np.array([np.log(max(1,np.median(amp[train]*np.exp(.85*(b[ids][train]-16.4))))),-.85,0,0,0])
        err = np.maximum(.2*np.exp(mat@init),.12*np.exp(init[0]))
        self.params = least_squares(lambda v:(np.exp(mat[train]@v)-amp[train])/err[train],init,
                            bounds=([0,-2,-1,-2,-2],[14,-.2,1,2,2]),loss="soft_l1").x
        hold = ~train & (abs(b[ids]-self.expected)<=.25)
        self.holdamps = amp[hold]
        positive = hold & (amp>0)
        phot_err=(np.log(amp[positive])-mat[positive]@self.params)/self.params[1]
        self.cal = dict(train=int(train.sum()),held_near=int(hold.sum()),
                    B_residual_16_50_84=np.percentile(phot_err,[16,50,84]).tolist() if any(positive) else [],
                    log_model=self.params.tolist())

    def amplitude(self,b,xy):
        return np.exp(self.params[0]+self.params[1]*(b-16.4)+(xy-self.pos)@self.params[3:]/600)

    def magnitude(self,a):
        return 16.4+(np.log(a)-self.params[0])/self.params[1] if a>0 else None

    def catalog_match(self,xy):
        # Rank alignments jointly by sky noise and distances to the nearest scene stars.
        noise = np.array([self.p.annulus(q,18,28) for q in xy])
        d = self.dist(xy)
        score = np.sum((np.log((d+3)/(self.neighbor+3)))**2,axis=1)+4*np.log(noise/self.noise)**2
        return score,noise

    def blank_designs(self,xy):
        images,weights,models=[],[],[]
        for q in xy:
            a,x,y,b,s = self.p.design(q,self.path)
            v = s-b @ np.linalg.lstsq(b,s,rcond=None)[0]
            images.append(a)
            weights.append(v/(v@v))
            models.append(s)
        return np.array(images),np.array(weights),np.array(models)

    def free_fit(self):
        a,x,y,b,s = self.p.design(self.pos,self.path)
        def residual(off,ret_amp=False):
            src = self.p.profile(x,y,self.pos+off,self.path)
            design=np.column_stack((b,src))
            coef=np.linalg.lstsq(design,a,rcond=None)[0]
            return coef[-1] if ret_amp else a-design@coef
        res=least_squares(residual,[0,0],bounds=(-9,9),diff_step=.002)
        sky=self.p.sky(self.pos+res.x)
        off=(sky-self.eph[1,:2])*3600*[np.cos(np.deg2rad(sky[1])),1]
        return dict(sky=sky.tolist(),east_north=off.tolist(),miss=np.linalg.norm(off),
                    amplitude=residual(res.x,True))

def translations(ms,delta,random=False):
    grid=np.arange(-608,609,16)+delta
    x,y=np.meshgrid(grid,grid)
    flat=np.column_stack((x.ravel(),y.ravel()))
    if random:
        flat=np.random.default_rng(RNG+1).uniform(-620,620,(8500,2))
    flat=flat[(np.linalg.norm(flat,axis=1)>150)&(np.linalg.norm(flat,axis=1)<620)]
    sky=np.array([ms[0].p.sky(ms[0].pos+off) for off in flat])
    diff=sky-ms[0].eph[1,:2]
    allxy=[m.p.pix(m.eph[1,:2]+diff) for m in ms]
    stats=[m.catalog_match(xy) for m,xy in zip(ms,allxy)]
    rank=np.argsort(np.sum([x[0] for x in stats],axis=0))
    if random:
        selected=[]
        for i in rank:
            if selected and np.min(np.linalg.norm(flat[selected]-flat[i],axis=1))<30: continue
            selected.append(i)
            if len(selected)==200: break
        if len(selected)!=200: raise ValueError("insufficient independent centers")
        order=selected
    else:
        order=rank[:200]
    return [xy[order] for xy in allxy],[x[1][order] for x in stats]

def score_coded(images,weights,locations):
    # The scorer receives no magnitudes, injected amplitudes or sham labels.
    return np.einsum("ij,ij->i",images,weights[locations])

def blind_trials(m,xy,imgs,w,models,trigger):
    rng=np.random.default_rng(RNG)
    levels=np.array([*GRADES,np.nan])
    grades=np.repeat(levels,len(xy))
    loc=np.tile(np.arange(len(xy)),len(levels))
    order=rng.permutation(len(loc))
    loc,grades=loc[order],grades[order]
    amp=np.zeros(len(loc))
    real=np.isfinite(grades)
    amp[real]=m.amplitude(grades[real],xy[loc[real]])
    coded=imgs[loc]+amp[:,None]*models[loc]
    scores=score_coded(coded,w,loc)
    return {str(b):int(np.sum((scores>trigger)&(grades==b))) for b in GRADES} | {
        "sham":int(np.sum((scores>trigger)&~real))}

def analyze(names,opened):
    ms=[Measurement(n) for n in names]
    train,noise=translations(ms,0)
    trial,_=translations(ms,8)
    random_xy,_=translations(ms,0,random=True)
    summaries={}
    random_scores=[]
    observed=[]
    triggers=[]
    for m,xy,z,ns,rd in zip(ms,train,trial,noise,random_xy):
        a,w,_=m.blank_designs(xy)
        null=score_coded(a,w,np.arange(len(xy)))
        lim=np.quantile(null,.99)
        imgs,weights,models=m.blank_designs(z)
        held=score_coded(imgs,weights,np.arange(len(z)))
        rr=np.array([m.p.measure(q,m.path) for q in rd])
        random_scores.append(rr)
        triggers.append(lim)
        recovery=blind_trials(m,z,imgs,weights,models,lim)
        depths=[b for b in GRADES if recovery[str(b)]>=160]
        summaries[m.p.name]=row=dict(hour=m.hour,ephemeris=m.eph.tolist(),path=m.path.tolist(),
                 corrected_xy=m.pos.tolist(),expected_B=m.expected,astrometry=m.p.ast,
                 calibration=m.cal,hold_trigger=int(sum(m.holdamps>lim)),q99=lim,
                 noise_mad=mad(null),null_med=np.median(null),trial= recovery,
                 lim80=max(depths) if depths else None,local_sky_mad=m.noise,
                 comparison_sky_mad=np.percentile(ns,[10,50,90]).tolist(),
                 matched_dist=m.neighbor.tolist(),sham=int(sum(held>lim)),random_above=int(sum(rr>lim)))
        if opened:
            score=m.p.measure(m.pos,m.path)
            observed.append(score)
            row.update(score=score,SNR=(score-np.median(null))/mad(null),B=m.magnitude(score),
                       free=m.free_fit(),extreme=int(sum(rr>=score)))
    held=np.array(random_scores)
    summaries["chance"]={"both_above_threshold":int(sum(np.all(held>np.array(triggers)[:,None],axis=0))),"n":200}
    if opened: summaries["chance"]["both_at_least_observed"]=int(sum(np.all(held>=np.array(observed)[:,None],axis=0)))
    return summaries

if __name__=="__main__":
    ap=argparse.ArgumentParser()
    ap.add_argument("group",choices=["historic","feb","fixed"])
    ap.add_argument("--open",action="store_true")
    args=ap.parse_args()
    ids={"historic":[HIST],"feb":FEB,"fixed":[OTHER]}[args.group]
    dump(args.group+("-open" if args.open else "-controls")+".json",analyze(ids,args.open))
