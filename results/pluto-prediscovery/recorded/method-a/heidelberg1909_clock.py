"""Date each exposure without using Pluto pixels."""
import json
import numpy as np
from scipy.optimize import least_squares
from heidelberg1909_plate import Plate, track

def one(name, num):
    p = Plate(name,"k"+str(num))
    def path(t):
        return p.pix(track(num,t)[:,:2])
    def poses(t):
        a,b,c=path(np.array([t-1.5,t,t+1.5]))
        return b,c-a
    # Grid spans the observable evening and a substantial part of daylight.
    def score(t, full=False):
        center,trail=poses(t)
        a,x,y,b,s=p.design(center,trail,rad=33)
        residual=s-b @ np.linalg.lstsq(b,s,rcond=None)[0]
        amp=(residual@a)/(residual@residual)
        return amp*np.linalg.norm(residual) if not full else (a,x,y,b,center,trail)

    times=np.arange(13,22.42,.083333333)
    values=np.array([score(t) for t in times])
    best=times[np.argmax(values)]
    a,x,y,b,center,trail=score(best,True)
    # Keep the window and all nuisance columns fixed when estimating length and time.
    def residual(params):
        sx,sy,length=params
        s=p.profile(x,y,center+[sx,sy],trail*length)
        design=np.column_stack((b,s))
        return a-design @ np.linalg.lstsq(design,a,rcond=None)[0]
    res=least_squares(residual,[0,0,1],bounds=([-10,-10,.15],[10,10,1.8]),
                      diff_step=.001)
    shift=res.x[:2]
    vel=(path([best+.05])-path([best-.05]))[0]/.1
    correction=shift@vel/(vel@vel)
    rss=lambda v:float(v@v)
    err0=a-b @ np.linalg.lstsq(b,a,rcond=None)[0]
    static=residual([*shift,0])
    return dict(mid_hour=best+correction, cross_px=float(np.linalg.norm(shift-vel*correction)),
                length_ratio=res.x[2], expected_length_px=float(np.linalg.norm(trail)),
                over_bg=1-rss(res.fun)/rss(err0), over_static=1-rss(res.fun)/rss(static),ast=p.ast)

if __name__=="__main__":
    import sys
    name=sys.argv[1]
    results={}
    for num in [179,168,417]:
        try: results[num]=one(name,num)
        except ValueError as exc: results[num]=dict(failure=str(exc))
    print(json.dumps(results,indent=2))
