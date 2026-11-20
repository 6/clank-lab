# Asteroid-trail clock: local astrometry around the asteroid, then 1-D along-track profile fit for shutter open/close.
import sys, json, os, numpy as np
from astropy.io import fits
from astropy.table import Table
from astropy.time import Time
from scipy import ndimage as nd
from scipy.spatial import cKDTree
from scipy.special import erf
from scipy.optimize import least_squares
plate, aid, mosaic, wd = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4]
H=int(sys.argv[5]) if len(sys.argv)>5 else 700
eph=np.load(f'{wd}/hz_{plate}_{aid}.npz')
def p2jd(s):
    from datetime import datetime
    d=datetime.strptime(s.strip(),'%Y-%b-%d %H:%M:%S')
    return d
T=np.array([(p2jd(s)-p2jd(eph['dt'][0])).total_seconds()/60 for s in eph['dt']])  # minutes since 21:00 UT
era,ede=eph['ra'],eph['dec']
# stamp centre: middle of the night's track
ra0d,de0d=float(np.median(era)),float(np.median(ede))
gfile=f'{wd}/gaia_{plate}_{aid}.fits'
if not os.path.exists(gfile):
    from astropy import log
    from urllib.parse import urlencode
    from urllib.request import urlopen
    log.setLevel('WARNING')
    q=f"""SELECT source_id, ra, dec, pmra, pmdec, phot_g_mean_mag FROM gaiadr3.gaia_source
    WHERE 1=CONTAINS(POINT('ICRS',ra,dec), CIRCLE('ICRS',{ra0d},{ede.mean()},0.42)) AND phot_g_mean_mag<18.5"""
    params=urlencode({'REQUEST':'doQuery','LANG':'ADQL','FORMAT':'csv','MAXREC':100000,'QUERY':q})
    for endpoint in ('https://gaia.ari.uni-heidelberg.de/tap/sync',
                     'https://gea.esac.esa.int/tap-server/tap/sync'):
        try:
            with urlopen(endpoint+'?'+params,timeout=90) as response:
                rows=response.read().decode().splitlines()
            Table.read(rows,format='ascii.csv').write(gfile,overwrite=True)
            break
        except Exception:
            continue
    else:
        from astroquery.vizier import Vizier
        from astropy.coordinates import SkyCoord
        import astropy.units as u
        V=Vizier(columns=['Source','RA_ICRS','DE_ICRS','pmRA','pmDE','Gmag'],column_filters={'Gmag':'<18.5'},row_limit=-1)
        V.VIZIER_SERVER='vizier.cfa.harvard.edu'
        t=V.query_region(SkyCoord(ra0d,ede.mean(),unit='deg'),radius=0.42*u.deg,catalog='I/355/gaiadr3')[0]
        t.rename_columns(['Source','RA_ICRS','DE_ICRS','pmRA','pmDE','Gmag'],['source_id','ra','dec','pmra','pmdec','phot_g_mean_mag']); t.write(gfile,overwrite=True)
g=Table.read(gfile)
ep=1908.973 if plate=='731' else 1908.976; dt=ep-2016.0
pmra=np.nan_to_num(np.array(g['pmra'],float)); pmdec=np.nan_to_num(np.array(g['pmdec'],float))
gde=np.array(g['dec'],float)+pmdec*dt/3.6e6; gra=np.array(g['ra'],float)+pmra*dt/3.6e6/np.cos(np.radians(gde))
G=np.array(g['phot_g_mean_mag'],float); haspm=~np.ma.getmaskarray(g['pmra'])
ra0,de0=np.radians(ra0d),np.radians(de0d)
def std(rad,ded):
    a=np.radians(rad);d=np.radians(ded)
    c=np.sin(d)*np.sin(de0)+np.cos(d)*np.cos(de0)*np.cos(a-ra0)
    return np.degrees(np.cos(d)*np.sin(a-ra0)/c)*3600,np.degrees((np.sin(d)*np.cos(de0)-np.cos(d)*np.sin(de0)*np.cos(a-ra0))/c)*3600
h=fits.open(mosaic); hd=h[1].header
from astropy.wcs import WCS
wl=WCS(naxis=2); wl.wcs.ctype=['RA---TAN','DEC--TAN']; wl.wcs.crval=[hd['CRVAL1'],hd['CRVAL2']]; wl.wcs.crpix=[hd['CRPIX1'],hd['CRPIX2']]
wl.wcs.cd=np.array([[hd['CD1_1'],hd['CD1_2']],[hd['CD2_1'],hd['CD2_2']]])
xc,yc=wl.all_world2pix(ra0d,de0d,0); xc,yc=int(xc),int(yc)
d=h[1].data; NY,NX=d.shape
y0,y1=max(0,yc-H),min(NY,yc+H); x0,x1=max(0,xc-H),min(NX,xc+H)
img=np.array(d[y0:y1,x0:x1]).astype(np.float32); ny,nx=img.shape
B=64
bm=np.median(img[:ny//B*B,:nx//B*B].reshape(ny//B,B,nx//B,B),axis=(1,3)); bm=nd.median_filter(bm,3)
bg=nd.zoom(bm,(ny/bm.shape[0],nx/bm.shape[1]),order=1)
bg=np.pad(bg,((0,ny-bg.shape[0]),(0,nx-bg.shape[1])),mode='edge')
r=img-bg
sm=nd.gaussian_filter(r,3.0); smad=1.4826*np.median(np.abs(sm-np.median(sm)))
pk=(sm==nd.maximum_filter(sm,15))&(sm>5*smad); ys,xs=np.nonzero(pk)
hw=7; yy,xx=np.mgrid[-hw:hw+1,-hw:hw+1]; cx=[];cy=[]
for y,x in zip(ys,xs):
    if y<hw or x<hw or y>=ny-hw or x>=nx-hw: continue
    st=np.clip(r[y-hw:y+hw+1,x-hw:x+hw+1],0,None); dx=dy=0
    for _ in range(2):
        w=st*np.exp(-((xx-dx)**2+(yy-dy)**2)/32.); s=w.sum(); dx=(w*xx).sum()/s; dy=(w*yy).sum()/s
    cx.append(x+dx); cy.append(y+dy)
cx=np.array(cx);cy=np.array(cy)
sra,sde=wl.all_pix2world(cx+x0,cy+y0,0); px,py=std(sra,sde)
gx,gy=std(gra,gde)
def design(u,v,o): return np.array([u**i*v**j for i in range(o+1) for j in range(o+1-i)]).T
u=(cx-nx/2)/1000; v=(cy-ny/2)/1000
br=np.nonzero((G<16.5)&haspm)[0]; tree=cKDTree(np.c_[gx[br],gy[br]])
for rad,o in [(90,1),(20,2),(6,3),(4,3)]:
    dd,k=tree.query(np.c_[px,py],distance_upper_bound=rad); ok=np.isfinite(dd)
    gi=br[k[ok]]; di=np.nonzero(ok)[0]; _,f=np.unique(gi,return_index=True); gi=gi[f]; di=di[f]
    A=design(u[di],v[di],o); a,*_=np.linalg.lstsq(A,gx[gi],rcond=None); b,*_=np.linalg.lstsq(A,gy[gi],rcond=None)
    res=np.hypot(A@a-gx[gi],A@b-gy[gi]); kp=res<3*np.median(res)+0.5
    a,*_=np.linalg.lstsq(A[kp],gx[gi][kp],rcond=None); b,*_=np.linalg.lstsq(A[kp],gy[gi][kp],rcond=None)
    Af=design(u,v,o); px,py=Af@a,Af@b
astro_med=float(np.median(res[kp])); nst=int(kp.sum())
# inverse map sky->pixel by local linearization + Newton
def sky2pix(xi,eta):
    xi=np.atleast_1d(xi);eta=np.atleast_1d(eta)
    X=np.full(xi.shape,nx/2.);Y=np.full(xi.shape,ny/2.)
    for _ in range(8):
        uu=(X-nx/2)/1000;vv=(Y-ny/2)/1000; D=design(uu,vv,3)
        fx=D@a-xi; fy=D@b-eta; e=1e-3
        D2=design(uu+e/1000,vv,3); D3=design(uu,vv+e/1000,3)
        j11=(D2@a-D@a)/e; j21=(D2@b-D@b)/e; j12=(D3@a-D@a)/e; j22=(D3@b-D@b)/e
        det=j11*j22-j12*j21
        X-= ( j22*fx-j12*fy)/det; Y-=(-j21*fx+j11*fy)/det
    return X,Y
# PSF sigma from moderately bright isolated stars
tx,ty=std(era,ede); TX,TY=sky2pix(tx,ty)
sx,sy=sky2pix(gx,gy)
sig=[]
for i in np.nonzero((G>12.5)&(G<14.5))[0]:
    X,Y=int(round(sx[i])),int(round(sy[i]))
    if X<12 or Y<12 or X>=nx-12 or Y>=ny-12: continue
    st=r[Y-10:Y+11,X-10:X+11]; yy2,xx2=np.mgrid[-10:11,-10:11]; w=np.clip(st,0,None)
    if w.sum()<=0: continue
    mx=(w*xx2).sum()/w.sum(); my=(w*yy2).sum()/w.sum()
    sig.append(np.sqrt(((w*((xx2-mx)**2+(yy2-my)**2)).sum()/w.sum())/2))
sigma=float(np.median(sig)) if sig else 5.0
# star mask (exclude stars, by Gaia G)
mask=np.zeros_like(r,bool)
rr=np.where(G<11,30,np.where(G<13,20,np.where(G<15,13,np.where(G<17,9,7))))
Yg,Xg=np.mgrid[0:ny,0:nx]
inb=(sx>-30)&(sy>-30)&(sx<nx+30)&(sy<ny+30)
for X,Y,R in zip(sx[inb],sy[inb],rr[inb]):
    Xi,Yi=int(X),int(Y); xa,xb=max(0,Xi-R),min(nx,Xi+R+1); ya,yb=max(0,Yi-R),min(ny,Yi+R+1)
    if xa>=xb or ya>=yb: continue
    mask[ya:yb,xa:xb]|=((Xg[ya:yb,xa:xb]-X)**2+(Yg[ya:yb,xa:xb]-Y)**2)<=R*R
# along-track profile at cross-track offsets
dTX=np.gradient(TX); dTY=np.gradient(TY); L=np.hypot(dTX,dTY); nxv=-dTY/L; nyv=dTX/L
rate=float(np.median(L))  # px per minute
rm=np.where(mask,np.nan,r)
def prof(off):
    cs=np.arange(-1.5*sigma,1.5*sigma+0.01,1.0); w=np.exp(-cs**2/(2*sigma**2))
    S=np.full(len(T),np.nan)
    for i in range(len(T)):
        X=TX[i]+nxv[i]*(off+cs); Y=TY[i]+nyv[i]*(off+cs)
        Xi=np.round(X).astype(int); Yi=np.round(Y).astype(int)
        ok=(Xi>=0)&(Yi>=0)&(Xi<nx)&(Yi<ny)
        if ok.sum()<len(cs)*0.6: continue
        vals=rm[Yi[ok],Xi[ok]]; ww=w[ok]; g2=np.isfinite(vals)
        if g2.sum()<len(cs)*0.5: continue
        S[i]=(vals[g2]*ww[g2]).sum()/ww[g2].sum()
    return S
tau=sigma/rate
def model(p,t): b,A,t1,t2=p; return b+A*0.5*(erf((t-t1)/(np.sqrt(2)*tau))-erf((t-t2)/(np.sqrt(2)*tau)))
best=None
OFFS=np.arange(-8,8.1,1.0) if len(sys.argv)<7 else np.arange(30,46.1,1.0)
for off in OFFS:
    S=prof(off); ok=np.isfinite(S)
    t=T[ok]; s=S[ok]
    if ok.sum()<100: continue
    b0=np.median(s);
    # grid search over t1,t2 (2-min) using closed-form A,b
    grid=np.arange(t.min(),t.max(),3.0); bestg=None
    cs=np.concatenate([[0],np.cumsum(s-b0)])
    tt=t
    for i1,t1 in enumerate(grid):
        j1=np.searchsorted(tt,t1)
        j2s=np.searchsorted(tt,grid[i1+5:])
        if len(j2s)==0: continue
        n=j2s-j1; m=(cs[j2s]-cs[j1])/np.maximum(n,1)
        score=m*np.sqrt(np.maximum(n,1))  # matched-filter SNR proxy
        k=np.argmax(score)
        if bestg is None or score[k]>bestg[0]: bestg=(score[k],t1,grid[i1+5+k],m[k])
    fit=least_squares(lambda p: model(p,t)-s,[b0,bestg[3],bestg[1],bestg[2]])
    resid=fit.fun; chi=np.sum(resid**2); chi0=np.sum((s-np.median(s))**2)
    noise=1.4826*np.median(np.abs(resid-np.median(resid)))
    snr=fit.x[1]/noise*np.sqrt(max((fit.x[3]-fit.x[2]),1)/1.0)
    if best is None or snr>best['snr']:
        best=dict(off=float(off),b=fit.x[0],A=fit.x[1],t1=fit.x[2],t2=fit.x[3],chi_red=1-chi/chi0,noise=noise,snr=float(snr))
def hhmm(m):
    tot=21*60+m; d=int(tot//1440); tot-=d*1440; return f'{"+1d " if d else ""}{int(tot//60):02d}:{tot%60:04.1f}'
b=best
mid=(b['t1']+b['t2'])/2
out=dict(plate=plate,asteroid=aid,nstars=nst,astro_med_arcsec=astro_med,sigma_px=sigma,rate_px_min=rate,cross_off_px=b['off'],
         t_open=hhmm(b['t1']),t_close=hhmm(b['t2']),t_mid=hhmm(mid),dur_min=b['t2']-b['t1'],trail_len_px=(b['t2']-b['t1'])*rate,
         amp=b['A'],noise=b['noise'],snr=b['snr'],frac_var_expl=b['chi_red'],mid_min_after_21UT=mid)
print(json.dumps(out))
np.savez(f'{wd}/trailS_{plate}_{aid}.npz',T=T,offs=np.arange(-4,5),S=np.array([prof(o) for o in range(-4,5)]),Sc=np.array([prof(o) for o in range(30,39)]),rate=rate,sigma=sigma)
np.save(f'{wd}/trailprof_{plate}_{aid}{"_ctrl" if len(sys.argv)>6 else ""}.npy',np.c_[T,prof(b['off'])])
