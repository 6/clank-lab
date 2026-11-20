# Independent astrometric solution: own source extraction + own polynomial fit to Gaia DR3 propagated to 1908.97.
import sys, json, numpy as np
from astropy.io import fits
from astropy.wcs import WCS
from astropy.table import Table
from scipy import ndimage as nd
from scipy.spatial import cKDTree
plate, mosaic, wd = sys.argv[1], sys.argv[2], sys.argv[3]
img=np.load(f'{wd}/cut{plate}.npy').astype(np.float32)
x0,y0=map(int,open(f'{wd}/cut{plate}.off').read().split())
# background: median of 64-px blocks, smoothed and upsampled
B=64; ny,nx=img.shape
bl=img[:ny//B*B,:nx//B*B].reshape(ny//B,B,nx//B,B)
bm=np.median(bl,axis=(1,3)); bm=nd.median_filter(bm,5)
bg=nd.zoom(bm,(img.shape[0]/bm.shape[0],img.shape[1]/bm.shape[1]),order=1)[:ny,:nx]
r=img-bg
mad=1.4826*np.median(np.abs(r-np.median(r)))
sm=nd.gaussian_filter(r,3.0)
smad=1.4826*np.median(np.abs(sm-np.median(sm)))
mx=nd.maximum_filter(sm,size=15)
pk=(sm==mx)&(sm>5*smad)
ys,xs=np.nonzero(pk)
# windowed centroid on residual image
hw=7
cx=[];cy=[];amp=[];flux=[]
yy,xx=np.mgrid[-hw:hw+1,-hw:hw+1]
for y,x in zip(ys,xs):
    if y<hw or x<hw or y>=ny-hw or x>=nx-hw: continue
    st=r[y-hw:y+hw+1,x-hw:x+hw+1]
    wgt=np.clip(st,0,None)*np.exp(-(xx**2+yy**2)/(2*4.0**2))
    s=wgt.sum()
    if s<=0: continue
    dx=(wgt*xx).sum()/s; dy=(wgt*yy).sum()/s
    # one refinement
    wgt=np.clip(st,0,None)*np.exp(-((xx-dx)**2+(yy-dy)**2)/(2*4.0**2)); s=wgt.sum()
    dx=(wgt*xx).sum()/s; dy=(wgt*yy).sum()/s
    cx.append(x+dx); cy.append(y+dy); amp.append(sm[y,x]); flux.append(np.clip(st,0,None)[(xx**2+yy**2)<=36].sum())
cx=np.array(cx);cy=np.array(cy);amp=np.array(amp);flux=np.array(flux)
print('detections',len(cx),'smad',smad,'mad',mad)
# Gaia at epoch
g=Table.read(f'{wd}/gaia.fits')
ep=1908.973; dt=ep-2016.0
pmra=np.nan_to_num(np.array(g['pmra'],float)); pmdec=np.nan_to_num(np.array(g['pmdec'],float))
dec=np.array(g['dec'],float)+pmdec*dt/3.6e6
ra=np.array(g['ra'],float)+pmra*dt/3.6e6/np.cos(np.radians(dec))
G=np.array(g['phot_g_mean_mag'],float)
haspm=~np.ma.getmaskarray(g['pmra'])
# tangent plane at Pluto approx
ra0,de0=np.radians(85.885),np.radians(16.017)
def std(rad,ded):
    a=np.radians(rad);d=np.radians(ded)
    c=np.sin(d)*np.sin(de0)+np.cos(d)*np.cos(de0)*np.cos(a-ra0)
    xi=np.cos(d)*np.sin(a-ra0)/c; eta=(np.sin(d)*np.cos(de0)-np.cos(d)*np.sin(de0)*np.cos(a-ra0))/c
    return np.degrees(xi)*3600,np.degrees(eta)*3600
def inv(xi,eta):
    xi=np.radians(xi/3600);eta=np.radians(eta/3600)
    den=np.cos(de0)-eta*np.sin(de0)
    a=ra0+np.arctan2(xi,den); d=np.arctan2(np.sin(de0)+eta*np.cos(de0),np.hypot(xi,den))
    return np.degrees(a)%360,np.degrees(d)
gx,gy=std(ra,dec)
# seed: linear TAN of the mosaic header (only to pair stars)
hd=fits.open(mosaic)[1].header
cd=np.array([[hd['CD1_1'],hd['CD1_2']],[hd['CD2_1'],hd['CD2_2']]])
from astropy.wcs import WCS
wl=WCS(naxis=2); wl.wcs.ctype=['RA---TAN','DEC--TAN']; wl.wcs.crval=[hd['CRVAL1'],hd['CRVAL2']]; wl.wcs.crpix=[hd['CRPIX1'],hd['CRPIX2']]; wl.wcs.cd=cd
sra,sde=wl.all_pix2world(cx+x0,cy+y0,0)
sx,sy=std(sra,sde)
def design(u,v,order):
    cols=[]
    for i in range(order+1):
        for j in range(order+1-i): cols.append(u**i*v**j)
    return np.array(cols).T
u=(cx-2100)/2000; v=(cy-2100)/2000
bright=(G<16.5)&haspm
tree=cKDTree(np.c_[gx[bright],gy[bright]])
idxb=np.nonzero(bright)[0]
px,py=sx,sy
for it,(rad,order) in enumerate([(40,1),(15,2),(6,3),(4,3),(4,3)]):
    d,k=tree.query(np.c_[px,py],distance_upper_bound=rad)
    ok=np.isfinite(d)
    # unique matches
    gi=idxb[k[ok]]; di=np.nonzero(ok)[0]
    _,first=np.unique(gi,return_index=True); gi=gi[first]; di=di[first]
    A=design(u[di],v[di],order)
    cxi,*_=np.linalg.lstsq(A,gx[gi],rcond=None); cet,*_=np.linalg.lstsq(A,gy[gi],rcond=None)
    res=np.hypot(A@cxi-gx[gi],A@cet-gy[gi])
    keep=res<3*np.median(res)+0.5
    A=A[keep]; cxi,*_=np.linalg.lstsq(A,gx[gi][keep],rcond=None); cet,*_=np.linalg.lstsq(A,gy[gi][keep],rcond=None)
    Af=design(u,v,order); px,py=Af@cxi,Af@cet
    print(f'iter{it} rad{rad} ord{order} matched {len(gi)} kept {keep.sum()} medres {np.median(res):.3f}"')
# final: cross-validated residuals, 5-fold, near Pluto (within 600") and overall
gi2=gi[keep]; di2=di[keep]
A=design(u[di2],v[di2],3)
rng=np.random.default_rng(1); fold=rng.integers(0,5,len(gi2)); cvres=np.zeros((len(gi2),2))
for f in range(5):
    tr=fold!=f
    a,*_=np.linalg.lstsq(A[tr],gx[gi2][tr],rcond=None); b,*_=np.linalg.lstsq(A[tr],gy[gi2][tr],rcond=None)
    cvres[~tr,0]=A[~tr]@a-gx[gi2][~tr]; cvres[~tr,1]=A[~tr]@b-gy[gi2][~tr]
cr=np.hypot(*cvres.T)
near=np.hypot(gx[gi2],gy[gi2])<600
print('N stars',len(gi2),'CV radial median %.2f" rms %.2f"; within 600" of Pluto: N %d median %.2f rms %.2f'%(np.median(cr),np.sqrt(np.mean(cr**2)),near.sum(),np.median(cr[near]),np.sqrt(np.mean(cr[near]**2))))
np.savez(f'{wd}/astrom{plate}.npz',cxi=cxi,cet=cet,x0=x0,y0=y0,cx=cx,cy=cy,amp=amp,flux=flux,smad=smad,gi=gi2,di=di2,cvres=cvres)
# Also invert: function pixel for given sky
print('seed vs own solution at Pluto approx: ', end='')
from scipy.optimize import least_squares
def topix(xi_t,eta_t):
    f=lambda p: np.r_[design(np.array([(p[0]-2100)/2000]),np.array([(p[1]-2100)/2000]),3)@cxi-xi_t, design(np.array([(p[0]-2100)/2000]),np.array([(p[1]-2100)/2000]),3)@cet-eta_t]
    return least_squares(f,[2100,2100]).x
p=topix(0,0); print('cut pixel of tangent point', p)
