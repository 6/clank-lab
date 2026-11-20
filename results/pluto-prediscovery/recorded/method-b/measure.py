import sys, json, numpy as np
import os; sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
from common import *
from astropy.table import Table
from scipy import ndimage as nd
wd=sys.argv[1]
hz=json.load(open(f'{wd}/pluto_hz.json'))
ap=Table.read(f'{wd}/apass.fits')
res={}
for pl in ['731','733']:
    P=Plate(wd,pl); r=P.r
    pra,pde=float(hz[pl]['mid'][3]),float(hz[pl]['mid'][4])
    px,py=P.sky2pix(pra,pde); px,py=float(px[0]),float(py[0])
    oa=[float(v) for v in hz[pl]['open'][3:5]]; ob=[float(v) for v in hz[pl]['close'][3:5]]
    ox,oy=P.sky2pix(*oa); cx_,cy_=P.sky2pix(*ob)
    # PSF sigma from APASS stars B 14-16 near Pluto (second moments)
    ax,ay=P.sky2pix(np.array(ap['RAJ2000'],float),np.array(ap['DEJ2000'],float))
    Bm=np.array(ap['Bmag'],float); BV=np.array(ap['B-V'],float)
    sig=[]
    yy,xx=np.mgrid[-12:13,-12:13]
    for X,Y,b in zip(ax,ay,Bm):
        if not(14<b<16) or X<20 or Y<20 or X>P.nx-20 or Y>P.ny-20: continue
        st=np.clip(r[int(Y)-12:int(Y)+13,int(X)-12:int(X)+13],0,None)
        if st.sum()<=0: continue
        mx=(st*xx).sum()/st.sum(); my=(st*yy).sum()/st.sum()
        sig.append(np.sqrt((st*((xx-mx)**2+(yy-my)**2)).sum()/st.sum()/2))
    sigma=float(np.median(sig))
    # matched filter: Gaussian sigma, plus trail smear for this plate (line convolved)
    mf=nd.gaussian_filter(r,sigma)
    rng=np.random.default_rng(0)
    rx=rng.integers(50,P.nx-50,20000); ry=rng.integers(50,P.ny-50,20000)
    v=mf[ry,rx]; noise=1.4826*np.median(np.abs(v-np.median(v))); base=np.median(v)
    def snr_at(x,y): return (nd.map_coordinates(mf,[[y],[x]],order=1)[0]-base)/noise
    # free centroid: local max of mf within 8 px of prediction, then windowed centroid on r
    X0,Y0=int(round(px)),int(round(py)); w=8
    sub=mf[Y0-w:Y0+w+1,X0-w:X0+w+1]; yy2,xx2=np.mgrid[-w:w+1,-w:w+1]; inside=(xx2**2+yy2**2)<=w*w
    k=np.argmax(np.where(inside,sub,-1e9)); my_,mx_=np.unravel_index(k,sub.shape)
    lx,ly=X0-w+mx_,Y0-w+my_
    # windowed centroid
    hw=7; yy3,xx3=np.mgrid[-hw:hw+1,-hw:hw+1]; st=np.clip(r[ly-hw:ly+hw+1,lx-hw:lx+hw+1],0,None); dx=dy=0
    for _ in range(3):
        ww=st*np.exp(-((xx3-dx)**2+(yy3-dy)**2)/(2*sigma**2)); dx=(ww*xx3).sum()/ww.sum(); dy=(ww*yy3).sum()/ww.sum()
    fx,fy=lx+dx,ly+dy
    fra,fde=P.pix2sky(fx,fy)
    dxi=(float(fra[0])-pra)*np.cos(np.radians(pde))*3600; deta=(float(fde[0])-pde)*3600
    edge=bool(not inside[my_,mx_] or np.hypot(mx_-w,my_-w)>w-1)
    # photometric calibration: peak mf (above base) vs APASS B with colour term
    sel=(Bm>13)&(Bm<17.6)&np.isfinite(BV)&(ax>30)&(ay>30)&(ax<P.nx-30)&(ay<P.ny-30)&(np.hypot(ax-px,ay-py)<1500)
    pk=np.array([nd.map_coordinates(mf,[[y],[x]],order=1)[0]-base for x,y in zip(ax[sel],ay[sel])])
    good=pk>3*noise
    L=np.log10(pk[good]); A=np.c_[np.ones(good.sum()),L,L**2,BV[sel][good]]
    for _ in range(3):
        c,*_=np.linalg.lstsq(A,Bm[sel][good],rcond=None); rs=A@c-Bm[sel][good]; m=np.abs(rs)<3*1.4826*np.median(np.abs(rs))
        A=A[m]; Bt=Bm[sel][good][m]; L=L[m];
        c,*_=np.linalg.lstsq(A,Bt,rcond=None)
        good_idx=None
        break
    rsd=1.4826*np.median(np.abs(A@c-Bt))
    peak_c=nd.map_coordinates(mf,[[fy],[fx]],order=1)[0]-base
    peak_p=nd.map_coordinates(mf,[[py],[px]],order=1)[0]-base
    def Bof(pk,bv=0.78): l=np.log10(pk); return c[0]+c[1]*l+c[2]*l*l+c[3]*bv
    # expected peak for B=16.35 (Pluto, B-V=0.78): invert
    grid=np.logspace(np.log10(noise*0.3),np.log10(noise*200),4000); Bg=Bof(grid); i=np.argmin(np.abs(Bg-16.35)); pk1635=grid[i]
    res[pl]=dict(pred_ra=pra,pred_dec=pde,pred_pix=[px,py],trail_pix=[[float(ox[0]),float(oy[0])],[float(cx_[0]),float(cy_[0])]],sigma_px=sigma,
        snr_at_pred=float(snr_at(px,py)),free_centroid_ra=float(fra[0]),free_centroid_dec=float(fde[0]),offset_east_arcsec=dxi,offset_north_arcsec=deta,
        offset_arcsec=float(np.hypot(dxi,deta)),snr_at_centroid=float(snr_at(fx,fy)),centroid_at_search_edge=edge,
        B_est_centroid=float(Bof(peak_c)) if peak_c>0 else None,B_est_pred=float(Bof(peak_p)) if peak_p>0 else None,
        calib_coeffs=c.tolist(),calib_nstars=int(len(Bt)),calib_rms_mag=float(rsd),colour_coeff=float(c[3]),snr_expected_B1635=float(pk1635/noise),noise=float(noise))
    print(pl,json.dumps({k:(round(v,3) if isinstance(v,float) else v) for k,v in res[pl].items() if k not in('calib_coeffs','trail_pix')}))
json.dump(res,open(f'{wd}/measure.json','w'),indent=1)
