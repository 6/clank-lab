import sys, json, numpy as np, urllib.request, urllib.parse
import os; sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
from common import *
from scipy import ndimage as nd
wd=sys.argv[1]; M=json.load(open(f'{wd}/measure.json'))
arch={'731':"'1908-12-21 06:46:36.5'",'733':"'1908-12-22 06:49:09.5'"}
out={}
for pl in ['731','733']:
    p=dict(format='json',COMMAND="'999'",OBJ_DATA='NO',MAKE_EPHEM='YES',EPHEM_TYPE='OBSERVER',CENTER="'coord@399'",COORD_TYPE='GEODETIC',SITE_COORD="'-71.0903,41.8997,0.003'",TLIST=arch[pl],QUANTITIES="'1'",CSV_FORMAT='YES',ANG_FORMAT='DEG',EXTRA_PREC='YES',TIME_DIGITS='FRACSEC')
    txt=json.load(urllib.request.urlopen('https://ssd.jpl.nasa.gov/api/horizons.api?'+urllib.parse.urlencode(p),timeout=120))['result']
    r=txt[txt.index('$$SOE')+5:txt.index('$$EOE')].strip().split(','); ra,de=float(r[3]),float(r[4])
    P=Plate(wd,pl); s=M[pl]['sigma_px']; mf=nd.gaussian_filter(P.r,s)
    rng=np.random.default_rng(0); rx=rng.integers(50,P.nx-50,20000); ry=rng.integers(50,P.ny-50,20000); v=mf[ry,rx]; b=np.median(v); n=1.4826*np.median(np.abs(v-b))
    X,Y=P.sky2pix(ra,de); sn=(nd.map_coordinates(mf,[Y,X],order=1)[0]-b)/n
    sub=(mf[int(Y[0])-3:int(Y[0])+4,int(X[0])-3:int(X[0])+4]-b)/n
    sep=np.hypot((ra-M[pl]['pred_ra'])*np.cos(np.radians(de)),de-M[pl]['pred_dec'])*3600
    # Pluto-implied time: along-track offset of free centroid / rate
    e=np.load(f'{wd}/hz_{pl}_999.npz');
    xi,eta=std(e['ra'],e['dec']); cxi,ceta=std(M[pl]['free_centroid_ra'],M[pl]['free_centroid_dec'])
    k=np.argmin(np.hypot(xi-cxi,eta-ceta));
    # sub-minute: project
    t_best=k; dxi=xi[k+1]-xi[k]; deta=eta[k+1]-eta[k]; frac=((cxi-xi[k])*dxi+(ceta-eta[k])*deta)/(dxi**2+deta**2)
    tmin=k+frac; tot=21*60+tmin; tot%=1440
    cross=abs((cxi-xi[k])*deta-(ceta-eta[k])*dxi)/np.hypot(dxi,deta)
    out[pl]=dict(archive_pos_sep_from_corrected_arcsec=float(sep),snr_at_archive_pos=float(np.ravel(sn)[0]),max_snr_within_3px_archive=float(sub.max()),pluto_implied_time_UT=f'{int(tot//60):02d}:{tot%60:04.1f}',cross_track_arcsec=float(cross))
    print(pl,json.dumps(out[pl]))
json.dump(out,open(f'{wd}/archpos.json','w'),indent=1)
