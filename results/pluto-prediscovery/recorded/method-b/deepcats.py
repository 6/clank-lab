# Deep-catalogue check at the MA 731 source position: Pan-STARRS DR2 (mean and stack), Legacy Survey DR10 (Tractor),
# 2MASS PSC, VSX and SIMBAD. Writes raw replies under WORKDIR and prints each source within 15".
# Usage: python3 -I deepcats.py WORKDIR
import sys, json, csv, io, urllib.request, urllib.parse, numpy as np
import os as _os
RA, DEC = float(_os.environ.get('POS_RA', 85.893709844)), float(_os.environ.get('POS_DEC', 16.016634745))   # round five: POS_RA/POS_DEC/POS_TAG for another position
TAG = _os.environ.get('POS_TAG', '')
wd = sys.argv[1]
def get(url, data=None, fn=None):
    req = urllib.request.Request(url, data=data, headers={'User-Agent': 'curl/8'})
    t = urllib.request.urlopen(req, timeout=180).read().decode()
    if fn: open(f'{wd}/{fn}', 'w').write(t)
    return t
def sep(ra, de): return np.hypot((np.asarray(ra, float)-RA)*np.cos(np.radians(DEC)), np.asarray(de, float)-DEC)*3600
out = {}
for kind in ('mean', 'stack'):
    t = get(f'https://catalogs.mast.stsci.edu/api/v0.1/panstarrs/dr2/{kind}.csv?ra={RA}&dec={DEC}&radius=0.0041667', fn=f'ps1_{kind}.csv')
    rows = list(csv.DictReader(io.StringIO(t)))
    rec = []
    for r in rows:
        ra = r.get('raMean') or r.get('raStack'); de = r.get('decMean') or r.get('decStack')
        if kind == 'stack' and r.get('primaryDetection') not in ('1', 'True', 'true'): continue
        mags = {b: r.get(f'{b}MeanPSFMag' if kind == 'mean' else f'{b}PSFMag') for b in 'grizy'}
        rec.append(dict(sep=round(float(sep(float(ra), float(de))), 2), nDet=r.get('nDetections'), **{b: (round(float(v), 2) if v not in (None, '', '-999.0', '-999') and float(v) > -900 else None) for b, v in mags.items()}))
    out[f'ps1_{kind}'] = sorted(rec, key=lambda x: x['sep'])
q = f"SELECT ra, dec, type, mag_g, mag_r, mag_z, nobs_g, nobs_r FROM ls_dr10.tractor WHERE ra BETWEEN {RA-0.0044} AND {RA+0.0044} AND dec BETWEEN {DEC-0.0042} AND {DEC+0.0042}"
try:
    t = get('https://datalab.noirlab.edu/tap/sync', data=urllib.parse.urlencode({'REQUEST': 'doQuery', 'LANG': 'ADQL', 'FORMAT': 'csv', 'QUERY': q}).encode(), fn='ls_dr10.csv')
    rows = list(csv.DictReader(io.StringIO(t)))
    out['ls_dr10'] = sorted([d for d in [dict(sep=round(float(sep(float(r['ra']), float(r['dec']))), 2), type=r['type'], g=r['mag_g'], r=r['mag_r'], z=r['mag_z'], nobs_g=r['nobs_g'], nobs_r=r['nobs_r']) for r in rows] if d['sep'] <= 15], key=lambda x: x['sep'])
    if not rows: out['ls_dr10_note'] = 'no Tractor sources within 15" (check coverage below)'
    q2 = f"SELECT count(*) AS n FROM ls_dr10.tractor WHERE ra BETWEEN {RA-0.0347} AND {RA+0.0347} AND dec BETWEEN {DEC-0.0333} AND {DEC+0.0333}"
    out['ls_dr10_sources_in_4x4arcmin_box'] = get('https://datalab.noirlab.edu/tap/sync', data=urllib.parse.urlencode({'REQUEST': 'doQuery', 'LANG': 'ADQL', 'FORMAT': 'csv', 'QUERY': q2}).encode()).split()[-1]
except Exception as e:
    out['ls_dr10_error'] = str(e)[:150]
from astroquery.vizier import Vizier
from astropy.coordinates import SkyCoord
import astropy.units as u
V = Vizier(row_limit=-1); V.VIZIER_SERVER = 'vizier.cfa.harvard.edu'
c = SkyCoord(RA, DEC, unit='deg')
for lab, cat, rad in (('2mass', 'II/246/out', 15), ('vsx', 'B/vsx/vsx', 60), ('gaia_dr3_all', 'I/355/gaiadr3', 15), ('ucac4', 'I/322A/out', 15), ('usnob1', 'I/284/out', 15)):
    try:
        r = V.query_region(c, radius=rad*u.arcsec, catalog=cat)
        if len(r) == 0: out[lab] = []; continue
        t = r[0]; rc = [k for k in t.colnames if k.upper().startswith(('RAJ2000', 'RA_ICRS', '_RA', 'RAICRS', 'RADEG'))][0]
        dc = [k for k in t.colnames if k.upper().startswith(('DEJ2000', 'DE_ICRS', '_DE', 'DEICRS', 'DEDEG'))][0]
        s = sep(t[rc], t[dc]); keep = [k for k in t.colnames if any(m in k for m in ('mag', 'Jmag', 'Hmag', 'Kmag', 'Gmag', 'Bmag', 'Rmag', 'Name', 'Type', 'max', 'min'))][:8]
        out[lab] = sorted([dict(sep=round(float(si), 2), **{k: (str(row[k])) for k in keep}) for si, row in zip(s, t)], key=lambda x: x['sep'])
    except Exception as e:
        out[lab + '_error'] = str(e)[:150]
try:
    from astroquery.simbad import Simbad
    r = Simbad.query_region(c, radius=60*u.arcsec)
    out['simbad_60arcsec'] = [] if r is None else [str(x) for x in r[r.colnames[0]]]
except Exception as e:
    out['simbad_error'] = str(e)[:150]
json.dump(out, open(f'{wd}/deepcats{"_" + TAG if TAG else ""}.json', 'w'), indent=1)
for k, v in out.items():
    print(k, ':', (v[:6] if isinstance(v, list) else v))
# The single-epoch Pan-STARRS z detection 0.9" away (MJD 55508.6276): is a known asteroid there then?
try:
    from astroquery.imcce import Skybot
    from astropy.time import Time
    sb = Skybot.cone_search(c, 60*u.arcsec, Time(55508.62759259, format='mjd'), location='F51', cache=False)
    out['skybot_ps1_epoch'] = [dict(name=str(r['Name']), number=str(r['Number']), sep=round(float(sep(float(r['RA']), float(r['DEC']))), 1), V=float(r['V'])) for r in sb]
except Exception as e:
    out['skybot_ps1_epoch'] = 'none or error: '+str(e)[:120]
json.dump(out, open(f'{wd}/deepcats{"_" + TAG if TAG else ""}.json', 'w'), indent=1)
print('skybot_ps1_epoch :', out['skybot_ps1_epoch'])
