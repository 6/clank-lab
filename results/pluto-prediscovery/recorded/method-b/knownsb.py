# Known asteroids or comets at the MA 731 source, at the corrected open, mid and close times of the exposure
# (asteroid-trail clock), Taunton.
#  (a) IMCCE SkyBoT cone searches, radius 60" and, for context, 600"; no magnitude cut. SkyBoT takes an IAU code, so the
#      geocentre ('500'); parallax at Taunton is under 9"/Delta[AU], i.e. under 9" for any asteroid beyond 1 AU.
#  (b) JPL sb_ident, site coordinates, 1' half-width box, mag-required false, second (n-body) pass, one orbit class at a
#      time (the all-body request is refused for 1908, see the report); every request's status is recorded.
#  (c) Every body that sbnbody.py / sbassist.py put within 1 deg of the source at mid-exposure, plus Pluto, checked
#      with JPL Horizons, topocentric at Taunton, at the three times: separation, V, trail length and direction, and
#      the closest approach of the trail to the source.
# Usage: python3 -I knownsb.py ORBITS_JSON NBODY_DIR OUT_JSON MODE   (MODE ab: SkyBoT and sb_ident; b: sb_ident only; c: Horizons;
# results merge into OUT_JSON). sb_ident requests are spaced 15 s apart, with backoff of 60 s doubling on HTTP 429.
import sys, json, glob, time, urllib.request, urllib.parse, urllib.error, numpy as np
from astropy.time import Time
from astropy.coordinates import SkyCoord
import astropy.units as u
orb, nbd, oj, mode = sys.argv[1:5]
import os
RA, DEC = 85.893709844, 16.016634745          # MA 731 source (free centroid)
LON, LAT, ALT = -71.0903, 41.8997, 0.003
T = {'open': '1908-12-21 00:21:54', 'mid': '1908-12-21 00:58:23.1', 'close': '1908-12-21 01:34:48'}
cosd = np.cos(np.radians(DEC))
def off(ra, de): return np.array([(ra-RA)*cosd*3600, (de-DEC)*3600])     # east, north (arcsec)
out = json.load(open(oj)) if os.path.exists(oj) else {'times_utc': T, 'source_radec_deg': [RA, DEC], 'skybot': {}, 'sb_ident': {}, 'horizons': {}}
# (a) SkyBoT
from astroquery.imcce import Skybot
for rad in ((60, 600) if mode == 'ab' else ()):
    for k, t in T.items():
        key = f'{k}_r{rad}'
        try:
            r = Skybot.cone_search(SkyCoord(RA, DEC, unit='deg'), rad*u.arcsec, Time(t, scale='utc'), location='500', cache=False)
            out['skybot'][key] = [dict(number=str(x['Number']), name=str(x['Name']), type=str(x['Type']), V=float(x['V'].value if hasattr(x['V'], 'value') else x['V']),
                                       sep_arcsec=round(float(np.hypot(*off(float(x['RA'].value if hasattr(x['RA'], 'value') else x['RA']),
                                                                             float(x['DEC'].value if hasattr(x['DEC'], 'value') else x['DEC'])))), 2))
                                  for x in r]
        except RuntimeError as e:
            out['skybot'][key] = [] if 'No solar system object' in str(e) else 'error: '+str(e)[:150]
        except Exception as e:
            out['skybot'][key] = 'error: '+str(e)[:150]
        print('skybot', key, out['skybot'][key], flush=True)
# (b) sb_ident, class by class
CLS = [('sb-kind', 'c')]+[('sb-class', c) for c in ('IEO', 'ATE', 'APO', 'AMO', 'MCA', 'IMB', 'MBA', 'OMB', 'TJN', 'CEN', 'TNO', 'AST', 'HYA', 'PAR', 'HYP')]
if os.environ.get('SBCLASSES'): CLS = [c for c in CLS if c[1] in os.environ['SBCLASSES'].split(',')]
for k, t in ([(k, t) for k, t in T.items() if k in os.environ.get('SBTIMES', 'open,mid,close').split(',')] if mode in ('ab', 'b') else ()):
    for fk, fv in CLS:
        p = {'obs-time': t.split('.')[0].replace(' ', '_'), 'lat': LAT, 'lon': LON, 'alt': ALT, 'fov-ra-center': '05-43-34.490', 'fov-dec-center': '16-00-59.89',
             'fov-ra-hwidth': 1/60, 'fov-dec-hwidth': 1/60, 'two-pass': 'true', 'suppress-first-pass': 'true', 'mag-required': 'false', fk: fv}
        t0 = time.time(); wait = 60; tries = 0
        while True:
            tries += 1; time.sleep(15)
            try:
                txt = urllib.request.urlopen('https://ssd-api.jpl.nasa.gov/sb_ident.api?'+urllib.parse.urlencode(p), timeout=900).read().decode()
                d = json.loads(txt)
                st = dict(status='ok', n_second_pass=d.get('n_second_pass'), warning=d.get('warning'), data=d.get('data_second_pass', []), fields=d.get('fields_second'))
            except urllib.error.HTTPError as e:
                body = e.read().decode()
                try: msg = json.loads(body).get('message')
                except ValueError: msg = body.split('<title>')[-1].split('</title>')[0][:150]
                st = dict(status=f'HTTP {e.code}', message=msg)
                if e.code == 429 and tries < 6:
                    time.sleep(wait); wait *= 2; continue
            except Exception as e:
                st = dict(status='error', message=str(e)[:150])
            break
        st['wall_s'] = round(time.time()-t0); st['tries'] = tries
        out['sb_ident'][f'{k}|{fk}={fv}'] = st
        json.dump(out, open(oj, 'w'), indent=1)
        print('sb_ident', k, fv, {a: b for a, b in st.items() if a not in ('data', 'fields')}, st.get('data', [])[:3], flush=True)
# (c) Horizons for Pluto and for every n-body body within 1 deg at mid-exposure
d = json.load(open(orb)); f = {k: i for i, k in enumerate(d['fields'])}; A = d['data']
near = []
for p in [] if mode != 'c' else sorted(glob.glob(f'{nbd}/rest*.npz'))+sorted(glob.glob(f'{nbd}/neo*.npz')):
    z = np.load(p)
    for i, s in zip(z['idx'], z['sep']):
        if s < 1.0: near.append((A[i][f['pdes']], A[i][f['class']], A[i][f['H']], float(s)))
out['nbody_within_1deg'] = [dict(pdes=a, cls=b, H=c, sep_deg=round(s, 4)) for a, b, c, s in sorted(near, key=lambda x: x[3])]
def hz(cmd):
    rows = []
    for t in T.values():
        p = dict(format='json', COMMAND=f"'{cmd}'", OBJ_DATA='NO', MAKE_EPHEM='YES', EPHEM_TYPE='OBSERVER', CENTER="'coord@399'", COORD_TYPE='GEODETIC',
                 SITE_COORD=f"'{LON},{LAT},{ALT}'", TLIST=f"'{t}'", QUANTITIES="'1,9'", CSV_FORMAT='YES', ANG_FORMAT='DEG', EXTRA_PREC='YES')
        r = json.load(urllib.request.urlopen('https://ssd.jpl.nasa.gov/api/horizons.api?'+urllib.parse.urlencode(p), timeout=120))['result']
        if '$$SOE' not in r: return r[:300]
        v = [x.strip() for x in r[r.index('$$SOE')+5:r.index('$$EOE')].strip().split(',')]
        rows.append((float(v[3]), float(v[4]), float(v[5]) if v[5] not in ('', 'n.a.') else None))
    return rows
for name, cmd in ([] if mode != 'c' else [('Pluto', '999')])+[(a, f'{a};' if a.isdigit() else f'DES={a};') for a, *_ in near]:
    try:
        rows = hz(cmd)
        if isinstance(rows, str): out['horizons'][name] = 'error: '+rows; continue
        (r0, d0, _), (r1, d1, m1), (r2, d2, _) = rows
        o0, o1, o2 = off(r0, d0), off(r1, d1), off(r2, d2); tr = o2-o0
        L2 = float(tr @ tr); tt = np.clip(-(o0 @ tr)/L2, 0, 1) if L2 > 0 else 0.0
        out['horizons'][name] = dict(sep_open_arcsec=round(float(np.hypot(*o0)), 2), sep_mid_arcsec=round(float(np.hypot(*o1)), 2),
                                     sep_close_arcsec=round(float(np.hypot(*o2)), 2), closest_approach_of_trail_arcsec=round(float(np.hypot(*(o0+tt*tr))), 2),
                                     V_mid=m1, trail_arcsec=round(float(np.sqrt(L2)), 2), trail_PA_deg=round(float(np.degrees(np.arctan2(tr[0], tr[1])) % 360), 1))
    except Exception as e:
        out['horizons'][name] = 'error: '+str(e)[:150]
    print('horizons', name, out['horizons'][name], flush=True)
json.dump(out, open(oj, 'w'), indent=1)
