# Accuracy of sbnbody.py against JPL Horizons (geocentric astrometric RA/Dec at MA 731 mid-exposure) for a random sample
# per orbit class from the chunks already run. Usage: python3 -I sbvalidate.py ORBITS_JSON OUTDIR NPERCLASS GROUP
import sys, json, glob, numpy as np, urllib.request, urllib.parse
d = json.load(open(sys.argv[1])); f = {k: i for i, k in enumerate(d['fields'])}; A = d['data']
Z = [np.load(p) for p in sorted(glob.glob(sys.argv[2]+'/'+sys.argv[4]+'*.npz'))]
idx = np.concatenate([z['idx'] for z in Z]); ra = np.concatenate([z['ra'] for z in Z]); de = np.concatenate([z['dec'] for z in Z])
cl = np.array([A[i][f['class']] for i in idx]); rng = np.random.default_rng(5); res = {}
for c in np.unique(cl):
    w = np.where(cl == c)[0]; errs = []
    for k in rng.choice(w, min(int(sys.argv[3]), len(w)), replace=False):
        pd = A[idx[k]][f['pdes']]; cmd = f'{pd};' if pd.isdigit() else f'DES={pd};'
        p = dict(format='json', COMMAND=f"'{cmd}'", OBJ_DATA='NO', MAKE_EPHEM='YES', EPHEM_TYPE='OBSERVER', CENTER="'500@399'",
                 TLIST="'2418296.540544'", TLIST_TYPE='JD', TIME_TYPE='UT', QUANTITIES="'1'", CSV_FORMAT='YES', ANG_FORMAT='DEG', EXTRA_PREC='YES')
        try:
            r = json.load(urllib.request.urlopen('https://ssd.jpl.nasa.gov/api/horizons.api?'+urllib.parse.urlencode(p), timeout=120))['result']
            v = r[r.index('$$SOE')+5:r.index('$$EOE')].strip().split(','); hr, hd = float(v[3]), float(v[4])
            cs = np.sin(np.radians(hd))*np.sin(np.radians(de[k]))+np.cos(np.radians(hd))*np.cos(np.radians(de[k]))*np.cos(np.radians(hr-ra[k]))
            errs.append(float(np.degrees(np.arccos(min(1, cs)))*3600))
        except Exception as e:
            print(c, pd, 'error', str(e)[:80])
    e = np.array(errs); res[c] = dict(n=len(e), n_over_60arcsec=int((e > 60).sum()), n_over_1deg=int((e > 3600).sum()), median_arcsec=float(np.median(e)), p90_arcsec=float(np.percentile(e, 90)), max_arcsec=float(e.max()))
    print(c, res[c], flush=True)
json.dump(res, open(sys.argv[2]+'/validate_'+sys.argv[4]+'.json', 'w'), indent=1)
