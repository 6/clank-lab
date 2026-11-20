# Barycentric ecliptic-J2000 states (AU, AU/day) from JPL Horizons for the Sun, planets (EMB and planetary-system
# barycentres) at the SBDB epoch, and of Earth's geocentre at MA 731's mid-exposure. Usage: python3 -I sbplanets.py OUT_JSON
import sys, json, urllib.request, urllib.parse
EP, TEND = 'JD 2461200.5', 'JD 2418296.540632'
MASS = {'10': 1.0, '199': 1/6023600, '299': 1/408523.71, '3': 1/328900.56, '4': 1/3098708, '5': 1/1047.3486,
        '6': 1/3497.898, '7': 1/22902.98, '8': 1/19412.24}
def vec(cmd, t):
    p = dict(format='json', COMMAND=f"'{cmd}'", OBJ_DATA='NO', MAKE_EPHEM='YES', EPHEM_TYPE='VECTORS', CENTER="'@0'", REF_PLANE='ECLIPTIC',
             REF_SYSTEM='ICRF', OUT_UNITS='AU-D', VEC_TABLE='2', CSV_FORMAT='YES', TLIST=f"'{t.split()[1]}'", TLIST_TYPE='JD', TIME_TYPE='TDB')
    r = json.load(urllib.request.urlopen('https://ssd.jpl.nasa.gov/api/horizons.api?'+urllib.parse.urlencode(p), timeout=120))['result']
    v = r[r.index('$$SOE')+5:r.index('$$EOE')].strip().split(',')
    return [float(x) for x in v[2:8]]
out = {'bodies': []}
for c, m in MASS.items():
    s = vec(c, EP); out['bodies'].append(dict(id=c, m=m, r=s[:3], v=s[3:]))
out['earth_tend'] = vec('399', TEND)
json.dump(out, open(sys.argv[1], 'w'), indent=1); print('ok', len(out['bodies']))
