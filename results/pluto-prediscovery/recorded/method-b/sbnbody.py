# Where were the known asteroids at MA 731's mid-exposure? A JPL-orbit n-body check for the classes sb_ident could not run for 1908.
# JPL SBDB osculating elements (heliocentric ecliptic J2000) are integrated back to 1908-12-21 00:58 UT with the Sun and eight
# planets (REBOUND test particles, WHFast, 4-day step). The 'neo' group (MERCURIUS) was a test that failed validation
# against Horizons; the reported NEO positions come from sbassist.py. Each body's geocentric astrometric position (one light-time
# step) is compared with the MA 731 source. Bodies near the source are then checked exactly with Horizons (knownsb.py).
# Only bodies that could reach V <= 18 here are kept: the source is near opposition, so Delta >= r - 0.9837 AU, and
# V >= H + 5 log10(q (q - 0.9837)) for perihelion q > 1.1 AU (phase only makes a body fainter).
# Usage: python3 -I sbnbody.py ORBITS_JSON PLANETS_JSON OUTDIR CHUNK NCHUNK GROUP   (GROUP: neo = ATE, APO, AMO, IEO; rest = others)
import sys, json, numpy as np, rebound
orb, pln, od, ch, nch, grp = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4]), int(sys.argv[5]), sys.argv[6]
RA0, DE0 = 85.893709844, 16.016634745
EP = 2461200.5                                   # common SBDB epoch (TDB)
TEND = 2418296.540545 + 7.5/86400               # 1908-12-21 00:58:23.1 UT as TDB (Delta T about 7.5 s)
K2 = 0.01720209895**2
d = json.load(open(orb)); f = {k: i for i, k in enumerate(d['fields'])}
A = d['data']
H = np.array([float(r[f['H']]) if r[f['H']] else 99 for r in A]); q = np.array([float(r[f['q']]) for r in A])
with np.errstate(invalid='ignore', divide='ignore'):
    vmin = np.where(q > 1.1, H+5*np.log10(q*(q-0.9837)), -99)
neo = np.array([r[f['class']] in ('ATE', 'APO', 'AMO', 'IEO') for r in A])
keep = np.where((vmin <= 18.0) & (neo if grp == 'neo' else ~neo))[0]
mine = keep[ch::nch]
P = json.load(open(pln))                           # barycentric ecliptic states at EP and Earth at TEND, from Horizons
sim = rebound.Simulation(); sim.G = K2; sim.t = EP
for b in P['bodies']:
    sim.add(m=b['m'], x=b['r'][0], y=b['r'][1], z=b['r'][2], vx=b['v'][0], vy=b['v'][1], vz=b['v'][2])
sim.N_active = sim.N; sim.testparticle_type = 0
for j in mine:
    r = A[j]; e = float(r[f['e']]); qq = float(r[f['q']]); a = qq/(1-e) if e < 1 else None
    M = np.radians(float(r[f['ma']]) if r[f['ma']] else 0.0)
    if a is not None and a > 0: M += np.sqrt(K2/a**3)*(EP-float(r[f['epoch']]))   # two-body shift for the few off-epoch orbits
    hp = rebound.Particle(simulation=sim, primary=sim.particles[0], m=0.0, a=a if a else qq/(1-e), e=e, inc=np.radians(float(r[f['i']])),
                          Omega=np.radians(float(r[f['om']])), omega=np.radians(float(r[f['w']])), M=M)
    sim.add(hp)
sim.integrator = 'mercurius' if grp == 'neo' else 'whfast'; sim.dt = -4.0
sim.integrate(TEND, exact_finish_time=1)
n0 = sim.N_active
xv = np.zeros((sim.N, 6)); sim.serialize_particle_data(xyzvxvyvz=xv); X = xv[n0:]
sunx = xv[0, :3]
E = np.array(P['earth_tend'][:3])
rho = X[:, :3]-E; D = np.linalg.norm(rho, axis=1)
rho = rho-X[:, 3:]*(D/173.1446)[:, None]; D = np.linalg.norm(rho, axis=1)   # light time (c = 173.1446 AU/day)
eps = np.radians(84381.448/3600)
x, y, z = rho[:, 0], rho[:, 1]*np.cos(eps)-rho[:, 2]*np.sin(eps), rho[:, 1]*np.sin(eps)+rho[:, 2]*np.cos(eps)
ra = np.degrees(np.arctan2(y, x)) % 360; de = np.degrees(np.arcsin(z/np.linalg.norm([x, y, z], axis=0)))
cs = np.sin(np.radians(de))*np.sin(np.radians(DE0))+np.cos(np.radians(de))*np.cos(np.radians(DE0))*np.cos(np.radians(ra-RA0))
sep = np.degrees(np.arccos(np.clip(cs, -1, 1)))
rh = np.linalg.norm(X[:, :3]-sunx, axis=1)
V = H[mine]+5*np.log10(rh*D)
np.savez(f'{od}/{grp}{ch:03d}.npz', idx=mine, sep=sep, ra=ra, dec=de, V=V, r=rh, D=D)
print(grp, 'chunk', ch, 'bodies', len(mine), 'kept-total', len(keep), 'within 1 deg', int((sep < 1).sum()), 'within 5 deg', int((sep < 5).sum()))
