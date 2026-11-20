# Near-Earth objects (classes ATE, APO, AMO, IEO) at MA 731's mid-exposure, integrated with ASSIST on JPL DE440 plus the
# sb441-n16 asteroid perturbers (the force model JPL uses for small bodies), one body at a time from its JPL SBDB osculating
# elements back to 1908-12-21 00:58 UT; geocentric astrometric RA/Dec (one light-time step) and separation from the
# MA 731 source. Bodies near the source are then checked with Horizons, topocentric (knownsb.py).
# Usage: python3 -I sbassist.py ORBITS_JSON EPHEM_DIR OUTDIR CHUNK NCHUNK
import sys, json, time, numpy as np, rebound, assist
orb, eph, od, ch, nch = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4]), int(sys.argv[5])
RA0, DE0 = 85.893709844, 16.016634745
EP = 2461200.5
TEND = 2418296.540545 + 7.5/86400
K2 = 0.01720209895**2
eps = np.radians(84381.448/3600); ce, se = np.cos(eps), np.sin(eps)
def ecl2eq(v): return np.array([v[0], v[1]*ce-v[2]*se, v[1]*se+v[2]*ce])
d = json.load(open(orb)); f = {k: i for i, k in enumerate(d['fields'])}; A = d['data']
keep = np.array([i for i, r in enumerate(A) if r[f['class']] in ('ATE', 'APO', 'AMO', 'IEO')])
mine = keep[ch::nch]
ephem = assist.Ephem(f'{eph}/linux_p1550p2650.440', f'{eph}/sb441-n16.bsp')
t0, t1 = EP-ephem.jd_ref, TEND-ephem.jd_ref
sun0 = ephem.get_particle('sun', t0); earth1 = ephem.get_particle('earth', t1); sun1 = ephem.get_particle('sun', t1)
E = np.array(earth1.xyz); S1 = np.array(sun1.xyz)
out = dict(idx=[], ra=[], dec=[], sep=[], r=[], D=[], cpu=[])
for j in mine:
    c0 = time.process_time(); r = A[j]
    e = float(r[f['e']]); qq = float(r[f['q']]); a = qq/(1-e)
    M = np.radians(float(r[f['ma']])) + np.sqrt(K2/abs(a)**3)*(EP-float(r[f['epoch']]))
    hs = rebound.Simulation(); hs.G = K2; hs.add(m=1.0)
    hs.add(primary=hs.particles[0], a=a, e=e, inc=np.radians(float(r[f['i']])), Omega=np.radians(float(r[f['om']])),
           omega=np.radians(float(r[f['w']])), M=M)
    p = hs.particles[1]; x = ecl2eq(p.xyz)+np.array(sun0.xyz); v = ecl2eq(p.vxyz)+np.array(sun0.vxyz)
    sim = rebound.Simulation(); sim.t = t0
    sim.add(x=x[0], y=x[1], z=x[2], vx=v[0], vy=v[1], vz=v[2])
    ex = assist.Extras(sim, ephem); sim.dt = -1.0; sim.ri_ias15.min_dt = 1e-4
    try:
        sim.integrate(t1)
    except Exception:
        continue
    q1 = sim.particles[0]; X = np.array(q1.xyz); Vv = np.array(q1.vxyz)
    rho = X-E; Dd = np.linalg.norm(rho); rho = rho-Vv*Dd/173.1446; Dd = np.linalg.norm(rho)
    ra = np.degrees(np.arctan2(rho[1], rho[0])) % 360; de = np.degrees(np.arcsin(rho[2]/Dd))
    cs = np.sin(np.radians(de))*np.sin(np.radians(DE0))+np.cos(np.radians(de))*np.cos(np.radians(DE0))*np.cos(np.radians(ra-RA0))
    for k, val in (('idx', j), ('ra', ra), ('dec', de), ('sep', np.degrees(np.arccos(min(1, cs)))), ('r', np.linalg.norm(X-S1)), ('D', Dd),
                   ('cpu', time.process_time()-c0)):
        out[k].append(val)
    del ex
np.savez(f'{od}/neo{ch:03d}.npz', **{k: np.array(v) for k, v in out.items()})
c = np.array(out['cpu']); s = np.array(out['sep'])
print('neo chunk', ch, 'bodies', len(mine), 'done', len(c), 'cpu mean %.3f max %.2f s' % (c.mean(), c.max()), 'within 1 deg', int((s < 1).sum()))
