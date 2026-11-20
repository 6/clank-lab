# Shape of the MA 731 source on the sky (second moments of the same elliptical-Gaussian fit as defect.py, now keeping
# its orientation), the same for the comparison stars, and what a trail of length L at position angle PA would do to a
# star image: a uniform trail adds L^2/12 to the image's variance along PA (applied to each comparison star in turn).
# Usage: python3 -I srcshape.py PLATES_DIR WORKDIR OUT_JSON [L_arcsec:PA_deg ...]
import sys, os, json, numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from pipeline import Plate, measure, peaks
from scipy.optimize import least_squares
from scipy.spatial import cKDTree
from astropy.table import Table
pd, wd, oj = sys.argv[1], sys.argv[2], sys.argv[3]
trails = [tuple(float(v) for v in a.split(':')) for a in sys.argv[4:]]
pr = (85.893540118, 16.016552086)
P = Plate('ma731', f'{pd}/ma00731_mosaic.fits.fz', 1, pr[0], pr[1], 1908.973, wd)
M, mf, _ = measure(P, pr[0], pr[1], (85.894059468, 16.016539111), (85.893020930, 16.016564908), 16.33)
pk = peaks(P, mf, M['base'], M['noise'], M['sigma_px'])
cx, cy = P.sky2pix(M['free_centroid_ra'], M['free_centroid_dec']); cx, cy = float(cx[0]), float(cy[0])
r = P.r
# pixel -> sky Jacobian at the source (arcsec per pixel; xi east, eta north)
x0, e0 = P.pix2std(cx, cy); x1, e1 = P.pix2std(cx+1, cy); x2, e2 = P.pix2std(cx, cy+1)
J = np.array([[x1[0]-x0[0], x2[0]-x0[0]], [e1[0]-e0[0], e2[0]-e0[0]]])
def fitcov(x, y, h=12):
    X, Y = int(round(x)), int(round(y)); st = r[Y-h:Y+h+1, X-h:X+h+1].astype(float)
    yy, xx = np.mgrid[-h:h+1, -h:h+1]
    def model(p):
        A, x0, y0, sa, sb, th, c = p; ct, s = np.cos(th), np.sin(th)
        u = (xx-x0)*ct+(yy-y0)*s; v = -(xx-x0)*s+(yy-y0)*ct
        return A*np.exp(-0.5*(u**2/sa**2+v**2/sb**2))+c
    p0 = [max(st.max()-np.median(st), 1), x-X, y-Y, 5, 5, 0, np.median(st)]
    f = least_squares(lambda p: (model(p)-st).ravel(), p0, bounds=([0, -6, -6, 1, 1, -np.pi, -np.inf], [np.inf, 6, 6, 20, 20, np.pi, np.inf]))
    A, _, _, sa, sb, th, c = f.x
    R = np.array([[np.cos(th), -np.sin(th)], [np.sin(th), np.cos(th)]])
    Cpix = R @ np.diag([sa**2, sb**2]) @ R.T
    return J @ Cpix @ J.T                                  # sky covariance, arcsec^2
def desc(C):
    w, V = np.linalg.eigh(C); a, b = np.sqrt(w[1]), np.sqrt(w[0]); v = V[:, 1]
    return dict(fwhm_major=2.3548*a, fwhm_minor=2.3548*b, ell=1-b/a, pa_deg=float(np.degrees(np.arctan2(v[0], v[1])) % 180))
Cs = fitcov(cx, cy)
g = Table.read(f'{wd}/gaia_ma731.fits'); dt = 1908.973-2016
gde = np.array(g['dec'], float)+np.nan_to_num(np.array(g['pmdec'], float))*dt/3.6e6
gra = np.array(g['ra'], float)+np.nan_to_num(np.array(g['pmra'], float))*dt/3.6e6/np.cos(np.radians(gde))
gx, gy = P.T.std(gra, gde); gt = cKDTree(np.c_[gx, gy]); ptree = cKDTree(np.c_[pk['xi'], pk['eta']])
cxi, ceta = P.pix2std(cx, cy); comp = []
for i in np.nonzero((pk['snr'] >= 4.5) & (pk['snr'] <= 9))[0]:     # same comparison stars as defect.py
    dd = np.hypot(pk['xi'][i]-cxi[0], pk['eta'][i]-ceta[0])
    if dd > 600 or dd < 5: continue
    if sum(pk['snr'][j] > 2 for j in ptree.query_ball_point([pk['xi'][i], pk['eta'][i]], 15.5)) > 1: continue
    if gt.query([pk['xi'][i], pk['eta'][i]])[0] > 2: continue
    X, Y = P.std2pix(pk['xi'][i], pk['eta'][i])
    try: comp.append(fitcov(float(X[0]), float(Y[0])))
    except Exception: pass
comp = np.array(comp); Cm = np.median(comp, axis=0)
st = [desc(C) for C in comp]
out = dict(source=desc(Cs), median_star=desc(Cm), n_stars=len(comp),
           star_pa_p16_p50_p84=[float(v) for v in np.percentile([s['pa_deg'] for s in st], [16, 50, 84])],
           star_ell_p16_p50_p84=[float(v) for v in np.percentile([s['ell'] for s in st], [16, 50, 84])],
           star_fwhm_major_p16_p50_p84=[float(v) for v in np.percentile([s['fwhm_major'] for s in st], [16, 50, 84])])
out['trails'] = []
for L, pa in trails:
    u = np.array([np.sin(np.radians(pa)), np.cos(np.radians(pa))])
    Ct = Cm+L**2/12*np.outer(u, u)
    per = [desc(C+L**2/12*np.outer(u, u)) for C in comp]       # each comparison star, trailed
    mj = np.array([p['fwhm_major'] for p in per])
    out['trails'].append(dict(L_arcsec=L, pa_deg=pa, predicted_from_median_star=desc(Ct),
                              trailed_stars_fwhm_major_p16_p50_p84=[float(v) for v in np.percentile(mj, [16, 50, 84])],
                              share_of_trailed_stars_with_major_le_source=float((mj <= out['source']['fwhm_major']).mean())))
json.dump(out, open(oj, 'w'), indent=1); print(json.dumps(out, indent=1))
