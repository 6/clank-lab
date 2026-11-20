# Is the MA 731 source a plate defect? Compare its profile with nearby stars of similar significance, stack bright
# stars to look for a second (duplicate) exposure, and render the source beside matched stars.
# Usage: python3 -I defect.py PLATES_DIR WORKDIR OUT_PNG
import sys, os, json, numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from pipeline import Plate, measure, peaks
from scipy.optimize import least_squares
from scipy.spatial import cKDTree
from astropy.table import Table
pd, wd, png = sys.argv[1], sys.argv[2], sys.argv[3]
pr = (85.893540118, 16.016552086)
P = Plate('ma731', f'{pd}/ma00731_mosaic.fits.fz', 1, pr[0], pr[1], 1908.973, wd)
M, mf, _ = measure(P, pr[0], pr[1], (85.894059468, 16.016539111), (85.893020930, 16.016564908), 16.33)
pk = peaks(P, mf, M['base'], M['noise'], M['sigma_px'])
cx, cy = P.sky2pix(M['free_centroid_ra'], M['free_centroid_dec']); cx, cy = float(cx[0]), float(cy[0])
r = P.r
def fit(x, y, h=12):
    X, Y = int(round(x)), int(round(y)); st = r[Y-h:Y+h+1, X-h:X+h+1].astype(float)
    yy, xx = np.mgrid[-h:h+1, -h:h+1]
    def model(p):
        A, x0, y0, sa, sb, th, c = p; ct, s = np.cos(th), np.sin(th)
        u = (xx-x0)*ct+(yy-y0)*s; v = -(xx-x0)*s+(yy-y0)*ct
        return A*np.exp(-0.5*(u**2/sa**2+v**2/sb**2))+c
    p0 = [max(st.max()-np.median(st), 1), x-X, y-Y, 5, 5, 0, np.median(st)]
    f = least_squares(lambda p: (model(p)-st).ravel(), p0, bounds=([0, -6, -6, 1, 1, -np.pi, -np.inf], [np.inf, 6, 6, 20, 20, np.pi, np.inf]))
    A, x0, y0, sa, sb, th, c = f.x
    rr = np.hypot(xx-x0, yy-y0); ap = (st-c)[rr <= 10].sum(); core = (st-c)[rr <= 1.5].mean()
    return dict(fwhm_px=2.3548*np.sqrt(sa*sb), ell=1-min(sa, sb)/max(sa, sb), conc=core/ap if ap > 0 else np.nan, amp=A,
                resid_rms=float(np.std(f.fun))/max(A, 1e-6))
cand = fit(cx, cy)
# comparison stars: S/N 4.5-9, within 600" of the source, isolated (no S/N>2 peak within 15 px), Gaia star within 2"
g = Table.read(f'{wd}/gaia_ma731.fits'); dt = 1908.973-2016
gde = np.array(g['dec'], float)+np.nan_to_num(np.array(g['pmdec'], float))*dt/3.6e6
gra = np.array(g['ra'], float)+np.nan_to_num(np.array(g['pmra'], float))*dt/3.6e6/np.cos(np.radians(gde))
gx, gy = P.T.std(gra, gde); gt = cKDTree(np.c_[gx, gy])
ptree = cKDTree(np.c_[pk['xi'], pk['eta']])
cxi, ceta = P.pix2std(cx, cy)
comp = []
for i in np.nonzero((pk['snr'] >= 4.5) & (pk['snr'] <= 9))[0]:
    if np.hypot(pk['xi'][i]-cxi[0], pk['eta'][i]-ceta[0]) > 600 or np.hypot(pk['xi'][i]-cxi[0], pk['eta'][i]-ceta[0]) < 5: continue
    nb = ptree.query_ball_point([pk['xi'][i], pk['eta'][i]], 15.5)
    if sum(pk['snr'][j] > 2 for j in nb) > 1: continue
    if gt.query([pk['xi'][i], pk['eta'][i]])[0] > 2: continue
    X, Y = P.std2pix(pk['xi'][i], pk['eta'][i])
    try: comp.append(dict(snr=float(pk['snr'][i]), X=float(X[0]), Y=float(Y[0]), **fit(float(X[0]), float(Y[0]))))
    except Exception: pass
def pct(key):
    v = np.array([c[key] for c in comp]); v = v[np.isfinite(v)]
    return dict(source=float(cand[key]), stars_p16_p50_p84=[float(x) for x in np.percentile(v, [16, 50, 84])], source_percentile=float((v < cand[key]).mean()*100), n=int(len(v)))
res = dict(source=dict(snr=M['snr_at_centroid'], **{k: float(v) for k, v in cand.items()}), n_comparison=len(comp),
           fwhm=pct('fwhm_px'), ellipticity=pct('ell'), concentration=pct('conc'), fit_residual=pct('resid_rms'))
# duplicate-exposure search: stack bright isolated stars (G 10.5-12.5), normalised to peak; look for a secondary image
sx, sy = P.sky2pix(gra, gde); G = np.array(g['phot_g_mean_mag'], float); h = 60; stack = []
for i in np.nonzero((G > 10.5) & (G < 12.5))[0]:
    X, Y = int(round(sx[i])), int(round(sy[i]))
    if X < h or Y < h or X >= P.nx-h or Y >= P.ny-h: continue
    if len(gt.query_ball_point([gx[i], gy[i]], 70)) > 1 and (G[gt.query_ball_point([gx[i], gy[i]], 70)] < 15).sum() > 1: continue
    st = r[Y-h:Y+h+1, X-h:X+h+1]; pkv = st[h-2:h+3, h-2:h+3].max()
    if pkv > 0: stack.append(st/pkv)
S = np.median(np.array(stack), axis=0); yy, xx = np.mgrid[-h:h+1, -h:h+1]; rr = np.hypot(xx, yy)
out = S[(rr > 15)]; noise = 1.4826*np.median(np.abs(out-np.median(out)))
k = np.argmax(np.where(rr > 15, S, -9)); ky, kx = np.unravel_index(k, S.shape)
far = rr > 25; out2 = S[far]; n2 = 1.4826*np.median(np.abs(out2-np.median(out2)))
k2 = np.argmax(np.where(far, S, -9)); ky2, kx2 = np.unravel_index(k2, S.shape)
prof = [float(np.median(S[(rr >= a) & (rr < a+5)])) for a in range(0, 60, 5)]
np.save(f'{wd}/star_stack.npy', S)
res['duplicate_exposure_beyond_25px'] = dict(max_rel_peak=float(S[ky2, kx2]), at_offset_px=[int(kx2-h), int(ky2-h)], sigma=float((S[ky2, kx2]-np.median(out2))/n2))
res['stack_radial_profile_5px_bins'] = prof
res['duplicate_exposure'] = dict(n_stars=len(stack), max_secondary_rel_peak=float(S[ky, kx]), at_offset_px=[int(kx-h), int(ky-h)],
                                 stack_noise=float(noise), max_secondary_sigma=float((S[ky, kx]-np.median(out))/noise))
json.dump(res, open(f'{wd}/defect.json', 'w'), indent=1)
print(json.dumps(res, indent=0)[:2500])
# figure: the source and the four comparison stars closest in S/N, same stretch per stamp
import matplotlib; matplotlib.use('Agg'); import matplotlib.pyplot as plt
best = sorted(comp, key=lambda c: abs(c['snr']-M['snr_at_centroid']))[:4]
fig, ax = plt.subplots(1, 5, figsize=(9, 2.2))
for a, (lab, X, Y) in zip(ax, [('MA 731 source', cx, cy)]+[(f"star S/N {c['snr']:.1f}", c['X'], c['Y']) for c in best]):
    st = r[int(Y)-20:int(Y)+21, int(X)-20:int(X)+21]; v = np.percentile(r[int(Y)-60:int(Y)+61, int(X)-60:int(X)+61], [5, 99.7])
    a.imshow(st, origin='lower', cmap='gray_r', vmin=v[0], vmax=v[1]); a.set_xticks([]); a.set_yticks([]); a.set_title(lab, fontsize=7)
fig.suptitle('MA 731 native scan, 41 px (~42") stamps', fontsize=7); plt.tight_layout(); plt.savefig(png, dpi=100)
