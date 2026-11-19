"""Plate clock from an asteroid trail.

Local cubic astrometry against Gaia DR3 around the asteroid's track, a star mask, then a fit of the
signal along the JPL track (one point per minute) with a blurred boxcar: the fitted shutter opening and
closing give the exposure midpoint. Only pixels within H of the asteroid's track are read; rerun.py records the
distance from that region to Pluto, so the clock uses no pixel near Pluto.
"""
import os
import numpy as np
from astropy.io import fits
from astropy.table import Table
from astropy.wcs import WCS
from scipy import ndimage as nd
from scipy.optimize import least_squares
from scipy.spatial import cKDTree
from scipy.special import erf


def gaia_cone(path, ra, dec, radius, gmax):
    if not os.path.exists(path):
        try:
            from astroquery.gaia import Gaia
            q = f"""SELECT source_id, ra, dec, pmra, pmdec, phot_g_mean_mag FROM gaiadr3.gaia_source
            WHERE 1=CONTAINS(POINT('ICRS',ra,dec), CIRCLE('ICRS',{ra},{dec},{radius})) AND phot_g_mean_mag<{gmax}"""
            Gaia.launch_job_async(q).get_results().write(path, overwrite=True)
        except Exception:  # the ESA archive is down: the same Gaia DR3 columns from VizieR
            from astroquery.vizier import Vizier
            from astropy.coordinates import SkyCoord
            import astropy.units as u
            cols = ['Source', 'RA_ICRS', 'DE_ICRS', 'pmRA', 'pmDE', 'Gmag']
            V = Vizier(columns=cols, column_filters={'Gmag': f'<{gmax}'}, row_limit=-1)
            t = V.query_region(SkyCoord(ra, dec, unit='deg'), radius=radius*u.deg, catalog='I/355/gaiadr3')[0]
            t.rename_columns(cols, ['source_id', 'ra', 'dec', 'pmra', 'pmdec', 'phot_g_mean_mag'])
            t.write(path, overwrite=True)
    return Table.read(path)


def design(u, v, o):
    return np.array([u**i*v**j for i in range(o+1) for j in range(o+1-i)]).T


def fit_trail(scan, hdu, T, era, ede, epoch, gaia_path, H=700):
    """T: minutes from an arbitrary origin; era, ede: the asteroid's topocentric ICRF track (deg)."""
    ra0d, de0d = float(np.median(era)), float(np.median(ede))
    g = gaia_cone(gaia_path, ra0d, de0d, 0.42, 18.5)
    dt = epoch-2016.0
    pmra = np.nan_to_num(np.array(g['pmra'], float)); pmdec = np.nan_to_num(np.array(g['pmdec'], float))
    gde = np.array(g['dec'], float)+pmdec*dt/3.6e6; gra = np.array(g['ra'], float)+pmra*dt/3.6e6/np.cos(np.radians(gde))
    G = np.array(g['phot_g_mean_mag'], float); haspm = ~np.ma.getmaskarray(g['pmra'])
    ra0, de0 = np.radians(ra0d), np.radians(de0d)

    def std(rad, ded):
        a = np.radians(rad); d = np.radians(ded)
        c = np.sin(d)*np.sin(de0)+np.cos(d)*np.cos(de0)*np.cos(a-ra0)
        return (np.degrees(np.cos(d)*np.sin(a-ra0)/c)*3600,
                np.degrees((np.sin(d)*np.cos(de0)-np.cos(d)*np.sin(de0)*np.cos(a-ra0))/c)*3600)
    h = fits.open(scan, memmap=True, do_not_scale_image_data=True); hd = h[hdu].header
    w = WCS(hd, naxis=2)
    xc, yc = w.all_world2pix(ra0d, de0d, 0); xc, yc = int(xc), int(yc)
    NY, NX = (hd['ZNAXIS2'], hd['ZNAXIS1']) if 'ZNAXIS1' in hd else (hd['NAXIS2'], hd['NAXIS1'])
    y0, y1 = max(0, yc-H), min(NY, yc+H); x0, x1 = max(0, xc-H), min(NX, xc+H)
    img = (np.array(h[hdu].section[y0:y1, x0:x1]).astype(np.float64)*hd.get('BSCALE', 1.0)+hd.get('BZERO', 0.0)).astype(np.float32)
    ny, nx = img.shape
    B = 64
    bm = np.median(img[:ny//B*B, :nx//B*B].reshape(ny//B, B, nx//B, B), axis=(1, 3)); bm = nd.median_filter(bm, 3)
    bg = nd.zoom(bm, (ny/bm.shape[0], nx/bm.shape[1]), order=1)
    bg = np.pad(bg, ((0, ny-bg.shape[0]), (0, nx-bg.shape[1])), mode='edge')
    r = img-bg
    sx0, sy0 = w.all_world2pix(gra[G < 13], gde[G < 13], 0); sx0 -= x0; sy0 -= y0
    ok = (sx0 > 5) & (sy0 > 5) & (sx0 < nx-5) & (sy0 < ny-5)
    if np.median(r[sy0[ok].astype(int), sx0[ok].astype(int)]) < 0:
        r = -r
    sm = nd.gaussian_filter(r, 3.0); smad = 1.4826*np.median(np.abs(sm-np.median(sm)))
    pk = (sm == nd.maximum_filter(sm, 15)) & (sm > 5*smad); ys, xs = np.nonzero(pk)
    hw = 7; yy, xx = np.mgrid[-hw:hw+1, -hw:hw+1]; cx = []; cy = []
    for y, x in zip(ys, xs):
        if y < hw or x < hw or y >= ny-hw or x >= nx-hw:
            continue
        st = np.clip(r[y-hw:y+hw+1, x-hw:x+hw+1], 0, None); dx = dy = 0
        for _ in range(2):
            ww = st*np.exp(-((xx-dx)**2+(yy-dy)**2)/32.); s = ww.sum(); dx = (ww*xx).sum()/s; dy = (ww*yy).sum()/s
        cx.append(x+dx); cy.append(y+dy)
    cx = np.array(cx); cy = np.array(cy)
    sra, sde = w.all_pix2world(cx+x0, cy+y0, 0); px, py = std(sra, sde)
    gx, gy = std(gra, gde)
    u = (cx-nx/2)/1000; v = (cy-ny/2)/1000
    br = np.nonzero((G < 16.5) & haspm)[0]; tree = cKDTree(np.c_[gx[br], gy[br]])
    for rad, o in [(40, 1), (20, 2), (6, 3), (4, 3)]:
        dd, k = tree.query(np.c_[px, py], distance_upper_bound=rad); okm = np.isfinite(dd)
        gi = br[k[okm]]; di = np.nonzero(okm)[0]; _, f = np.unique(gi, return_index=True); gi = gi[f]; di = di[f]
        A = design(u[di], v[di], o); a, *_ = np.linalg.lstsq(A, gx[gi], rcond=None); b, *_ = np.linalg.lstsq(A, gy[gi], rcond=None)
        res = np.hypot(A@a-gx[gi], A@b-gy[gi]); kp = res < 3*np.median(res)+0.5
        a, *_ = np.linalg.lstsq(A[kp], gx[gi][kp], rcond=None); b, *_ = np.linalg.lstsq(A[kp], gy[gi][kp], rcond=None)
        Af = design(u, v, o); px, py = Af@a, Af@b
    astro_med = float(np.median(res[kp])); nst = int(kp.sum())

    def sky2pix(xi, eta):
        xi = np.atleast_1d(xi); eta = np.atleast_1d(eta)
        X = np.full(xi.shape, nx/2.); Y = np.full(xi.shape, ny/2.)
        for _ in range(8):
            uu = (X-nx/2)/1000; vv = (Y-ny/2)/1000; D = design(uu, vv, 3)
            fx = D@a-xi; fy = D@b-eta; e = 1e-3
            D2 = design(uu+e/1000, vv, 3); D3 = design(uu, vv+e/1000, 3)
            j11 = (D2@a-D@a)/e; j21 = (D2@b-D@b)/e; j12 = (D3@a-D@a)/e; j22 = (D3@b-D@b)/e
            det = j11*j22-j12*j21
            X -= (j22*fx-j12*fy)/det; Y -= (-j21*fx+j11*fy)/det
        return X, Y
    tx, ty = std(era, ede); TX, TY = sky2pix(tx, ty)
    sx, sy = sky2pix(gx, gy)
    sig = []
    for i in np.nonzero((G > 12.5) & (G < 14.5))[0]:
        X, Y = int(round(sx[i])), int(round(sy[i]))
        if X < 12 or Y < 12 or X >= nx-12 or Y >= ny-12:
            continue
        st = r[Y-10:Y+11, X-10:X+11]; yy2, xx2 = np.mgrid[-10:11, -10:11]; ww = np.clip(st, 0, None)
        if ww.sum() <= 0:
            continue
        mx = (ww*xx2).sum()/ww.sum(); my = (ww*yy2).sum()/ww.sum()
        sig.append(np.sqrt(((ww*((xx2-mx)**2+(yy2-my)**2)).sum()/ww.sum())/2))
    sigma = float(np.median(sig)) if sig else 5.0
    mask = np.zeros_like(r, bool)
    rr = np.where(G < 11, 30, np.where(G < 13, 20, np.where(G < 15, 13, np.where(G < 17, 9, 7))))
    Yg, Xg = np.mgrid[0:ny, 0:nx]
    inb = (sx > -30) & (sy > -30) & (sx < nx+30) & (sy < ny+30)
    for X, Y, R in zip(sx[inb], sy[inb], rr[inb]):
        Xi, Yi = int(X), int(Y); xa, xb = max(0, Xi-R), min(nx, Xi+R+1); ya, yb = max(0, Yi-R), min(ny, Yi+R+1)
        if xa >= xb or ya >= yb:
            continue
        mask[ya:yb, xa:xb] |= ((Xg[ya:yb, xa:xb]-X)**2+(Yg[ya:yb, xa:xb]-Y)**2) <= R*R
    dTX = np.gradient(TX); dTY = np.gradient(TY); L = np.hypot(dTX, dTY); nxv = -dTY/L; nyv = dTX/L
    rate = float(np.median(L))
    rm = np.where(mask, np.nan, r)

    def prof(off):
        cs = np.arange(-1.5*sigma, 1.5*sigma+0.01, 1.0); wt = np.exp(-cs**2/(2*sigma**2))
        S = np.full(len(T), np.nan)
        for i in range(len(T)):
            X = TX[i]+nxv[i]*(off+cs); Y = TY[i]+nyv[i]*(off+cs)
            Xi = np.round(X).astype(int); Yi = np.round(Y).astype(int)
            okp = (Xi >= 0) & (Yi >= 0) & (Xi < nx) & (Yi < ny)
            if okp.sum() < len(cs)*0.6:
                continue
            vals = rm[Yi[okp], Xi[okp]]; ww = wt[okp]; g2 = np.isfinite(vals)
            if g2.sum() < len(cs)*0.5:
                continue
            S[i] = (vals[g2]*ww[g2]).sum()/ww[g2].sum()
        return S
    tau = sigma/rate

    def model(p, t):
        b0, A, t1, t2 = p
        return b0+A*0.5*(erf((t-t1)/(np.sqrt(2)*tau))-erf((t-t2)/(np.sqrt(2)*tau)))
    best = None
    for off in np.arange(-8, 8.1, 1.0):
        S = prof(off); okk = np.isfinite(S)
        t = T[okk]; s = S[okk]
        if okk.sum() < 100:
            continue
        b0 = np.median(s)
        grid = np.arange(t.min(), t.max(), 3.0); bestg = None
        cs = np.concatenate([[0], np.cumsum(s-b0)])
        for i1, t1 in enumerate(grid):
            j1 = np.searchsorted(t, t1)
            j2s = np.searchsorted(t, grid[i1+5:])
            if len(j2s) == 0:
                continue
            n = j2s-j1; m = (cs[j2s]-cs[j1])/np.maximum(n, 1)
            score = m*np.sqrt(np.maximum(n, 1))
            k = np.argmax(score)
            if bestg is None or score[k] > bestg[0]:
                bestg = (score[k], t1, grid[i1+5+k], m[k])
        fit = least_squares(lambda p: model(p, t)-s, [b0, bestg[3], bestg[1], bestg[2]])
        resid = fit.fun; chi = np.sum(resid**2); chi0 = np.sum((s-np.median(s))**2)
        noise = 1.4826*np.median(np.abs(resid-np.median(resid)))
        snr = fit.x[1]/noise*np.sqrt(max((fit.x[3]-fit.x[2]), 1)/1.0)
        if best is None or snr > best['snr']:
            # 1-sigma errors from the fit's covariance, inflated for the correlation of neighbouring minutes
            # (the trail profile spans several samples): factor 1 + 2 * sum of residual autocorrelations
            # up to the first lag where it falls below 0.05
            cov = np.linalg.pinv(fit.jac.T @ fit.jac)*chi/max(len(s)-4, 1)
            rz = resid-resid.mean(); f = 1.0
            for lag in range(1, 120):
                rho = float(np.sum(rz[lag:]*rz[:-lag])/np.sum(rz*rz))
                if rho < 0.05:
                    break
                f += 2*rho
            e_open, e_close = np.sqrt(cov[2, 2]*f), np.sqrt(cov[3, 3]*f)
            e_mid = 0.5*np.sqrt((cov[2, 2]+cov[3, 3]+2*cov[2, 3])*f)
            best = dict(cross_track_px=float(off), t_open=float(fit.x[2]), t_close=float(fit.x[3]),
                        frac_var_explained=float(1-chi/chi0), snr=float(snr), t_open_err=float(e_open),
                        t_close_err=float(e_close), t_mid_err=float(e_mid), correlation_factor=float(f))
    best.update(t_mid=(best['t_open']+best['t_close'])/2, duration_min=best['t_close']-best['t_open'],
                astrometry_stars=nst, astrometry_median_arcsec=astro_med, sigma_px=sigma, rate_px_per_min=rate)
    return best
