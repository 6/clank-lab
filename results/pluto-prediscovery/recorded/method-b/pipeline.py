# One-plate pipeline used for the MA pair and for the positive controls (same code, same parameters).
# Steps: cut ~70' around the prediction; own cubic astrometry against Gaia DR3 at the plate epoch;
# Gaussian matched filter; S/N at the prediction; free centroid (filtered max within 8 px, windowed centroid);
# B from an APASS calibration (quadratic in log peak + colour term, at B-V 0.78);
# single-plate null rates at random positions; injection-recovery at the expected B.
# Usage: python3 -I pipeline.py LABEL SCAN HDU RA DEC RA_OPEN DEC_OPEN RA_CLOSE DEC_CLOSE EPOCH_YR B_EXPECTED WORKDIR
import sys, os, json, numpy as np
from astropy.io import fits
from astropy.wcs import WCS
from astropy.table import Table
from scipy import ndimage as nd
from scipy.spatial import cKDTree

def design(u, v, o=3): return np.array([u**i*v**j for i in range(o+1) for j in range(o+1-i)]).T

class Tangent:
    def __init__(s, ra, dec): s.ra0, s.de0 = np.radians(ra), np.radians(dec)
    def std(s, rad, ded):
        a = np.radians(rad); d = np.radians(ded); ra0, de0 = s.ra0, s.de0
        c = np.sin(d)*np.sin(de0)+np.cos(d)*np.cos(de0)*np.cos(a-ra0)
        return (np.degrees(np.cos(d)*np.sin(a-ra0)/c)*3600,
                np.degrees((np.sin(d)*np.cos(de0)-np.cos(d)*np.sin(de0)*np.cos(a-ra0))/c)*3600)
    def inv(s, xi, eta):
        xi = np.radians(np.asarray(xi)/3600); eta = np.radians(np.asarray(eta)/3600)
        den = np.cos(s.de0)-eta*np.sin(s.de0)
        return (np.degrees(s.ra0+np.arctan2(xi, den)) % 360,
                np.degrees(np.arctan2(np.sin(s.de0)+eta*np.cos(s.de0), np.hypot(xi, den))))

def catalogues(wd, label, ra, dec):
    gf, af = f'{wd}/gaia_{label}.fits', f'{wd}/apass_{label}.fits'
    if not os.path.exists(gf):
        try:
            from astroquery.gaia import Gaia
            q = f"""SELECT source_id, ra, dec, pmra, pmdec, phot_g_mean_mag FROM gaiadr3.gaia_source
            WHERE 1=CONTAINS(POINT('ICRS',ra,dec), CIRCLE('ICRS',{ra},{dec},0.75)) AND phot_g_mean_mag<19.5"""
            Gaia.launch_job_async(q).get_results().write(gf, overwrite=True)
        except Exception:
            from astroquery.vizier import Vizier
            from astropy.coordinates import SkyCoord
            import astropy.units as u
            V = Vizier(columns=['Source', 'RA_ICRS', 'DE_ICRS', 'pmRA', 'pmDE', 'Gmag'], column_filters={'Gmag': '<19.5'}, row_limit=-1)
            V.VIZIER_SERVER = 'vizier.cfa.harvard.edu'
            t = V.query_region(SkyCoord(ra, dec, unit='deg'), radius=0.75*u.deg, catalog='I/355/gaiadr3')[0]
            t.rename_columns(['Source', 'RA_ICRS', 'DE_ICRS', 'pmRA', 'pmDE', 'Gmag'], ['source_id', 'ra', 'dec', 'pmra', 'pmdec', 'phot_g_mean_mag'])
            t.write(gf, overwrite=True)
    if not os.path.exists(af):
        from astroquery.vizier import Vizier
        from astropy.coordinates import SkyCoord
        import astropy.units as u
        V = Vizier(columns=['RAJ2000', 'DEJ2000', 'Bmag', 'e_Bmag', 'Vmag', 'e_Vmag', 'B-V'], row_limit=-1)
        V.VIZIER_SERVER = 'vizier.cfa.harvard.edu'
        V.query_region(SkyCoord(ra, dec, unit='deg'), radius=0.75*u.deg, catalog='II/336/apass9')[0].write(af, overwrite=True)
    return Table.read(gf), Table.read(af)

class Plate:
    """Cut-out, background-subtracted residual image r, own astrometry (cubic, tangent at the prediction)."""
    def __init__(s, label, scan, hdu, ra, dec, epoch, wd, H=2100):
        s.T = Tangent(ra, dec)
        h = fits.open(scan, memmap=True, do_not_scale_image_data=True); hd = h[hdu].header
        w = WCS(hd, naxis=2)
        x, y = w.all_world2pix(ra, dec, 0); x, y = int(round(float(x))), int(round(float(y)))
        d = h[hdu].section; NY, NX = hd['NAXIS2'], hd['NAXIS1']
        if 'ZNAXIS1' in hd: NY, NX = hd['ZNAXIS2'], hd['ZNAXIS1']
        y0, y1 = max(0, y-H), min(NY, y+H); x0, x1 = max(0, x-H), min(NX, x+H)
        img = (np.array(d[y0:y1, x0:x1]).astype(np.float64)*hd.get('BSCALE', 1.0)+hd.get('BZERO', 0.0)).astype(np.float32); ny, nx = img.shape
        s.x0, s.y0, s.nx, s.ny = x0, y0, nx, ny
        B = 64
        bm = np.median(img[:ny//B*B, :nx//B*B].reshape(ny//B, B, nx//B, B), axis=(1, 3)); bm = nd.median_filter(bm, 5)
        bg = nd.zoom(bm, (ny/bm.shape[0], nx/bm.shape[1]), order=1); bg = np.pad(bg, ((0, ny-bg.shape[0]), (0, nx-bg.shape[1])), mode='edge')
        r = img-bg
        g, s.ap = catalogues(wd, label, ra, dec)
        dt = epoch-2016.0
        pmra = np.nan_to_num(np.array(g['pmra'], float)); pmdec = np.nan_to_num(np.array(g['pmdec'], float))
        gde = np.array(g['dec'], float)+pmdec*dt/3.6e6; gra = np.array(g['ra'], float)+pmra*dt/3.6e6/np.cos(np.radians(gde))
        G = np.array(g['phot_g_mean_mag'], float); haspm = ~np.ma.getmaskarray(g['pmra'])
        # sign check: stars must be positive in r (scans may store transmission rather than density)
        sx, sy = w.all_world2pix(gra[G < 13], gde[G < 13], 0); sx -= x0; sy -= y0
        ok = (sx > 5) & (sy > 5) & (sx < nx-5) & (sy < ny-5)
        s.inverted = bool(np.median(r[sy[ok].astype(int), sx[ok].astype(int)]) < 0)
        if s.inverted: r = -r
        s.r = r
        # source extraction (as astrom.py)
        sm = nd.gaussian_filter(r, 3.0); smad = 1.4826*np.median(np.abs(sm-np.median(sm)))
        pk = (sm == nd.maximum_filter(sm, 15)) & (sm > 5*smad); ys, xs = np.nonzero(pk)
        hw = 7; yy, xx = np.mgrid[-hw:hw+1, -hw:hw+1]; cx = []; cy = []
        for yv, xv in zip(ys, xs):
            if yv < hw or xv < hw or yv >= ny-hw or xv >= nx-hw: continue
            st = r[yv-hw:yv+hw+1, xv-hw:xv+hw+1]; wgt = np.clip(st, 0, None)*np.exp(-(xx**2+yy**2)/(2*4.0**2)); sw = wgt.sum()
            if sw <= 0: continue
            dx = (wgt*xx).sum()/sw; dy = (wgt*yy).sum()/sw
            wgt = np.clip(st, 0, None)*np.exp(-((xx-dx)**2+(yy-dy)**2)/(2*4.0**2)); sw = wgt.sum()
            cx.append(xv+(wgt*xx).sum()/sw); cy.append(yv+(wgt*yy).sum()/sw)
        cx = np.array(cx); cy = np.array(cy)
        sra, sde = w.all_pix2world(cx+x0, cy+y0, 0); px, py = s.T.std(sra, sde); gx, gy = s.T.std(gra, gde)
        u = (cx-2100)/2000; v = (cy-2100)/2000
        br = np.nonzero((G < 16.5) & haspm)[0]; tree = cKDTree(np.c_[gx[br], gy[br]])
        for rad, o in [(40, 1), (15, 2), (6, 3), (4, 3), (4, 3)]:
            dd, k = tree.query(np.c_[px, py], distance_upper_bound=rad); okm = np.isfinite(dd)
            gi = br[k[okm]]; di = np.nonzero(okm)[0]; _, f = np.unique(gi, return_index=True); gi = gi[f]; di = di[f]
            A = design(u[di], v[di], o); a, *_ = np.linalg.lstsq(A, gx[gi], rcond=None); b, *_ = np.linalg.lstsq(A, gy[gi], rcond=None)
            res = np.hypot(A@a-gx[gi], A@b-gy[gi]); kp = res < 3*np.median(res)+0.5
            a, *_ = np.linalg.lstsq(A[kp], gx[gi][kp], rcond=None); b, *_ = np.linalg.lstsq(A[kp], gy[gi][kp], rcond=None)
            Af = design(u, v, o); px, py = Af@a, Af@b
        s.a, s.b = a, b
        A = A[kp]; gxk, gyk = gx[gi][kp], gy[gi][kp]
        rng = np.random.default_rng(1); fold = rng.integers(0, 5, len(gxk)); cv = np.zeros(len(gxk))
        for f in range(5):
            tr = fold != f
            aa, *_ = np.linalg.lstsq(A[tr], gxk[tr], rcond=None); bb, *_ = np.linalg.lstsq(A[tr], gyk[tr], rcond=None)
            cv[~tr] = np.hypot(A[~tr]@aa-gxk[~tr], A[~tr]@bb-gyk[~tr])
        near = np.hypot(gxk, gyk) < 600
        s.astrometry = dict(stars=int(kp.sum()), cv_median=float(np.median(cv)), cv_rms=float(np.sqrt(np.mean(cv**2))),
                            near_n=int(near.sum()), near_median=float(np.median(cv[near])) if near.any() else None,
                            inverted=s.inverted)
    def pix2std(s, x, y):
        D = design((np.atleast_1d(x)-2100)/2000, (np.atleast_1d(y)-2100)/2000); return D @ s.a, D @ s.b
    def std2pix(s, xi, eta):
        xi = np.atleast_1d(np.asarray(xi, float)); eta = np.atleast_1d(np.asarray(eta, float))
        X = np.full(xi.shape, 2100.); Y = np.full(xi.shape, 2100.)
        for _ in range(10):
            f1, f2 = s.pix2std(X, Y); e = 0.01
            g1, g2 = s.pix2std(X+e, Y); h1, h2 = s.pix2std(X, Y+e)
            j11 = (g1-f1)/e; j21 = (g2-f2)/e; j12 = (h1-f1)/e; j22 = (h2-f2)/e; det = j11*j22-j12*j21
            dx = xi-f1; dy = eta-f2
            X += (j22*dx-j12*dy)/det; Y += (-j21*dx+j11*dy)/det
        return X, Y
    def sky2pix(s, ra, dec): return s.std2pix(*s.T.std(ra, dec))
    def pix2sky(s, x, y): return s.T.inv(*s.pix2std(x, y))

def measure(P, ra, dec, open_, close_, Bexp, seed=0):
    r = P.r
    px, py = P.sky2pix(ra, dec); px, py = float(px[0]), float(py[0])
    ox, oy = P.sky2pix(*open_); cx_, cy_ = P.sky2pix(*close_)
    ap = P.ap
    ax, ay = P.sky2pix(np.array(ap['RAJ2000'], float), np.array(ap['DEJ2000'], float))
    Bm = np.array(ap['Bmag'], float); BV = np.array(ap['B-V'], float)
    sig = []; yy, xx = np.mgrid[-12:13, -12:13]
    for X, Y, b in zip(ax, ay, Bm):
        if not (14 < b < 16) or X < 20 or Y < 20 or X > P.nx-20 or Y > P.ny-20: continue
        st = np.clip(r[int(Y)-12:int(Y)+13, int(X)-12:int(X)+13], 0, None)
        if st.sum() <= 0: continue
        mx = (st*xx).sum()/st.sum(); my = (st*yy).sum()/st.sum()
        sig.append(np.sqrt((st*((xx-mx)**2+(yy-my)**2)).sum()/st.sum()/2))
    sigma = float(np.median(sig))
    mf = nd.gaussian_filter(r, sigma)
    rng = np.random.default_rng(seed); rx = rng.integers(50, P.nx-50, 20000); ry = rng.integers(50, P.ny-50, 20000)
    v = mf[ry, rx]; base = np.median(v); noise = 1.4826*np.median(np.abs(v-base))
    def snr_at(x, y): return float((nd.map_coordinates(mf, [[y], [x]], order=1)[0]-base)/noise)
    X0, Y0 = int(round(px)), int(round(py)); w = 8
    sub = mf[Y0-w:Y0+w+1, X0-w:X0+w+1]; yy2, xx2 = np.mgrid[-w:w+1, -w:w+1]; inside = (xx2**2+yy2**2) <= w*w
    k = np.argmax(np.where(inside, sub, -1e9)); my_, mx_ = np.unravel_index(k, sub.shape); lx, ly = X0-w+mx_, Y0-w+my_
    hw = 7; yy3, xx3 = np.mgrid[-hw:hw+1, -hw:hw+1]; st = np.clip(r[ly-hw:ly+hw+1, lx-hw:lx+hw+1], 0, None); dx = dy = 0
    for _ in range(3):
        ww = st*np.exp(-((xx3-dx)**2+(yy3-dy)**2)/(2*sigma**2)); dx = (ww*xx3).sum()/ww.sum(); dy = (ww*yy3).sum()/ww.sum()
    fx, fy = lx+dx, ly+dy
    fra, fde = P.pix2sky(fx, fy)
    dxi = (float(fra[0])-ra)*np.cos(np.radians(dec))*3600; deta = (float(fde[0])-dec)*3600
    sel = (Bm > 13) & (Bm < 17.6) & np.isfinite(BV) & (ax > 30) & (ay > 30) & (ax < P.nx-30) & (ay < P.ny-30) & (np.hypot(ax-px, ay-py) < 1500)
    pk = np.array([nd.map_coordinates(mf, [[y], [x]], order=1)[0]-base for x, y in zip(ax[sel], ay[sel])])
    good = pk > 3*noise
    L = np.log10(pk[good]); A = np.c_[np.ones(good.sum()), L, L**2, BV[sel][good]]
    c, *_ = np.linalg.lstsq(A, Bm[sel][good], rcond=None); rs = A@c-Bm[sel][good]; m = np.abs(rs) < 3*1.4826*np.median(np.abs(rs))
    A = A[m]; Bt = Bm[sel][good][m]; c, *_ = np.linalg.lstsq(A, Bt, rcond=None)
    rsd = 1.4826*np.median(np.abs(A@c-Bt))
    def Bof(p, bv=0.78): l = np.log10(p); return float(c[0]+c[1]*l+c[2]*l*l+c[3]*bv)
    grid = np.logspace(np.log10(noise*0.2), np.log10(noise*300), 6000); Lg = np.log10(grid)
    Bg = c[0]+c[1]*Lg+c[2]*Lg*Lg+c[3]*0.78
    Bg = np.where(c[1]+2*c[2]*Lg < 0, Bg, np.inf)   # invert only on the branch where B falls as the peak rises (round five fix)
    pkexp = grid[np.argmin(np.abs(Bg-Bexp))]
    peak_c = nd.map_coordinates(mf, [[fy], [fx]], order=1)[0]-base
    out = dict(pred_pix=[px, py], sigma_px=sigma, snr_at_pred=snr_at(px, py), free_centroid_ra=float(fra[0]), free_centroid_dec=float(fde[0]),
               offset_east=dxi, offset_north=deta, offset=float(np.hypot(dxi, deta)), snr_at_centroid=snr_at(fx, fy),
               B_centroid=Bof(peak_c) if peak_c > 0 else None, calib_n=int(len(Bt)), calib_rms=float(rsd), colour_coeff=float(c[3]),
               snr_expected=float(pkexp/noise), calib=c.tolist(), noise=float(noise), base=float(base))
    return out, mf, (ox, oy, cx_, cy_)

def peaks(P, mf, base, noise, sigma):
    snr = (mf-base)/noise
    pk = (snr == nd.maximum_filter(snr, 9)) & (snr > 2.0); ys, xs = np.nonzero(pk)
    hw = 7; yy, xx = np.mgrid[-hw:hw+1, -hw:hw+1]; C = []
    for y, x in zip(ys, xs):
        if y < hw or x < hw or y >= P.ny-hw or x >= P.nx-hw: C.append((np.nan, np.nan)); continue
        st = np.clip(P.r[y-hw:y+hw+1, x-hw:x+hw+1], 0, None); dx = dy = 0
        for _ in range(3):
            w = st*np.exp(-((xx-dx)**2+(yy-dy)**2)/(2*sigma*sigma)); sw = w.sum()
            if sw <= 0: break
            dx = (w*xx).sum()/sw; dy = (w*yy).sum()/sw
        C.append((x+dx, y+dy))
    C = np.array(C); ok = np.isfinite(C[:, 0])
    xi, eta = P.pix2std(C[ok, 0], C[ok, 1])
    return dict(xi=xi, eta=eta, snr=snr[ys[ok], xs[ok]], peakval=(mf[ys[ok], xs[ok]]-base))

def single_null(P, M, pk, N=200000, seed=42):
    """Fraction of random positions (excluding 30" around the prediction) with a peak as good as the measured one,
    and with S/N>=5 / S/N>=3 within 3"."""
    T = cKDTree(np.c_[pk['xi'], pk['eta']])
    rng = np.random.default_rng(seed); off = rng.uniform(-1500, 1500, (N, 2)); off = off[np.hypot(off[:, 0], off[:, 1]) > 30]
    px, py = P.T.std(M['ra'], M['dec']); pos = np.c_[px+off[:, 0], py+off[:, 1]]
    # keep only positions inside the cut
    X, Y = P.std2pix(pos[:, 0], pos[:, 1]); ins = (X > 60) & (Y > 60) & (X < P.nx-60) & (Y < P.ny-60); pos = pos[ins]
    def frac(rad, smin):
        idx = T.query_ball_point(pos, rad); return float(np.mean([bool(l) and (pk['snr'][l] >= smin).any() for l in idx]))
    return dict(N=int(len(pos)), as_good=frac(max(M['offset'], 0.5), M['snr_at_centroid']), snr5_within3=frac(3.0, 5.0), snr3_within3=frac(3.0, 3.0))

def inject(P, mf, base, noise, sigma, calib, trail, Bs=(15.77, 16.02, 16.27, 16.52, 16.77), n=300, seed=7):
    ox, oy, cx, cy = trail; tvx, tvy = float(cx[0]-ox[0]), float(cy[0]-oy[0])
    c = calib; grid = np.logspace(np.log10(noise*0.2), np.log10(noise*300), 6000); Lg = np.log10(grid)
    Bg = c[0]+c[1]*Lg+c[2]*Lg*Lg+c[3]*0.78
    Bg = np.where(c[1]+2*c[2]*Lg < 0, Bg, np.inf)   # same branch rule as measure()
    rng = np.random.default_rng(seed); out = {}
    for Bt in Bs:
        pkB = grid[np.argmin(np.abs(Bg-Bt))]; r3 = r5 = 0
        for _ in range(n):
            X = rng.uniform(300, P.nx-300); Y = rng.uniform(300, P.ny-300)
            yy, xx = np.mgrid[-25:26, -25:26]; Xi, Yi = int(X), int(Y); fx, fy = X-Xi, Y-Yi
            add = np.zeros_like(xx, float)
            for t in np.linspace(-0.5, 0.5, 15): add += np.exp(-((xx-fx-t*tvx)**2+(yy-fy-t*tvy)**2)/(4*sigma*sigma))
            add *= pkB/15
            sn = (mf[Yi-25:Yi+26, Xi-25:Xi+26]+add-base)/noise; m = sn[22:29, 22:29].max()
            r3 += m >= 3; r5 += m >= 5
        out[str(Bt)] = dict(snr_ge3=r3/n, snr_ge5=r5/n)
    return out

if __name__ == '__main__':
    lab, scan, hdu = sys.argv[1], sys.argv[2], int(sys.argv[3])
    ra, dec, rao, deo, rac, dec_c, ep, Bexp = map(float, sys.argv[4:12]); wd = sys.argv[12]
    P = Plate(lab, scan, hdu, ra, dec, ep, wd)
    M, mf, trail = measure(P, ra, dec, (rao, deo), (rac, dec_c), Bexp)
    M.update(ra=ra, dec=dec)
    pk = peaks(P, mf, M['base'], M['noise'], M['sigma_px'])
    nul = single_null(P, M, pk)
    inj = inject(P, mf, M['base'], M['noise'], M['sigma_px'], M['calib'], trail, Bs=tuple(round(Bexp+d, 2) for d in (-0.5, -0.25, 0, 0.25, 0.5)))
    out = dict(label=lab, astrometry=P.astrometry, measure={k: v for k, v in M.items() if k not in ('calib',)}, null=nul, injection=inj)
    json.dump(out, open(f'{wd}/pipeline_{lab}.json', 'w'), indent=1)
    print(json.dumps(dict(label=lab, astrometry=P.astrometry, snr_pred=round(M['snr_at_pred'], 2), snr_centroid=round(M['snr_at_centroid'], 2),
                          offset=round(M['offset'], 2), B=M['B_centroid'] and round(M['B_centroid'], 2), snr_expected=round(M['snr_expected'], 2),
                          calib_rms=round(M['calib_rms'], 3), null=nul, inj=inj)))
