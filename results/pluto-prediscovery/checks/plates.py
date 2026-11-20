"""One-plate measurement used for every plate (the same code and parameters throughout).

Steps: cut about 70 arcmin around the prediction; own cubic astrometry against Gaia DR3 at the plate
epoch; Gaussian matched filter; S/N at the prediction; free centroid (filtered maximum within 8 px,
then a windowed centroid); B from an APASS calibration (quadratic in log peak plus a colour term,
evaluated at B-V 0.78); single-plate rates at random positions; injection and recovery at the expected B.
"""
import os
import numpy as np
from astropy.io import fits
from astropy.wcs import WCS
from astropy.table import MaskedColumn, Table
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

VIZIER_MIRRORS = ('vizier.cfa.harvard.edu', 'vizier.cfa.harvard.edu', 'vizier.cfa.harvard.edu',
                  'vizier.cfa.harvard.edu', 'vizier.cds.unistra.fr', 'vizier.cds.unistra.fr')

def vizier_table(V, coord, radius, catalog):
    """VizieR cone query that retries an error or an empty answer with backoff (2, 4, 8, ... s),
    trying the CDS mirror last, and fails with a clear message if every attempt comes back empty.
    The CfA mirror has been seen to answer a valid query with an empty result intermittently."""
    import time
    last = 'no answer'
    for i, server in enumerate(VIZIER_MIRRORS):
        if i:
            time.sleep(2**i)
        V.VIZIER_SERVER = server
        try:
            # cache=False: astroquery would otherwise replay a cached empty answer on every retry and later run
            res = V.query_region(coord, radius=radius, catalog=catalog, cache=False)
        except Exception as e:  # a network or service error: retry
            last = f'{type(e).__name__}: {e}'
            continue
        if len(res) and len(res[0]):
            return res[0]
        last = 'an empty result'
    raise RuntimeError(f'VizieR returned {last} for {catalog} within {radius} of {coord.to_string()} '
                       f'after {len(VIZIER_MIRRORS)} attempts; the service may be down, so rerun later')

PINNED = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'data', 'apass')
APASS_SOURCE = {}  # label -> which APASS source the plate used; rerun.py prints it and saves it in results.json

def pinned_apass(label, ra, dec):
    """The pinned APASS DR9 cut for this plate (../data/apass), its SHA-256 verified against pinned.json, with the
    blank values masked as a VizieR download reads them; None if no cut is pinned for this plate or cone."""
    import hashlib, json
    try:
        man = json.load(open(os.path.join(PINNED, 'pinned.json')))
    except FileNotFoundError:
        return None
    c = man['cuts'].get(label)
    if c is None or max(abs(ra-c['ra'])*np.cos(np.radians(dec)), abs(dec-c['dec']))*3600 > 0.1:
        return None
    f = os.path.join(PINNED, c['file'])
    h = hashlib.sha256(open(f, 'rb').read()).hexdigest()
    if h != c['sha256']:
        raise RuntimeError(f'pinned APASS cut {c["file"]} has SHA-256 {h}, not {c["sha256"]} as data/apass/pinned.json records')
    t = Table.read(f, format='ascii.ecsv')
    for k in t.colnames:
        if np.isnan(np.asarray(t[k], float)).any():
            t[k] = MaskedColumn(t[k], mask=np.isnan(np.asarray(t[k], float)))
    if len(t) != c['rows']:
        raise RuntimeError(f'pinned APASS cut {c["file"]} has {len(t)} rows, not {c["rows"]}')
    return t, c

def same_apass(a, b):
    """Whether two APASS cuts hold the same stars and values in the same order (blanks compared as blanks)."""
    if len(a) != len(b) or list(a.colnames) != list(b.colnames):
        return False
    return all(np.array_equal(np.ma.filled(np.ma.asarray(a[k], float), np.nan), np.ma.filled(np.ma.asarray(b[k], float), np.nan),
                              equal_nan=True) for k in a.colnames)

def apass(af, label, ra, dec):
    """APASS DR9 within 0.75 deg: the live VizieR query first (or this run's earlier download in WORK), checked
    against the pinned cut; the pinned cut, its hash verified, when VizieR fails after its retries."""
    pin = pinned_apass(label, ra, dec)
    if os.path.exists(af):
        t, how = Table.read(af), f'the download in the work directory ({os.path.basename(af)})'
    else:
        from astroquery.vizier import Vizier
        from astropy.coordinates import SkyCoord
        import astropy.units as u
        V = Vizier(columns=['RAJ2000', 'DEJ2000', 'Bmag', 'e_Bmag', 'Vmag', 'e_Vmag', 'B-V'], row_limit=-1)
        if os.environ.get('PLUTO_FORCE_VIZIER_FAILURE'):  # a test of the fallback: behave as if VizieR were down
            V.VIZIER_SERVER = 'vizier.invalid'
            def fail(*a, **k): raise ConnectionError('VizieR forced to fail (PLUTO_FORCE_VIZIER_FAILURE)')
            V.query_region = fail
        try:
            vizier_table(V, SkyCoord(ra, dec, unit='deg'), 0.75*u.deg, 'II/336/apass9').write(af, overwrite=True)
        except RuntimeError as e:
            if pin is None:
                raise
            t, c = pin
            APASS_SOURCE[label] = f'pinned cut data/apass/{c["file"]} (SHA-256 verified, {len(t)} stars), because {e}'
            print(f'APASS for {label}: {APASS_SOURCE[label]}', flush=True)
            return t
        t, how = Table.read(af), 'a live VizieR query'
    if pin is None:
        APASS_SOURCE[label] = f'{how} ({len(t)} stars); no pinned cut to compare'
    elif same_apass(t, pin[0]):
        APASS_SOURCE[label] = f'{how} ({len(t)} stars), identical to the pinned cut data/apass/{pin[1]["file"]}'
    else:
        raise RuntimeError(f'APASS for {label} from {how} ({len(t)} stars) differs from the pinned cut data/apass/{pin[1]["file"]} '
                           f'({len(pin[0])} stars): the catalog or the query has changed, so the recorded values may no longer hold')
    print(f'APASS for {label}: {APASS_SOURCE[label]}', flush=True)
    return t

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
            t = vizier_table(V, SkyCoord(ra, dec, unit='deg'), 0.75*u.deg, 'I/355/gaiadr3')
            t.rename_columns(['Source', 'RA_ICRS', 'DE_ICRS', 'pmRA', 'pmDE', 'Gmag'], ['source_id', 'ra', 'dec', 'pmra', 'pmdec', 'phot_g_mean_mag'])
            t.write(gf, overwrite=True)
    return Table.read(gf), apass(af, label, ra, dec)

class Plate:
    """Cut-out, background-subtracted residual image r, own astrometry (cubic, tangent at the prediction)."""
    def __init__(s, label, scan, hdu, ra, dec, epoch, wd, H=2100):
        s.label = label; s.T = Tangent(ra, dec)
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
        s.gaia = (gra, gde, G)  # Gaia DR3 (G < 19.5) moved to the plate epoch
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
        s._match_in = (px, py, u, v, gx, gy, np.nonzero((G < 16.5) & haspm)[0])
        a, b, A, gi, kp, fs = s._solve(())
        s.a, s.b = a, b
        s.fit_set = fs  # the stars of the final fit
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
    def _solve(s, exclude):
        """The plate solution: iterative matching of extracted sources to Gaia DR3 (G < 16.5, with proper motions, moved
        to the plate epoch), starting from the archive WCS, with polynomial order 1, 2, 3, 3, 3 and match radii 40, 15,
        6, 4, 4 arcsec, each step clipped at 3 x median residual + 0.5 arcsec. Gaia stars whose indices are in exclude
        take no part in any step (matching, clipping or fitting)."""
        px, py, u, v, gx, gy, br = s._match_in
        br = br[~np.isin(br, np.asarray(list(exclude), int))]; tree = cKDTree(np.c_[gx[br], gy[br]])
        for rad, o in [(40, 1), (15, 2), (6, 3), (4, 3), (4, 3)]:
            dd, k = tree.query(np.c_[px, py], distance_upper_bound=rad); okm = np.isfinite(dd)
            gi = br[k[okm]]; di = np.nonzero(okm)[0]; _, f = np.unique(gi, return_index=True); gi = gi[f]; di = di[f]
            A = design(u[di], v[di], o); a, *_ = np.linalg.lstsq(A, gx[gi], rcond=None); b, *_ = np.linalg.lstsq(A, gy[gi], rcond=None)
            res = np.hypot(A@a-gx[gi], A@b-gy[gi]); kp = res < 3*np.median(res)+0.5
            a, *_ = np.linalg.lstsq(A[kp], gx[gi][kp], rcond=None); b, *_ = np.linalg.lstsq(A[kp], gy[gi][kp], rcond=None)
            Af = design(u, v, o); px, py = Af@a, Af@b
        return a, b, A, gi, kp, dict(u=u[di][kp], v=v[di][kp], gaia=gi[kp])
    def refit(s, exclude):
        """The whole plate solution again (matching, clipping and fitting) with the Gaia stars in exclude left out."""
        a, b, A, gi, kp, fs = s._solve(exclude)
        return a, b, int(kp.sum())
    def pix2std(s, x, y, ab=None):
        a, b = (s.a, s.b) if ab is None else ab
        D = design((np.atleast_1d(x)-2100)/2000, (np.atleast_1d(y)-2100)/2000); return D @ a, D @ b
    def std2pix(s, xi, eta, ab=None):
        xi = np.atleast_1d(np.asarray(xi, float)); eta = np.atleast_1d(np.asarray(eta, float))
        X = np.full(xi.shape, 2100.); Y = np.full(xi.shape, 2100.)
        for _ in range(10):
            f1, f2 = s.pix2std(X, Y, ab); e = 0.01
            g1, g2 = s.pix2std(X+e, Y, ab); h1, h2 = s.pix2std(X, Y+e, ab)
            j11 = (g1-f1)/e; j21 = (g2-f2)/e; j12 = (h1-f1)/e; j22 = (h2-f2)/e; det = j11*j22-j12*j21
            dx = xi-f1; dy = eta-f2
            X += (j22*dx-j12*dy)/det; Y += (-j21*dx+j11*dy)/det
        return X, Y
    def sky2pix(s, ra, dec): return s.std2pix(*s.T.std(ra, dec))
    def pix2sky(s, x, y): return s.T.inv(*s.pix2std(x, y))

def mono(Bg):
    """Keep only the branch of the quadratic magnitude calibration on which B falls as the peak grows,
    connected to the bright end (a quadratic can turn over below the faintest calibration stars)."""
    d = np.diff(Bg, append=Bg[-1]-1); ok = d < 0; k = len(ok)-1
    while k > 0 and ok[k-1]: k -= 1
    m = np.zeros_like(ok); m[k:] = True; return m

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
    c, rsd, ncal = calibrate(mf, base, noise, ax, ay, Bm, BV, px, py, P.nx, P.ny)
    def Bof(p, bv=0.78): l = np.log10(p); return float(c[0]+c[1]*l+c[2]*l*l+c[3]*bv)
    grid = np.logspace(np.log10(noise*0.2), np.log10(noise*300), 6000); Lg = np.log10(grid)
    Bg = c[0]+c[1]*Lg+c[2]*Lg*Lg+c[3]*0.78
    pkexp = grid[np.argmin(np.abs(Bg-Bexp)+1e9*~mono(Bg))]
    peak_c = nd.map_coordinates(mf, [[fy], [fx]], order=1)[0]-base
    out = dict(pred_pix=[px, py], sigma_px=sigma, snr_at_pred=snr_at(px, py), free_centroid_ra=float(fra[0]), free_centroid_dec=float(fde[0]),
               offset_east=dxi, offset_north=deta, offset=float(np.hypot(dxi, deta)), snr_at_centroid=snr_at(fx, fy),
               B_centroid=Bof(peak_c) if peak_c > 0 else None, calib_n=ncal, calib_rms=float(rsd), colour_coeff=float(c[3]),
               snr_expected=float(pkexp/noise), calib=c.tolist(), noise=float(noise), base=float(base))
    return out, mf, (ox, oy, cx_, cy_)

def calibrate(mf, base, noise, ax, ay, Bm, BV, px, py, nx, ny, exclude=None):
    """B calibration on APASS stars of the plate (13 < B < 17.6, within 1500 px): quadratic in log filtered peak plus a
    colour term, one 3-sigma clip. exclude: APASS rows left out (the held-out validation stars)."""
    sel = (Bm > 13) & (Bm < 17.6) & np.isfinite(BV) & (ax > 30) & (ay > 30) & (ax < nx-30) & (ay < ny-30) & (np.hypot(ax-px, ay-py) < 1500)
    if exclude is not None:
        sel[np.asarray(list(exclude), int)] = False
    pk = np.array([nd.map_coordinates(mf, [[y], [x]], order=1)[0]-base for x, y in zip(ax[sel], ay[sel])])
    good = pk > 3*noise
    L = np.log10(pk[good]); A = np.c_[np.ones(good.sum()), L, L**2, BV[sel][good]]
    c, *_ = np.linalg.lstsq(A, Bm[sel][good], rcond=None); rs = A@c-Bm[sel][good]; m = np.abs(rs) < 3*1.4826*np.median(np.abs(rs))
    A = A[m]; Bt = Bm[sel][good][m]; c, *_ = np.linalg.lstsq(A, Bt, rcond=None)
    return c, 1.4826*np.median(np.abs(A@c-Bt)), int(len(Bt))

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

def inject(P, mf, base, noise, sigma, calib, trail, Bs=(15.77, 16.02, 16.27, 16.52, 16.77), n=300, seed=7):
    ox, oy, cx, cy = trail; tvx, tvy = float(cx[0]-ox[0]), float(cy[0]-oy[0])
    c = calib; grid = np.logspace(np.log10(noise*0.2), np.log10(noise*300), 6000); Lg = np.log10(grid)
    Bg = c[0]+c[1]*Lg+c[2]*Lg*Lg+c[3]*0.78
    rng = np.random.default_rng(seed); out = {}
    for Bt in Bs:
        pkB = grid[np.argmin(np.abs(Bg-Bt)+1e9*~mono(Bg))]; r3 = r5 = 0
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


def free_centroid(P, mf, px, py, sigma, w=8):
    """The measurement's own centroid rule: the filtered maximum within w pixels of the rounded predicted pixel, then
    a Gaussian-weighted centroid (weights from the unfiltered scan, clipped at zero) in the 15 x 15 pixel box around
    that maximum, three iterations. The final centroid is not constrained: it can lie up to about 7 pixels beyond
    the w-pixel circle."""
    return centroid_arrays(P.r, mf, px, py, sigma, w)


def centroid_arrays(r, mf, px, py, sigma, w=8):
    X0, Y0 = int(round(px)), int(round(py))
    sub = mf[Y0-w:Y0+w+1, X0-w:X0+w+1]; yy2, xx2 = np.mgrid[-w:w+1, -w:w+1]; inside = (xx2**2+yy2**2) <= w*w
    k = np.argmax(np.where(inside, sub, -1e9)); my_, mx_ = np.unravel_index(k, sub.shape); lx, ly = X0-w+mx_, Y0-w+my_
    hw = 7; yy3, xx3 = np.mgrid[-hw:hw+1, -hw:hw+1]; st = np.clip(r[ly-hw:ly+hw+1, lx-hw:lx+hw+1], 0, None); dx = dy = 0
    for _ in range(3):
        ww = st*np.exp(-((xx3-dx)**2+(yy3-dy)**2)/(2*sigma**2)); sw = ww.sum()
        if sw <= 0: break
        dx = (ww*xx3).sum()/sw; dy = (ww*yy3).sum()/sw
    return lx+dx, ly+dy


def faint_stars(P, mf, M, Bexp, half_width=0.5, radius_px=1500, isolation=15.0):
    """Comparably faint catalog stars measured exactly as the image is: APASS stars with B within half_width of
    Pluto's predicted B, within radius_px of the prediction, with a Gaia DR3 counterpart within 2" (whose position,
    moved to the plate epoch, is the truth) and no other Gaia star within isolation arcsec. For each: the centroid
    offset from Gaia, the S/N and the calibrated B minus the APASS B."""
    gra, gde, G = P.gaia; gx, gy = P.T.std(gra, gde); gt = cKDTree(np.c_[gx, gy])
    ap = P.ap; ara = np.array(ap['RAJ2000'], float); ade = np.array(ap['DEJ2000'], float)
    Bm = np.array(ap['Bmag'], float); BV = np.array(ap['B-V'], float)
    ax, ay = P.T.std(ara, ade); c = M['calib']; px0, py0 = M['pred_pix']
    off, snr, dB = [], [], []
    for xi, eta, b, bv in zip(ax, ay, Bm, BV):
        if not (abs(b-Bexp) <= half_width) or not np.isfinite(bv):
            continue
        near = gt.query_ball_point([xi, eta], isolation)
        if not near:
            continue
        d = np.hypot(gx[near]-xi, gy[near]-eta); j = near[int(np.argmin(d))]
        if d.min() > 2.0 or len(near) > 1:
            continue
        X, Y = P.std2pix(gx[j], gy[j]); X, Y = float(np.atleast_1d(X)[0]), float(np.atleast_1d(Y)[0])
        if np.hypot(X-px0, Y-py0) > radius_px or np.hypot(X-px0, Y-py0) < 60 or X < 60 or Y < 60 or X > P.nx-60 or Y > P.ny-60:
            continue
        fx, fy = free_centroid(P, mf, X, Y, M['sigma_px'])
        fxi, feta = P.pix2std(fx, fy); fxi, feta = float(np.atleast_1d(fxi)[0]), float(np.atleast_1d(feta)[0])
        off.append(float(np.hypot(fxi-gx[j], feta-gy[j])))
        pk = nd.map_coordinates(mf, [[fy], [fx]], order=1)[0]-M['base']; snr.append(float(pk/M['noise']))
        if pk > 0:
            l = np.log10(pk); dB.append(float(c[0]+c[1]*l+c[2]*l*l+c[3]*bv-b))
    off = np.array(off); snr = np.array(snr); dB = np.array(dB)
    out = dict(n=int(len(off)))
    if len(off):
        out.update(offset_median=float(np.median(off)), offset_p68=float(np.percentile(off, 68)), offset_p90=float(np.percentile(off, 90)),
                   image_offset_rank=float(np.mean(off <= M['offset'])), snr_median=float(np.median(snr)),
                   frac_snr_ge4=float(np.mean(snr >= 4)))
    if len(dB) > 2:
        out.update(dB_median=float(np.median(dB)), dB_robust_sd=float(1.4826*np.median(np.abs(dB-np.median(dB)))),
                   dB_p16=float(np.percentile(dB, 16)), dB_p84=float(np.percentile(dB, 84)))
    return out


def replay(P, mf, M, xi, eta, prefilter_snr, gaia_veto=3.0):
    """The measurement's own statistic at arbitrary predicted positions (tangent-plane arcsec): the brightest
    filtered pixel within 8 pixels of the rounded predicted pixel, the windowed centroid around it, the S/N
    interpolated at that centroid and the centroid's distance from the predicted position; plus whether a
    Gaia DR3 star (G < 19.5, moved to the plate epoch) lies within gaia_veto arcsec of the centroid.
    Positions whose 33 x 33 pixel neighbourhood never reaches prefilter_snr are skipped (returned as S/N -inf).
    That cannot drop a qualifying event: the brightest pixel lies within 8 pixels, the windowed centroid within
    7 more, and the interpolated S/N there cannot exceed the largest of its four neighbouring pixels.
    Also returns the centroid's distance from the predicted pixel (offpx), for the final 8-pixel constraint."""
    base, noise = M['base'], M['noise']
    dm = nd.maximum_filter(mf, size=33)
    X, Y = P.std2pix(np.asarray(xi, float), np.asarray(eta, float))
    Xi = np.round(X).astype(int); Yi = np.round(Y).astype(int)
    ok = (Xi > 20) & (Yi > 20) & (Xi < P.nx-20) & (Yi < P.ny-20)
    snr = np.full(len(X), -np.inf); off = np.full(len(X), np.inf); cat = np.zeros(len(X), bool); offpx = np.full(len(X), np.inf)
    cand = np.nonzero(ok)[0]
    cand = cand[(dm[Yi[cand], Xi[cand]]-base)/noise >= prefilter_snr]
    gra, gde, G = P.gaia; gt = cKDTree(np.c_[P.T.std(gra, gde)])
    for i in cand:
        fx, fy = free_centroid(P, mf, float(X[i]), float(Y[i]), M['sigma_px'])
        snr[i] = (nd.map_coordinates(mf, [[fy], [fx]], order=1)[0]-base)/noise
        fxi, feta = P.pix2std(fx, fy); fxi, feta = float(np.ravel(fxi)[0]), float(np.ravel(feta)[0])
        off[i] = float(np.hypot(fxi-xi[i], feta-eta[i])); offpx[i] = float(np.hypot(fx-X[i], fy-Y[i]))
        cat[i] = bool(gt.query_ball_point([fxi, feta], gaia_veto))
    return snr, off, cat, offpx


def validation_stars(P, M, Bexp, half_width=0.5, radius_px=1500, isolation=15.0):
    """The faint_stars selection, returned as (APASS row, Gaia index) pairs: APASS stars with B within half_width of
    Pluto's predicted B and a finite B-V, a Gaia DR3 counterpart within 2" and no other Gaia star within isolation
    arcsec, 60 to radius_px pixels from the prediction and 60 pixels inside the cut-out."""
    gra, gde, G = P.gaia; gx, gy = P.T.std(gra, gde); gt = cKDTree(np.c_[gx, gy])
    ap = P.ap; ax, ay = P.T.std(np.array(ap['RAJ2000'], float), np.array(ap['DEJ2000'], float))
    Bm = np.array(ap['Bmag'], float); BV = np.array(ap['B-V'], float); px0, py0 = M['pred_pix']; out = []
    for i, (xi, eta, b, bv) in enumerate(zip(ax, ay, Bm, BV)):
        if not (abs(b-Bexp) <= half_width) or not np.isfinite(bv):
            continue
        near = gt.query_ball_point([xi, eta], isolation)
        if len(near) != 1 or np.hypot(gx[near[0]]-xi, gy[near[0]]-eta) > 2.0:
            continue
        X, Y = P.std2pix(gx[near[0]], gy[near[0]]); X, Y = float(np.ravel(X)[0]), float(np.ravel(Y)[0])
        if not (60 <= np.hypot(X-px0, Y-py0) <= radius_px) or X < 60 or Y < 60 or X > P.nx-60 or Y > P.ny-60:
            continue
        out.append((i, near[0]))
    return out


def heldout(P, mf, M, Bexp, folds=5, seed=2026):
    """Held-out validation. The faint validation stars (validation_stars) are split at random into folds. For each
    fold the cubic astrometric solution is solved again (P.refit) with that fold's Gaia stars removed before any
    matching, clipping or fitting, and the B calibration is refitted without its APASS stars; the fold's stars are then measured exactly as the image is (free_centroid, S/N and B at the
    centroid), so no star is measured with a solution or calibration it helped to fit. Returns the 2-D positional
    residuals (east, north: median and robust spread), the radial misses, the photometric bias and scatter, and the
    image's percentile among the radial misses."""
    stars = validation_stars(P, M, Bexp)
    rng = np.random.default_rng(seed); fold = rng.integers(0, folds, len(stars))
    gra, gde, G = P.gaia; gx, gy = P.T.std(gra, gde)
    ap = P.ap; Bm = np.array(ap['Bmag'], float); BV = np.array(ap['B-V'], float)
    px, py = M['pred_pix']; base, noise = M['base'], M['noise']
    rows = []; nfit = []
    for f in range(folds):
        mine = [stars[k] for k in np.nonzero(fold == f)[0]]
        if not mine:
            continue
        a, b, n = P.refit({j for _, j in mine}); nfit.append(n)
        ax, ay = P.std2pix(*P.T.std(np.array(ap['RAJ2000'], float), np.array(ap['DEJ2000'], float)), ab=(a, b))
        c, _, ncal = calibrate(mf, base, noise, ax, ay, Bm, BV, px, py, P.nx, P.ny, exclude={i for i, _ in mine})
        for i, j in mine:
            X, Y = P.std2pix(gx[j], gy[j], ab=(a, b)); X, Y = float(np.ravel(X)[0]), float(np.ravel(Y)[0])
            fx, fy = free_centroid(P, mf, X, Y, M['sigma_px'])
            fxi, feta = P.pix2std(fx, fy, ab=(a, b)); fxi, feta = float(np.ravel(fxi)[0]), float(np.ravel(feta)[0])
            pk = nd.map_coordinates(mf, [[fy], [fx]], order=1)[0]-base
            dB = float(c[0]+c[1]*np.log10(pk)+c[2]*np.log10(pk)**2+c[3]*BV[i]-Bm[i]) if pk > 0 else np.nan
            dB78 = float(c[0]+c[1]*np.log10(pk)+c[2]*np.log10(pk)**2+c[3]*0.78-Bm[i]) if pk > 0 else np.nan  # as the image
            rows.append((fxi-gx[j], feta-gy[j], float(pk/noise), dB, f, dB78))
    R = np.array(rows, float); de, dn, sn, dB = R[:, 0], R[:, 1], R[:, 2], R[:, 3]; rad = np.hypot(de, dn)
    rsd = lambda x: float(1.4826*np.median(np.abs(x-np.median(x))))
    ok = np.isfinite(dB)
    return dict(n=int(len(R)), folds=folds, astrometric_stars_per_fit=[int(min(nfit)), int(max(nfit))],
                east_median=float(np.median(de)), north_median=float(np.median(dn)), east_robust_sd=rsd(de), north_robust_sd=rsd(dn),
                east_rms=float(np.sqrt(np.mean(de**2))), north_rms=float(np.sqrt(np.mean(dn**2))),
                radial_median=float(np.median(rad)), radial_p68=float(np.percentile(rad, 68)), radial_p90=float(np.percentile(rad, 90)),
                image_offset_rank=float(np.mean(rad <= M['offset'])), snr_median=float(np.median(sn)),
                n_B=int(ok.sum()), dB_median=float(np.median(dB[ok])), dB_robust_sd=rsd(dB[ok]),
                dB_p16=float(np.percentile(dB[ok], 16)), dB_p84=float(np.percentile(dB[ok], 84)),
                dB_colour_078_median=float(np.median(R[ok, 5])), dB_colour_078_robust_sd=rsd(R[ok, 5]))


def inject_pipeline(P, mf, M, trail, Bs, n=200, seed=11, snr_min=4.0, max_offset=6.0, max_dB=0.45, half=60):
    """Injection and recovery through the measurement itself. Each artificial source is a trailed Gaussian with the
    plate's stellar width, added to the background-subtracted, unfiltered scan (P.r) at a random position at least
    300 pixels inside the cut-out, with the amplitude the B calibration assigns to the injected B. The scan is then
    filtered again around it (the Gaussian filter is linear, so filtering a 2*half+1 pixel box of scan plus source
    equals the full filtered scan there), and the unchanged measurement runs at the injected position: filtered
    maximum within 8 pixels, windowed centroid, S/N and B at the centroid. A source is recovered when S/N >= snr_min,
    the centroid lies within max_offset arcsec of the injected position and |B - injected B| <= max_dB. The same
    positions measured without the source give the rate at which the rule passes on the bare scan. The background
    and the noise scale are not re-estimated; one source changes neither measurably."""
    ox, oy, cx, cy = trail; tvx, tvy = float(cx[0]-ox[0]), float(cy[0]-oy[0]); sigma = M['sigma_px']
    c = M['calib']; base, noise = M['base'], M['noise']
    grid = np.logspace(np.log10(noise*0.2), np.log10(noise*300), 6000); Lg = np.log10(grid)
    Bg = c[0]+c[1]*Lg+c[2]*Lg*Lg+c[3]*0.78
    def Bof(p): l = np.log10(p); return float(c[0]+c[1]*l+c[2]*l*l+c[3]*0.78)
    rng = np.random.default_rng(seed); yy, xx = np.mgrid[-half:half+1, -half:half+1]; out = {}
    pos = [(rng.uniform(300, P.nx-300), rng.uniform(300, P.ny-300)) for _ in range(n)]
    def run(rs, ms, X, Y, Xi, Yi):
        fx, fy = centroid_arrays(rs, ms, half+(X-Xi), half+(Y-Yi), sigma)
        pk = nd.map_coordinates(ms, [[fy], [fx]], order=1)[0]-base
        gx, gy = P.pix2std(Xi-half+fx, Yi-half+fy); tx, ty = P.pix2std(X, Y)
        return float(pk/noise), float(np.hypot(float(gx[0]-tx[0]), float(gy[0]-ty[0]))), (Bof(pk) if pk > 0 else np.inf)
    # forced S/N at the nominal position, read with a random registration error (1 arcsec rms per axis, about the
    # held-out stars' robust spread), as a fixed-position measurement would be
    e1 = P.pix2std(np.array([2100., 2101.]), np.array([2100., 2100.])); scale = float(np.hypot(e1[0][1]-e1[0][0], e1[1][1]-e1[1][0]))
    reg = np.random.default_rng(seed+1).normal(0, 1.0/scale, (n, 2))
    def forced(ms, X, Y, Xi, Yi, d): return float((nd.map_coordinates(ms, [[half+Y-Yi+d[1]], [half+X-Xi+d[0]]], order=1)[0]-base)/noise)
    bare = []; bare_forced = []
    for (X, Y), d in zip(pos, reg):
        Xi, Yi = int(X), int(Y); bare_forced.append(forced(mf[Yi-half:Yi+half+1, Xi-half:Xi+half+1], X, Y, Xi, Yi, d))
    for X, Y in pos:
        Xi, Yi = int(X), int(Y)
        bare.append(run(P.r[Yi-half:Yi+half+1, Xi-half:Xi+half+1], mf[Yi-half:Yi+half+1, Xi-half:Xi+half+1], X, Y, Xi, Yi))
    for Bt in Bs:
        pkB = grid[np.argmin(np.abs(Bg-Bt)+1e9*~mono(Bg))]; res = []; fs = []
        for (X, Y), d in zip(pos, reg):
            Xi, Yi = int(X), int(Y); fx, fy = X-Xi, Y-Yi; add = np.zeros_like(xx, float)
            for t in np.linspace(-0.5, 0.5, 15):
                add += np.exp(-((xx-fx-t*tvx)**2+(yy-fy-t*tvy)**2)/(2*sigma*sigma))
            add *= 2*pkB/15  # a Gaussian of width sigma filtered by one of width sigma keeps half its peak
            rs = P.r[Yi-half:Yi+half+1, Xi-half:Xi+half+1]+add
            ms = mf[Yi-half:Yi+half+1, Xi-half:Xi+half+1]+nd.gaussian_filter(add, sigma)
            res.append(run(rs, ms, X, Y, Xi, Yi)); fs.append(forced(ms, X, Y, Xi, Yi, d))
        fs = np.array(fs)
        sn, of, bb = (np.array(v) for v in zip(*res))
        rec = (sn >= snr_min) & (of <= max_offset) & (np.abs(bb-Bt) <= max_dB)
        out[str(Bt)] = dict(recovered=float(rec.mean()), snr_ge_min=float(np.mean(sn >= snr_min)),
                            within_offset=float(np.mean(of <= max_offset)), within_dB=float(np.mean(np.abs(bb-Bt) <= max_dB)),
                            median_offset=float(np.median(of)), median_dB=float(np.median(bb[np.isfinite(bb)]-Bt)) if np.isfinite(bb).any() else None,
                            forced_snr_median=float(np.median(fs)), forced_snr_p10=float(np.percentile(fs, 10)),
                            forced_snr_ge2=float(np.mean(fs >= 2)), forced_snr_ge3=float(np.mean(fs >= 3)))
    sn, of, bb = (np.array(v) for v in zip(*bare))
    out['bare'] = dict(passes_snr=float(np.mean(sn >= snr_min)),
                       passes_rule_at_any_B=float(np.mean((sn >= snr_min) & (of <= max_offset))),
                       forced_snr_median=float(np.median(bare_forced)), forced_snr_p90=float(np.percentile(bare_forced, 90)),
                       forced_snr_ge2=float(np.mean(np.array(bare_forced) >= 2)))
    out['registration_error_arcsec_rms_per_axis'] = 1.0
    out['rule'] = dict(n=n, snr_min=snr_min, max_offset_arcsec=max_offset, max_dB=max_dB)
    return out
