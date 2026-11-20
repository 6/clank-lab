# Is the MA 731 source a fixed object? Measure its sky position on every DASCH plate of comparable depth.
# For each plate: DASCH cutout (835 x 835, 1.44"/px, resampled by DASCH) at the MA 731 centroid; own astrometry
# and photometric calibration with pipeline.py; forced S/N at the position, free centroid within 8 px, and the
# S/N a fixed B 16.2 source would give on that plate (from its own calibration).
# Usage: [POS_RA=.. POS_DEC=.. POS_TAG=..] python3 -I fixedpos.py WORKDIR CUTOUT_DIR [plate_id ...]   (default: every plate in WORKDIR/exps_ma731pos.json with limit >= 15.9)
import sys, os, json, base64, gzip, urllib.request, numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from pipeline import Plate, measure
import os as _os
RA, DEC = float(_os.environ.get('POS_RA', 85.893709844)), float(_os.environ.get('POS_DEC', 16.016634745))   # default: MA 731 free centroid (round one)
TAG = _os.environ.get('POS_TAG', '')   # round five: another position, e.g. the February 1909 source
wd, cd = sys.argv[1], sys.argv[2]
rows = json.load(open(f'{wd}/exps_{TAG or "ma731"}pos.json'))
def lim(r):
    for k in ('limMagApass', 'limMagAtlas'):
        if r[k]: return float(r[k])
    return None
sel = [r for r in rows if lim(r) and lim(r) >= 15.9 and r['wcssource'] != 'logbook']
if len(sys.argv) > 3: sel = [r for r in rows if f"{r['series']}{int(r['platenum']):05d}" in sys.argv[3:] and r['wcssource'] != 'logbook' and lim(r) and lim(r) >= 15.9]
def cutout(pid, sol):
    fn = f'{cd}/{pid}_{sol}{"_" + TAG if TAG else ""}.fits'
    if not os.path.exists(fn):
        req = urllib.request.Request('https://api.starglass.cfa.harvard.edu/public/dasch/dr7/cutout',
            data=json.dumps({'plate_id': pid, 'solution_number': int(sol), 'center_ra_deg': RA, 'center_dec_deg': DEC}).encode(),
            headers={'Content-Type': 'application/json', 'Accept': 'application/json', 'User-Agent': 'curl/8'})
        r = json.load(urllib.request.urlopen(req, timeout=300))
        open(fn, 'wb').write(gzip.decompress(base64.b64decode(r)))
    return fn
out = []
for r in sel:
    pid = f"{r['series']}{int(r['platenum']):05d}"; ep = float(r['expdate'][:4])+(int(r['expdate'][5:7])-0.5)/12
    rec = dict(plate=pid, sol=r['solnum'], date=r['expdate'][:16], exptime=r['exptime'], lim=lim(r))
    try:
        fn = cutout(pid, r['solnum'])
        P = Plate(f'pos{TAG or "731"}', fn, 0, RA, DEC, ep, wd, H=417)
        M, _, _ = measure(P, RA, DEC, (RA, DEC), (RA, DEC), 16.2)
        valid = float(np.mean(P.img_valid)) if hasattr(P, 'img_valid') else None
        rec.update(stars=P.astrometry['stars'], astro_med=P.astrometry['cv_median'], snr_pos=M['snr_at_pred'], snr_centroid=M['snr_at_centroid'],
                   centroid_offset=M['offset'], B_centroid=M['B_centroid'], snr_expected_B162=M['snr_expected'], calib_rms=M['calib_rms'], calib_n=M['calib_n'])
    except Exception as e:
        rec.update(error=str(e)[:120])
    out.append(rec)
    print(json.dumps({k: (round(v, 2) if isinstance(v, float) else v) for k, v in rec.items()}), flush=True)
json.dump(out, open(f'{wd}/fixedpos{"_" + TAG if TAG else ""}{"_" + "_".join(sys.argv[3:]) if len(sys.argv) > 3 else ""}.json', 'w'), indent=1)
