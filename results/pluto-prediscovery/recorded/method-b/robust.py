# Robustness of the measurement to the cut-out centre (background-mesh phase): shift the cut centre in a 3x3 grid
# of 40" steps and remeasure at the fixed Pluto prediction. Usage: python3 -I robust.py PLATES_DIR WORKDIR
import sys, os, json, numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from pipeline import Plate, measure
pd, wd = sys.argv[1], sys.argv[2]
cfg = {'731': (f'{pd}/ma00731_mosaic.fits.fz', (85.893540118, 16.016552086), (85.894059468, 16.016539111), (85.893020930, 16.016564908), 1908.973),
       '733': (f'{pd}/ma00733_mosaic.fits.fz', (85.872769077, 16.017045092), (85.873938791, 16.017012857), (85.871596225, 16.017076450), 1908.976)}
out = {}
for pl, (scan, pr, op, cl, ep) in cfg.items():
    if len(sys.argv) > 3 and pl != sys.argv[3]:
        continue
    rows = []
    for i in (-1, 0, 1):
        for j in (-1, 0, 1):
            cra = pr[0]+i*40/3600/np.cos(np.radians(pr[1])); cde = pr[1]+j*40/3600
            P = Plate(f'ma{pl}', scan, 1, cra, cde, ep, wd)
            M, _, _ = measure(P, pr[0], pr[1], op, cl, 16.33)
            rows.append(dict(shift=(i*40, j*40), snr_pred=M['snr_at_pred'], snr_c=M['snr_at_centroid'], off=M['offset'],
                             east=M['offset_east'], north=M['offset_north'], B=M['B_centroid']))
    out[pl] = rows
    a = np.array([[r['snr_pred'], r['snr_c'], r['off'], r['east'], r['north'], r['B'] or np.nan] for r in rows])
    print(pl, 'min/median/max  snr_pred', np.round(np.nanpercentile(a[:, 0], [0, 50, 100]), 2), 'offset', np.round(np.nanpercentile(a[:, 2], [0, 50, 100]), 2),
          'east', np.round(np.nanpercentile(a[:, 3], [0, 50, 100]), 2), 'north', np.round(np.nanpercentile(a[:, 4], [0, 50, 100]), 2), 'B', np.round(np.nanpercentile(a[:, 5], [0, 50, 100]), 2))
json.dump(out, open(f'{wd}/robust.json', 'w'), indent=1)
