"""Post-unmask diagnostic: inject at each prediction and inspect local backgrounds."""
import json
import sys
from pathlib import Path

import numpy as np
from measure import MAGS, Plate


def check(folder, frozen):
    with open(frozen) as stream:
        pair = json.load(stream)
    for result in pair["plates"]:
        plate = Plate(folder, result["name"])
        plate.calibrate()
        model = plate.response(plate.target,plate.trail)
        threshold = result["null_threshold"]
        target_scores = {str(m):round(plate.injected(model,m),2) for m in MAGS}
        # Raw pixels must be usable throughout the fitted stamp.
        pixels = plate.delta + np.rint(plate.target).astype(int)
        stamp = plate.img[pixels[:,1],pixels[:,0]]
        print(json.dumps(dict(plate=plate.name,target_scores=target_scores,
              threshold=threshold,finite=int(np.isfinite(stamp).sum()),
              pixels=len(stamp),stamp_range=[float(stamp.min()),float(stamp.max())])))


if __name__ == "__main__":
    check(Path(sys.argv[1]),sys.argv[2])
