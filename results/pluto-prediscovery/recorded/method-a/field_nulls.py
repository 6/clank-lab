"""Translate the two-epoch track onto disjoint sky fields on the same scans."""
import argparse
import base64
import gzip
import json
from pathlib import Path

import numpy as np
from astropy.io import fits

from extra_inputs import gaia
from fetch import archive
from measure import Plate


def field(fixed, scratch, pair, ix, iy):
    folder = scratch / f"field-{ix}-{iy}"
    folder.mkdir(parents=True, exist_ok=True)
    records = [json.loads((fixed/(r["name"]+".json")).read_text()) for r in pair["plates"]]
    origin = records[0]["cutout"]
    dec = round(origin["center_dec_deg"]+.43*iy, 6)
    ra = round(origin["center_ra_deg"]+.43*ix/np.cos(np.deg2rad(dec)), 6)
    gaia(folder, "ma", ra, dec)
    apass = folder/"ma-apass.csv"
    if not apass.exists():
        rows = archive("dasch/dr7/querycat", dict(refcat="apass", ra_deg=ra, dec_deg=dec, radius_arcsec=1200))
        apass.write_text("\n".join(rows)+"\n")
    plates = []
    for r, rec in zip(pair["plates"], records):
        name = r["name"]
        patch = rec["cutout"]
        # Translate in local tangent-plane units, retaining the track's sky orientation.
        geo = np.array(rec["endpoint_midpoint_endpoint"])
        geo[:,0] = ra+(geo[:,0]-patch["center_ra_deg"])*np.cos(np.deg2rad(patch["center_dec_deg"]))/np.cos(np.deg2rad(dec))
        geo[:,1] += dec-patch["center_dec_deg"]
        patch.update(center_ra_deg=ra, center_dec_deg=dec)
        rec["endpoint_midpoint_endpoint"] = geo.tolist()
        scan = folder/(name+".fits")
        if not scan.exists():
            encoded = archive("dasch/dr7/cutout", patch)
            scan.write_bytes(gzip.decompress(base64.b64decode(encoded)))
        (folder/(name+".json")).write_text(json.dumps(rec))
        with fits.open(scan, do_not_scale_image_data=True) as hdus:
            hdu = hdus[0]
            blank = hdu.header.get("BLANK")
            blank_fraction = float(np.mean(hdu.data == blank)) if blank is not None else 0.
        if blank_fraction > .8:
            return dict(field=[ix,iy], center_deg=[ra,dec], excluded_plate=name,
                        blank_fraction=blank_fraction, valid=0)
        p = Plate(folder,name)
        p.calibrate()
        plates.append(p)
    counts = dict(valid=0, invalid=0, both_threshold=0, both_photometry_veto=0, both_as_bright=0, both_as_bright_and_veto=0)
    for y in range(-336,337,56):
        for x in range(-336,337,56):
            off = np.array([x,y])
            try:
                score = np.array([p.response(p.target+off,p.trail)[0] for p in plates])
                opposite = [p.response(p.target+off+plates[1-i].raw_target-p.raw_target,p.trail)[0]
                            for i,p in enumerate(plates)]
            except ValueError:
                counts["invalid"] += 1
                continue
            cuts = np.array([r["null_threshold"]*p.peak(16.33)/central_peak(r) for r,p in zip(pair["plates"],plates)])
            observed = [p.peak(r["inferred_B"]) for r,p in zip(pair["plates"],plates)]
            counts["valid"] += 1
            counts["both_threshold"] += int(all(score>cuts))
            if all(score>cuts) and all(opposite<cuts):
                magnitudes = [16.33-np.log(a/p.peak(16.33))/(.4*np.log(10)*p.gamma) for a,p in zip(score,plates)]
                counts["both_photometry_veto"] += int(all(abs(m-16.33)<=.45 for m in magnitudes))
            if all(score>=observed):
                counts["both_as_bright"] += 1
                counts["both_as_bright_and_veto"] += int(all(opposite<cuts))
    return dict(field=[ix,iy],center_deg=[ra,dec],**counts)


def central_peak(record):
    gamma = record["photometry"]["exponent"]
    return record["score"]*10**(.4*gamma*(record["inferred_B"]-16.33))


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__)
    for arg in ["fixed","scratch","pair"]:
        ap.add_argument(arg,type=Path)
    ap.add_argument("ix",type=int)
    ap.add_argument("iy",type=int)
    a = ap.parse_args()
    print(json.dumps(field(a.fixed,a.scratch,json.loads(a.pair.read_text()),a.ix,a.iy)))
