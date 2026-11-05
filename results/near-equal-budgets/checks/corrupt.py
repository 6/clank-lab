#!/usr/bin/env python3
"""Write the corrupted inputs used by the corruption runs (each must be rejected).
  c1: certificate with one multiplier changed (first type-B certificate's lambda doubled)
  c2: certificate checked against a corrupted instance (Alice's value of good v set from 6 to 1;
      the float search finds a CE at budgets e + d/100 for this instance)
  c3: the corrupted instance itself, for check_ray.py
Usage: corrupt.py certificate.json instance.json outdir"""
import json, sys, os
cert, inst, out = sys.argv[1:4]
c = json.load(open(cert)); I = json.load(open(inst))
c1 = json.loads(json.dumps(c))
k = next(x for x in c1["certificates"] if x["type"] == "B")
from fractions import Fraction
k["lambda"][0][2] = str(2 * Fraction(k["lambda"][0][2]))
json.dump(c1, open(os.path.join(out, "c1-certificate.json"), "w"))
bad = json.loads(json.dumps(I)); bad["values"][0][0] = 1
c2 = json.loads(json.dumps(c)); c2["instance"] = bad
json.dump(c2, open(os.path.join(out, "c2-certificate.json"), "w"))
json.dump(bad, open(os.path.join(out, "c3-instance.json"), "w"))
