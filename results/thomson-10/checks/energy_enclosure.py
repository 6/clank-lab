#!/usr/bin/env python3
"""Separate rigorous decimal enclosure, not a clause of the Lean theorem."""
from pathlib import Path
import sys
sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
from check_certificate import Fr, Iv, parse_lean_height

height = parse_lean_height(str(Path(__file__).resolve().parents[1] / 'lean/ThomsonN10/Candidate.lean'))
h = Iv(height['heightLower'], height['heightUpper'])
rho = (Iv(1) - h * h).sqrt()
q = rho * Iv(2).sqrt() * Fr(1, 2)
z = Iv(0)
points = [(z,z,Iv(1)), (z,z,Iv(-1)), (rho,z,h), (z,rho,h),
          (-rho,z,h), (z,-rho,h), (q,q,-h), (-q,q,-h),
          (-q,-q,-h), (q,-q,-h)]
energy = Iv(0)
for i in range(10):
    for j in range(i+1,10):
        distance_squared = Iv(0)
        for k in range(3):
            delta = points[i][k] - points[j][k]
            distance_squared = distance_squared + delta * delta
        energy = energy + distance_squared.sqrt().inv()
lo, hi = Fr('32.716949460147'), Fr('32.716949460149')
assert lo < energy.lo <= energy.hi < hi, 'decimal enclosure does not contain interval'
print('PASS: 32.716949460147 < E(candidate) < 32.716949460149')
