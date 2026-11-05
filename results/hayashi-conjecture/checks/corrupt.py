#!/usr/bin/env python3
"""Corruptions that both checkers must reject.

c1: g0 with zero V_3-block part (the F_3 component): the 3-part of every
    translation c(t) vanishes, so the profile no longer refutes the
    conjecture (check_class.py: profile differs; check_table: every length
    divides the longest).
c2: P with the identity as its F_7 block: c0 no longer normalises G
    (check_class.py), and the class is not closed under * (build_table.py).
c3: the table with entry (1, 0) set equal to entry (2, 0): R_0 is no
    longer a bijection (check_table).

usage: corrupt.py qprime.json TABLE.bin OUTDIR
"""
import copy, json, os, sys
import numpy as np

cert = json.load(open(sys.argv[1]))
out = sys.argv[3]
c1 = copy.deepcopy(cert); c1["g0"][1] = [0, 0, 0]
json.dump(c1, open(os.path.join(out, "c1.json"), "w"))
c2 = copy.deepcopy(cert); c2["P"][3] = [[1, 0], [0, 1]]
json.dump(c2, open(os.path.join(out, "c2.json"), "w"))
T = np.fromfile(sys.argv[2], dtype="<u2")
n = int(round(len(T) ** 0.5))
T = T.reshape(n, n)
T[1, 0] = T[2, 0]
T.astype("<u2").tofile(os.path.join(out, "c3.bin"))
