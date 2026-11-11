"""Corruptions of data/G1-cert.json that check_cert.py must reject (nonzero exit).

Prints each corruption, the exit status and the rejection line; exits 1 if any
corruption is accepted or fails for a reason other than a FAIL line.
Usage: corruptions.py TMPDIR
"""
import copy, json, os, subprocess, sys
from decimal import Decimal, getcontext
from fractions import Fraction as Fr

getcontext().prec = 80
here = os.path.dirname(os.path.abspath(__file__))
cert = json.load(open(os.path.join(here, "..", "data", "G1-cert.json")))

def c_flip(x):      # flip the sign of one negative off-diagonal C entry (both copies)
    C = x["C_rows_T_order"]
    a, b = next((a, b) for a in range(len(C)) for b in range(a + 1, len(C)) if Fr(C[a][b]) < 0)
    C[a][b] = C[b][a] = str(-Fr(C[a][b]))

def g6_edit(x):     # change one graph6 data character
    s = list(x["graph6"]); s[3] = chr(ord(s[3]) ^ 1); x["graph6"] = "".join(s)

def umid_shift(x):  # move the box centre by 1e-30
    x["u_mid"][0] = str(Decimal(x["u_mid"][0]) + Decimal("1e-30"))

def bfixed_sign(x): # make one fixed S-T entry positive
    k = next(iter(x["B_fixed"])); x["B_fixed"][k] = str(-Fr(x["B_fixed"][k]))

def c_diag(x):      # perturb a diagonal entry of C
    x["C_rows_T_order"][0][0] = str(Fr(x["C_rows_T_order"][0][0]) + 100)

def c_two_neg(x):   # a second negative eigenvalue: negate C's diagonal entry for vertex 8
    k = x["T"].index(8)                         # (no neighbour inside T, so C stays a valid pattern)
    x["C_rows_T_order"][k][k] = str(-Fr(x["C_rows_T_order"][k][k]))

bad = 0
for f in (c_flip, g6_edit, umid_shift, bfixed_sign, c_diag, c_two_neg):
    x = copy.deepcopy(cert); f(x)
    path = os.path.join(sys.argv[1], f.__name__ + ".json")
    json.dump(x, open(path, "w"))
    r = subprocess.run([sys.executable, "-I", os.path.join(here, "check_cert.py"), path],
                       capture_output=True, text=True)
    last = (r.stdout.strip().splitlines() or [""])[-1]
    ok = r.returncode != 0 and last.startswith("FAIL:")
    bad += not ok
    print("%-12s exit %d  %s  %s" % (f.__name__, r.returncode, last, "rejected" if ok else "NOT REJECTED"))
# SAP routine on a matrix without SAP: 4I - (adjacency of G1) with the rows and columns of
# the non-adjacent pair (1, 3) zeroed, so X = E_13 + E_31 has M0 X = 0.
sys.path.insert(0, here)
import check_cert as cc
from fractions import Fraction
g = json.load(open(os.path.join(here, "..", "data", "G1-cert.json")))
n, E = cc.graph6_edges(g["graph6"])
M0 = [[Fraction(0)] * n for _ in range(n)]
for i, j in E: M0[i][j] = M0[j][i] = Fraction(-1)
for i in range(n): M0[i][i] = Fraction(4)
for k in range(n): M0[1][k] = M0[k][1] = M0[3][k] = M0[k][3] = Fraction(0)
NE = [(i, j) for i in range(n) for j in range(i + 1, n) if (i, j) not in E]
assert (1, 3) in NE
r = cc.sap_eps(M0, NE)
print("%-12s sap_eps -> %s  %s" % ("sap_kernel", r, "rejected" if r is None else "NOT REJECTED"))
bad += r is not None
sys.exit(1 if bad else 0)
