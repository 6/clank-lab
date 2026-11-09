"""Checked import: the numbers in the Lean certificate axiom match the certificate and the checkers.

Usage: python3 -I checks/cert_import.py CAPD_OUTPUT ARB_OUTPUT
where the two files hold the output of `bnf check cert.txt` and `check_arb.py cert.txt`
(checks/run.sh writes them).

It checks, with exact rationals:
- lean/ABC/Flow.lean's certBox has centre (centre_num_x, centre_num_y) / 2^40 and half-width
  2^radius_log2, as in checks/cert.txt;
- lean/ABC/Cert.lean's return-time and trace bounds equal checks/cert.txt's time_lo/time_hi and
  trace_lo/trace_hi;
- its z' lower bound is at most both checkers' certified lower bounds;
- both checkers' outputs end in a pass, and each states the facts the axiom imports, including
  the nonzero twist coefficient (CertFacts.twist).
It exits nonzero on any mismatch.
"""
import re
import sys
from fractions import Fraction as F
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


def cert_fields():
    out = {}
    for line in (ROOT / "checks/cert.txt").read_text().splitlines():
        line = line.strip()
        if line and not line.startswith("#"):
            k, v = line.split()
            out[k] = v
    return out


def frac(s):
    """An exact rational from a Lean literal 'a / b' or 'a / 2 ^ k'."""
    s = s.strip()
    m = re.fullmatch(r"(-?\d+)\s*/\s*2\s*\^\s*(\d+)", s)
    if m:
        return F(int(m.group(1)), 2 ** int(m.group(2)))
    m = re.fullmatch(r"(-?\d+)\s*/\s*(\d+)", s)
    if m:
        return F(int(m.group(1)), int(m.group(2)))
    raise ValueError(s)


def fail(msg):
    print("FAIL:", msg)
    sys.exit(1)


def main():
    if len(sys.argv) != 3:
        sys.exit(__doc__)
    c = cert_fields()
    flow = (ROOT / "lean/ABC/Flow.lean").read_text()
    cert = (ROOT / "lean/ABC/Cert.lean").read_text()

    m = re.search(r"\|a 0 - (\d+ / 2 \^ \d+)\| ≤ (1 / 2 \^ \d+) ∧ "
                  r"\|a 1 - (\d+ / 2 \^ \d+)\| ≤ (1 / 2 \^ \d+)", flow)
    if not m:
        fail("certBox not found in Flow.lean")
    cx, rx, cy, ry = (frac(g) for g in m.groups())
    if cx != F(int(c["centre_num_x"]), 2 ** 40) or cy != F(int(c["centre_num_y"]), 2 ** 40):
        fail("certBox centre differs from cert.txt")
    if rx != ry or rx != F(2) ** int(c["radius_log2"]):
        fail("certBox half-width differs from cert.txt")
    print("ok: certBox = cert.txt box X, centre", c["centre_num_x"], c["centre_num_y"],
          "/ 2^40, half-width 2^" + c["radius_log2"])

    m = re.search(r"(\d+ / \d+) ≤ T ∧ T ≤ (\d+ / \d+)", cert)
    if not m or (frac(m.group(1)), frac(m.group(2))) != (F(c["time_lo"]), F(c["time_hi"])):
        fail("return-time bounds differ from cert.txt")
    print("ok: return time in [%s, %s]" % (c["time_lo"], c["time_hi"]))

    m = re.search(r"(-\d+ / \d+) ≤ LinearMap\.trace.*?≤ (-\d+ / \d+)", cert, re.S)
    if not m or (frac(m.group(1)), frac(m.group(2))) != (F(c["trace_lo"]), F(c["trace_hi"])):
        fail("trace bounds differ from cert.txt")
    print("ok: trace in [%s, %s]" % (c["trace_lo"], c["trace_hi"]))

    m = re.search(r"(\d+ / \d+) ≤ abcField \(γ t\) 2", cert)
    if not m:
        fail("z' bound not found in Cert.lean")
    zb = frac(m.group(1))
    capd = Path(sys.argv[1]).read_text()
    arb = Path(sys.argv[2]).read_text()
    mc = re.search(r"z' > 0 along the orbit segment .*min lower bound ([0-9.]+)\)", capd)
    # the box run covers every point of X; the point run covers only its centre
    ma = re.findall(r"\[box X', D=3\].*min z' lower bound ([0-9.]+)", arb)
    if not mc or not ma:
        fail("z' lower bounds not found in the checkers' outputs")
    if not (zb <= F(mc.group(1)) and zb <= F(ma[0])):
        fail("Cert.lean z' bound exceeds a certified bound")
    print("ok: z' >= %s <= certified bounds %s (CAPD) and %s (arb)" % (zb, mc.group(1), ma[0]))

    need_capd = ["return time inside claimed [3.2352, 3.2354]: yes",
                 "unique fixed point of P in X",
                 "trace inside claimed [-1.9650, -1.9640] within (-2,-1): yes",
                 "twist Re a1 excludes 0: yes",
                 "ALL CHECKS PASSED"]
    need_arb = ["PASS: (1a)", "PASS: (1b)", "PASS: (1c)", "PASS: (2a)", "PASS: (7a)",
                "RESULT: ALL CHECKS PASS"]
    for s in need_capd:
        if s not in capd:
            fail("CAPD output lacks: " + s)
    for s in need_arb:
        if s not in arb:
            fail("arb output lacks: " + s)
    print("ok: both checkers' outputs state the imported facts and pass")


if __name__ == "__main__":
    main()
