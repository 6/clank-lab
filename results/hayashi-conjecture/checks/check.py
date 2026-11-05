#!/usr/bin/env python3
"""Check both counterexamples to Hayashi's conjecture and to Filipi's
Conjecture 4.1, and that every checker rejects deliberately corrupted inputs.

Run from the result's directory:  python3 -I checks/check.py [--full]

For each certificate in data/ (orders 1890 and 5670):
  checker A  (check_class.py)         the class C of c0, its order, the cycle
                                      type of R_c0, connectedness;
  checker B  (build_table.py, then    the full operation table, every quandle
              check_table.c)          axiom, connectedness, the profile and
                                      faithfulness;
  checker F1 (check_filipi_group.py)  Filipi's Conjecture 4.1 fails at c0;
  checker F2 (check_filipi_table.py)  it fails at every c in C.
Right self-distributivity is checked over all triples for order 1890, and
for order 5670 over the triples with z < 100 (all triples with --full,
about 7 CPU-minutes more).  The corruptions come from corrupt.py.
"""
import os, subprocess, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
PY = sys.executable
FULL = "--full" in sys.argv[1:]

CASES = [
    # order, certificate, checker A's seed, table SHA-256, profile line
    (1890, "data/q1890.json", "3",
     "6a9f90c725aec58f056a01836ea15649ae7fab22e962f08885d535e0b355a2f6",
     "profile (length^count): 1^2 2^104 60^7 84^5 140^3 210^2"),
    (5670, "data/q5670.json", "2",
     "d5a3b361344cd9a7208ac66b3cdb668a56896e78b566a53e6be9554c00f95493",
     "profile (length^count): 1^2 2^314 60^21 84^15 140^9 210^6"),
]


def run(cmd, expect_ok=True, needles=()):
    """Run cmd from ROOT; demand its exit status and every needle among its lines."""
    p = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True)
    out = p.stdout + p.stderr
    lines = out.splitlines()
    shown = " ".join("python3" if c == PY else os.path.basename(c) if os.path.isabs(c) else c
                     for c in cmd if c != "-I")
    if (p.returncode == 0) != expect_ok:
        print(out)
        sys.exit("FAILED: %s exited %d, expected %s" % (shown, p.returncode,
                 "success" if expect_ok else "a rejection"))
    for needle in needles:
        if not any(line.startswith(needle) or needle in line for line in lines):
            print(out)
            sys.exit("FAILED: %s did not print %r" % (shown, needle))
    last = lines[-1] if lines else ""
    print("  ok   %s%s" % (shown, ("\n         " + last) if last else ""))
    return out


def py(script, *args):
    return [PY, "-I", os.path.join(HERE, script), *args]


with tempfile.TemporaryDirectory() as tmp:
    exe = os.path.join(tmp, "check_table")
    cc = os.environ.get("CC", "cc")
    subprocess.run([cc, "-O2", "-o", exe, os.path.join(HERE, "check_table.c")], check=True)
    for n, cert, seed, sha, profile in CASES:
        print("order %d (%s)" % (n, cert))
        d = os.path.join(tmp, str(n))
        os.mkdir(d)
        table = os.path.join(d, "q.bin")
        run(py("check_class.py", cert, seed), needles=["ACCEPT"])
        run(py("build_table.py", cert, table), needles=["table sha256 " + sha])
        if n == 1890:
            run([exe, str(n), table], needles=[profile, "faithful (distinct right translations): yes", "ACCEPT"])
        else:
            run([exe, str(n), table, "0", "0"],
                needles=[profile, "faithful (distinct right translations): yes", "ACCEPT"])
            step = 945 if FULL else 100
            for z in range(0, n if FULL else 100, step):
                run([exe, str(n), table, str(z), str(min(n, z + step))])
        run(py("check_filipi_group.py", cert), needles=["ACCEPT"])
        run(py("check_filipi_table.py", str(n), table), needles=["ACCEPT"])

        print("  corruptions of order %d (each must be rejected)" % n)
        run(py("corrupt.py", cert, table, d))
        c1, c2, c3 = (os.path.join(d, f) for f in ("c1.json", "c2.json", "c3.bin"))
        run(py("check_class.py", c1, seed), expect_ok=False, needles=["REJECT: profile differs"])
        run(py("check_class.py", c2, seed), expect_ok=False, needles=["REJECT: c0 does not normalise G"])
        t1 = os.path.join(d, "c1.bin")
        run(py("build_table.py", c1, t1))
        run([exe, str(n), t1, "0", "0"], expect_ok=False)
        run(py("build_table.py", c2, os.path.join(d, "c2.bin")), expect_ok=False)
        run([exe, str(n), c3, "0", "0"], expect_ok=False, needles=["FAIL R_0 not bijective"])
        run(py("check_filipi_group.py", c1), expect_ok=False, needles=["REJECT: Filipi's condition holds"])
        run(py("check_filipi_table.py", str(n), t1), expect_ok=False, needles=["REJECT: at c = "])

print("ALL CHECKS PASSED: two connected quandles refute Hayashi's conjecture and Filipi's Conjecture 4.1;"
      " every corruption was rejected" + ("" if FULL else " (run with --full for all distributivity triples of order 5670)"))
