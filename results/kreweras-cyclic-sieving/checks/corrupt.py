"""Run both checkers on corrupted copies of the E6 certificate and table; each
corruption must exit nonzero with the expected REJECT code.

usage: python3 -I checks/corrupt.py TABLES.json CERT_E6.json"""
import copy, json, os, subprocess, sys, tempfile

tables_p, cert_p = sys.argv[1], sys.argv[2]
here = os.path.dirname(os.path.abspath(__file__))
tables, cert = json.load(open(tables_p)), json.load(open(cert_p))


def coef(c, t):
    e = next(x for x in c["reduction"] if x["h1"] == 3 and x["nu"] == 2)
    L = sorted(e["binomial_coeffs"])[0]
    e["binomial_coeffs"][L][0] += 1


def drop(c, t):
    c["reduction"] = [x for x in c["reduction"] if not (x["h1"] == 4 and x["nu"] == 3)]


def swap(c, t):
    a = next(x for x in c["classes"] if x["label"] == "A3")
    b = next(x for x in c["classes"] if x["label"] == "D4")
    a["label"], b["label"] = b["label"], a["label"]


def formula(c, t):
    r = next(x for x in t if x["type"] == "E6" and x["label"] == "A3")
    assert "q**(3m-11)" in r["f"]
    r["f"] = r["f"].replace("q**(3m-11)", "q**(3m-10)")


def zero(c, t):
    # a well-formed product row with wrong values: [m-3] -> [m-5] in E6 A3
    r = next(x for x in t if x["type"] == "E6" and x["label"] == "A3")
    assert "B(m-3)" in r["f"]
    r["f"] = r["f"].replace("B(m-3)", "B(m-5)")


def shape(c, t):
    # an exponent that is not linear in m
    r = next(x for x in t if x["type"] == "E6" and x["label"] == "A3")
    r["f"] = r["f"].replace("q**(3m-11)", "q**(3m*m-11)")


cases = [("coefficient", coef, {"A": "LHS", "B": "LHS"}),
         ("missing-case", drop, {"A": "COVER", "B": "COVER"}),
         ("label-swap", swap, {"A": "LABEL", "B": "LABEL"}),
         ("table-formula", formula, {"A": "NOT_RATIONAL", "B": "NOT_RATIONAL"}),
         ("table-bracket", zero, {"A": "IDENTITY", "B": "IDENTITY"}),
         ("table-shape", shape, {"A": "SHAPE", "B": "SHAPE"})]
fail = 0
with tempfile.TemporaryDirectory() as d:
    for name, fn, want in cases:
        c, t = copy.deepcopy(cert), copy.deepcopy(tables)
        fn(c, t)
        cp, tp = os.path.join(d, "c.json"), os.path.join(d, "t.json")
        json.dump(c, open(cp, "w"))
        json.dump(t, open(tp, "w"))
        for ck in ("A", "B"):
            r = subprocess.run([sys.executable, "-I", os.path.join(here, f"check_{ck.lower()}.py"), tp, cp],
                               capture_output=True, text=True)
            line = (r.stderr.strip().splitlines() or [""])[-1]
            ok = r.returncode != 0 and line.startswith(f"REJECT {want[ck]}:")
            fail += not ok
            print(f"{name} checker_{ck}: exit {r.returncode} {line} -> {'OK' if ok else 'NOT REJECTED AS EXPECTED'}")
sys.exit(1 if fail else 0)
