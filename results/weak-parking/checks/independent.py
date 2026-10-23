#!/usr/bin/env python3
"""Independent certificate replay, without producer or primary-checker imports."""
import argparse
import gzip
import json
from pathlib import Path
import subprocess
import tempfile

import sympy as sp


def require(condition, message):
    if not condition:
        raise ValueError(message)


def integers(value):
    if isinstance(value, list):
        return all(integers(x) for x in value)
    return type(value) is int


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("data", type=Path)
    parser.add_argument("certificate", type=Path)
    args = parser.parse_args()
    source = Path(__file__).with_suffix(".g")
    data_bytes = args.data.read_bytes()
    cert_bytes = args.certificate.read_bytes()
    data = json.loads(data_bytes)
    cert = json.loads(gzip.decompress(cert_bytes))
    names = ["rank", "h", "group_order", "roots", "nc_count", "orbits", "w_classes",
             "class_matrices", "class_sizes", "character"]
    d = {k: data[k] for k in names}
    require(all(integers(v) for v in d.values()), "nonintegral data")
    require(set(cert) == {"rank", "parents", "orbits", "subgroup_classes"}, "certificate schema")
    require(all(integers(v) for v in cert.values()), "nonintegral certificate")
    n, h = d["rank"], d["h"]
    require(n in (6, 7, 8) and cert["rank"] == n, "rank")
    require(h == {6: 12, 7: 18, 8: 30}[n], "Coxeter number")
    q = len(d["class_matrices"])
    require(q == d["w_classes"] == len(d["class_sizes"]) == len(d["character"]), "W class dimensions")
    require(all(len(m) == n and all(len(r) == n for r in m) for m in d["class_matrices"]), "matrix shape")
    require(all(len(row) == h and all(v >= 0 for v in row) for row in d["character"]), "character dimensions")
    require(all(v > 0 for v in d["class_sizes"]), "class sizes positive")
    require(len(cert["parents"]) == d["nc_count"] and cert["parents"][0] == [0, 0], "parent dimensions")
    require(len(cert["orbits"]) == d["orbits"] == len(cert["subgroup_classes"]), "orbit dimensions")
    require(all(len(r) == 2 for r in cert["parents"] + cert["orbits"]), "pair schema")
    require(all(len(r) == 4 and isinstance(r[0], list) and isinstance(r[3], list)
                and len(r[0]) == n and len(r[3]) == n
                and type(r[1]) is int and r[1] > 0
                and type(r[2]) is int and 1 <= r[2] <= q
                and all(1 <= x <= d["roots"] for x in r[0] + r[3])
                for rows in cert["subgroup_classes"] for r in rows), "K class schema")

    # An independent exact spectral calculation uses rational cyclotomic factors.
    x = sp.Symbol("x")
    divisors = sp.divisors(h)
    cyclotomic = {a: sp.Poly(sp.cyclotomic_poly(a, x), x) for a in divisors}
    for index, matrix in enumerate(d["class_matrices"]):
        poly = sp.Poly(sp.Matrix(matrix).charpoly(x).as_expr(), x)
        multiplicities = {}
        for order in divisors:
            remaining, multiplicity = poly, 0
            while True:
                quotient, remainder = remaining.div(cyclotomic[order])
                if not remainder.is_zero:
                    break
                multiplicity += 1
                remaining = quotient
            multiplicities[order] = multiplicity
        for exponent in range(h):
            order = h // __import__("math").gcd(exponent, h)
            require(d["character"][index][exponent] == (h + 1) ** multiplicities[order],
                    f"spectral character mismatch class {index + 1}, exponent {exponent}")
    print(f"INDEPENDENT spectral E{n} PASS", flush=True)

    with tempfile.TemporaryDirectory(prefix="weak-parking-independent-") as tmp:
        driver = Path(tmp) / "input.g"
        assignments = [f"D_{k}:={json.dumps(v, separators=(',', ':'))};;" for k, v in d.items()]
        assignments += [f"C_{k}:={json.dumps(v, separators=(',', ':'))};;" for k, v in cert.items()]
        # GAP strings use JSON-compatible quoting for this generated local filename.
        assignments.append(f"Read({json.dumps(str(source.resolve()))});")
        driver.write_text("\n".join(assignments) + "\n")
        process = subprocess.Popen(["gap", "-q", "-b", "-T", str(driver)], text=True,
                                   stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        output = []
        for line in process.stdout:
            print(line, end="", flush=True)
            output.append(line.rstrip("\n"))
        returncode = process.wait()
    marker = f"INDEPENDENT GAP E{n} PASS"
    require(returncode == 0 and output.count(marker) == 1,
            "GAP failed or explicit pass marker missing")
    print(f"INDEPENDENT E{n} PASS", flush=True)


if __name__ == "__main__":
    main()
