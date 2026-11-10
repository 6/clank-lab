#!/usr/bin/env python3
"""Check the six explicit billiard paths with both exact checkers, then confirm that both reject
two corrupted certificates. Python 3.10 or later, standard library only.
usage: python3 checks/check.py   (from the folder above checks/)"""
import json, os, subprocess, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(HERE, "..", "data", "small-paths.json")
CHECKERS = ["paths_sqrt5.py", "paths_zeta.py"]

def run(checker, path):
    r = subprocess.run([sys.executable, "-I", os.path.join(HERE, checker), path],
                       capture_output=True, text=True)
    return r.returncode, (r.stdout + r.stderr).strip().splitlines()

def corruptions(paths):
    c1 = json.loads(json.dumps(paths))          # claim half-period 22 for the period-42 path
    next(p for p in c1 if p["l"] == 21)["l"] = 22
    c2 = json.loads(json.dumps(paths))          # tilt the direction of the period-10 path
    next(p for p in c2 if p["l"] == 5)["dir"][0][0] = "-37/10"
    return [("half-period 21 relabeled 22", c1), ("period-10 direction tilted", c2)]

def main():
    ok = True
    for checker in CHECKERS:
        code, out = run(checker, DATA)
        print(f"{checker}: {out[-1] if out else ''}")
        ok &= code == 0
    paths = json.load(open(DATA))
    with tempfile.TemporaryDirectory() as tmp:
        for name, bad in corruptions(paths):
            path = os.path.join(tmp, "corrupt.json")
            json.dump(bad, open(path, "w"))
            for checker in CHECKERS:
                code, out = run(checker, path)
                print(f"corruption ({name}): {checker} " + (f"rejects: {out[-1][:90]}" if code else "ACCEPTS"))
                ok &= code != 0
    print("PASS: six asymmetric periodic paths, periods 8, 10, 30, 42, 58 and 102" if ok else "FAIL")
    sys.exit(0 if ok else 1)

if __name__ == "__main__":
    main()
