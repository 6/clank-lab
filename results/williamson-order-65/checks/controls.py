"""controls: each reduction, switched off on its own, against the reference set.

Usage: python3 -I controls.py n m reference.txt workdir
For each variant it rebuilds the inputs it needs, runs search on every unit and
checks that the closure of the found solutions under row permutations and unit
multipliers equals the reference set (closure.py). Prints one line per variant."""
import os, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
VARIANTS = [  # name, rows mode, units mode, search options
    ("full", "", "orbits", []),
    ("no-rowfilter", "nofilter", "orbits", []),
    ("no-orbit", "", "sorted", []),
    ("no-rowperm-no-orbit", "", "all", []),
    ("no-pair", "", "orbits", ["--no-pair"]),
    ("no-xor", "", "orbits", ["--no-xor"]),
    ("no-kmin", "", "orbits", ["--no-kmin"]),
    ("weak-hash-12bit", "", "orbits", ["--keybits", "12"]),
    ("forced-multipass-cap64", "", "orbits", ["--cap", "64"]),
    ("compression-only", "nofilter", "all", ["--no-pair", "--no-xor", "--no-kmin"]),
]


def run(cmd):
    r = subprocess.run(cmd, capture_output=True, text=True)
    if r.returncode not in (0, 1):
        raise SystemExit("command failed: %s\n%s" % (" ".join(cmd), r.stderr[-2000:]))
    return r


def main():
    n, m, ref, wd = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4]
    os.makedirs(wd, exist_ok=True)
    ok_all = True
    for name, rmode, umode, opts in VARIANTS:
        d = os.path.join(wd, "rows_" + (rmode or "filter"))
        if not os.path.exists(os.path.join(d, "classes.tsv")):
            os.makedirs(d, exist_ok=True)
            run([os.path.join(HERE, "rows"), n, m, d] + ([rmode] if rmode else []))
        uf = os.path.join(d, "units_%s.tsv" % umode)
        if not os.path.exists(uf):
            run([sys.executable, "-I", os.path.join(HERE, "units.py"), n, m, os.path.join(d, "classes.tsv"), uf, umode])
        nu = sum(1 for _ in open(uf))
        od = os.path.join(wd, "out_" + name)
        subprocess.run(["rm", "-rf", od])
        run([os.path.join(HERE, "search"), n, m, d, uf, "0", str(nu), od] + opts)
        tot = [0] * 6
        for fn in os.listdir(od):
            if fn.startswith("batch_") and fn.endswith(".tsv"):
                for line in open(os.path.join(od, fn)):
                    f = line.split("\t")
                    if f[0] == "U":
                        for i in range(6):
                            tot[i] += int(f[13 + i])
        r = run([sys.executable, "-I", os.path.join(HERE, "closure.py"), n, ref, os.path.join(od, "solutions.tsv")])
        ok = r.returncode == 0
        ok_all &= ok
        print("n=%s m=%s %-24s units=%d pairs=%d surv=%d matches=%d sols=%d %s %s" % (
            n, m, name, nu, tot[0] + tot[1], tot[2] + tot[3], tot[4], tot[5], "PASS" if ok else "FAIL", r.stdout.strip()), flush=True)
    sys.exit(0 if ok_all else 1)


if __name__ == "__main__":
    main()
