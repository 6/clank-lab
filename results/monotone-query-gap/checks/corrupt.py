"""Corruption controls: each corrupted copy of certificate.json must be rejected.

Usage: python3 -I corrupt.py certificate.json CHECKER.py...
Exit 0 iff every checker rejects every corruption and accepts the original.
Rejection must be a normal exit with a REJECT message, not an exception.
"""
import copy, json, os, subprocess, sys, tempfile


def corruptions(c):
    def mod(name, fn):
        d = copy.deepcopy(c)
        fn(d)
        return name, d
    yield mod("flip truth-table bit 7", lambda d: d.__setitem__(
        "truth_table", d["truth_table"][:7] + str(1 - int(d["truth_table"][7])) + d["truth_table"][8:]))
    yield mod("raise root lower bound to 7/2", lambda d: d["lower_bound_table"].__setitem__("*****", "7/2"))
    yield mod("raise an inner L entry", lambda d: d["lower_bound_table"].__setitem__("1****", "4"))
    yield mod("drop a restriction from L", lambda d: d["lower_bound_table"].pop("0*1*1"))
    yield mod("drop a partition cube", lambda d: d["partition"].pop(3))
    yield mod("widen a partition cube", lambda d: d["partition"].__setitem__(0, "0****"))
    yield mod("merge two cells into a non-monochromatic cube",
              lambda d: d["partition"].__setitem__(slice(9, 11), ["1000*", "11100"]))
    yield mod("raise a dual entry", lambda d: d["sc_dual"].__setitem__(7, "6"))
    def balanced_dual(d):
        # Preserve the objective; only the subcube inequalities reject this.
        d["sc_dual"][0], d["sc_dual"][1] = "6", "-6"
    yield mod("change dual entries preserving the objective", balanced_dual)
    yield mod("prune the tree at the root's 1-branch",
              lambda d: d["optimal_tree"].__setitem__("1", {"leaf": 1}))
    yield mod("wrong leaf label", lambda d: d["optimal_tree"]["0"].__setitem__("0", {"leaf": 1}))


def run(cmd, path):
    return subprocess.run(cmd + [path], capture_output=True, text=True)


def main():
    base = json.load(open(sys.argv[1]))
    checkers = [[sys.executable, "-I", c] for c in sys.argv[2:]]
    if not checkers:
        raise SystemExit("at least one checker is required")
    ok = True
    with tempfile.TemporaryDirectory() as tmp:
        for cmd in checkers:
            result = run(cmd, sys.argv[1])
            if result.returncode != 0 or not result.stdout.startswith("ACCEPT") or result.stderr:
                print(f"FAIL: {' '.join(cmd)} rejects the original")
                ok = False
        for name, d in corruptions(base):
            path = os.path.join(tmp, "c.json")
            json.dump(d, open(path, "w"))
            for cmd in checkers:
                result = run(cmd, path)
                rejected = (result.returncode == 1 and
                            result.stdout.startswith("REJECT") and not result.stderr)
                status = "rejected" if rejected else "FAILED"
                if not rejected:
                    ok = False
                print(f"{status:9s} {name}  [{os.path.basename(cmd[-1])}]")
    print("CORRUPTIONS OK" if ok else "CORRUPTIONS FAIL")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
