"""Check the four computed premises of the Lean theorem.

  python3 checks/check.py quick --work DIR   a few minutes, a few GB of memory
  python3 checks/check.py full  --work DIR   hours; about 72 GB and 33 GB of memory

Run from the result's folder, with a new work directory outside it. See
checks/README.md for what each step establishes.

quick:
  1. cover: the independent checker accepts all rows of the tail certificate
     (premise CertifiedCoverP3) and rejects seven corrupted certificates;
  2. prefix rehearsal at N = 10^8: both generators and the minimality checker
     agree with each other and with the recorded checkpoint, threshold and
     equality lines, and a swapped and a bumped term are each rejected by the
     hash comparison and by the minimality checker;
  3. figure data: every value in data/figure-data.csv is a term of the
     generated sequence.
full:
  the quick steps, then both generators to N = 16,000,000,000, each compared
  line by line with data/prefix-checkpoints.txt, from which the premises
  FiniteFa, FiniteFbP3 and FiniteFcP3 are read off.
"""
import argparse
import csv
import os
import shutil
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
DATA = os.path.join(ROOT, "data")
CERT = os.path.join(DATA, "cover-p3-13328000000.csv.xz")
L = 16_000_000_000          # Lean's L: the computed prefix is a(1..L)
E0 = 13_328_000_000         # Lean's P3.e0: the cover starts here
KFIN = 329                  # Lean's P3.Kfin
X_FB = 14_130_000_000       # threshold used to read off Fb and Fc
THRESHOLDS = [100_000_000, 1_000_000_000, 2_239_000_000, 2_600_000_000,
              10_000_000_000, 14_130_000_000, 15_850_000_000]


class Fail(Exception):
    pass


def say(msg):
    print(msg, flush=True)


def run(cmd, out=None, expect=0):
    t = time.monotonic()
    with open(out, "w") if out else open(os.devnull, "w") as f:
        r = subprocess.run(cmd, stdout=f if out else subprocess.PIPE,
                           stderr=subprocess.STDOUT, text=True)
    if expect is not None and r.returncode != expect:
        tail = open(out).read()[-2000:] if out else (r.stdout or "")[-2000:]
        raise Fail(f"{os.path.basename(cmd[0])} exited {r.returncode}, expected {expect}\n{tail}")
    return r.returncode, time.monotonic() - t


def expected():
    exp = {"ckpt": {}, "threshold": {}, "equality": set(), "violations": None}
    with open(os.path.join(DATA, "prefix-checkpoints.txt")) as f:
        for line in f:
            w = line.split()
            if not w or w[0].startswith("#"):
                continue
            if w[0] == "ckpt":
                exp["ckpt"][int(w[1])] = (int(w[2]), int(w[3]), int(w[4]), int(w[5]), int(w[6], 16))
            elif w[0] == "threshold":
                exp["threshold"][int(w[1])] = (int(w[2]), int(w[3]))
            elif w[0] == "equality":
                exp["equality"].add((int(w[1]), int(w[2]), w[3]))
            elif w[0] == "violations":
                exp["violations"] = int(w[1])
    return exp


def parse(path, kind):
    """Read a generator's output into ckpt, threshold, equality and violation fields."""
    got = {"ckpt": {}, "threshold": {}, "equality": set(), "violations": None}
    with open(path) as f:
        for line in f:
            w = line.split()
            if not w:
                continue
            if w[0] == "ckpt":
                got["ckpt"][int(w[1])] = (int(w[2]), int(w[3]), int(w[4]), int(w[5]), int(w[6], 16))
            elif w[0] == "threshold":       # both programs: threshold X <label> n <label> maxK
                got["threshold"][int(w[1])] = (int(w[3]), int(w[5]))
            elif w[0] in ("upper_equality", "lower_equality"):          # ekg_gen, ekg_check
                got["equality"].add((int(w[1]), int(w[2]), w[0].split("_")[0]))
            elif w[0] == "equality":                                      # ekgv
                got["equality"].add((int(w[1]), int(w[2]), w[3]))
            elif w[0] == "violations" and kind == "gen":
                got["violations"] = int(w[1])
            elif w[0] == "counts" and kind == "ekgv":
                got["violations"] = int(w[2])
            elif w[0] == "N" and kind == "check":
                got["violations"] = int(w[w.index("violations") + 1])
            elif w[0] in ("violation", "violation_cap"):
                got["violations"] = (got["violations"] or 0) + 1
    return got


def compare(name, got, exp, n_max, ckpts=True):
    if got["violations"] != 0:
        raise Fail(f"{name}: bound violations reported")
    if got["equality"] != exp["equality"]:
        raise Fail(f"{name}: equality cases {sorted(got['equality'])}")
    want = {n: v for n, v in exp["ckpt"].items() if n <= n_max}
    have = {n: v for n, v in got["ckpt"].items() if n <= n_max}
    if ckpts and have != want:
        bad = sorted(set(have.items()) ^ set(want.items()))[:3]
        raise Fail(f"{name}: checkpoints differ from data/prefix-checkpoints.txt, e.g. {bad}")
    for x, v in got["threshold"].items():
        if exp["threshold"].get(x) != v:
            raise Fail(f"{name}: threshold {x} gives {v}, expected {exp['threshold'].get(x)}")
    say(f"  {name}: {len(have) if ckpts else 'no'} checkpoints, {len(got['threshold'])} thresholds, "
        f"equalities {sorted(got['equality'])}, no violations: as recorded")


def build(work):
    cxx = os.environ.get("CXX", "g++")
    cc = os.environ.get("CC", "gcc")
    flags = os.environ.get("CXXFLAGS", "-O3").split()
    for src, std in (("ekg_gen.cpp", "c++17"), ("ekg_check.cpp", "c++17"), ("ekgv.cpp", "c++20")):
        run([cxx, *flags, f"-std={std}", "-o", os.path.join(work, src[:-4]), os.path.join(HERE, src)])
    run([cc, "-O2", "-o", os.path.join(work, "fnvcheck"), os.path.join(HERE, "fnvcheck.c")])
    say("built ekg_gen, ekgv, ekg_check, fnvcheck")


def cover(work):
    say("cover certificate (premise CertifiedCoverP3):")
    out = os.path.join(work, "cover.txt")
    _, t = run([sys.executable, "-I", os.path.join(HERE, "cover_check.py"), CERT, "--controls"], out)
    lines = open(out).read().splitlines()
    acc = [l for l in lines if l.startswith("ACCEPT: ")]
    rejected = [l for l in lines if l.startswith("control rejected: ")]
    if not acc or not acc[0].startswith("ACCEPT: 16857 rows; first ea=13328000000") or len(rejected) != 7:
        raise Fail("cover checker output not as expected:\n" + "\n".join(lines[:3]))
    say(f"  {acc[0][:60]}...")
    say(f"  all 7 corrupted certificates rejected ({t:.0f} s)")


def prefix_rehearsal(work, exp):
    n = 100_000_000
    say(f"prefix rehearsal at N = {n:,}:")
    b = lambda p: os.path.join(work, p)
    seq = b("seq.bin")
    _, t1 = run([b("ekg_gen"), str(n), seq, str(THRESHOLDS[0])], b("gen-1e8.txt"))
    compare("ekg_gen", parse(b("gen-1e8.txt"), "gen"), exp, n)
    _, t2 = run([b("ekgv"), str(n), str(THRESHOLDS[0]), "--state", b("ekgv-1e8"),
                 "--output", b("ekgv-1e8.txt"), "--quiet"])
    compare("ekgv", parse(b("ekgv-1e8.txt"), "ekgv"), exp, n)
    _, t3 = run([b("ekg_check"), seq, str(THRESHOLDS[0])], b("check-1e8.txt"))
    got = parse(b("check-1e8.txt"), "check")
    if "ACCEPT" not in open(b("check-1e8.txt")).read().split():
        raise Fail("ekg_check did not accept the generated prefix")
    compare("ekg_check (minimality)", got, exp, n, ckpts=False)
    h = "%016x" % exp["ckpt"][n][4]
    run([b("fnvcheck"), seq, str(n), h])
    say(f"  hash of the generated prefix equals the recorded checkpoint {h}")
    say(f"  ({t1:.0f} s, {t2:.0f} s, {t3:.0f} s)")
    # Corruptions at a fixed index (paper n = 54,321,988): a swap of two
    # adjacent terms and a term raised by 2. Both checks must reject each.
    i = 54_321_987
    with open(seq, "rb") as f:
        data = bytearray(f.read())
    x = int.from_bytes(data[8 * i:8 * i + 8], "little")
    y = int.from_bytes(data[8 * i + 8:8 * i + 16], "little")
    corrupt = {
        "swap": data[:8 * i] + y.to_bytes(8, "little") + x.to_bytes(8, "little") + data[8 * i + 16:],
        "bump": data[:8 * i] + (x + 2).to_bytes(8, "little") + data[8 * i + 8:],
    }
    for name, blob in corrupt.items():
        path = b(name + ".bin")
        with open(path, "wb") as f:
            f.write(blob)
        if run([b("fnvcheck"), path, str(n), h], expect=None)[0] == 0:
            raise Fail(f"hash comparison accepted the {name} corruption")
        if run([b("ekg_check"), path], b(f"check-{name}.txt"), expect=None)[0] == 0:
            raise Fail(f"ekg_check accepted the {name} corruption")
        reason = open(b(f"check-{name}.txt")).read().split("\n")[-2]
        say(f"  {name} at n = {i + 1:,}: rejected by the hash ({reason} by ekg_check)")
        os.remove(path)
    return seq


def figure_data(seq):
    say("figure data:")
    with open(os.path.join(DATA, "figure-data.csv")) as f:
        rows = list(csv.DictReader(f))
    with open(seq, "rb") as f:
        for r in rows:
            n = int(r["n"])
            f.seek(8 * (n - 1))
            if int.from_bytes(f.read(8), "little") != int(r["a"]):
                raise Fail(f"data/figure-data.csv: a({n}) differs from the generated sequence")
    say(f"  all {len(rows)} plotted values are terms of the generated sequence")


def full(work, exp, which):
    b = lambda p: os.path.join(work, p)
    xs = [str(x) for x in THRESHOLDS[1:]]
    if which in ("both", "gen"):
        say(f"ekg_gen to N = {L:,} (about 45 minutes and 72 GB of memory):")
        _, t = run([b("ekg_gen"), str(L), "-", *xs], b("gen-full.txt"))
        g = parse(b("gen-full.txt"), "gen")
        compare("ekg_gen", g, exp, L)
        if len(g["ckpt"]) != 160 or len(g["threshold"]) != 6:
            raise Fail("ekg_gen: incomplete output")
        say(f"  ({t / 60:.0f} min)")
    if which in ("both", "ekgv"):
        say(f"ekgv to N = {L:,} (about 2 hours, 33 GB of memory, tens of GB of disk):")
        _, t = run([b("ekgv"), str(L), *xs, "--state", b("ekgv-full"),
                    "--output", b("ekgv-full.txt"), "--quiet"])
        v = parse(b("ekgv-full.txt"), "ekgv")
        compare("ekgv", v, exp, L)
        if len(v["ckpt"]) != 160 or len(v["threshold"]) != 6:
            raise Fail("ekgv: incomplete output")
        say(f"  ({t / 60:.0f} min)")
    first_n, maxk = exp["threshold"][X_FB]
    assert first_n <= L - 2 and X_FB >= E0 and maxk <= KFIN
    say(f"FiniteFa: 13n <= 28a(n) and 7a(n) <= 12n for all n <= {L:,}, equality only at n = 28 and n = 7")
    say(f"FiniteFbP3: E first reaches {X_FB:,} at n = {first_n:,} <= L-2, so E(L-2) >= {E0:,}")
    say(f"FiniteFcP3: every state with E < {X_FB:,} (hence every state with E < {E0:,}) has K <= {maxk} <= {KFIN}")


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("mode", choices=["quick", "full", "cover"])
    ap.add_argument("--work", required=True, help="a new directory outside this folder")
    ap.add_argument("--program", choices=["both", "gen", "ekgv"], default="both",
                    help="full mode: run one generator only (to run them on different machines)")
    a = ap.parse_args()
    work = os.path.abspath(a.work)
    if os.path.commonpath([work, ROOT]) == ROOT:
        sys.exit("--work must be outside the result's folder")
    if os.path.exists(work) and os.listdir(work):
        sys.exit("--work must be a new or empty directory")
    os.makedirs(work, exist_ok=True)
    exp = expected()
    try:
        if a.mode == "cover":
            cover(work)
        else:
            build(work)
            cover(work)
            seq = prefix_rehearsal(work, exp)
            figure_data(seq)
            os.remove(seq)
            if a.mode == "full":
                full(work, exp, a.program)
    except Fail as e:
        say(f"FAIL: {e}")
        sys.exit(1)
    if a.mode == "full":
        say("PASS: all four computed premises checked" if a.program == "both"
            else f"PASS: quick checks and the {a.program} full run")
    else:
        say(f"PASS ({a.mode}). This does not replay the prefix to N = 16,000,000,000; "
            "run `full` for that." if a.mode == "quick" else "PASS (cover)")


if __name__ == "__main__":
    main()
