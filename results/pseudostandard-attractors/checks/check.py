#!/usr/bin/env python3
"""Check the result: run both checkers, then confirm they reject the inputs in data/rejected/.

Usage, from the result's folder: python3 checks/check.py

Exit status 0 means both checkers accept the witnesses, the obstruction and
the upper-bound table in data/, every input in data/rejected/ is rejected by
each checker that reads it, and the figure data/word.svg matches the data.
Standard library only.
"""

import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DATA = ROOT / "data"
EXHAUSTIVE = ROOT / "checks" / "check_exhaustive.py"
DRAW = ROOT / "checks" / "draw_word.py"
PROOF = ROOT / "checks" / "check_proof.py"


def run(checker, witnesses="witnesses.json", obstruction="obstruction.json", upper="upper-bound.json"):
    """Run one checker; return (accepted, last output line)."""
    args = [sys.executable, "-I", str(checker), str(DATA / witnesses)]
    if checker == PROOF:
        args += [str(DATA / obstruction), str(DATA / upper)]
    result = subprocess.run(args, capture_output=True, text=True, cwd=ROOT)
    lines = result.stdout.strip().splitlines() or [result.stderr.strip()]
    return result.returncode == 0, result.stdout, lines[-1]


# Each input that must be rejected, which file it replaces, and which checkers read it.
CORRUPTIONS = [
    ("a letter of the 36-letter word flipped", {"witnesses": "rejected/flipped-letter.json"}, [EXHAUSTIVE, PROOF]),
    ("one closure changed from E to R", {"witnesses": "rejected/changed-theta.json"}, [EXHAUSTIVE, PROOF]),
    ("five positions that are not an attractor", {"witnesses": "rejected/not-an-attractor.json"}, [EXHAUSTIVE, PROOF]),
    ("an attractor of only four positions", {"witnesses": "rejected/four-positions.json"}, [EXHAUSTIVE, PROOF]),
    ("a Thue-Morse prefix, which has a four-position attractor", {"witnesses": "rejected/thue-morse.json"},
     [EXHAUSTIVE, PROOF]),
    ("an occurrence left out of the obstruction", {"obstruction": "rejected/missing-occurrence.json"}, [PROOF]),
    ("a factor dropped from the obstruction", {"obstruction": "rejected/dropped-factor.json"}, [PROOF]),
    ("a factor dropped from the upper-bound table", {"upper": "rejected/missing-gap-factor.json"}, [PROOF]),
]


def main():
    failures = 0
    for checker in (EXHAUSTIVE, PROOF):
        accepted, output, _ = run(checker)
        print(output.rstrip())
        if not accepted:
            failures += 1
            print("FAIL: %s rejected the result" % checker.name)
    print()
    for description, replaced, checkers in CORRUPTIONS:
        missing = [name for name in replaced.values() if not (DATA / name).is_file()]
        if missing:
            print("FAIL: missing input %s" % ", ".join(missing))
            failures += 1
            continue
        for checker in checkers:
            accepted, _, last = run(checker, **replaced)
            verdict = last.split(": ", 1)[-1] if not accepted else "ACCEPTED (failure)"
            print("should be rejected, %s: %s says %s" % (description, checker.name, verdict))
            failures += accepted
    # The README's figure is an illustration, not part of the proof; check it matches the data.
    figure = subprocess.run([sys.executable, "-I", str(DRAW), str(DATA / "witnesses.json"),
                             str(DATA / "obstruction.json"), str(DATA / "word.svg"), "--check"],
                            capture_output=True, text=True)
    print()
    print("data/word.svg: " + (figure.stdout.strip() or figure.stderr.strip()))
    failures += figure.returncode != 0
    if failures:
        print("FAILED: %d problem(s)" % failures)
        return 1
    print("All checks passed.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
