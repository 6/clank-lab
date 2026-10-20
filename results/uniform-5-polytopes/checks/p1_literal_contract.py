"""Check P1Separated's literal rational ranges, beyond sampled tail tests.

The universal delta bounds themselves use the paper's closed-form proof.
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent / "check_caseb"))
import p1check as p


def check():
    interval = p.iv.mpf
    path = Path(__file__).resolve().parent / "check_caseb/p1_excluded.txt"
    excluded = [tuple(map(int, line.split(",")))
                for line in path.read_text().splitlines() if line]
    if len(excluded) != 67 or len(set(excluded)) != 67:
        raise ValueError("expected 67 distinct excluded configurations")
    bounded = []
    for tail, top in [((3, 7), 41), ((3, 8), 23), ((3, 9), 17), ((4, 5), 19)]:
        for n in range(17, top + 1):
            delta, state = p.delta_general(tail, n)
            if state != 1:
                raise ValueError("unresolved bounded tail")
            bounded.append(delta)
    if len(bounded) != 36:
        raise ValueError("bounded-tail inventory mismatch")
    ranges = [
        interval([p.lo(interval(186963) / 1000000), p.hi(interval(3) / 16)]),
        interval([p.lo(interval(1) / 3), p.hi(interval(337262) / 1000000)]),
    ]
    for config in excluded:
        radius_sq = p.config_R2([p.chord(q) for q in config])
        found = False
        for q in sorted(set(config).intersection(p.FAMILY)):
            delta = radius_sq - p.r_poly(q) ** 2
            antiprism = (1 - 1 / (4 * p.iv.cos(p.PI / (2 * q)) ** 2)) / 4
            alternatives = [antiprism, interval(1) / 4, *ranges, *bounded]
            differences = [delta - value for value in alternatives]
            if all(d.a > interval(1) / 2000 or d.b < -interval(1) / 2000
                   for d in differences):
                found = True
                break
        if not found:
            raise ValueError(f"literal P1Separated clause unresolved: {config}")
    print("PASS literal P1Separated: 67 configurations, 36 bounded tails; "
          "every selected separation > 1/2000")


if __name__ == "__main__":
    check()
