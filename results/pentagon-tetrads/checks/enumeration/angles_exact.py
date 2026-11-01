"""angles2.py's screen with every leaf decided by the exact rational LP
(exact_linear.angle_margin) instead of floating point."""
import sys

import angles2
from exact_linear import angle_margin


def exact_lp_feasible(rows, n, pattern):
    t = angle_margin(rows, n, pattern)
    return (float(t) if t > 0 else -1.0), ([0.0] * n if t > 0 else None)


angles2.lp_feasible = exact_lp_feasible
angles2.THRESH = 0

if __name__ == '__main__':
    only = int(sys.argv[4]) if len(sys.argv) > 4 and sys.argv[4] != '-' else None
    chunk = tuple(int(x) for x in sys.argv[5].split('/')) if len(sys.argv) > 5 else None
    angles2.main(sys.argv[1], int(sys.argv[2]), sys.argv[3], only, chunk)
