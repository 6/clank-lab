"""check_cos: the doubles the C programs use for cos(2 pi j/n) are within 2^-49 of the true value,
certified with mpmath interval arithmetic (the bound is taken against both ends of an enclosure).
Usage: ./rows n m --cos | python3 -I check_cos.py n"""
import sys
import mpmath
mpmath.mp.dps = 50
from mpmath import iv
iv.dps = 50
n = int(sys.argv[1]); worst = mpmath.mpf(0); cnt = 0
for line in sys.stdin:
    j, v = line.split()
    j = int(j); c = float.fromhex(v)
    # certified enclosure of cos(2 pi j/n) by interval arithmetic; the error bound uses its far end
    enc = iv.cos(2 * iv.pi * j / n)
    err = max(abs(mpmath.mpf(c) - enc.a), abs(mpmath.mpf(c) - enc.b))
    worst = max(worst, err); cnt += 1
assert cnt == n, cnt
bound = mpmath.mpf(2) ** -49
print("n=%d entries=%d max_error=%s bound=2^-49 %s" % (n, cnt, mpmath.nstr(worst, 5), "PASS" if worst <= bound else "FAIL"))
sys.exit(0 if worst <= bound else 1)
