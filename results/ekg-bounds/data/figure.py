"""Draw the figure of a(n)/n against the two bounds (optional; not part of the proof).

Computes the EKG sequence a(1..10^6) from its definition, writes the plotted
values to figure-data.csv, and draws ratio.pdf (for the paper) and ratio.svg
(for the README). `python3 checks/check.py quick` compares every value in
figure-data.csv with the sequence produced by the prefix programs.

Requires matplotlib. Usage: python3 data/figure.py
"""
import csv
import os
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
N = 10**6
FIRST = 60


def ekg(n):
    """a(1..n) by the rule a(k) = least unused m with gcd(m, a(k-1)) > 1,
    computed as the minimum over primes q | a(k-1) of the least unused
    multiple of q (any such m is a multiple of one of these primes)."""
    vmax = 2 * n + 10
    spf = list(range(vmax + 1))
    for p in range(2, int(vmax**0.5) + 1):
        if spf[p] == p:
            for m in range(p * p, vmax + 1, p):
                if spf[m] == m:
                    spf[m] = p
    used = bytearray(vmax + 1)
    nxt = {}  # prime q -> a multiple of q with all smaller multiples used
    a = [0, 1, 2]
    used[1] = used[2] = 1
    while len(a) <= n:
        x, best = a[-1], None
        while x > 1:
            q = spf[x]
            while x % q == 0:
                x //= q
            m = nxt.get(q, q)
            while m <= vmax and used[m]:
                m += q
            nxt[q] = m
            if m <= vmax and (best is None or m < best):
                best = m
        assert best is not None  # some candidate lies below vmax, so best is exact
        used[best] = 1
        a.append(best)
    return a


def main():
    a = ekg(N)
    rows = [("term", k, a[k]) for k in range(1, FIRST + 1)]
    k = 1
    while 2**k <= N:
        block = range(2**k, min(2 ** (k + 1), N + 1))
        lo = min(block, key=lambda n: Fraction(a[n], n))
        hi = max(block, key=lambda n: Fraction(a[n], n))
        rows += [("blockmin", lo, a[lo]), ("blockmax", hi, a[hi])]
        k += 1
    with open(os.path.join(HERE, "figure-data.csv"), "w", newline="") as f:
        w = csv.writer(f, lineterminator="\n")
        w.writerow(("kind", "n", "a"))
        w.writerows(rows)

    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    plt.rcParams.update({"font.size": 9, "svg.hashsalt": "ekg", "svg.fonttype": "path"})
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(7.2, 2.9))
    lo_b, hi_b = 13 / 28, 12 / 7
    terms = [(n, v) for kind, n, v in rows if kind == "term"]
    for ax in (ax1, ax2):
        ax.axhline(hi_b, color="tab:red", lw=1)
        ax.axhline(lo_b, color="tab:blue", lw=1)
        ax.set_xlabel("$n$")
        ax.set_ylim(0.3, 1.9)
    ax1.set_ylabel("$a(n)/n$")
    ax1.plot([n for n, _ in terms], [v / n for n, v in terms], "o", ms=2.5, color="0.2")
    ax1.plot([7], [12 / 7], "o", ms=6, mfc="none", color="tab:red")
    ax1.plot([28], [13 / 28], "o", ms=6, mfc="none", color="tab:blue")
    ax1.annotate("$a(7)=12$", (7, 12 / 7), (12, 1.78), fontsize=8)
    ax1.annotate("$a(28)=13$", (28, 13 / 28), (32, 0.36), fontsize=8)
    ax1.text(FIRST, hi_b + 0.04, "$12/7$", ha="right", color="tab:red", fontsize=8)
    ax1.text(FIRST, lo_b - 0.11, "$13/28$", ha="right", color="tab:blue", fontsize=8)
    ax1.set_title(f"$a(n)/n$ for $n \\leq {FIRST}$", fontsize=9)
    mins = [(n, v / n) for kind, n, v in rows if kind == "blockmin"]
    maxs = [(n, v / n) for kind, n, v in rows if kind == "blockmax"]
    ax2.set_xscale("log")
    ax2.plot(*zip(*maxs), "v-", ms=3, lw=0.8, color="0.2", label="largest in $[2^k,2^{k+1})$")
    ax2.plot(*zip(*mins), "^-", ms=3, lw=0.8, color="0.5", label="smallest in $[2^k,2^{k+1})$")
    ax2.axhline(1.5, color="0.6", lw=0.6, ls=":")
    ax2.axhline(0.5, color="0.6", lw=0.6, ls=":")
    ax2.legend(loc="center right", fontsize=7, frameon=False)
    ax2.set_title("extremes of $a(n)/n$ over dyadic blocks, $n \\leq 10^6$", fontsize=9)
    fig.tight_layout()
    fig.savefig(os.path.join(HERE, "ratio.pdf"), metadata={"CreationDate": None, "ModDate": None})
    fig.savefig(os.path.join(HERE, "ratio.svg"), metadata={"Date": None})


if __name__ == "__main__":
    main()
