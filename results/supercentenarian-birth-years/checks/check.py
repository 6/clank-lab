"""Check observed totals, state overlap and exact empirical quantiles offline."""
import csv
from bisect import bisect_left, bisect_right
from fractions import Fraction
from pathlib import Path

DATA = Path(__file__).resolve().parents[1] / "data"


def rows(filename):
    with (DATA / filename).open() as source:
        return list(csv.DictReader(source))


def require(ok, message):
    if not ok:
        raise ValueError(message)


def main():
    states = rows("state-counts.csv")
    hist = rows("shuffle-counts.csv")
    require(len({r["state"] for r in states}) == len(states) == 45, "state roster")
    require(sum(int(r["records"]) for r in states) == 690, "mapped records")
    require(all(int(r["records"]) == sum(int(r["aligned_" + col])
                for col in ("before", "after", "outside")) for r in states), "aligned denominator")
    require({r["method"] for r in hist} == {"s1", "aligned"}, "histogram labels")
    for method, totals, limits, overlap in [
        ("s1", (534, 112), ("264/323", "271/323"), (5, 42, 42)),
        ("aligned", (552, 134), ("541/687", "185/228"), (4, 50, 65)),
    ]:
        pairs = [(int(r[method + "_before"]), int(r[method + "_after"])) for r in states]
        require(tuple(map(sum, zip(*pairs))) == totals, method + " observed counts")
        both = [(b, a) for b, a in pairs if b and a]
        require((len(both), *map(sum, zip(*both))) == overlap, method + " overlap")
        draws = []
        for row in hist:
            if row["method"] != method:
                continue
            b, n, freq = (int(row[c]) for c in ("early", "eligible", "draws"))
            require(0 <= b <= n and n > 0 and freq > 0, method + " invalid draw")
            draws.extend([Fraction(b, n)] * freq)
        require(len(draws) == 10000, method + " draw count")
        draws.sort()
        lo, hi = draws[249], draws[9749]
        require((lo, hi) == tuple(map(Fraction, limits)), method + " interval")
        obs = Fraction(totals[0], sum(totals))
        require(lo <= obs <= hi, method + " observed share outside interval")
        if method == "s1":
            require(lo <= Fraction("0.826") <= hi, "printed share outside interval")
        print(f"{method}: {totals[0]}/{sum(totals)} ({100*float(obs):.2f}%), "
              f"central 95% {100*float(lo):.2f}% to {100*float(hi):.2f}%")
        median = (draws[4999] + draws[5000]) / 2
        midrank = (bisect_left(draws, obs) + bisect_right(draws, obs)) / (2 * len(draws))
        print(f"  median {100*float(median):.2f}%, observed midrank {100*midrank:.2f}%")
        # Marginal 95% binomial rank intervals at p=0.025 and its reflection.
        for first, last in [(220, 282), (9719, 9781)]:
            print(f"  ranks {first}–{last}: {100*float(draws[first-1]):.2f}% "
                  f"to {100*float(draws[last-1]):.2f}%")


if __name__ == "__main__":
    main()
