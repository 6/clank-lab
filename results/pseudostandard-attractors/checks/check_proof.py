#!/usr/bin/env python3
"""Second checker: the written proof's facts, and the minimum by a search.

Usage: check_proof.py WITNESSES.json OBSTRUCTION.json UPPER-BOUND.json

Written separately from check_exhaustive.py and importing nothing from it.
Positions are counted from 0. It checks

  1. membership: each closure is the paper's formula v x theta(v), where x is
     the longest theta-fixed suffix; the result is theta-fixed, starts with
     the seed, and no shorter theta-fixed word starts with the seed (every
     shorter extension is tried letter by letter);
  2. the lower bound for the 36-letter word: the seven factors of the
     obstruction, their complete occurrence lists, and the three disjoint
     regions, giving 2 + 1 + 2 = 5;
  3. the upper bound for the 36-letter word: every factor lying inside a gap
     between consecutive attractor positions appears in the table with an
     occurrence that contains an attractor position;
  4. for every witness, the smallest attractor size, computed by a
     branch-and-bound search over hitting sets.

Standard library only.
"""

import itertools
import json
import sys


def require(condition, message):
    if not condition:
        raise ValueError(message)


def apply(antimorphism, word):
    """R reverses; E reverses and exchanges 0 and 1 (Definition 1)."""
    reverse = word[::-1]
    if antimorphism == "R":
        return reverse
    require(antimorphism == "E", "unknown antimorphism " + repr(antimorphism))
    return reverse.translate(str.maketrans("01", "10"))


def closure(seed, antimorphism):
    """seed = v x with x the longest suffix fixed by the antimorphism; the
    closure is v x theta(v) (the remark after Definition 1)."""
    for cut in range(len(seed) + 1):
        suffix = seed[cut:]
        if apply(antimorphism, suffix) == suffix:
            return seed + apply(antimorphism, seed[:cut])
    raise ValueError("unreachable: the empty suffix is fixed")


def shortest_by_trial(seed, antimorphism, limit):
    """True when no word shorter than limit that starts with seed is fixed."""
    for extra in range(0, limit - len(seed)):
        for tail in itertools.product("01", repeat=extra):
            candidate = seed + "".join(tail)
            if apply(antimorphism, candidate) == candidate:
                return False
    return True


def occurrences(word, factor):
    return [i for i in range(len(word) - len(factor) + 1) if word.startswith(factor, i)]


def check_membership(witness):
    delta, theta = witness["delta"], witness["theta"]
    lengths = witness["prefix_lengths"]
    require(len(delta) == len(theta) == len(lengths) - 1, "lengths disagree")
    require(lengths[0] == 0, "w_0 is not the empty word")
    previous = ""
    for step, (letter, antimorphism) in enumerate(zip(delta, theta), 1):
        require(letter in "01", "a directive letter is not 0 or 1")
        seed = previous + letter
        word = closure(seed, antimorphism)
        require(apply(antimorphism, word) == word and word.startswith(seed), "bad closure")
        require(shortest_by_trial(seed, antimorphism, len(word)), "a shorter closure exists")
        require(len(word) == lengths[step] and witness["word"].startswith(word),
                "prefix w_%d is wrong" % step)
        previous = word
    require(witness["word"] == previous, "the word is not the last prefix")
    return previous


def factor_masks(word):
    """Bit mask of positions covered by the occurrences of each distinct factor."""
    masks = {}
    for i in range(len(word)):
        for j in range(i + 1, len(word) + 1):
            mask = ((1 << (j - i)) - 1) << i
            masks[word[i:j]] = masks.get(word[i:j], 0) | mask
    return masks


def smallest_attractor(word):
    """Exact minimum hitting set of the factor masks, by branch and bound:
    some position of the least-covered unhit factor must be chosen."""
    masks = sorted(set(factor_masks(word).values()), key=lambda m: bin(m).count("1"))
    best = [len(word)]

    def search(chosen, count):
        if count >= best[0]:
            return
        unhit = next((m for m in masks if not m & chosen), None)
        if unhit is None:
            best[0] = count
            return
        for p in range(len(word)):
            if unhit >> p & 1:
                search(chosen | 1 << p, count + 1)

    search(0, 0)
    return best[0]


def check_obstruction(word, data):
    require(data["word"] == word, "the obstruction is for another word")
    groups = data["groups"]
    used = set()
    total = 0
    for group in groups:
        covers = []
        for entry in group["factors"]:
            factor = entry["factor"]
            starts = occurrences(word, factor)
            require(factor and starts == entry["starts"], "occurrences of %s are not as listed" % factor)
            covers.append({p for s in starts for p in range(s, s + len(factor))})
        region = set().union(*covers)
        require(not region & used, "two regions overlap")
        used |= region
        if len(covers) == 1:
            bound = 1
        else:
            # No single position lies in all the covers, so two are needed.
            require(len(covers) >= 2 and not set.intersection(*covers), "the covers share a position")
            bound = 2
        require(group["lower_bound"] == bound, "a group's bound is misstated")
        total += bound
    require(total == 5, "the bound is not 5")
    return sum(len(g["factors"]) for g in groups)


def gaps(n, positions):
    result, previous = [], -1
    for p in sorted(positions) + [n]:
        if p - previous > 1:
            result.append([previous + 1, p - 1])
        previous = p
    return result


def check_upper_bound(word, data):
    """Every occurrence of a factor either contains an attractor position or
    lies inside a gap. So the positions form an attractor exactly when every
    factor of every gap word has an occurrence containing one of them."""
    positions = data["attractor"]
    require(data["word"] == word, "the table is for another word")
    require(data["gaps"] == gaps(len(word), positions), "the gaps are misstated")
    table = {row["factor"]: row for row in data["factors"]}
    require(len(table) == len(data["factors"]), "a factor is listed twice")
    needed = {word[i:j] for a, b in data["gaps"] for i in range(a, b + 1) for j in range(i + 1, b + 2)}
    require(set(table) == needed, "the table does not list exactly the factors inside gaps")
    for factor, row in table.items():
        start, crossed = row["start"], row["crosses"]
        require(word.startswith(factor, start), "%s does not occur at %d" % (factor, start))
        require(crossed in positions and start <= crossed < start + len(factor),
                "the occurrence of %s does not contain %d" % (factor, crossed))
    return len(table)


def direct_gap_check(word, positions):
    """The same criterion as check_upper_bound, without a table."""
    for a, b in gaps(len(word), positions):
        for i in range(a, b + 1):
            for j in range(i + 1, b + 2):
                factor = word[i:j]
                require(any(any(s <= p < s + len(factor) for p in positions)
                            for s in occurrences(word, factor)),
                        "the factor %s misses the attractor" % factor)


def main():
    require(len(sys.argv) == 4, "usage: check_proof.py WITNESSES.json OBSTRUCTION.json UPPER-BOUND.json")
    loaded = []
    for path in sys.argv[1:]:
        with open(path, encoding="utf-8") as handle:
            loaded.append(json.load(handle))
    witnesses, obstruction, upper = loaded
    first = True
    for witness in witnesses["witnesses"]:
        word = check_membership(witness)
        positions = witness["attractor"]
        require(len(set(positions)) == 5, "the attractor is not five positions")
        direct_gap_check(word, positions)
        line = "delta=%s theta=%s: closures confirmed, length %d" % (witness["delta"], witness["theta"], len(word))
        if first:
            require(upper["attractor"] == positions, "the table is for other positions")
            line += ", %d-factor obstruction gives at least 5" % check_obstruction(word, obstruction)
            line += ", %d gap factors all cross %s" % (check_upper_bound(word, upper), positions)
            first = False
        smallest = smallest_attractor(word)
        require(smallest == 5, "the smallest attractor has size %d, not 5" % smallest)
        print(line + ", smallest attractor size 5 by search")
    print("check_proof: VERIFIED")


if __name__ == "__main__":
    try:
        main()
    except (ValueError, TypeError, KeyError, IndexError, OSError, json.JSONDecodeError) as error:
        print("check_proof: REJECTED: %s" % error)
        sys.exit(1)
