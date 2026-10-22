#!/usr/bin/env python3
"""First checker: rebuild each witness and test every four-position set.

Usage: check_exhaustive.py WITNESSES.json

Follows Definitions 1 and 3 of Dvořáková and Hendrychová, "String attractors
of Rote sequences" (DMTCS 26:3, 2024). Positions are counted from 0, as in
the paper. For each witness it

  1. rebuilds the prefixes w_1, ..., w_n from the directive sequences, each
     closure as the shortest word fixed by R or E that has the given prefix,
     and compares the last with the word and all with the listed lengths;
  2. checks that the listed five positions form a string attractor;
  3. tries every set of four positions and checks that none is an attractor.

A set of fewer than four positions that were an attractor would stay one
after adding positions, so step 3 also excludes every smaller set.
Standard library only; imports nothing from the other checker.
"""

import itertools
import json
import math
import sys


def require(condition, message):
    if not condition:
        raise ValueError(message)


def image(letter, antimorphism):
    """The letter that R or E puts at the mirror position."""
    if antimorphism == "R":
        return letter
    return "1" if letter == "0" else "0"


def closure(prefix, antimorphism):
    """The shortest word fixed by the antimorphism that starts with prefix.

    For a length L between len(prefix) and 2*len(prefix), a fixed word of
    length L with this prefix exists exactly when the letters forced on the
    prefix positions and on their mirror images (position i and L-1-i) agree.
    Every position is forced, since it or its mirror lies in the prefix.
    Length 2*len(prefix) always works, so the first consistent L is the answer.
    """
    require(antimorphism in ("E", "R"), "unknown antimorphism " + repr(antimorphism))
    require(set(prefix) <= {"0", "1"}, "the word is not binary")
    for length in range(len(prefix), 2 * len(prefix) + 1):
        letters = [None] * length
        consistent = True
        for i, letter in enumerate(prefix):
            for position, value in ((i, letter), (length - 1 - i, image(letter, antimorphism))):
                if letters[position] not in (None, value):
                    consistent = False
                    break
                letters[position] = value
            if not consistent:
                break
        if consistent:
            require(None not in letters, "an unforced position")
            return "".join(letters)
    raise ValueError("no closure found")


def prefixes(delta, theta):
    require(len(delta) == len(theta) > 0, "directive sequences of different lengths")
    words = [""]
    for letter, antimorphism in zip(delta, theta):
        words.append(closure(words[-1] + letter, antimorphism))
    return words


def coverages(word):
    """For each distinct nonempty factor, the set of positions (as a bit mask)
    lying in at least one of its occurrences. A set of positions attracts the
    factor exactly when it meets this set."""
    cover = {}
    for start in range(len(word)):
        mask = 0
        for end in range(start + 1, len(word) + 1):
            mask |= 1 << (end - 1)
            factor = word[start:end]
            cover[factor] = cover.get(factor, 0) | mask
    return cover


def is_attractor(cover, positions):
    selected = 0
    for p in positions:
        selected |= 1 << p
    return all(selected & mask for mask in cover.values())


def minimum_by_enumeration(word):
    """Smallest attractor size, by trying all sets in increasing size."""
    cover = coverages(word)
    for size in range(len(word) + 1):
        if any(is_attractor(cover, s) for s in itertools.combinations(range(len(word)), size)):
            return size
    raise ValueError("no attractor at all")


def paper_controls():
    """The paper's own examples, recomputed."""
    example2 = [("000", "R", "000"), ("000", "E", "000111"),
                ("0001", "R", "0001000"), ("0001", "E", "000111"),
                ("01101", "R", "0110110"), ("01101", "E", "01101001")]
    for seed, antimorphism, expected in example2:
        require(closure(seed, antimorphism) == expected, "Example 2 is not reproduced")
    thue_morse = ["", "0", "01", "0110", "01101001", "0110100110010110"]
    require(prefixes("01111", "RERER") == thue_morse, "Example 4 is not reproduced")
    require(is_attractor(coverages("010010"), [1, 3]), "the attractor {1,3} of 010010 fails")
    require(minimum_by_enumeration("010010") == 2, "010010 should need two positions")
    return "Example 2 (6 closures), Example 4 (Thue-Morse prefixes), attractor {1,3} of 010010"


def check_witness(witness):
    require(set(witness) == {"delta", "theta", "prefix_lengths", "word", "attractor"},
            "unexpected witness fields")
    words = prefixes(witness["delta"], witness["theta"])
    word = witness["word"]
    require(word == words[-1], "the word is not the last closure")
    require(witness["prefix_lengths"] == [len(w) for w in words],
            "the listed prefix lengths are not those of the closures")
    require(word == word[::-1] or word == "".join(image(c, "E") for c in reversed(word)),
            "the word is not a pseudopalindrome")
    positions = witness["attractor"]
    require(len(positions) == 5 and len(set(positions)) == 5
            and all(type(p) is int and 0 <= p < len(word) for p in positions),
            "the attractor is not five distinct positions of the word")
    cover = coverages(word)
    require(is_attractor(cover, positions), "the five positions miss a factor")
    tried = 0
    for four in itertools.combinations(range(len(word)), 4):
        tried += 1
        require(not is_attractor(cover, four), "a four-position attractor exists: %s" % (four,))
    require(tried == math.comb(len(word), 4), "not every four-set was tried")
    return "delta=%s theta=%s: length %d, %d distinct factors, attractor %s, all %d four-sets fail" % (
        witness["delta"], witness["theta"], len(word), len(cover), positions, tried)


def main():
    require(len(sys.argv) == 2, "usage: check_exhaustive.py WITNESSES.json")
    with open(sys.argv[1], encoding="utf-8") as handle:
        data = json.load(handle)
    require(set(data) == {"witnesses"} and data["witnesses"], "no witnesses")
    print("controls: " + paper_controls())
    for witness in data["witnesses"]:
        print(check_witness(witness))
    print("check_exhaustive: VERIFIED, every witness has smallest attractor size 5")


if __name__ == "__main__":
    try:
        main()
    except (ValueError, TypeError, KeyError, OSError, json.JSONDecodeError) as error:
        print("check_exhaustive: REJECTED: %s" % error)
        sys.exit(1)
