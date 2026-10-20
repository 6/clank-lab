#!/usr/bin/env python3
"""Check the alphabet symmetry and finite slice cover for c_7 <= 1302.

This diagnostic does not establish the three UNSAT cap lemmas.  Those
lemmas, and the sixteen main UNSAT cases, require their proof checks.
No third-party Python packages or local data files are used.
"""

import itertools
import json
import math


def require(condition, message):
    if not condition:
        raise ValueError(message)


def lines(dimension):
    """All unordered combinatorial lines, using 3 for a wildcard."""
    result = set()
    for pattern in itertools.product(range(4), repeat=dimension):
        if 3 in pattern:
            result.add(frozenset(
                tuple(value if digit == 3 else digit for digit in pattern)
                for value in range(3)
            ))
    require(len(result) == 4 ** dimension - 3 ** dimension,
            "line enumeration has the wrong size")
    return result


def transform(point, permutation):
    """Apply the same alphabet permutation in every coordinate."""
    return tuple(permutation[value] for value in point)


def main():
    dimension, minimum = 7, 1303
    permutations = list(itertools.permutations(range(3)))
    universe = tuple(itertools.product(range(3), repeat=dimension))
    all_lines = lines(dimension)
    symmetry_checks = 0
    for permutation in permutations:
        image_points = {transform(point, permutation) for point in universe}
        require(len(image_points) == len(universe), "point map is not a bijection")
        for line in all_lines:
            image = frozenset(transform(point, permutation) for point in line)
            require(image in all_lines, "global permutation does not preserve a line")
            symmetry_checks += 1

    # Relabelling just the first coordinate is not such a symmetry.
    diagonal = frozenset(((0, 0), (1, 1), (2, 2)))
    swap = (1, 0, 2)
    changed = frozenset((swap[first], second) for first, second in diagonal)
    two_dimensional_lines = lines(2)
    require(diagonal in two_dimensional_lines, "missing diagonal control")
    require(changed not in two_dimensional_lines, "counterexample became a line")
    require(not any(line <= changed for line in two_dimensional_lines),
            "counterexample is not line-free")
    restored = frozenset((swap[first], second) for first, second in changed)
    require(restored == diagonal, "coordinate-only relabelling control failed")

    # Conditional cap chain: UNSAT at (d, K) implies c_d <= K - 1.
    # Between these dimensions, splitting a coordinate gives c_d <= 3c_(d-1).
    cap_lemma_cases = {1: 3, 4: 53, 5: 151}
    cap = {0: 1}
    lemma_inputs = {}
    for d in range(1, dimension):
        if d in cap_lemma_cases:
            lemma_inputs[d] = [cap[k] for k in range(1, d)]
            cap[d] = min(3 * cap[d - 1], cap_lemma_cases[d] - 1)
        else:
            cap[d] = 3 * cap[d - 1]
    require([cap[d] for d in range(1, dimension)] == [2, 6, 18, 52, 150, 450],
            "conditional cap chain disagrees")
    require(lemma_inputs == {1: [], 4: [2, 6, 18], 5: [2, 6, 18, 52]},
            "cap lemma uses a cap of its own or a later dimension")

    maximum = cap[dimension - 1]
    need = set(range((minimum + 2) // 3, maximum + 1))
    require(need == set(range(435, 451)), "wrong slice-size cover")
    found = set()
    sorted_profiles = set()
    triples = 0
    # Enumerate every labelled triple with entries <= 450 and total >= 1303.
    # Starting at the smallest feasible value avoids scanning impossible triples.
    for a in range(max(0, minimum - 2 * maximum), maximum + 1):
        for b in range(max(0, minimum - a - maximum), maximum + 1):
            for c in range(max(0, minimum - a - b), maximum + 1):
                counts = (a, b, c)
                old_labels = sorted(range(3), key=lambda value: (-counts[value], value))
                permutation = [None] * 3
                for new_label, old_label in enumerate(old_labels):
                    permutation[old_label] = new_label
                require(tuple(permutation) in permutations, "sorting map is not a permutation")
                new_counts = [None] * 3
                for old_label in range(3):
                    new_counts[permutation[old_label]] = counts[old_label]
                require(new_counts[0] >= new_counts[1] >= new_counts[2],
                        "sorting permutation failed")
                require(sum(new_counts) == sum(counts), "sorting changes total size")
                require(new_counts[0] in need, "feasible triple is not covered")
                found.add(new_counts[0])
                sorted_profiles.add(tuple(new_counts))
                triples += 1
    require(found == need, "slice-size cover is not exact")
    require(triples == math.comb(3 * maximum - minimum + 3, 3),
            "feasible-triple enumeration is incomplete")

    print(json.dumps({
        "verdict": "PASS",
        "dimension": dimension,
        "global_alphabet_permutations": len(permutations),
        "lines": len(all_lines),
        "line_images_checked": symmetry_checks,
        "coordinate_only_counterexample": {
            "line": sorted(diagonal),
            "image_is_line_free": sorted(changed),
            "same_swap_restores_line": True,
        },
        "cap_lemma_UNSAT_cases_required": sorted(cap_lemma_cases.items()),
        "cap_lemma_prior_cap_inputs": lemma_inputs,
        "conditional_caps_dimensions_1_through_6": [cap[d] for d in range(1, dimension)],
        "minimum_set_size": minimum,
        "largest_slice_sizes_required": sorted(need),
        "feasible_labelled_slice_triples_checked": triples,
        "distinct_sorted_slice_triples_checked": len(sorted_profiles),
        "scope": "Symmetry and cover only; UNSAT certificates checked separately.",
    }, indent=2))


if __name__ == "__main__":
    main()
