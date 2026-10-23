#!/usr/bin/env python3
"""Check a literal strategy DAG without importing a solver or another checker.

Written independently from certificate-format.md and Havet--Zhu, INRIA
report 7646, Introduction (ordinary and greedy colouring game definitions).
Each accepted arc colours exactly one vertex, so local strategy obligations
and matching terminal outcomes prove the root outcome by finite induction.

Stopping on the first blocked vertex preserves the winner: its neighbours'
colours never disappear, so it cannot subsequently receive a colour <= k.
For greedy play this is equivalent to forcing the unrestricted game's final
maximum colour above k. Ordered play is the control variant in the format.
"""

import argparse
import json
import sys


class InvalidCertificate(ValueError):
    """The input fails a structural or game-theoretic obligation."""


def require(condition, message):
    if not condition:
        raise InvalidCertificate(message)


def integer_between(value, low, high):
    # JSON booleans are not integers, despite Python's bool/int inheritance.
    return type(value) is int and low <= value <= high


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, "duplicate JSON object key: " + repr(key))
        result[key] = value
    return result


def reject_constant(value):
    raise InvalidCertificate("non-JSON numeric constant: " + value)


def load_certificate(path):
    with open(path, encoding="utf-8") as stream:
        return json.load(stream, object_pairs_hook=unique_object,
                         parse_constant=reject_constant)


def verify(certificate):
    """Return a small report, or raise InvalidCertificate on any failed check."""
    fields = {"version", "n", "edges", "k", "game", "first", "winner",
              "ordered", "nodes"}
    require(type(certificate) is dict, "certificate must be a JSON object")
    require(set(certificate) == fields, "incorrect certificate fields")
    require(integer_between(certificate["version"], 1, 1),
            "unsupported certificate version")
    n = certificate["n"]
    k = certificate["k"]
    require(integer_between(n, 1, 15), "n must be an integer in 1..15")
    require(integer_between(k, 1, n), "k must be an integer in 1..n")
    game = certificate["game"]
    first = certificate["first"]
    winner = certificate["winner"]
    require(type(game) is str and game in ("ordinary", "greedy"),
            "unknown game")
    require(type(first) is str and first in ("Alice", "Bob"),
            "unknown first player")
    require(type(winner) is str and winner in ("Alice", "Bob"),
            "unknown winner")
    require(type(certificate["ordered"]) is bool, "ordered must be boolean")
    ordered = certificate["ordered"]

    edges = certificate["edges"]
    require(type(edges) is list, "edges must be a list")
    seen_edges = set()
    neighbours = [set() for _ in range(n)]
    for edge in edges:
        require(type(edge) is list and len(edge) == 2, "malformed edge")
        u, v = edge
        require(integer_between(u, 0, n - 1) and
                integer_between(v, 0, n - 1) and u < v,
                "edge must satisfy 0 <= u < v < n")
        require((u, v) not in seen_edges, "duplicate edge")
        seen_edges.add((u, v))
        neighbours[u].add(v)
        neighbours[v].add(u)

    nodes = certificate["nodes"]
    require(type(nodes) is dict, "nodes must be an object")
    states = {}
    moves = {}
    for key, supplied in nodes.items():
        require(type(key) is str, "state key must be a string")
        parts = key.split(",")
        require(len(parts) == n, "incorrect state length: " + repr(key))
        # Canonical decimal spelling makes each mathematical state one key.
        colour_names = {str(colour): colour for colour in range(k + 1)}
        require(all(part in colour_names for part in parts),
                "invalid or noncanonical state colour: " + repr(key))
        state = tuple(colour_names[part] for part in parts)
        require(all(state[u] == 0 or state[v] == 0 or state[u] != state[v]
                    for u, v in seen_edges), "improper colouring: " + key)
        require(type(supplied) is list, "node moves must be a list: " + key)
        parsed_moves = []
        for move in supplied:
            require(type(move) is list and len(move) == 2,
                    "malformed move at " + key)
            vertex, colour = move
            require(integer_between(vertex, 0, n - 1) and
                    integer_between(colour, 1, k),
                    "move outside vertex/colour range at " + key)
            parsed_moves.append((vertex, colour))
        require(len(set(parsed_moves)) == len(parsed_moves),
                "duplicate move at " + key)
        states[key] = state
        moves[key] = parsed_moves

    root = ",".join("0" for _ in range(n))
    require(root in states, "missing root state")
    pending = [root]
    reached = {root}
    arc_count = 0
    terminal_count = 0
    while pending:
        key = pending.pop()
        state = states[key]
        listed = moves[key]
        empty = [v for v in range(n) if state[v] == 0]
        available = {
            v: [c for c in range(1, k + 1)
                if all(state[u] != c for u in neighbours[v])]
            for v in empty
        }
        terminal_winner = None
        if not empty:
            terminal_winner = "Alice"
        elif any(not available[v] for v in empty):
            terminal_winner = "Bob"
        if terminal_winner is not None:
            require(not listed, "terminal state has moves: " + key)
            require(terminal_winner == winner,
                    "terminal outcome contradicts claimed winner: " + key)
            terminal_count += 1
            continue

        selectable = empty[:1] if ordered else empty
        legal = set()
        for vertex in selectable:
            colours = available[vertex]
            if game == "greedy":
                colours = colours[:1]
            legal.update((vertex, colour) for colour in colours)
        depth = n - len(empty)
        player = first if depth % 2 == 0 else (
            "Bob" if first == "Alice" else "Alice")
        if player == winner:
            require(len(listed) == 1 and listed[0] in legal,
                    "winner must select exactly one legal move: " + key)
        else:
            require(set(listed) == legal,
                    "opponent moves are not exactly all legal moves: " + key)
        for vertex, colour in listed:
            successor = list(state)
            successor[vertex] = colour
            next_key = ",".join(map(str, successor))
            require(next_key in states, "missing successor state: " + next_key)
            arc_count += 1
            if next_key not in reached:
                reached.add(next_key)
                pending.append(next_key)
    require(len(reached) == len(states), "certificate contains unreachable states")
    return {"accepted": True, "game": game, "first": first,
            "winner": winner, "n": n, "k": k, "ordered": ordered,
            "nodes": len(reached), "arcs": arc_count,
            "terminals": terminal_count}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificate", help="literal strategy DAG JSON file")
    args = parser.parse_args()
    try:
        report = verify(load_certificate(args.certificate))
    except (InvalidCertificate, OSError, UnicodeError, ValueError,
            RecursionError) as error:
        print(json.dumps({"accepted": False, "error": str(error)}),
              file=sys.stderr)
        return 1
    print(json.dumps(report, sort_keys=True))
    return 0


if __name__ == "__main__":
    sys.exit(main())
