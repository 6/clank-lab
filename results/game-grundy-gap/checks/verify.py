#!/usr/bin/env python3
"""Check the graph, two strategy certificates, semantic controls, and figures."""

import copy
import gzip
import importlib.util
import json
from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parent.parent
sys.dont_write_bytecode = True
EDGES = [
    [0, 3], [0, 5], [0, 7], [0, 8],
    [1, 4], [1, 6], [1, 8], [1, 9], [1, 10],
    [2, 5], [2, 6], [2, 7], [2, 9], [2, 10],
    [3, 7],
    [4, 6], [4, 8], [4, 9], [4, 10],
    [5, 7], [5, 8], [5, 10],
    [6, 9], [6, 10], [7, 9], [8, 10], [9, 10],
]
EXPECTED = {
    "ordinary": {"winner": "Alice", "nodes": 108669,
                 "arcs": 216995, "terminals": 2800},
    "greedy": {"winner": "Bob", "nodes": 5594,
               "arcs": 6730, "terminals": 2010},
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def load_module(name):
    spec = importlib.util.spec_from_file_location(name, ROOT / "checks" / (name + ".py"))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def read_json(raw, independent):
    return json.loads(raw, object_pairs_hook=independent.unique_object,
                      parse_constant=independent.reject_constant)


def check_graph(graph):
    require(type(graph) is dict and
            set(graph) == {"n", "edges", "k", "first", "ordered"},
            "incorrect graph data fields")
    require(type(graph["n"]) is int and graph["n"] == 11, "expected 11 vertices")
    require(type(graph["k"]) is int and graph["k"] == 5, "expected palette 1..5")
    require(graph["first"] == "Alice", "Alice must move first")
    require(graph["ordered"] is False, "vertex choice must be unrestricted")
    edges = graph["edges"]
    require(type(edges) is list and all(
        type(edge) is list and len(edge) == 2 and
        all(type(vertex) is int for vertex in edge) for edge in edges),
        "edges must be pairs of integer vertices")
    require(edges == EDGES and len(edges) == 27, "graph differs from the stated graph")


def corruptions(certificate):
    """Modify semantic proof obligations, after all input binding checks."""
    winner = certificate["winner"]
    bad = copy.deepcopy(certificate)
    for state, moves in bad["nodes"].items():
        depth = sum(int(color) != 0 for color in state.split(","))
        player = "Alice" if depth % 2 == 0 else "Bob"
        if player != winner and moves:
            moves.pop()
            break
    else:
        raise ValueError("no opponent reply available to corrupt")
    yield "omitted-opponent-reply", bad

    bad = copy.deepcopy(certificate)
    bad["winner"] = "Bob" if winner == "Alice" else "Alice"
    yield "flipped-outcome", bad

    bad = copy.deepcopy(certificate)
    for state, moves in bad["nodes"].items():
        if sum(int(color) != 0 for color in state.split(",")) % 2 == 0 and moves:
            moves[0] = [0, 0]
            break
    else:
        raise ValueError("no Alice move available to corrupt")
    yield "illegal-Alice-move", bad

    bad = copy.deepcopy(certificate)
    require([0, 1] not in bad["edges"], "edge control already present")
    bad["edges"].append([0, 1])
    yield "changed-edge", bad

    bad = copy.deepcopy(certificate)
    bad["first"] = "Bob"
    yield "swapped-starter", bad

    bad = copy.deepcopy(certificate)
    bad["nodes"][",".join(["0"] * certificate["n"])] = []
    yield "internal-node-as-leaf", bad

    bad = copy.deepcopy(certificate)
    for moves in bad["nodes"].values():
        if not moves:
            moves.append([0, 1])
            break
    else:
        raise ValueError("no terminal available to corrupt")
    yield "terminal-with-move", bad


def expected_rejection(checker_index, game, kind):
    """Require a semantic rejection, not an unrelated parser or runtime error."""
    if checker_index == 0:
        if kind == "terminal-with-move":
            return "false terminal"
        if game == "ordinary":
            return "winner move" if kind in (
                "illegal-Alice-move", "internal-node-as-leaf") else "opponent coverage"
        return "opponent coverage" if kind in (
            "omitted-opponent-reply", "illegal-Alice-move",
            "internal-node-as-leaf") else "winner move"
    if kind == "illegal-Alice-move":
        return "move outside vertex/colour range at "
    if kind == "changed-edge":
        return "improper colouring: "
    if kind == "terminal-with-move":
        return "terminal state has moves: "
    selects_one = ((game == "ordinary" and kind == "internal-node-as-leaf") or
                   (game == "greedy" and kind in ("flipped-outcome", "swapped-starter")))
    if selects_one:
        return "winner must select exactly one legal move: "
    return "opponent moves are not exactly all legal moves: "


def main():
    checkers = [load_module("check"), load_module("check_independent")]
    independent = checkers[1]
    graph = read_json((ROOT / "data" / "graph.json").read_bytes(), independent)
    check_graph(graph)
    print("PASS graph: 11 vertices, 27 edges; palette 1..5; Alice first; unrestricted vertex choice")
    rejected = 0
    for game, expected in EXPECTED.items():
        with gzip.open(ROOT / "data" / (game + "-k5.json.gz"), "rb") as stream:
            certificate = read_json(stream.read(), independent)
        for key, value in graph.items():
            require(certificate[key] == value, "certificate differs from graph data: " + key)
        require(certificate["game"] == game, "incorrect game")
        require(certificate["winner"] == expected["winner"], "incorrect claimed winner")
        reports = [checker.verify(certificate) for checker in checkers]
        require(reports[0] == {"accepted": True, "winner": expected["winner"],
                               "nodes": expected["nodes"]}, "first checker report differs")
        expected_report = dict(expected, accepted=True, game=game, first="Alice",
                               n=11, k=5, ordered=False)
        require(reports[1] == expected_report, "independent checker report differs")
        for kind, bad in corruptions(certificate):
            for checker_index, checker in enumerate(checkers):
                rejection_type = ValueError if checker_index == 0 else independent.InvalidCertificate
                try:
                    checker.verify(bad)
                except rejection_type as error:
                    require(type(error) is rejection_type,
                            "unexpected exception type for " + kind)
                    require(str(error).startswith(expected_rejection(checker_index, game, kind)),
                            "unexpected rejection reason for " + kind + ": " + str(error))
                    rejected += 1
                else:
                    raise ValueError("semantic corruption accepted: " + game + "/" + kind)
        print("PASS {}: {}; {:,} states, {:,} arcs, {:,} terminals (both checkers)".format(
            game, expected["winner"], expected["nodes"], expected["arcs"], expected["terminals"]))
    require(rejected == 28, "incorrect semantic rejection count")
    print("PASS semantic corruptions: 28 rejections (7 corruptions x 2 games x 2 checkers)")
    load_module("figure").check_figures(graph)
    print("PASS figures: SVG and TikZ match graph.json")
    load_module("exact_values").verify(graph, checkers)
    print("PASS conclusion: chi_g(G) = 5 and Gamma_g(G) = 6")


if __name__ == "__main__":
    main()
