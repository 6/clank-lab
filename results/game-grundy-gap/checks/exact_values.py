"""Check the clique obstruction and Alice's six-color greedy strategy."""

import copy
import gzip
import itertools
import json
from pathlib import Path


def require(condition, message):
    if not condition:
        raise ValueError(message)


def facts(graph):
    edges = {tuple(edge) for edge in graph["edges"]}
    require(graph["n"] == 11 and all(0 <= a < b < 11 for a, b in edges),
            "incorrect vertex labels")
    clique = (1, 4, 6, 9, 10)
    require(all(pair in edges for pair in itertools.combinations(clique, 2)),
            "missing clique edge")
    require(all(sum(v in edge for edge in edges) <= 5 for v in range(9)),
            "degree bound failed")


def verify(graph, checkers):
    facts(graph)
    bad = copy.deepcopy(graph)
    bad["edges"].remove([1, 4])
    high = copy.deepcopy(graph)
    high["edges"].extend([[0, 1], [0, 2]])
    shifted = copy.deepcopy(graph)
    shifted["edges"] = sorted(sorted(((a + 1) % 11, (b + 1) % 11))
                              for a, b in graph["edges"])
    for candidate in (bad, high, shifted):
        try:
            facts(candidate)
        except ValueError:
            pass
        else:
            raise ValueError("local-fact corruption accepted")
    print("PASS exact local facts: ten clique edges and degree bounds; 3 corruptions rejected")

    path = Path(__file__).resolve().parent.parent / "data/greedy-k6.json.gz"
    independent = checkers[1]
    certificate = json.loads(gzip.decompress(path.read_bytes()),
                             object_pairs_hook=independent.unique_object,
                             parse_constant=independent.reject_constant)
    for key in ("n", "edges", "first", "ordered"):
        require(certificate[key] == graph[key], "six-color certificate graph/rules mismatch")
    require(certificate["game"] == "greedy" and certificate["k"] == 6 and
            certificate["winner"] == "Alice", "incorrect six-color obligation")
    reports = [checker.verify(certificate) for checker in checkers]
    require(reports[0] == {"accepted": True, "nodes": 2223, "winner": "Alice"},
            "six-color first checker report differs")
    require(reports[1] == dict(accepted=True, n=11, game="greedy", k=6,
            first="Alice", ordered=False, winner="Alice", nodes=2223,
            arcs=3339, terminals=208), "six-color independent report differs")
    # All leaves are full: no threshold stop substitutes for unbounded play.
    require(all(moves or all(int(c) > 0 for c in state.split(","))
                for state, moves in certificate["nodes"].items()),
            "six-color certificate has an unfinished leaf")
    root = ",".join(["0"] * 11)
    after_ten = ",".join(["0"] * 10 + ["1"])
    cases = []
    def mutate(name, prefixes):
        candidate = copy.deepcopy(certificate)
        cases.append((name, candidate, prefixes))
        return candidate
    coverage = ("opponent coverage", "opponent moves are not exactly all legal moves: ")
    selection = ("winner move", "winner must select exactly one legal move: ")
    mutate("missing Bob reply", coverage)["nodes"][after_ten].pop()
    mutate("Alice pass", selection)["nodes"][root] = []
    mutate("nonleast greedy color", selection)["nodes"][root] = [[10, 2]]
    mutate("ordered play", selection)["ordered"] = True
    mutate("Bob first", coverage)["first"] = "Bob"
    mutate("unfinished leaf", coverage)["nodes"][after_ten] = []
    mutate("threshold five", ("false terminal", "move outside vertex/colour range at "))["k"] = 5
    del mutate("missing successor", ("missing state ", "missing successor state: "))["nodes"][after_ten]
    for name, candidate, prefixes in cases:
        for i, checker in enumerate(checkers):
            expected = ValueError if i == 0 else independent.InvalidCertificate
            try:
                checker.verify(candidate)
            except expected as error:
                require(type(error) is expected and str(error).startswith(prefixes[i]),
                        "unexpected semantic rejection: " + name)
            else:
                raise ValueError("six-color semantic corruption accepted: " + name)
    print("PASS greedy upper six: Alice; 2,223 states, 3,339 arcs, 208 full terminals (both checkers)")
    print("PASS greedy-six semantic corruptions: 16 rejections (8 x 2 checkers)")
