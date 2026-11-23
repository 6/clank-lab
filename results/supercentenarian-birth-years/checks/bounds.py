"""Verify the six sharp common-window bounds using integer minimum-cost flows."""
import csv

import networkx as nx


def check(work):
    with (work / "registration-totals.csv").open() as stream:
        registrations = {row["registration"]: int(row["records"]) for row in csv.DictReader(stream)}
    with (work / "year-totals.csv").open() as stream:
        years = {int(row["year"]): int(row["records"]) for row in csv.DictReader(stream)}
    if sum(registrations.values()) != sum(years.values()) or sum(years.values()) != 697:
        raise ValueError("inconsistent US margins")

    # States with the same registration date have identical cell costs.
    # Any integral allocation to a date can be split among its state slots.
    graph = nx.DiGraph()
    for registration, count in registrations.items():
        graph.add_node(registration, demand=-count)
    for year, count in years.items():
        graph.add_node(year, demand=count)
    for registration in registrations:
        for year in years:
            offset = year - int(registration) if registration else None
            early = offset is not None and -60 <= offset <= 1
            eligible = offset is not None and -60 <= offset <= 60
            graph.add_edge(registration, year, early=int(early), eligible=int(eligible))

    # The ratio endpoints p/q are attained exactly when the appropriate
    # extremum of q*early - p*eligible equals zero. Eligibility is positive.
    objectives = [
        ("minimum early count", 1, 0, 487), ("negative maximum early count", -1, 0, -636),
        ("minimum eligible count", 0, 1, 668), ("negative maximum eligible count", 0, -1, -690),
        ("minimum share 487/685", 685, -487, 0), ("maximum share 636/673", -673, 636, 0),
    ]
    for label, early_cost, eligible_cost, expected in objectives:
        for _, _, edge in graph.edges(data=True):
            edge["weight"] = early_cost * edge["early"] + eligible_cost * edge["eligible"]
        actual, _ = nx.network_simplex(graph)
        if actual != expected:
            raise ValueError(f"{label}: expected {expected}, got {actual}")
    print("Verified six sharp common-window bounds from the public source margins.")
