"""Replay the stored searches from the Weierstrass equations using SageMath."""
import argparse
import json
from pathlib import Path
from tempfile import TemporaryDirectory

from run import search


def partition(value):
    try:
        part, count = map(int, value.split("/"))
        if 1 <= part <= count:
            return part, count
    except ValueError:
        pass
    raise argparse.ArgumentTypeError("expected K/N with 1 <= K <= N")


def records():
    data = Path(__file__).parent.parent / "data"
    for filename in ("cohort.jsonl", "additional.jsonl"):
        for line in (data / filename).read_text().splitlines():
            expected = json.loads(line)
            options = {}
            if filename == "additional.jsonl":
                cap = {37: 613, 109: 1783}.get(expected["p"], 440)
                options = dict(all_rank_two=True, ell_cap=cap, attempts=2, flag_cap=35000)
            yield expected, options


def replay(expected, options):
    label, D, p = (expected[key] for key in ("label", "D", "p"))
    with TemporaryDirectory() as temp:
        actual = search(expected["ainvs"], D, p, Path(temp), **options)
    actual["label"] = label
    if actual != expected:
        raise ValueError(f"{label}, D={D}, p={p}: regenerated record differs")
    print(f"{label}, D={D}, p={p}: {actual['verdict']}", flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--part", type=partition, default=(1, 1), metavar="K/N")
    part, count = parser.parse_args().part
    for index, (expected, options) in enumerate(records()):
        if index % count == part - 1:
            replay(expected, options)
