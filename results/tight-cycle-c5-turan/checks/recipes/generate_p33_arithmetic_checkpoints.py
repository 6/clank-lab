#!/usr/bin/env python3
"""Quote bounded rangeCheck proof files; never change arithmetic semantics.

Default ownership is the remaining clean-validation indices 30208..40546.
Other owners may select disjoint global 64-class shard numbers explicitly.
The source of a given shard is independent of the selected ownership range.
"""
import argparse
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
COUNT, WIDTH = 40547, 64
TOTAL = (COUNT + WIDTH - 1) // WIDTH
NS = "TightCycleC5.Bridge.P33Arithmetic"


def shard_source(shard):
    if not 0 <= shard < TOTAL:
        raise ValueError("global shard number outside 0..633")
    start = shard * WIDTH
    count = min(WIDTH, COUNT - start)
    return f'''import P33ArithmeticRanges

/-! Exact unchanged rangeCheck on class indices [{start}, {start + count}).
This is one bounded native evaluation, not an in-flight evaluator checkpoint. -/
namespace {NS}
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checkpoint_shard{shard} : rangeCheck {start} {count} = true := by
  native_decide

#print axioms checkpoint_shard{shard}
end {NS}
'''


def sources(first=472, stop=634):
    if not 0 <= first < stop <= TOTAL:
        raise ValueError("require 0 <= first < stop <= 634")
    outputs, units, groups = {}, [], {}
    for shard in range(first, stop):
        start, count = WIDTH * shard, min(WIDTH, COUNT - WIDTH * shard)
        name = f"P33ArithmeticCheckpointShard{shard}.lean"
        text = shard_source(shard)
        outputs[name] = text
        units.append({
            "shard": shard, "module": name[:-5],
            "theorem": f"{NS}.checkpoint_shard{shard}",
            "statement": f"rangeCheck {start} {count} = true",
            "start": start, "count": count, "stop": start + count,
            "source_sha256": hashlib.sha256(text.encode()).hexdigest(),
            "native_axiom": f"checkpoint_shard{shard}._native.native_decide.ax_1_1",
        })
        groups.setdefault(start // 512, []).append(shard)
    old_groups = []
    for old, shards in sorted(groups.items()):
        start, count = old * 512, min(512, COUNT - old * 512)
        full = shards == list(range(start // WIDTH, (start + count + WIDTH - 1) // WIDTH))
        old_groups.append({
            "old_shard": old, "start": start, "count": count,
            "original_range_statement": f"rangeCheck {start} {count} = true",
            "selected_micro_shards": shards, "complete_old_range": full,
            "assembly": "Parent-owned standard kernel rangeCheck_add lemma; no assembly generated here",
        })
    plan = {
        "schema": "p33-range-checkpoint-plan-v1",
        "scope": "Bounded exact arithmetic proof units; no Core/Finite/data/guard changes",
        "global_class_count": COUNT, "global_micro_shard_count": TOTAL,
        "width": WIDTH, "first_shard": first, "stop_shard": stop,
        "start": first * WIDTH, "stop": min(stop * WIDTH, COUNT),
        "classes": min(stop * WIDTH, COUNT) - first * WIDTH,
        "units": units, "old_range_groups": old_groups,
        "lean_options": ["-j", "1", "-M12000"],
        "hard_wall_seconds": 590,
        "checkpoint": "Complete guarded source/object/dependency receipt and compact proof archive, atomically renamed under scratch/keep after every finished unit",
        "resume": "Restore verified completed proof objects only; internal native_decide state is never resumable",
    }
    outputs[f"p33-arithmetic-checkpoint-range-plan-{first}-{stop}.json"] = (
        json.dumps(plan, indent=2, sort_keys=True) + "\n")
    return outputs


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--first", type=int, default=472)
    parser.add_argument("--stop", type=int, default=634)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    outputs = sources(args.first, args.stop)
    for name, text in outputs.items():
        path = HERE / name
        if args.check:
            if not path.exists() or path.read_bytes() != text.encode():
                raise SystemExit(f"source bytes differ: {name}")
        else:
            path.write_bytes(text.encode())
    print(json.dumps({
        "status": "SOURCE_MATCH" if args.check else "QUOTED_NOT_PROVED",
        "first": args.first, "stop": args.stop,
        "units": args.stop - args.first,
        "classes": min(args.stop * WIDTH, COUNT) - args.first * WIDTH,
        "source_manifest_sha256": hashlib.sha256(json.dumps(
            {name: hashlib.sha256(text.encode()).hexdigest()
             for name, text in outputs.items()}, sort_keys=True).encode()).hexdigest(),
    }, sort_keys=True))


if __name__ == "__main__":
    main()
