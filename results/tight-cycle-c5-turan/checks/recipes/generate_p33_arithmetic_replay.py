#!/usr/bin/env python3
"""Quote independent finite domains for the unchanged P33 arithmetic checker."""
import argparse
from pathlib import Path

HERE = Path(__file__).resolve().parent
COUNT, WIDTH = 40547, 512
SHARDS = (COUNT + WIDTH - 1) // WIDTH
NS = "TightCycleC5.Bridge.P33Arithmetic"
HEADER = f"namespace {NS}\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n\n"


def sources():
    files = {}
    files['P33ArithmeticReplayShardIndex.lean'] = '''import P33ArithmeticFinite

/-! Kernel-checked indexing only; no arithmetic evaluation or native axiom. -/
''' + HEADER + '''def replayShardLength (s : Fin 80) : Nat :=
  min 512 (40547 - s.val * 512)

def replayShardIndex (s : Fin 80) (j : Fin (replayShardLength s)) : Fin 40547 :=
  ⟨s.val * 512 + j.val, by
    have hs := s.isLt
    have hj := j.isLt
    simp only [replayShardLength, lt_min_iff] at hj
    omega⟩

theorem replay_shard_sizes :
    (∀ s : Fin 79, replayShardLength ⟨s.val, by omega⟩ = 512) ∧
      replayShardLength 79 = 99 := by decide +kernel

theorem replay_shard_cover (i : Fin 40547) :
    ∃ s : Fin 80, ∃ j : Fin (replayShardLength s), replayShardIndex s j = i := by
  have hi := i.isLt
  have hm := Nat.mod_lt i.val (by decide : 0 < 512)
  have hd := Nat.div_add_mod i.val 512
  let s : Fin 80 := ⟨i.val / 512, by omega⟩
  have hj : i.val % 512 < replayShardLength s := by
    simp only [replayShardLength, s, lt_min_iff]
    omega
  refine ⟨s, ⟨i.val % 512, hj⟩, ?_⟩
  apply Fin.ext
  simp only [replayShardIndex, s]
  omega

#print axioms replay_shard_sizes
#print axioms replay_shard_cover
end ''' + NS + '\n'
    for s in range(SHARDS):
        start, count = s * WIDTH, min(WIDTH, COUNT - s * WIDTH)
        if s == 0:
            files['P33ArithmeticReplayShard0.lean'] = (
                'import P33ArithmeticCheckpointFirstRange\n\n'
                '/-! Exact original first domain, from its checked short-range assembly. -/\n'
                + HEADER + '''theorem p33_arithmetic_replay_shard0 :
    ∀ j : Fin (replayShardLength 0),
      classCheck (classAt (replayShardIndex 0 j)) = true := by
  exact checkpoint_first_range

#print axioms p33_arithmetic_replay_shard0
end ''' + NS + '\n')
            continue
        micro_first = start // 64
        micro_stop = (start + count + 63) // 64
        imports = ''.join(f'import P33ArithmeticCheckpointShard{k}\n'
                          for k in range(micro_first, micro_stop))

        def checked_range(first, stop):
            if first + 1 == stop:
                return f'checkpoint_shard{first}'
            rest = sum(min(64, COUNT - k * 64) for k in range(first + 1, stop))
            return (f'(rangeCheck_add {first * 64} 64 {rest} '
                    f'checkpoint_shard{first} {checked_range(first + 1, stop)})')

        files[f'P33ArithmeticReplayShard{s}.lean'] = (
            'import P33ArithmeticReplayShardIndex\n'
            'import P33ArithmeticCheckpointRanges\n' + imports + '\n'
            f'/-! Exact original class domain [{start}, {start + count}), assembled\n'
            'from bounded native checks using kernel range concatenation. -/\n'
            + HEADER + f'''theorem p33_arithmetic_replay_shard{s} :
    ∀ j : Fin (replayShardLength {s}),
      classCheck (classAt (replayShardIndex {s} j)) = true := by
  have checked : rangeCheck {start} {count} = true :=
    {checked_range(micro_first, micro_stop)}
  intro j
  apply rangeCheck_sound {start} {count} checked
  · simp only [replayShardIndex]
    omega
  · have hj := j.isLt
    norm_num [replayShardLength] at hj
    simp only [replayShardIndex]
    omega

#print axioms p33_arithmetic_replay_shard{s}
end {NS}
''')
    imports = ''.join(f'import P33ArithmeticReplayShard{s}\n' for s in range(SHARDS))
    cases = ''.join(f'  · exact p33_arithmetic_replay_shard{s}\n' for s in range(SHARDS))
    files['P33ArithmeticReplay.lean'] = imports + '\n' + HEADER + '''theorem p33_arithmetic_replay_shards :
    ∀ s : Fin 80, ∀ j : Fin (replayShardLength s),
      classCheck (classAt (replayShardIndex s j)) = true := by
  intro s
  fin_cases s
''' + cases + '''
/-- All 40,547 exact arithmetic checks, with no additional hypothesis.
Each classCheck includes all 720 orders, lookup bounds, target quotation
and the exact signed integer inequality. Semantic row transport is separate. -/
theorem p33_arithmetic_replay :
    ∀ i : Fin 40547, classCheck (classAt i) = true := by
  intro i
  obtain ⟨s, j, rfl⟩ := replay_shard_cover i
  exact p33_arithmetic_replay_shards s j

#print axioms p33_arithmetic_replay_shards
#print axioms p33_arithmetic_replay
end ''' + NS + '\n'
    return files


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    for name, content in sources().items():
        path = HERE / name
        if args.check:
            if not path.exists() or path.read_text() != content:
                raise SystemExit(f'stale replay source: {name}')
        else:
            path.write_text(content)
    print(f'PASS replay source domains: {SHARDS} assembled ranges, {COUNT} classes; 634 bounded checks; last=99')


if __name__ == '__main__':
    main()
