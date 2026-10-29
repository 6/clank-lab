#!/usr/bin/env python3
"""Reproduce the literal MSW rows; no discovery or graph computation."""
import argparse
import hashlib
import json
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent
INPUT = HERE.parent / "data/msw-input.json"


def render():
    raw = INPUT.read_bytes()
    rows = [[Fraction(x) for x in row] for row in json.loads(raw)]
    assert len(rows) == 40 and all(len(row) == 21 for row in rows)
    assert all(row[:2] == [1, 100 if i < 20 else -100] for i, row in enumerate(rows))
    def lit(x):
        return str(x.numerator) if x.denominator == 1 else f"({x.numerator} / {x.denominator})"
    tail = ",\n    ".join("![" + ", ".join(map(lit, row[2:])) + "]" for row in rows)
    prefix = f'''import ProductCells

/- Literal transcription generated from the frozen source input.
   msw-input.json SHA256: {hashlib.sha256(raw).hexdigest()}
   The generator checks all 840 entries, including the factored first two
   columns. No graph or diameter fact is asserted by this transcription. -/
namespace ADKZPricing
open Matrix Finset
noncomputable section

def mswTail : Matrix (Fin 40) (Fin 19) ℚ :=
  ![{tail}]

def mswSource : Matrix (Fin 40) (Fin 21) ℚ :=
  fun i => Fin.cons 1 (Fin.cons (if i.val < 20 then 100 else -100) (mswTail i))

def mswMinus : Fin 21 → ℚ := Fin.cons 1 (Fin.cons (-1 / 100) (fun _ => 0))
def mswPlus : Fin 21 → ℚ := Fin.cons 1 (Fin.cons (1 / 100) (fun _ => 0))

theorem msw_origin_strict (i : Fin 40) : 0 < mswSource i 0 := by
  norm_num [mswSource]

theorem msw_minus_slacks (i : Fin 40) :
    mswSource i ⬝ᵥ mswMinus = if i.val < 20 then 0 else 2 := by
  by_cases h : i.val < 20 <;>
    norm_num [mswSource, mswMinus, dotProduct, Fin.sum_univ_succ, h]

theorem msw_plus_slacks (i : Fin 40) :
    mswSource i ⬝ᵥ mswPlus = if i.val < 20 then 2 else 0 := by
  by_cases h : i.val < 20 <;>
    norm_num [mswSource, mswPlus, dotProduct, Fin.sum_univ_succ, h]

theorem msw_endpoint_labels (i : Fin 40) :
    (mswSource i ⬝ᵥ mswMinus = 0 ↔ i.val < 20) ∧
    (mswSource i ⬝ᵥ mswPlus = 0 ↔ 20 ≤ i.val) := by
  rw [msw_minus_slacks, msw_plus_slacks]
  by_cases h : i.val < 20 <;> simp [h, Nat.not_lt.mp, Nat.le_of_not_lt]

theorem msw_endpoint_feasible :
    StarFeasible mswSource none mswMinus ∧ StarFeasible mswSource none mswPlus := by
  constructor
  · intro i
    change 0 ≤ 1 * (mswSource i ⬝ᵥ mswMinus)
    rw [one_mul, msw_minus_slacks]
    split_ifs <;> norm_num
  · intro i
    change 0 ≤ 1 * (mswSource i ⬝ᵥ mswPlus)
    rw [one_mul, msw_plus_slacks]
    split_ifs <;> norm_num

#print axioms msw_endpoint_labels
#print axioms msw_endpoint_feasible
end
end ADKZPricing
'''
    return prefix


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    target = HERE.parent / "lean/MSWSource.lean"
    rendered = render()
    if args.check:
        assert target.read_text() == rendered, "source transcription changed"
        print("all 840 source entries bound; graph discovery and endpoint distance unrun")
    else:
        target.write_text(rendered)


if __name__ == "__main__":
    main()
