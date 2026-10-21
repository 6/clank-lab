import R3P10.Cubes

/-! # Every 3-colouring of the edges of K_18 has a monochromatic P_10

## The certified facts, as hypotheses

`K18_P10_of_certs` takes nine hypotheses, each of the form `UnsatWithPaths n m F`: the
formula `F` together with every path clause for `P_m` in `K_n` (`IsPathClause`)
has no satisfying assignment. Here `F` is `encode n k`, possibly followed by a
cube's unit clauses or the negated cubes of `finalCubes`.

The hypotheses are discharged as theorems, each checked by Lean's verified
LRAT checker from a regenerated certificate: the seven rungs and the cover in
`R3P10Ladder.lean`, the 15,956 cubes in the generated modules `R3P10Cubes.C*`,
joined in `R3P10Final.lean`, whose `R3_P10_eq_18` is the main theorem
(see `README.md`).
-/

namespace R3P10

/-- The theorem from the certified facts given as explicit hypotheses
(no axioms beyond Lean's standard ones). -/
theorem K18_P10_of_certs
    (h5 : UnsatWithPaths 5 3 (encode 5 0)) (h6 : UnsatWithPaths 6 4 (encode 6 3))
    (h9 : UnsatWithPaths 9 5 (encode 9 4)) (h10 : UnsatWithPaths 10 6 (encode 10 5))
    (h13 : UnsatWithPaths 13 7 (encode 13 6)) (h14 : UnsatWithPaths 14 8 (encode 14 7))
    (h17 : UnsatWithPaths 17 9 (encode 17 8))
    (hcover : UnsatWithPaths 18 10 (encode 18 9 ++ finalCubes.map negCube))
    (hcubes : ∀ c ∈ finalCubes, UnsatWithPaths 18 10 (encode 18 9 ++ cubeUnits c)) :
    ∀ X : Col 18, HasMonoPath 18 10 X := by
  have r5 : ∀ X : Col 5, HasMonoPath 5 3 X := rung (k := 0) (by norm_num) (Or.inl rfl) h5
  have r6 : ∀ X : Col 6, HasMonoPath 6 4 X :=
    rung (k := 3) (by norm_num) (Or.inr (mono_restrict (by norm_num) r5)) h6
  have r9 : ∀ X : Col 9, HasMonoPath 9 5 X :=
    rung (k := 4) (by norm_num) (Or.inr (mono_restrict (by norm_num) r6)) h9
  have r10 : ∀ X : Col 10, HasMonoPath 10 6 X :=
    rung (k := 5) (by norm_num) (Or.inr (mono_restrict (by norm_num) r9)) h10
  have r13 : ∀ X : Col 13, HasMonoPath 13 7 X :=
    rung (k := 6) (by norm_num) (Or.inr (mono_restrict (by norm_num) r10)) h13
  have r14 : ∀ X : Col 14, HasMonoPath 14 8 X :=
    rung (k := 7) (by norm_num) (Or.inr (mono_restrict (by norm_num) r13)) h14
  have r17 : ∀ X : Col 17, HasMonoPath 17 9 X :=
    rung (k := 8) (by norm_num) (Or.inr (mono_restrict (by norm_num) r14)) h17
  exact rung (k := 9) (by norm_num) (Or.inr (mono_restrict (by norm_num) r17))
    (unsat_of_cubes finalCubes_ne_zero hcover hcubes)

end R3P10
