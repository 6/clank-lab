import R3P10

/-! # Checks run by `lake build`

The statements' exact types, small tests of the definitions, the faithfulness
of the formula and data Lean reads to the files in `../data`, and the axioms
of the main declarations. -/

open R3P10

/-! ## The statements, unfolded to the definitions -/

/-- The 3-color Ramsey number of the path on `m` vertices. -/
example (m : ℕ) : ramsey3Path m =
    sInf {n | ∀ X : Sym2 (Fin n) → Fin 3, ∃ (c : Fin 3) (p : Fin m → Fin n),
      Function.Injective p ∧ ∀ (i : ℕ) (h : i + 1 < m), X s(p ⟨i, by omega⟩, p ⟨i + 1, h⟩) = c} :=
  rfl

/-- The lower bound: the coloring `k17Col` of `K_17` has no monochromatic `P_10`. -/
example : ¬ ∃ (c : Fin 3) (p : Fin 10 → Fin 17), Function.Injective p ∧
    ∀ (i : ℕ) (h : i + 1 < 10), k17Col s(p ⟨i, by omega⟩, p ⟨i + 1, h⟩) = c :=
  K17_no_mono_P10

/-- The value, from the nine certified facts given as hypotheses. -/
example
    (h5 : UnsatWithPaths 5 3 (encode 5 0)) (h6 : UnsatWithPaths 6 4 (encode 6 3))
    (h9 : UnsatWithPaths 9 5 (encode 9 4)) (h10 : UnsatWithPaths 10 6 (encode 10 5))
    (h13 : UnsatWithPaths 13 7 (encode 13 6)) (h14 : UnsatWithPaths 14 8 (encode 14 7))
    (h17 : UnsatWithPaths 17 9 (encode 17 8))
    (hcover : UnsatWithPaths 18 10 (encode 18 9 ++ finalCubes.map negCube))
    (hcubes : ∀ c ∈ finalCubes, UnsatWithPaths 18 10 (encode 18 9 ++ cubeUnits c)) :
    ramsey3Path 10 = 18 :=
  R3_P10_eq_18_of_certs h5 h6 h9 h10 h13 h14 h17 hcover hcubes

/-- What a certified fact says: `F` together with every path clause for `P_m`
in `K_n` has no satisfying assignment. -/
example (n m : ℕ) (F : CNF) : UnsatWithPaths n m F ↔
    ∀ A : ℕ → Prop, (∀ C ∈ F, ∃ l ∈ C, LitTrue A l) →
      (∀ C, IsPathClause n m C → ∃ l ∈ C, LitTrue A l) → False :=
  Iff.rfl

/-- The base formula the cube certificates are checked against is the encoder's. -/
example : encode 18 9 = k18Base := encode_k18

/-! ## Small tests of the definitions -/

#guard (edges 4) = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
#guard (edges 18).length = 153
#guard eidx 18 0 1 = 0 && eidx 18 2 1 = 17 && eidx 18 16 17 = 152
#guard var 17 2 = 54
-- the path 0-1-2 in color 1 on K_4: edges 0 and 3
#guard pclause 4 1 [0, 1, 2] = [-2, -11]
#guard pvalid 4 3 1 [0, 1, 2] && !pvalid 4 3 1 [0, 1, 1] && !pvalid 4 3 3 [0, 1, 2] && !pvalid 4 3 1 [0, 1, 4]
-- 36 transpositions of {9, ..., 17}, the reversal of the path, the color swap
#guard (gens 18 9).length = 38
-- 10 vertex transpositions and two color swaps on K_5
#guard (gens 5 0).length = 12
#guard fixUnits 18 9 = (List.range 8).map fun t => [((3 * eidx 18 t (t + 1) + 1 : ℕ) : Int)]
#guard negCube [3, -7] = [-3, 7] && cubeUnits [3, -7] = [[3], [-7]]

/-! ## The formula and data Lean reads are the files in `../data`

`dimacs n m k` prints `encode n k` in DIMACS form; it equals every formula
file the solver reads, byte for byte. -/

#guard dimacs 5 3 0 = include_str "../data/cnf/k5p3.cnf"
#guard dimacs 6 4 3 = include_str "../data/cnf/k6p4.cnf"
#guard dimacs 9 5 4 = include_str "../data/cnf/k9p5.cnf"
#guard dimacs 10 6 5 = include_str "../data/cnf/k10p6.cnf"
#guard dimacs 13 7 6 = include_str "../data/cnf/k13p7.cnf"
#guard dimacs 14 8 7 = include_str "../data/cnf/k14p8.cnf"
#guard dimacs 17 9 8 = include_str "../data/cnf/k17p9.cnf"
#guard dimacs 18 10 9 = include_str "../data/cnf/k18p10.cnf"

#guard finalCubes.length = 15956
#guard (parseCubes cubesTxt).length = 15316 && (parseNats parentsTxt).length = 16 &&
  (parseCubes childrenTxt).length = 656

/-- The lower-bound coloring as lines `i j c`, `i < j`. -/
def k17Lines : String := Id.run do
  let mut s := ""
  for i in List.finRange 17 do
    for j in List.finRange 17 do
      if i < j then s := s ++ s!"{i} {j} {k17Col s(i, j)}\n"
  return s

#guard k17Lines = include_str "../data/k17-coloring.txt"

/-! ## Axioms

The encoding proof, the conditional value and the lower bound use only Lean's
three standard axioms. The identity `encode_k18` is evaluated natively, so it
also uses `Lean.ofReduceBool` and `Lean.trustCompiler`. -/

/-- info: 'R3P10.K18_P10_of_certs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms K18_P10_of_certs

/-- info: 'R3P10.R3_P10_eq_18_of_certs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms R3_P10_eq_18_of_certs

/-- info: 'R3P10.K17_no_mono_P10' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms K17_no_mono_P10

/-- info: 'R3P10.checkCompact_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkCompact_sound

/-- info: 'R3P10.encode_k18' depends on axioms: [propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound] -/
#guard_msgs in #print axioms encode_k18
