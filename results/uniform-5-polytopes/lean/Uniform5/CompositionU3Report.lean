import Mathlib.Data.List.Count
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Nodup

/-! The discrete logical projection of the U3 P16 report.
The retained fields use the report's class, vertex-figure and realization
indices. Interval enclosures, timing and diagnostic logs remain in the
JSON; no geometric search states or encodings are serialized there. -/
noncomputable section
namespace Uniform5.Composition

abbrev U3Verdict := Fin 3
namespace U3Verdict
noncomputable def known : U3Verdict := 0
noncomputable def refuted : U3Verdict := 1
noncomputable def «open» : U3Verdict := 2
end U3Verdict

abbrev U3EmbeddingVerdict := Fin 4
namespace U3EmbeddingVerdict
noncomputable def «match» : U3EmbeddingVerdict := 0
noncomputable def no : U3EmbeddingVerdict := 1
noncomputable def noCount : U3EmbeddingVerdict := 2
noncomputable def undecided : U3EmbeddingVerdict := 3
end U3EmbeddingVerdict

structure U3LocalReport where
  neighbours : Nat
  unique : Nat
  valid_g : Nat
  tested_g : Nat
  forced : Bool
  failures : List (Nat × Nat)
  no_valid : List Nat

noncomputable instance : DecidableEq U3LocalReport := fun a b =>
  decidable_of_iff
    (a.neighbours = b.neighbours ∧ a.unique = b.unique ∧ a.valid_g = b.valid_g ∧
      a.tested_g = b.tested_g ∧ a.forced = b.forced ∧ a.failures = b.failures ∧
      a.no_valid = b.no_valid)
    (by cases a; cases b; simp only [U3LocalReport.mk.injEq])

/-- Logical fields of a realization row. `embedding` retains the status of
each named model; its numeric diagnostics are not equality certificates. -/
structure U3ReportRow where
  classIndex : Nat
  figureIndex : Nat
  realizationIndex : Nat
  search_states : Nat
  facets : Nat
  vf_points : Nat
  unique_root : Bool
  local_uniqueness : U3LocalReport
  known_names : List String
  embedding : List (String × U3EmbeddingVerdict)
  verdict : U3Verdict

noncomputable instance : DecidableEq U3ReportRow := fun a b =>
  decidable_of_iff
    (a.classIndex = b.classIndex ∧ a.figureIndex = b.figureIndex ∧
      a.realizationIndex = b.realizationIndex ∧ a.search_states = b.search_states ∧
      a.facets = b.facets ∧ a.vf_points = b.vf_points ∧ a.unique_root = b.unique_root ∧
      a.local_uniqueness = b.local_uniqueness ∧ a.known_names = b.known_names ∧
      a.embedding = b.embedding ∧ a.verdict = b.verdict)
    (by cases a; cases b; simp only [U3ReportRow.mk.injEq])

def U3ReportRow.index (r : U3ReportRow) : Nat × Nat × Nat :=
  (r.classIndex, r.figureIndex, r.realizationIndex)

def U3ReportRow.signatureIndex (r : U3ReportRow) : Nat × Nat :=
  (r.classIndex, r.figureIndex)

end Uniform5.Composition
