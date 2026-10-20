import Uniform5.CompositionCaseBCanonicalCycle
import Mathlib.Data.List.Permutation

/-! Small partner cycles retain dihedral order. These enumerations are
proved in the kernel; no computational assumption is used. -/
namespace Uniform5.CaseB
theorem three_dihedral_of_perm {α : Type} {a b c : α} {l : List α} (h : l.Perm [a,b,c]) :
 l.IsRotated [a,b,c] ∨ l.reverse.IsRotated [a,b,c] := by
 have hh := List.mem_permutations'.mpr h
 simp only [List.permutations', List.permutations'Aux, List.flatMap_cons,
   List.flatMap_nil, List.map_cons, List.map_nil, List.append_nil,
   List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hh
 rcases hh with rfl | rfl | rfl | rfl | rfl | rfl
 all_goals first | exact Or.inl ⟨0, rfl⟩ | exact Or.inl ⟨1, rfl⟩ |
   exact Or.inl ⟨2, rfl⟩ | exact Or.inr ⟨0, rfl⟩ | exact Or.inr ⟨1, rfl⟩ |
   exact Or.inr ⟨2, rfl⟩

/-- With three equal entries every four-cycle permutation is a rotation. -/
theorem repeated_four_rotation_of_perm {α : Type} {a b : α} {l : List α}
    (h : l.Perm [a,b,b,b]) : l.IsRotated [a,b,b,b] := by
  have hh := List.mem_permutations'.mpr h
  simp only [List.permutations', List.permutations'Aux, List.flatMap_cons,
    List.flatMap_nil, List.map_cons, List.map_nil, List.append_nil,
    List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ⟨0, rfl⟩ | exact ⟨1, rfl⟩ | exact ⟨2, rfl⟩ | exact ⟨3, rfl⟩

/-- The exact partner-tail list upgrades multiplicity data to cyclic labels. -/
theorem partnerTail_dihedral {m : ℕ} {tail l : List ℕ}
    (ht : PartnerTail m tail) (hp : l.Perm (m :: tail)) :
    l.IsRotated (m :: tail) ∨ l.reverse.IsRotated (m :: tail) := by
  rcases ht with ht | ht
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · exact three_dihedral_of_perm hp
    · exact Or.inl (repeated_four_rotation_of_perm hp)
    · exact three_dihedral_of_perm hp
  · rcases ht.2 with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;>
      exact three_dihedral_of_perm hp

/-- The W list has exactly the same permitted partner tails. -/
theorem wListed_paired_dihedral {p1 : P1} {n : PolygonParameter}
    {m : ℕ} {tail l : List ℕ}
    (hw : WListed p1 n (.pairedI (some (m : ℝ)) tail))
    (hp : l.Perm (m :: tail)) :
    l.IsRotated (m :: tail) ∨ l.reverse.IsRotated (m :: tail) := by
  apply partnerTail_dihedral (m := m) _ hp
  rcases hw with ⟨_, ht⟩ | ⟨k, he, hb, _⟩
  · exact Or.inl ht
  · have hk : m = k := by exact_mod_cast Option.some.inj he
    subst k
    exact Or.inr hb

end Uniform5.CaseB
