import Uniform5.CompositionCaseBPartnerConfigurations
import Mathlib.Data.List.Rotate
import Mathlib.Data.List.Lex

/-! Canonicalization preserves cyclic order up to reversal. Sorting all
parameters would preserve the radius but could change the fan, so the
finite minimum is taken only over the actual dihedral orbit. -/
noncomputable section
namespace Uniform5.CaseB
open Set

noncomputable def cycleVariants (c : List ℕ) : Finset (List ℕ) :=
  (((List.range (c.length + 1)).map c.rotate) ++
    ((List.range (c.reverse.length + 1)).map c.reverse.rotate)).toFinset

theorem mem_cycleVariants {c d : List ℕ} :
    d ∈ cycleVariants c ↔ c.IsRotated d ∨ c.reverse.IsRotated d := by
  simp only [cycleVariants, List.mem_toFinset, List.mem_append,
    ← List.isRotated_iff_mem_map_range]

/-- Every finite cycle has a canonical rotation or reflected rotation,
without permuting its cyclic adjacency data. -/
theorem exists_canonicalCycle_dihedral (c : List ℕ) :
    ∃ d, (c.IsRotated d ∨ c.reverse.IsRotated d) ∧ CanonicalCycle d := by
  classical
  have hc : c ∈ cycleVariants c := mem_cycleVariants.mpr (Or.inl (List.IsRotated.refl c))
  obtain ⟨d, hd, hmin⟩ := (cycleVariants c).exists_min_image id ⟨c, hc⟩
  have hrel := mem_cycleVariants.mp hd
  refine ⟨d, hrel, ?_⟩
  intro i _
  have hrot : d.rotate i ∈ cycleVariants c := by
    apply mem_cycleVariants.mpr
    rcases hrel with h | h
    · exact Or.inl (h.trans ⟨i, rfl⟩)
    · exact Or.inr (h.trans ⟨i, rfl⟩)
  have hrev : d.reverse.rotate i ∈ cycleVariants c := by
    apply mem_cycleVariants.mpr
    rcases hrel with h | h
    · exact Or.inr (h.reverse.trans ⟨i, rfl⟩)
    · left
      have hh : c.IsRotated d.reverse := by simpa using h.reverse
      exact hh.trans ⟨i, rfl⟩
  exact ⟨eq_or_lt_of_le (hmin _ hrot), eq_or_lt_of_le (hmin _ hrev)⟩

/-- The canonical representative has precisely the original multiplicities
as well as its cyclic order, so the exact radius and closure transfer. -/
theorem exists_canonicalCycle_perm (c : List ℕ) :
    ∃ d, c.Perm d ∧ (c.IsRotated d ∨ c.reverse.IsRotated d) ∧ CanonicalCycle d := by
  obtain ⟨d, hd, hc⟩ := exists_canonicalCycle_dihedral c
  refine ⟨d, ?_, hd, hc⟩
  rcases hd with h | h
  · exact h.perm
  · exact (List.reverse_perm c).symm.trans h.perm

end Uniform5.CaseB
