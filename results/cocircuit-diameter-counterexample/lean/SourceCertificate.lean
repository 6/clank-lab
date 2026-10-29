import CellEdges
import OrderedSource

namespace ADKZPricing
open Matrix Finset
noncomputable section
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- Exact finite facts checked by the independent source validators:
    feasible normalized points, complete injective basis labels, and one
    neighbor for EVERY removed label. No cover or edge theorem is a field. -/
structure SourceVertexCertificate {n d : ℕ} (A : Matrix (Fin n) (Fin d) 𝕜)
    (b : Fin n → 𝕜) (V : Type*) where
  point : V → Fin d → 𝕜
  basis : V → Fin d → Fin n
  next : V → Fin d → V
  feasible : ∀ v, AffineFeasible A b (point v)
  basis_injective : ∀ v, Function.Injective (basis v)
  active_exact : ∀ v i, A i ⬝ᵥ point v = b i ↔ ∃ j, basis v j = i
  neighbor_keeps : ∀ v j k, k ≠ j → A (basis v k) ⬝ᵥ point (next v j) = b (basis v k)
  neighbor_leaves : ∀ v j, A (basis v j) ⬝ᵥ point (next v j) ≠ b (basis v j)

namespace SourceVertexCertificate
variable {n d : ℕ} {A : Matrix (Fin n) (Fin d) 𝕜} {b : Fin n → 𝕜} {V : Type*}
variable (C : SourceVertexCertificate A b V)

def gain (v : V) (j : Fin d) : 𝕜 := A (C.basis v j) ⬝ᵥ C.point (C.next v j) - b (C.basis v j)

theorem gain_positive (v : V) (j : Fin d) : 0 < C.gain v j := by
  exact sub_pos.mpr (lt_of_le_of_ne (C.feasible (C.next v j) (C.basis v j))
    (Ne.symm (C.neighbor_leaves v j)))

omit [IsStrictOrderedRing 𝕜] in
theorem basis_active (v : V) (j : Fin d) : A (C.basis v j) ⬝ᵥ C.point v = b (C.basis v j) :=
  (C.active_exact v _).mpr ⟨j, rfl⟩

omit [IsStrictOrderedRing 𝕜] in
theorem active_count (v : V) : (activeRows A b (C.point v)).card = d := by
  classical
  have he : activeRows A b (C.point v) = univ.image (C.basis v) := by
    ext i
    simp only [activeRows, mem_filter, mem_univ, true_and, mem_image]
    simpa using C.active_exact v i
  rw [he, card_image_of_injective _ (C.basis_injective v)]
  simp

theorem neighbor_inverse (v : V) :
    neighborDirections (C.point v) (fun j => C.point (C.next v j)) (C.gain v) *
      A.submatrix (C.basis v) id = 1 := by
  apply neighbor_inverse_of_slacks A (C.point v) (C.basis v) _ (C.gain v) (C.gain_positive v)
  intro i j
  rw [dotProduct_sub, C.basis_active]
  by_cases he : i = j
  · subst i
    simp only [↓reduceIte, gain]
  · rw [C.neighbor_keeps v j i he]
    simp [he]

theorem basis_nonsingular (v : V) : (A.submatrix (C.basis v) id).det ≠ 0 :=
  certified_basis_independent A (C.basis v) _ (C.neighbor_inverse v)

/-- All ordered active labels are covered by a finite list accepted via
    local basis directions; graph connectedness is not an assumption. -/
theorem covers_active_labels [Fintype V] [Nonempty V]
    (x : Fin d → 𝕜) (hx : AffineFeasible A b x)
    (label : Fin d → Fin n) (hl : Function.Injective label)
    (ha : ∀ j, A (label j) ⬝ᵥ x = b (label j)) :
    (∃ v, x = C.point v) ∧ (activeRows A b x).card = d := by
  have hsub : univ.image label ⊆ activeRows A b x := by
    intro i hi
    obtain ⟨j, _, rfl⟩ := mem_image.mp hi
    exact mem_filter.mpr ⟨mem_univ _, ha j⟩
  have hc : d ≤ (activeRows A b x).card := by
    simpa [card_image_of_injective _ hl] using card_le_card hsub
  obtain ⟨v, hv, hn⟩ := certified_list_covers_many_active A b C.point C.basis C.next C.gain
    C.feasible C.active_count C.gain_positive C.basis_active C.neighbor_inverse x hx hc
  exact ⟨⟨v, hv⟩, hn⟩

omit [IsStrictOrderedRing 𝕜] in
/-- The new tight row at each neighbor exists from complete labels and
    equal cardinality. It is not an unverified edge-interface premise. -/
theorem neighbor_new_row (v : V) (j : Fin d) :
    ∃ i, A i ⬝ᵥ C.point (C.next v j) = b i ∧ b i < A i ⬝ᵥ C.point v := by
  classical
  let P := activeRows A b (C.point v)
  let Q := activeRows A b (C.point (C.next v j))
  have hn : ¬ Q ⊆ P := by
    intro hsub
    have he : Q = P := eq_of_subset_of_card_le hsub (by
      simp only [P, Q, C.active_count, le_refl])
    have hm : C.basis v j ∈ P := mem_filter.mpr ⟨mem_univ _, C.basis_active v j⟩
    rw [← he] at hm
    exact C.neighbor_leaves v j (mem_filter.mp hm).2
  obtain ⟨i, hiQ, hiP⟩ := Finset.not_subset.mp hn
  refine ⟨i, (mem_filter.mp hiQ).2, lt_of_le_of_ne (C.feasible v i) ?_⟩
  intro he
  exact hiP (mem_filter.mpr ⟨mem_univ _, he.symm⟩)

/-- Every checker-certified neighbor is an actual geometric closed edge
    with every shared original facet retained. -/
theorem neighbor_face_segment (v : V) (j : Fin d) (x : Fin d → 𝕜) :
    (AffineFeasible A b x ∧ ∀ k, k ≠ j → A (C.basis v k) ⬝ᵥ x = b (C.basis v k)) ↔
      ∃ t : 𝕜, 0 ≤ t ∧ t ≤ 1 ∧ x = affineSegment (C.point v) (C.point (C.next v j)) t := by
  obtain ⟨i, hi, hs⟩ := C.neighbor_new_row v j
  exact certified_common_face_segment A b _ _ (C.basis v) j (C.basis_nonsingular v)
    (C.feasible v) (C.feasible (C.next v j)) (C.basis_active v) (C.neighbor_keeps v j)
    (C.gain_positive v j) i hi hs x

omit [IsStrictOrderedRing 𝕜] in
/-- The complete common zero-label set has exactly d-1 rows. This is the
    geometric neighbor relation needed by the factor transition count. -/
theorem neighbor_shared_label_count (v : V) (j : Fin d) :
    ((activeRows A b (C.point v)) ∩ (activeRows A b (C.point (C.next v j)))).card + 1 = d := by
  classical
  have he : (activeRows A b (C.point v)) ∩ (activeRows A b (C.point (C.next v j))) =
      (activeRows A b (C.point v)).erase (C.basis v j) := by
    ext i
    constructor
    · intro hi
      obtain ⟨hp, hq⟩ := mem_inter.mp hi
      apply mem_erase.mpr
      refine ⟨?_, hp⟩
      intro hij
      rw [hij] at hq
      exact C.neighbor_leaves v j (mem_filter.mp hq).2
    · intro hi
      obtain ⟨hne, hp⟩ := mem_erase.mp hi
      obtain ⟨k, hk⟩ := (C.active_exact v i).mp (mem_filter.mp hp).2
      have hkj : k ≠ j := by intro h; subst k; exact hne hk.symm
      refine mem_inter.mpr ⟨hp, mem_filter.mpr ⟨mem_univ _, ?_⟩⟩
      rw [← hk]
      exact C.neighbor_keeps v j k hkj
  have hm : C.basis v j ∈ activeRows A b (C.point v) :=
    mem_filter.mpr ⟨mem_univ _, C.basis_active v j⟩
  rw [he, card_erase_add_one hm, C.active_count]

#print axioms neighbor_inverse
#print axioms covers_active_labels
#print axioms neighbor_face_segment
#print axioms neighbor_shared_label_count
end SourceVertexCertificate
end
end ADKZPricing
