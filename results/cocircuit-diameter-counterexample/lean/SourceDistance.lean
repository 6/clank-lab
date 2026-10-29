import SourceCertificate
import CommonFaceLabels
import GuardedDistances

namespace ADKZPricing
open Matrix Finset
noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

namespace SourceVertexCertificate
variable {n d : ℕ} {V : Type*} {A : Matrix (Fin n) (Fin d) K} {b : Fin n → K}
variable (C : SourceVertexCertificate A b V)

def labels (v : V) : Finset (Fin n) := univ.image (C.basis v)

omit [IsStrictOrderedRing K] in
theorem labels_card (v : V) : (C.labels v).card = d := by
  simp [labels, Finset.card_image_of_injective _ (C.basis_injective v)]

omit [IsStrictOrderedRing K] in
theorem labels_active (v : V) (i : Fin n) : A i ⬝ᵥ C.point v = b i ↔ i ∈ C.labels v := by
  simpa [labels] using C.active_exact v i

omit [IsStrictOrderedRing K] in
theorem labels_of_point_eq (v w : V) (h : C.point v = C.point w) : C.labels v = C.labels w := by
  ext i
  rw [← C.labels_active, ← C.labels_active, h]

/-- Every geometric shared-label edge occurs among the certificate's
    checked local neighbors. A neighbor-closed list alone is not merely
    assumed to contain all edges: the entire common face is used. -/
theorem common_edge_is_neighbor (v w : V)
    (hc : (C.labels v ∩ C.labels w).card + 1 = d) :
    ∃ j : Fin d, C.point w = C.point (C.next v j) := by
  obtain ⟨drop, newRow, _, hnew, hnewp, hcommon⟩ :=
    complete_labels_exchange (C.basis v) (C.basis_injective v) (C.labels w) (C.labels_card w) hc
  have hkeep : ∀ j, j ≠ drop → A (C.basis v j) ⬝ᵥ C.point w = b (C.basis v j) := by
    intro j hj
    exact (C.labels_active w _).mpr ((hcommon j).mpr hj)
  obtain ⟨t, ht, ht1, he⟩ := (C.neighbor_face_segment v drop (C.point w)).mp ⟨C.feasible w, hkeep⟩
  have hstrict : b newRow < A newRow ⬝ᵥ C.point v := by
    apply lt_of_le_of_ne (C.feasible v newRow)
    intro h
    exact hnewp ((C.labels_active v _).mp h.symm)
  have hqzero := (C.labels_active w newRow).mpr hnew
  rw [he, affineSegment_value] at hqzero
  have hn := C.feasible (C.next v drop) newRow
  have ht_one : t = 1 := by
    have hm := mul_nonneg ht (sub_nonneg.mpr hn)
    nlinarith
  refine ⟨drop, ?_⟩
  rw [ht_one] at he
  have hs : affineSegment (C.point v) (C.point (C.next v drop)) (1 : K) = C.point (C.next v drop) := by
    ext i
    simp [affineSegment]
  exact he.trans hs

/-- An actual finite source-cell graph on original labels; every endpoint
    is guarded by membership in the certified geometrically complete list. -/
def labelCell : LabelledCell (Finset (Fin n)) where
  vertex Z := ∃ v, C.labels v = Z
  edge Z W := (∃ v, C.labels v = Z) ∧ (∃ w, C.labels w = W) ∧ (Z ∩ W).card + 1 = d
  edge_vertices _ _ h := ⟨h.1, h.2.1⟩

/-- Local certificate potential inequalities imply the same inequality
    on EVERY geometric source-cell edge, including unlisted edge claims. -/
theorem potential_edge (P : Finset (Fin n) → ℤ)
    (hP : ∀ v j, P (C.labels (C.next v j)) ≤ P (C.labels v) + 1)
    {Z W : Finset (Fin n)} (he : C.labelCell.edge Z W) : P W ≤ P Z + 1 := by
  obtain ⟨⟨v, rfl⟩, ⟨w, rfl⟩, hc⟩ := he
  obtain ⟨j, hj⟩ := C.common_edge_is_neighbor v w hc
  rw [C.labels_of_point_eq w (C.next v j) hj]
  exact hP v j

/-- A potential lower bound applies to the COMPLETE geometric cell graph,
    not only to paths in an imported adjacency table. -/
theorem potential_walk (P : Finset (Fin n) → ℤ)
    (hP : ∀ v j, P (C.labels (C.next v j)) ≤ P (C.labels v) + 1)
    {Z W : Finset (Fin n)} {L : ℕ} (h : LabelledCell.CellWalk C.labelCell Z W L) :
    P W ≤ P Z + (L : ℤ) := by
  induction h with
  | nil Z _ => simp
  | @cons Z Y W L he _ ih =>
    have hs := C.potential_edge P hP he
    push_cast
    omega

theorem specified_distance_lower_bound (P : Finset (Fin n) → ℤ)
    (hP : ∀ v j, P (C.labels (C.next v j)) ≤ P (C.labels v) + 1)
    (Z W : Finset (Fin n)) (D : ℕ) (hD : (D : ℤ) ≤ P W - P Z)
    {L : ℕ} (h : LabelledCell.CellWalk C.labelCell Z W L) : D ≤ L := by
  have he := C.potential_walk P hP h
  omega

#print axioms common_edge_is_neighbor
#print axioms potential_edge
#print axioms specified_distance_lower_bound
end SourceVertexCertificate
end
end ADKZPricing
