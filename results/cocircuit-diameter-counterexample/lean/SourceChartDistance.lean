import SourceRegularity
import SourceDistance
import ProductCellGraph

namespace ADKZPricing
open Matrix Finset
noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- A normalized homogeneous ray is exactly a point of the original
    affine source chart, with every original zero label retained. -/
theorem source_normalized_slack {n d : ℕ}
    (A : Matrix (Fin n) (Fin (d + 1)) K) (v : Fin (d + 1) → K) (hv : v 0 = 1) (i : Fin n) :
    A i ⬝ᵥ v = sourceSpatial A i ⬝ᵥ (fun j => v j.succ) - sourceBound A i := by
  simp [dotProduct, Fin.sum_univ_succ, hv, sourceSpatial, sourceBound, add_comm]

/-- Cover binds actual chart vertices to the finite original source
    labels in both directions, not to an assumed abstract graph. -/
theorem source_chart_vertex_iff {n d : ℕ} {V : Type*} [Fintype V] [Nonempty V]
    (A : Matrix (Fin n) (Fin (d + 1)) K)
    (C : SourceVertexCertificate (sourceSpatial A) (sourceBound A) V)
    (Z : Finset (Fin n)) :
    ChartVertex A none Z ↔ C.labelCell.vertex Z := by
  classical
  constructor
  · rintro ⟨hc, v, hv0, hf, hz⟩
    have hfeas : AffineFeasible (sourceSpatial A) (sourceBound A) (fun j => v j.succ) := by
      intro i
      have he := hf i
      change 0 ≤ starSign none i * (A i ⬝ᵥ v) at he
      simp only [starSign, reduceCtorEq, if_false, one_mul] at he
      rw [source_normalized_slack A v hv0, sub_nonneg] at he
      exact he
    let e := (Z.equivFinOfCardEq hc).symm
    let label : Fin d → Fin n := fun j => (e j).val
    have hl : Function.Injective label := by
      intro i j he
      exact e.injective (Subtype.ext he)
    have ha (j : Fin d) : sourceSpatial A (label j) ⬝ᵥ (fun k => v k.succ) = sourceBound A (label j) := by
      have he := (hz (label j)).mpr (e j).property
      rw [source_normalized_slack A v hv0, sub_eq_zero] at he
      exact he
    obtain ⟨⟨w, hw⟩, _⟩ := C.covers_active_labels _ hfeas label hl ha
    refine ⟨w, ?_⟩
    ext i
    rw [← C.labels_active, ← hw, ← sub_eq_zero, ← source_normalized_slack A v hv0]
    exact hz i
  · rintro ⟨w, rfl⟩
    let v : Fin (d + 1) → K := Fin.cons 1 (C.point w)
    have hv : v 0 = 1 := rfl
    have he (i : Fin n) : A i ⬝ᵥ v = sourceSpatial A i ⬝ᵥ C.point w - sourceBound A i :=
      source_normalized_slack A v hv i
    refine ⟨C.labels_card w, v, hv, ?_, ?_⟩
    · intro i
      change 0 ≤ starSign none i * (A i ⬝ᵥ v)
      simp only [starSign, reduceCtorEq, if_false, one_mul]
      rw [he]
      exact sub_nonneg.mpr (C.feasible w i)
    · intro i
      rw [he, sub_eq_zero]
      exact C.labels_active w i

/-- The complete actual central chart graph transfers to the certificate
    graph with the SAME vertex labels and every original common edge. -/
theorem source_chart_walk {n d : ℕ} {V : Type*} [Fintype V] [Nonempty V]
    (A : Matrix (Fin n) (Fin (d + 1)) K)
    (C : SourceVertexCertificate (sourceSpatial A) (sourceBound A) V)
    {Z W : Finset (Fin n)} {L : ℕ} (h : LabelledCell.CellWalk (chartCell A none) Z W L) :
    LabelledCell.CellWalk C.labelCell Z W L := by
  apply h.transfer (fun Z hz => (source_chart_vertex_iff A C Z).mp hz)
  intro Z W he
  exact ⟨(source_chart_vertex_iff A C Z).mp he.1,
    (source_chart_vertex_iff A C W).mp he.2.1, he.2.2⟩

/-- A source-layer certificate proves the specified-pair lower bound on
    all actual central chart paths, after the separately checked cover. -/
theorem source_chart_distance {n d : ℕ} {V : Type*} [Fintype V] [Nonempty V]
    (A : Matrix (Fin n) (Fin (d + 1)) K)
    (C : SourceVertexCertificate (sourceSpatial A) (sourceBound A) V)
    (P : Finset (Fin n) → ℤ)
    (hP : ∀ v j, P (C.labels (C.next v j)) ≤ P (C.labels v) + 1)
    (Z W : Finset (Fin n)) (D : ℕ) (hD : (D : ℤ) ≤ P W - P Z)
    {L : ℕ} (h : LabelledCell.CellWalk (chartCell A none) Z W L) : D ≤ L :=
  C.specified_distance_lower_bound P hP Z W D hD (source_chart_walk A C h)

#print axioms source_chart_vertex_iff
#print axioms source_chart_distance
end
end ADKZPricing
