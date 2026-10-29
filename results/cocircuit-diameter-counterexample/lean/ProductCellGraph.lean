import ProductVertexLabels
import GuardedDistances

namespace ADKZPricing
open Matrix Finset
noncomputable section

def leftLabels {n m : ℕ} (Z : Finset (Fin (n + m))) : Finset (Fin n) :=
  univ.filter (fun i => Fin.castAdd m i ∈ Z)

def rightLabels {n m : ℕ} (Z : Finset (Fin (n + m))) : Finset (Fin m) :=
  univ.filter (fun i => Fin.natAdd n i ∈ Z)

/-- Every original product label splits and rejoins exactly, including
    the labels of arbitrary full-graph path vertices. -/
theorem productLabels_split {n m : ℕ} (Z : Finset (Fin (n + m))) :
    productLabels (leftLabels Z) (rightLabels Z) = Z := by
  ext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp [productLabels_left, productLabels_right, leftLabels, rightLabels]

def chartCell {K : Type*} [Field K] [LinearOrder K] {n d : ℕ}
    (A : Matrix (Fin n) (Fin (d + 1)) K) (c : Option (Fin n)) :
    LabelledCell (Finset (Fin n)) where
  vertex Z := ChartVertex A c Z
  edge Z W := ChartVertex A c Z ∧ ChartVertex A c W ∧ (Z ∩ W).card + 1 = d
  edge_vertices _ _ h := ⟨h.1, h.2.1⟩

/-- This is the actual product chart-cell relation, pulled back only by
    the original row embeddings. It still contains every shared facet. -/
def productChartCell {K : Type*} [Field K] [LinearOrder K] {n m d e : ℕ}
    (A : Matrix (Fin n) (Fin (d + 1)) K) (B : Matrix (Fin m) (Fin (e + 1)) K)
    (c : Option (Fin (n + m))) : LabelledCell (Finset (Fin n) × Finset (Fin m)) where
  vertex Z := ChartVertex (orderedProduct A B) c (productLabels Z.1 Z.2)
  edge Z W := (chartCell (orderedProduct A B) c).edge (productLabels Z.1 Z.2) (productLabels W.1 W.2)
  edge_vertices _ _ h := ⟨h.1, h.2.1⟩

/-- The guarded Cartesian relation is DERIVED from actual feasible rays
    and actual common-row counts. There is no graph-isomorphism premise. -/
theorem product_chart_edge_iff {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {n m d e : ℕ} (A : Matrix (Fin n) (Fin (d + 1)) K) (B : Matrix (Fin m) (Fin (e + 1)) K)
    (huA : ∀ f : Fin (d + 1) → Fin n, Function.Injective f → (A.submatrix f id).det ≠ 0)
    (huB : ∀ f : Fin (e + 1) → Fin m, Function.Injective f → (B.submatrix f id).det ≠ 0)
    (c : Option (Fin (n + m))) (Z W : Finset (Fin n) × Finset (Fin m)) :
    (productChartCell A B c).edge Z W ↔
      (LabelledCell.cartesian (chartCell A (leftStar c)) (chartCell B (rightStar c))).edge Z W := by
  constructor
  · rintro ⟨hz, hw, hc⟩
    have hz' := (product_chart_vertex_iff A B huA huB c Z.1 Z.2).mp hz
    have hw' := (product_chart_vertex_iff A B huA huB c W.1 W.2).mp hw
    have he := (product_labels_edge_iff Z.1 W.1 Z.2 W.2 hz'.1.1 hw'.1.1 hz'.2.1 hw'.2.1).mp hc
    rcases he with ⟨hl, hr⟩ | ⟨hr, hl⟩
    · exact Or.inl ⟨⟨hz'.1, hw'.1, hl⟩, hr, hz'.2⟩
    · exact Or.inr ⟨⟨hz'.2, hw'.2, hr⟩, hl, hz'.1⟩
  · intro he
    have hv := (LabelledCell.cartesian (chartCell A (leftStar c)) (chartCell B (rightStar c))).edge_vertices Z W he
    have hz := (product_chart_vertex_iff A B huA huB c Z.1 Z.2).mpr hv.1
    have hw := (product_chart_vertex_iff A B huA huB c W.1 W.2).mpr hv.2
    refine ⟨hz, hw, ?_⟩
    apply (product_labels_edge_iff Z.1 W.1 Z.2 W.2 hv.1.1.1 hv.2.1.1 hv.1.2.1 hv.2.2.1).mpr
    rcases he with ⟨he, hfix, _⟩ | ⟨he, hfix, _⟩
    · exact Or.inl ⟨he.2.2, hfix⟩
    · exact Or.inr ⟨he.2.2, hfix⟩

/-- Product walks, with all vertex guards, now transfer to actual factor
    chart-cell walks of exactly the same length. -/
theorem product_chart_walk {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {n m d e : ℕ} (A : Matrix (Fin n) (Fin (d + 1)) K) (B : Matrix (Fin m) (Fin (e + 1)) K)
    (huA : ∀ f : Fin (d + 1) → Fin n, Function.Injective f → (A.submatrix f id).det ≠ 0)
    (huB : ∀ f : Fin (e + 1) → Fin m, Function.Injective f → (B.submatrix f id).det ≠ 0)
    (c : Option (Fin (n + m))) {Z W : Finset (Fin n) × Finset (Fin m)} {L : ℕ}
    (h : LabelledCell.CellWalk (productChartCell A B c) Z W L) :
    LabelledCell.CellWalk (LabelledCell.cartesian
      (chartCell A (leftStar c)) (chartCell B (rightStar c))) Z W L :=
  h.transfer (fun Z hz => (product_chart_vertex_iff A B huA huB c Z.1 Z.2).mp hz)
    (fun Z W he => (product_chart_edge_iff A B huA huB c Z W).mp he)

/-- Factor uniformity is instantiated from the actual first perturbation
    for all real product cells and all shared original labels. -/
theorem firstProduct_chart_edge {n d : ℕ}
    (A : Matrix (Fin n) (Fin (d + 1)) ℤ) (C : IntegralStarChart A) (h0 : 0 < C.chart 0)
    (c : Option (Fin (n + n))) (Z W : Finset (Fin n) × Finset (Fin n)) :
    let F := (chartedGenericFactor A C).map (Rat.castHom ℝ)
    (productChartCell F F c).edge Z W ↔
      (LabelledCell.cartesian (chartCell F (leftStar c)) (chartCell F (rightStar c))).edge Z W := by
  have hu := (chartedGenericFactor_real_properties A C h0).1
  exact product_chart_edge_iff _ _ hu hu c Z W

#print axioms productLabels_split
#print axioms product_chart_edge_iff
#print axioms firstProduct_chart_edge
end
end ADKZPricing
