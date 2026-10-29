import RealActiveTransport
import LabelledUnion

namespace ADKZPricing
open Matrix Finset
noncomputable section

/-- Disjoint ORIGINAL left/right row embeddings; no new vertex numbers. -/
def productLabels {n m : ℕ} (Z : Finset (Fin n)) (W : Finset (Fin m)) : Finset (Fin (n + m)) :=
  (Z.disjSum W).map finSumFinEquiv.toEmbedding

theorem productLabels_left {n m : ℕ} (Z : Finset (Fin n)) (W : Finset (Fin m)) (i : Fin n) :
    Fin.castAdd m i ∈ productLabels Z W ↔ i ∈ Z := by
  change finSumFinEquiv (Sum.inl i) ∈ _ ↔ _
  simp [productLabels]

theorem productLabels_right {n m : ℕ} (Z : Finset (Fin n)) (W : Finset (Fin m)) (i : Fin m) :
    Fin.natAdd n i ∈ productLabels Z W ↔ i ∈ W := by
  change finSumFinEquiv (Sum.inr i) ∈ _ ↔ _
  simp [productLabels]

theorem productLabels_card {n m : ℕ} (Z : Finset (Fin n)) (W : Finset (Fin m)) :
    (productLabels Z W).card = Z.card + W.card := by simp [productLabels]

theorem productLabels_inter {n m : ℕ} (Z Z' : Finset (Fin n)) (W W' : Finset (Fin m)) :
    productLabels Z W ∩ productLabels Z' W' = productLabels (Z ∩ Z') (W ∩ W') := by
  ext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp [productLabels_left, productLabels_right]

/-- Actual normalized real/rational chart vertices and their complete
    original zero sets. The cell guard is part of the predicate. -/
def ChartVertex {K : Type*} [Field K] [LinearOrder K] {n d : ℕ}
    (A : Matrix (Fin n) (Fin (d + 1)) K) (c : Option (Fin n)) (Z : Finset (Fin n)) : Prop :=
  Z.card = d ∧ ∃ v : Fin (d + 1) → K, v 0 = 1 ∧ StarFeasible A c v ∧
    ∀ i, A i ⬝ᵥ v = 0 ↔ i ∈ Z

def productJoin {K : Type*} {d e : ℕ} (p : Fin (d + 1) → K) (q : Fin (e + 1) → K) :
    Fin (d + e + 1) → K := Fin.cons (p 0) (Fin.append (fun j => p j.succ) (fun j => q j.succ))

theorem productJoin_left {K : Type*} {d e : ℕ}
    (p : Fin (d + 1) → K) (q : Fin (e + 1) → K) : productLeft (productJoin p q) = p := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [productLeft, productJoin]

theorem productJoin_right {K : Type*} {d e : ℕ}
    (p : Fin (d + 1) → K) (q : Fin (e + 1) → K) (h0 : p 0 = q 0) :
    productRight (productJoin p q) = q := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [productRight, productJoin, h0]

/-- Complete product vertices split into actual factor vertices, and
    actual factor vertices join back. Uniformity supplies each factor's
    zero count; the product is not assumed globally uniform. -/
theorem product_chart_vertex_iff {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {n m d e : ℕ} (A : Matrix (Fin n) (Fin (d + 1)) K) (B : Matrix (Fin m) (Fin (e + 1)) K)
    (huA : ∀ f : Fin (d + 1) → Fin n, Function.Injective f → (A.submatrix f id).det ≠ 0)
    (huB : ∀ f : Fin (e + 1) → Fin m, Function.Injective f → (B.submatrix f id).det ≠ 0)
    (c : Option (Fin (n + m))) (Z : Finset (Fin n)) (W : Finset (Fin m)) :
    ChartVertex (orderedProduct A B) c (productLabels Z W) ↔
      ChartVertex A (leftStar c) Z ∧ ChartVertex B (rightStar c) W := by
  classical
  constructor
  · rintro ⟨hcard, v, hv0, hf, hz⟩
    have hfeas := (orderedProduct_star_iff A B c v).mp hf
    have hl (i : Fin n) : A i ⬝ᵥ productLeft v = 0 ↔ i ∈ Z := by
      simpa only [orderedProduct_left_value, productLabels_left] using hz (Fin.castAdd m i)
    have hr (i : Fin m) : B i ⬝ᵥ productRight v = 0 ↔ i ∈ W := by
      simpa only [orderedProduct_right_value, productLabels_right] using hz (Fin.natAdd n i)
    have hln : productLeft v ≠ 0 := by
      intro h; have he := congrFun h 0; change v 0 = 0 at he; rw [hv0] at he; exact one_ne_zero he
    have hrn : productRight v ≠ 0 := by
      intro h; have he := congrFun h 0; change v 0 = 0 at he; rw [hv0] at he; exact one_ne_zero he
    have hzl : (univ.filter (fun i => A i ⬝ᵥ productLeft v = 0)) = Z := by ext i; simp [hl]
    have hzr : (univ.filter (fun i => B i ⬝ᵥ productRight v = 0)) = W := by ext i; simp [hr]
    have hcl := uniform_zero_count A huA _ hln
    have hcr := uniform_zero_count B huB _ hrn
    rw [hzl] at hcl
    rw [hzr] at hcr
    rw [productLabels_card] at hcard
    exact ⟨⟨by omega, productLeft v, hv0, hfeas.1, hl⟩,
      ⟨by omega, productRight v, hv0, hfeas.2, hr⟩⟩
  · rintro ⟨⟨hzcard, p, hp0, hp, hz⟩, ⟨hwcard, q, hq0, hq, hw⟩⟩
    have he : p 0 = q 0 := hp0.trans hq0.symm
    refine ⟨by rw [productLabels_card, hzcard, hwcard], productJoin p q, hp0, ?_, ?_⟩
    · rw [orderedProduct_star_iff, productJoin_left, productJoin_right p q he]
      exact ⟨hp, hq⟩
    · intro i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · rw [orderedProduct_left_value, productJoin_left, productLabels_left]
        exact hz j
      · rw [orderedProduct_right_value, productJoin_right p q he, productLabels_right]
        exact hw j

/-- The shared-row edge count of an actual product changes exactly one
    factor label by one row; the other factor label is literally equal. -/
theorem product_labels_edge_iff {n m d e : ℕ}
    (Z Z' : Finset (Fin n)) (W W' : Finset (Fin m))
    (hz : Z.card = d) (hz' : Z'.card = d) (hw : W.card = e) (hw' : W'.card = e) :
    (productLabels Z W ∩ productLabels Z' W').card + 1 = d + e ↔
      ((Z ∩ Z').card + 1 = d ∧ W = W') ∨
      ((W ∩ W').card + 1 = e ∧ Z = Z') := by
  rw [productLabels_inter, productLabels_card]
  have hl : (Z ∩ Z').card ≤ d := by simpa only [hz] using card_le_card (show Z ∩ Z' ⊆ Z from inter_subset_left)
  have hr : (W ∩ W').card ≤ e := by simpa only [hw] using card_le_card (show W ∩ W' ⊆ W from inter_subset_left)
  have eq_left (h : (Z ∩ Z').card = d) : Z = Z' := by
    have h1 : Z ∩ Z' = Z := eq_of_subset_of_card_le inter_subset_left (by omega)
    have h2 : Z ∩ Z' = Z' := eq_of_subset_of_card_le inter_subset_right (by omega)
    exact h1.symm.trans h2
  have eq_right (h : (W ∩ W').card = e) : W = W' := by
    have h1 : W ∩ W' = W := eq_of_subset_of_card_le inter_subset_left (by omega)
    have h2 : W ∩ W' = W' := eq_of_subset_of_card_le inter_subset_right (by omega)
    exact h1.symm.trans h2
  constructor
  · intro hc
    by_cases h : (Z ∩ Z').card = d
    · exact Or.inr ⟨by omega, eq_left h⟩
    · exact Or.inl ⟨by omega, eq_right (by omega)⟩
  · rintro (⟨hc, rfl⟩ | ⟨hc, rfl⟩) <;> simp only [inter_self, hz, hw] at * <;> omega

#print axioms product_chart_vertex_iff
#print axioms product_labels_edge_iff
end
end ADKZPricing
