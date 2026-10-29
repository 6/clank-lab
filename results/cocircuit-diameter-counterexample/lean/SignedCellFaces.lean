import CommonFaceLabels
import RealActiveTransport

namespace ADKZPricing
open Matrix Finset
noncomputable section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def signedSpatial {n d : ℕ} (A : Matrix (Fin n) (Fin (d + 1)) K)
    (c : Option (Fin n)) : Matrix (Fin n) (Fin d) K :=
  fun i j => starSign c i * A i j.succ

def signedBound {n d : ℕ} (A : Matrix (Fin n) (Fin (d + 1)) K)
    (c : Option (Fin n)) : Fin n → K := fun i => -(starSign c i * A i 0)

theorem starSign_ne_zero {n : ℕ} (c : Option (Fin n)) (i : Fin n) :
    (starSign c i : K) ≠ 0 := by
  unfold starSign
  split_ifs <;> norm_num

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem signedSpatial_value {n d : ℕ} (A : Matrix (Fin n) (Fin (d + 1)) K)
    (c : Option (Fin n)) (v : Fin (d + 1) → K) (hv : v 0 = 1) (i : Fin n) :
    signedSpatial A c i ⬝ᵥ (fun j => v j.succ) - signedBound A c i =
      starSign c i * (A i ⬝ᵥ v) := by
  simp only [signedSpatial, signedBound, dotProduct, Fin.sum_univ_succ, hv, mul_one]
  simp only [mul_assoc, ← Finset.mul_sum]
  ring

theorem signedSpatial_feasible {n d : ℕ} (A : Matrix (Fin n) (Fin (d + 1)) K)
    (c : Option (Fin n)) (v : Fin (d + 1) → K) (hv : v 0 = 1) :
    AffineFeasible (signedSpatial A c) (signedBound A c) (fun j => v j.succ) ↔
      StarFeasible A c v := by
  apply forall_congr'
  intro i
  rw [← sub_nonneg, signedSpatial_value A c v hv]

theorem signedSpatial_active {n d : ℕ} (A : Matrix (Fin n) (Fin (d + 1)) K)
    (c : Option (Fin n)) (v : Fin (d + 1) → K) (hv : v 0 = 1) (i : Fin n) :
    signedSpatial A c i ⬝ᵥ (fun j => v j.succ) = signedBound A c i ↔ A i ⬝ᵥ v = 0 := by
  rw [← sub_eq_zero, signedSpatial_value A c v hv, mul_eq_zero_iff_left (starSign_ne_zero c i)]

theorem signedSpatial_minor {n d : ℕ} (A : Matrix (Fin n) (Fin (d + 1)) K)
    (c : Option (Fin n)) (label : Fin d → Fin n)
    (hd : (A.submatrix label Fin.succ).det ≠ 0) :
    ((signedSpatial A c).submatrix label id).det ≠ 0 := by
  have he := Matrix.det_mul_column (fun i => (starSign c (label i) : K))
    (A.submatrix label Fin.succ)
  change Matrix.det (fun i j => starSign c (label i) * A (label i) j.succ) =
    (∏ i, starSign c (label i)) * (A.submatrix label Fin.succ).det at he
  change Matrix.det (fun i j => starSign c (label i) * A (label i) j.succ) ≠ 0
  rw [he]
  exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr (fun i _ => starSign_ne_zero c (label i))) hd

/-- The geometric common face uses every original shared row and the
    closed signed inequalities. It is an actual segment in the common
    chart, rather than an assertion about an abstract graph. -/
def StarCommonFaceSegment {n d : ℕ} (A : Matrix (Fin n) (Fin (d + 1)) K)
    (c : Option (Fin n)) (p q : Fin (d + 1) → K) (Z W : Finset (Fin n)) : Prop :=
  ∀ x : Fin d → K,
    (AffineFeasible (signedSpatial A c) (signedBound A c) x ∧
      ∀ i ∈ Z ∩ W, signedSpatial A c i ⬝ᵥ x = signedBound A c i) ↔
    ∃ t : K, 0 ≤ t ∧ t ≤ 1 ∧
      x = affineSegment (fun j => p j.succ) (fun j => q j.succ) t

theorem star_complete_common_face {n d : ℕ}
    (A : Matrix (Fin n) (Fin (d + 1)) K) (c : Option (Fin n))
    (p q : Fin (d + 1) → K) (hp0 : p 0 = 1) (hq0 : q 0 = 1)
    (hp : StarFeasible A c p) (hq : StarFeasible A c q)
    (bas : Fin d → Fin n) (hb : Function.Injective bas) (W : Finset (Fin n))
    (hw : W.card = d) (hc : ((univ.image bas) ∩ W).card + 1 = d)
    (hd : (A.submatrix bas Fin.succ).det ≠ 0)
    (hzp : ∀ i, A i ⬝ᵥ p = 0 ↔ i ∈ univ.image bas)
    (hzq : ∀ i, A i ⬝ᵥ q = 0 ↔ i ∈ W) :
    StarCommonFaceSegment A c p q (univ.image bas) W := by
  intro x
  apply complete_labels_common_face _ _ _ _ bas hb W hw hc
    (signedSpatial_minor A c bas hd)
    ((signedSpatial_feasible A c p hp0).mpr hp) ((signedSpatial_feasible A c q hq0).mpr hq)
  · intro i
    exact (signedSpatial_active A c p hp0 i).trans (hzp i)
  · intro i
    exact (signedSpatial_active A c q hq0 i).trans (hzq i)

/-- Product regularity discharges the geometric edge theorem's minor
    AND complete-label premises for actual real product rays. -/
theorem firstProduct_real_common_face {n d : ℕ}
    (A : Matrix (Fin n) (Fin (d + 1)) ℤ) (C : IntegralStarChart A)
    (h0 : 0 < C.chart 0) (hn : d < n)
    (c : Option (Fin (n + n))) (p q : Fin (d + d + 1) → ℝ)
    (hp0 : p 0 = 1) (hq0 : q 0 = 1)
    (hp : StarFeasible ((firstProduct A C).map (Rat.castHom ℝ)) c p)
    (hq : StarFeasible ((firstProduct A C).map (Rat.castHom ℝ)) c q)
    (lp lq : Fin (d + d) → Fin (n + n))
    (hlp : Function.Injective lp) (hlq : Function.Injective lq)
    (hap : ∀ j, ((firstProduct A C).map (Rat.castHom ℝ)) (lp j) ⬝ᵥ p = 0)
    (haq : ∀ j, ((firstProduct A C).map (Rat.castHom ℝ)) (lq j) ⬝ᵥ q = 0)
    (hc : ((univ.image lp) ∩ (univ.image lq)).card + 1 = d + d) :
    StarCommonFaceSegment ((firstProduct A C).map (Rat.castHom ℝ)) c p q
      (univ.image lp) (univ.image lq) := by
  have hpn : p ≠ 0 := by intro he; have hz := congrFun he 0; rw [hp0] at hz; norm_num at hz
  have hqn : q ≠ 0 := by intro he; have hz := congrFun he 0; rw [hq0] at hz; norm_num at hz
  have hrp := firstProduct_real_regularity A C h0 hn c p hp hpn lp hlp hap
  have hrq := firstProduct_real_regularity A C h0 hn c q hq hqn lq hlq haq
  have hlabels (v : Fin (d + d + 1) → ℝ) (l : Fin (d + d) → Fin (n + n))
      (ha : ∀ j, ((firstProduct A C).map (Rat.castHom ℝ)) (l j) ⬝ᵥ v = 0)
      (hs : ∀ i, i ∉ Set.range l →
        0 < starSign c i * (((firstProduct A C).map (Rat.castHom ℝ)) i ⬝ᵥ v)) :
      ∀ i, ((firstProduct A C).map (Rat.castHom ℝ)) i ⬝ᵥ v = 0 ↔ i ∈ univ.image l := by
    intro i
    constructor
    · intro hi
      by_contra hout
      have hnot : i ∉ Set.range l := by simpa using hout
      have he := hs i hnot
      rw [hi, mul_zero] at he
      exact lt_irrefl _ he
    · intro hi
      obtain ⟨j, _, rfl⟩ := mem_image.mp hi
      exact ha j
  exact star_complete_common_face _ c p q hp0 hq0 hp hq lp hlp (univ.image lq)
    (by simp [Finset.card_image_of_injective _ hlq]) hc hrp.2.1
    (hlabels p lp hap hrp.2.2) (hlabels q lq haq hrq.2.2)

/-- The final perturbation has the same genuine geometric edge property;
    its uniformity and spatial minor are supplied from the construction. -/
theorem second_real_common_face {n d : ℕ}
    (A : Matrix (Fin n) (Fin (d + 1)) ℤ) (C : IntegralStarChart A)
    (h0 : 0 < C.chart 0) (hn : d < n)
    (c : Option (Fin (n + n))) (p q : Fin (d + d + 1) → ℝ)
    (hp0 : p 0 = 1) (hq0 : q 0 = 1)
    (hp : StarFeasible ((secondPerturbedMatrix A C h0).map (Rat.castHom ℝ)) c p)
    (hq : StarFeasible ((secondPerturbedMatrix A C h0).map (Rat.castHom ℝ)) c q)
    (lp lq : Fin (d + d) → Fin (n + n))
    (hlp : Function.Injective lp) (hlq : Function.Injective lq)
    (hap : ∀ j, ((secondPerturbedMatrix A C h0).map (Rat.castHom ℝ)) (lp j) ⬝ᵥ p = 0)
    (haq : ∀ j, ((secondPerturbedMatrix A C h0).map (Rat.castHom ℝ)) (lq j) ⬝ᵥ q = 0)
    (hc : ((univ.image lp) ∩ (univ.image lq)).card + 1 = d + d) :
    StarCommonFaceSegment ((secondPerturbedMatrix A C h0).map (Rat.castHom ℝ)) c p q
      (univ.image lp) (univ.image lq) := by
  have hpn : p ≠ 0 := by intro he; have hz := congrFun he 0; rw [hp0] at hz; norm_num at hz
  have hqn : q ≠ 0 := by intro he; have hz := congrFun he 0; rw [hq0] at hz; norm_num at hz
  have hu := (chartedGenericFactor_real_properties _ _ (secondIntegralChart_pivot A C h0)).1
  have hd := uniform_charted_spatial_basis
    ((secondPerturbedMatrix A C h0).map (Rat.castHom ℝ)) (by omega) hu lp hlp p hp0 hap
  have hzp := uniform_complete_active_labels _ hu p hpn lp hlp hap
  have hzq := uniform_complete_active_labels _ hu q hqn lq hlq haq
  exact star_complete_common_face _ c p q hp0 hq0 hp hq lp hlp (univ.image lq)
    (by simp [Finset.card_image_of_injective _ hlq]) hc hd
    (by simpa using hzp) (by simpa using hzq)

#print axioms second_real_common_face
#print axioms star_complete_common_face
#print axioms firstProduct_real_common_face
end
end ADKZPricing
