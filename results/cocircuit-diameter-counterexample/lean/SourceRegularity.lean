import SourceCertificate
import RealActiveTransport

namespace ADKZPricing
open Matrix Finset
noncomputable section

/-- The original affine chart of a homogeneous source matrix. -/
def sourceSpatial {K : Type*} {n d : ℕ} (A : Matrix (Fin n) (Fin (d + 1)) K) :
    Matrix (Fin n) (Fin d) K := fun i j => A i j.succ

def sourceBound {K : Type*} [Neg K] {n d : ℕ} (A : Matrix (Fin n) (Fin (d + 1)) K) :
    Fin n → K := fun i => -A i 0

/-- The finite local neighbor certificate proves original central
    regularity on EVERY real/rational ray, including previously unlisted
    active bases. Boundedness and strict coordinate-zero chart are derived. -/
theorem source_homogeneous_regularity {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] {n d : ℕ} {V : Type*} [Fintype V] [Nonempty V]
    (A : Matrix (Fin n) (Fin (d + 1)) K)
    (C : SourceVertexCertificate (sourceSpatial A) (sourceBound A) V)
    (i₀ : Fin n) (ha : ∀ i, 0 < A i 0)
    (v : Fin (d + 1) → K) (hv : v ≠ 0) (hf : StarFeasible A none v)
    (label : Fin d → Fin n) (hl : Function.Injective label)
    (hx : ∀ j, A (label j) ⬝ᵥ v = 0) :
    0 < v 0 ∧ (A.submatrix label Fin.succ).det ≠ 0 ∧
      ∀ i, i ∉ Set.range label → 0 < A i ⬝ᵥ v := by
  have hnon : v 0 ≠ 0 ∨ (fun j : Fin d => v j.succ) ≠ 0 := by
    by_contra hn
    push_neg at hn
    apply hv
    ext i
    exact Fin.cases hn.1 (fun j => congrFun hn.2 j) i
  have hcone (i : Fin n) : 0 ≤ A i 0 * v 0 + sourceSpatial A i ⬝ᵥ (fun j => v j.succ) := by
    have he := hf i
    simpa [starSign, dotProduct, Fin.sum_univ_succ, sourceSpatial] using he
  have hactive (j : Fin d) :
      A (label j) 0 * v 0 + sourceSpatial A (label j) ⬝ᵥ (fun k => v k.succ) = 0 := by
    simpa [dotProduct, Fin.sum_univ_succ, sourceSpatial] using hx j
  have hr := certified_ordered_homogeneous_regularity (fun i => A i 0) (sourceSpatial A)
    i₀ ha C.point C.basis C.next C.gain C.feasible C.active_count C.gain_positive
    C.basis_active C.neighbor_inverse (v 0) (fun j => v j.succ) hnon hcone label hl hactive
  refine ⟨hr.1, hr.2.1, ?_⟩
  intro i hi
  simpa [dotProduct, Fin.sum_univ_succ, sourceSpatial] using hr.2.2 i hi

/-- Cast the exact source certificate to the real field without replacing
    its points, neighbor indices or original basis labels. -/
def SourceVertexCertificate.toReal {n d : ℕ} {V : Type*}
    {A : Matrix (Fin n) (Fin d) ℚ} {b : Fin n → ℚ}
    (C : SourceVertexCertificate A b V) :
    SourceVertexCertificate (A.map (Rat.castHom ℝ)) (fun i => (b i : ℝ)) V where
  point v j := (C.point v j : ℝ)
  basis := C.basis
  next := C.next
  feasible v i := by
    change (b i : ℝ) ≤ ∑ j, (A i j : ℝ) * (C.point v j : ℝ)
    exact_mod_cast C.feasible v i
  basis_injective := C.basis_injective
  active_exact v i := by
    have he : (∑ j, (A i j : ℝ) * (C.point v j : ℝ)) = (b i : ℝ) ↔ A i ⬝ᵥ C.point v = b i := by
      unfold dotProduct
      norm_cast
    exact he.trans (C.active_exact v i)
  neighbor_keeps v j k hk := by
    change (∑ l, (A (C.basis v k) l : ℝ) * (C.point (C.next v j) l : ℝ)) = (b (C.basis v k) : ℝ)
    exact_mod_cast C.neighbor_keeps v j k hk
  neighbor_leaves v j := by
    change (∑ l, (A (C.basis v j) l : ℝ) * (C.point (C.next v j) l : ℝ)) ≠ (b (C.basis v j) : ℝ)
    exact_mod_cast C.neighbor_leaves v j

/-- The rational finite source instance supplies the integer cofactor
    interface for the FIRST perturbation; no stability premise is added. -/
theorem source_regularOrderedLabel {n d : ℕ} {V : Type*} [Fintype V] [Nonempty V]
    (A : Matrix (Fin n) (Fin (d + 1)) ℤ)
    (C : SourceVertexCertificate (sourceSpatial (A.map (Int.castRingHom ℚ)))
      (sourceBound (A.map (Int.castRingHom ℚ))) V)
    (i₀ : Fin n) (ha : ∀ i, 0 < A i 0) (f : Fin (d + 1) → Fin n)
    (hf : Function.Injective (fun j : Fin d => f j.succ)) :
    RegularOrderedLabel A (starUnit none) f := by
  intro v hv hfeas hactive
  let q : Fin (d + 1) → ℚ := fun j => (v j : ℚ)
  have hqn : q ≠ 0 := by
    obtain ⟨j, hj⟩ := hv
    intro hz
    exact hj (by have he := congrFun hz j; change (v j : ℚ) = 0 at he; exact_mod_cast he)
  have hqf : StarFeasible (A.map (Int.castRingHom ℚ)) none q := by
    intro i
    have he := hfeas i
    simp only [starUnit, ↓reduceIte, Units.val_one, one_mul] at he
    change 0 ≤ starSign none i * (∑ j, (A i j : ℚ) * (v j : ℚ))
    simp only [starSign, ↓reduceIte, one_mul]
    exact_mod_cast he
  have hqa (j : Fin d) : (A.map (Int.castRingHom ℚ)) (f j.succ) ⬝ᵥ q = 0 := by
    change ∑ k, (A (f j.succ) k : ℚ) * (v k : ℚ) = 0
    exact_mod_cast hactive j
  have hr := source_homogeneous_regularity (A.map (Int.castRingHom ℚ)) C i₀
    (fun i => by change (0 : ℚ) < (A i 0 : ℚ); exact_mod_cast ha i) q hqn hqf _ hf hqa
  constructor
  · intro hz
    have he := Int.cast_det (R := ℚ) (A.submatrix (fun j : Fin d => f j.succ) Fin.succ)
    change (((A.submatrix (fun j : Fin d => f j.succ) Fin.succ).det : ℤ) : ℚ) =
      ((A.map (Int.castRingHom ℚ)).submatrix (fun j : Fin d => f j.succ) Fin.succ).det at he
    rw [hz, Int.cast_zero] at he
    exact hr.2.1 he.symm
  · intro i hi
    have he := hr.2.2 i hi
    change (0 : ℚ) < ∑ j, (A i j : ℚ) * (v j : ℚ) at he
    have hz : 0 < ∑ j, A i j * v j := by exact_mod_cast he
    simpa [starUnit] using hz

#print axioms source_homogeneous_regularity
#print axioms SourceVertexCertificate.toReal
#print axioms source_regularOrderedLabel
end
end ADKZPricing
