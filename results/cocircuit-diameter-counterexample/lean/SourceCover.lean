import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Finset.Max

/- Soundness of the bounded simple-cell source certificate. This file
   proves geometric coverage from local neighbor/basis data; it does not
   assume that a supplied graph already contains every vertex. -/
namespace ADKZPricing
open Matrix Finset
noncomputable section

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

def AffineFeasible {n d : ℕ} (A : Matrix (Fin n) (Fin d) 𝕜) (b : Fin n → 𝕜)
    (x : Fin d → 𝕜) : Prop := ∀ i, b i ≤ A i ⬝ᵥ x

def activeRows {n d : ℕ} (A : Matrix (Fin n) (Fin d) 𝕜) (b : Fin n → 𝕜)
    (x : Fin d → 𝕜) : Finset (Fin n) := Finset.univ.filter (fun i => A i ⬝ᵥ x = b i)

def neighborDirections {d : ℕ} (p : Fin d → 𝕜) (neighbors : Fin d → Fin d → 𝕜)
    (gain : Fin d → 𝕜) : Matrix (Fin d) (Fin d) 𝕜 :=
  fun i j => (neighbors j i - p i) / gain j

omit [IsStrictOrderedRing 𝕜] in
theorem neighbor_inverse_of_slacks {n d : ℕ}
    (A : Matrix (Fin n) (Fin d) 𝕜) (p : Fin d → 𝕜) (bas : Fin d → Fin n)
    (neighbors : Fin d → Fin d → 𝕜) (gain : Fin d → 𝕜)
    (hgain : ∀ j, 0 < gain j)
    (hslack : ∀ i j, A (bas i) ⬝ᵥ (neighbors j - p) = if i = j then gain j else 0) :
    neighborDirections p neighbors gain *
      A.submatrix bas id = 1 := by
  apply Matrix.mul_eq_one_comm.mp
  ext i j
  change (∑ k, A (bas i) k * ((neighbors j k - p k) / gain j)) = if i = j then 1 else 0
  simp only [← mul_div_assoc, ← Finset.sum_div]
  change (A (bas i) ⬝ᵥ (neighbors j - p)) / gain j = _
  rw [hslack]
  split_ifs <;> simp [(hgain j).ne']

theorem local_max_is_global {n d : ℕ}
    (A : Matrix (Fin n) (Fin d) 𝕜) (b : Fin n → 𝕜)
    (p : Fin d → 𝕜) (bas : Fin d → Fin n)
    (neighbors : Fin d → Fin d → 𝕜) (gain : Fin d → 𝕜)
    (hgain : ∀ j, 0 < gain j)
    (hactive : ∀ j, A (bas j) ⬝ᵥ p = b (bas j))
    (hinverse : neighborDirections p neighbors gain *
      A.submatrix bas id = 1)
    (c x : Fin d → 𝕜) (hx : AffineFeasible A b x)
    (hlocal : ∀ j, c ⬝ᵥ neighbors j ≤ c ⬝ᵥ p) : c ⬝ᵥ x ≤ c ⬝ᵥ p := by
  let B := A.submatrix bas id
  let D : Matrix (Fin d) (Fin d) 𝕜 := fun i j => (neighbors j i - p i) / gain j
  let α := B *ᵥ (x - p)
  have hα : ∀ j, 0 ≤ α j := by
    intro j
    change 0 ≤ A (bas j) ⬝ᵥ (x - p)
    rw [dotProduct_sub, hactive]
    exact sub_nonneg.mpr (hx (bas j))
  have hdecomp : D *ᵥ α = x - p := by
    rw [show α = B *ᵥ (x - p) by rfl, Matrix.mulVec_mulVec]
    change (D * B) *ᵥ (x - p) = _
    have hDB : D * B = 1 := hinverse
    rw [hDB, Matrix.one_mulVec]
  have hdir : ∀ j, (c ᵥ* D) j ≤ 0 := by
    intro j
    change (∑ i, c i * ((neighbors j i - p i) / gain j)) ≤ 0
    have heq : (∑ i, c i * ((neighbors j i - p i) / gain j)) =
        (c ⬝ᵥ neighbors j - c ⬝ᵥ p) / gain j := by
      simp only [← mul_div_assoc, ← Finset.sum_div]
      congr 1
      simp only [dotProduct, mul_sub, Finset.sum_sub_distrib]
    rw [heq]
    exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hlocal j)) (hgain j).le
  have hobj : c ⬝ᵥ (x - p) ≤ 0 := by
    rw [← hdecomp, dotProduct_mulVec]
    exact Finset.sum_nonpos (fun j _ => mul_nonpos_of_nonpos_of_nonneg (hdir j) (hα j))
  rw [dotProduct_sub] at hobj
  exact sub_nonpos.mp hobj

/-- A finite list closed under all of the certified basis directions
    contains a global maximizer for EVERY linear objective. -/
theorem certified_list_maximizes {n d : ℕ} {V : Type*} [Fintype V] [Nonempty V]
    (A : Matrix (Fin n) (Fin d) 𝕜) (b : Fin n → 𝕜) (p : V → Fin d → 𝕜)
    (bas : V → Fin d → Fin n) (next : V → Fin d → V) (gain : V → Fin d → 𝕜)
    (hgain : ∀ v j, 0 < gain v j)
    (hactive : ∀ v j, A (bas v j) ⬝ᵥ p v = b (bas v j))
    (hinverse : ∀ v, neighborDirections (p v) (fun j => p (next v j)) (gain v) *
      A.submatrix (bas v) id = 1)
    (c : Fin d → 𝕜) :
    ∃ v, ∀ x, AffineFeasible A b x → c ⬝ᵥ x ≤ c ⬝ᵥ p v := by
  classical
  obtain ⟨v, _, hv⟩ := Finset.exists_max_image Finset.univ (fun v => c ⬝ᵥ p v) Finset.univ_nonempty
  refine ⟨v, ?_⟩
  intro x hx
  exact local_max_is_global A b (p v) (bas v) (fun j => p (next v j)) (gain v)
    (hgain v) (hactive v) (hinverse v) c x hx (fun j => hv (next v j) (Finset.mem_univ _))

/-- Every nonempty face specified by input rows contains a listed vertex.
    This covers even a hypothetical omitted vertex/face: x is arbitrary,
    not drawn from the certificate. -/
theorem certified_list_covers_faces {n d : ℕ} {V : Type*} [Fintype V] [Nonempty V]
    (A : Matrix (Fin n) (Fin d) 𝕜) (b : Fin n → 𝕜) (p : V → Fin d → 𝕜)
    (bas : V → Fin d → Fin n) (next : V → Fin d → V) (gain : V → Fin d → 𝕜)
    (hvertices : ∀ v, AffineFeasible A b (p v))
    (hgain : ∀ v j, 0 < gain v j)
    (hactive : ∀ v j, A (bas v j) ⬝ᵥ p v = b (bas v j))
    (hinverse : ∀ v, neighborDirections (p v) (fun j => p (next v j)) (gain v) *
      A.submatrix (bas v) id = 1)
    (I : Finset (Fin n)) (x : Fin d → 𝕜) (hx : AffineFeasible A b x)
    (hIx : ∀ i ∈ I, A i ⬝ᵥ x = b i) :
    ∃ v, ∀ i ∈ I, A i ⬝ᵥ p v = b i := by
  classical
  let c : Fin d → 𝕜 := fun j => -(∑ i ∈ I, A i j)
  have hc (y : Fin d → 𝕜) : c ⬝ᵥ y = -(∑ i ∈ I, A i ⬝ᵥ y) := by
    simp only [c, dotProduct, neg_mul, Finset.sum_neg_distrib, Finset.sum_mul]
    rw [Finset.sum_comm]
  obtain ⟨v, hv⟩ := certified_list_maximizes A b p bas next gain hgain hactive hinverse c
  have hobj := hv x hx
  rw [hc, hc] at hobj
  have hxs : (∑ i ∈ I, A i ⬝ᵥ x) = ∑ i ∈ I, b i := Finset.sum_congr rfl hIx
  rw [hxs] at hobj
  have hnonneg : ∀ i ∈ I, 0 ≤ A i ⬝ᵥ p v - b i :=
    fun i _ => sub_nonneg.mpr (hvertices v i)
  have hsum : (∑ i ∈ I, (A i ⬝ᵥ p v - b i)) = 0 := by
    have h := Finset.sum_nonneg hnonneg
    rw [Finset.sum_sub_distrib] at h ⊢
    linarith
  refine ⟨v, ?_⟩
  intro i hi
  exact sub_eq_zero.mp ((Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum i hi)

/-- The certificate's EXACT active-row counts, together with its local
    closure, discharge whole-arrangement regularity at every feasible
    point with at least d active input rows. Abstract simplicity is not
    assumed. In particular no omitted vertex with excess active rows can
    exist when these finite certificate premises hold. -/
theorem certified_list_covers_many_active {n d : ℕ} {V : Type*} [Fintype V] [Nonempty V]
    (A : Matrix (Fin n) (Fin d) 𝕜) (b : Fin n → 𝕜) (p : V → Fin d → 𝕜)
    (bas : V → Fin d → Fin n) (next : V → Fin d → V) (gain : V → Fin d → 𝕜)
    (hvertices : ∀ v, AffineFeasible A b (p v))
    (hcount : ∀ v, (activeRows A b (p v)).card = d)
    (hgain : ∀ v j, 0 < gain v j)
    (hactive : ∀ v j, A (bas v j) ⬝ᵥ p v = b (bas v j))
    (hinverse : ∀ v, neighborDirections (p v) (fun j => p (next v j)) (gain v) *
      A.submatrix (bas v) id = 1)
    (x : Fin d → 𝕜) (hx : AffineFeasible A b x)
    (hxcount : d ≤ (activeRows A b x).card) :
    ∃ v, x = p v ∧ (activeRows A b x).card = d := by
  obtain ⟨v, hv⟩ := certified_list_covers_faces A b p bas next gain hvertices hgain hactive hinverse
    (activeRows A b x) x hx (fun i hi => (Finset.mem_filter.mp hi).2)
  have hsub : activeRows A b x ⊆ activeRows A b (p v) := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv i hi⟩
  have heq : activeRows A b x = activeRows A b (p v) :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hcount]; exact hxcount)
  have hb : (A.submatrix (bas v) id) *ᵥ x = (A.submatrix (bas v) id) *ᵥ p v := by
    ext j
    change A (bas v j) ⬝ᵥ x = A (bas v j) ⬝ᵥ p v
    rw [hactive]
    have hm : bas v j ∈ activeRows A b (p v) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hactive v j⟩
    rw [← heq] at hm
    exact (Finset.mem_filter.mp hm).2
  have h := congrArg (fun w => neighborDirections (p v) (fun j => p (next v j)) (gain v) *ᵥ w) hb
  dsimp only at h
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hinverse, Matrix.one_mulVec, Matrix.one_mulVec] at h
  exact ⟨v, h, by rw [heq, hcount]⟩

theorem certified_basis_independent {n d : ℕ}
    (A : Matrix (Fin n) (Fin d) 𝕜) (bas : Fin d → Fin n) (D : Matrix (Fin d) (Fin d) 𝕜)
    (hinverse : D * A.submatrix bas id = 1) : (A.submatrix bas id).det ≠ 0 := by
  have h := congrArg Matrix.det hinverse
  rw [Matrix.det_mul, Matrix.det_one] at h
  intro hz
  rw [hz, mul_zero] at h
  exact zero_ne_one h

/-- The previously proved maximizer property excludes every nonzero
    recession direction. No boundedness assumption is smuggled in. -/
theorem no_recession_of_maximizers {n d : ℕ} {V : Type*}
    (A : Matrix (Fin n) (Fin d) 𝕜) (b : Fin n → 𝕜) (p : V → Fin d → 𝕜)
    (hvertices : ∀ v, AffineFeasible A b (p v))
    (hmax : ∀ c, ∃ v, ∀ x, AffineFeasible A b x → c ⬝ᵥ x ≤ c ⬝ᵥ p v)
    (y : Fin d → 𝕜) (hy : ∀ i, 0 ≤ A i ⬝ᵥ y) : y = 0 := by
  have hbound (c : Fin d → 𝕜) : c ⬝ᵥ y ≤ 0 := by
    obtain ⟨v, hv⟩ := hmax c
    have hfeas : AffineFeasible A b (p v + y) := by
      intro i
      rw [dotProduct_add]
      exact (hvertices v i).trans (le_add_of_nonneg_right (hy i))
    have h := hv (p v + y) hfeas
    rw [dotProduct_add] at h
    linarith
  ext j
  have hp : y j ≤ 0 := by simpa using hbound (Pi.single j 1)
  have hn : -y j ≤ 0 := by simpa using hbound (Pi.single j (-1))
  change y j = 0
  linarith

/-- An origin-strict affine system with no recession directions has a
    strictly positive homogeneous chart on every nonzero feasible ray. -/
theorem strict_source_chart {n d : ℕ}
    (a : Fin n → 𝕜) (A : Matrix (Fin n) (Fin d) 𝕜) (i₀ : Fin n)
    (ha : ∀ i, 0 < a i)
    (hrec : ∀ y, (∀ i, 0 ≤ A i ⬝ᵥ y) → y = 0)
    (t : 𝕜) (y : Fin d → 𝕜) (hne : t ≠ 0 ∨ y ≠ 0)
    (hcone : ∀ i, 0 ≤ a i * t + A i ⬝ᵥ y) : 0 < t := by
  by_contra hn
  have ht : t ≤ 0 := le_of_not_gt hn
  have hy : y = 0 := hrec y (by
    intro i
    have hc := hcone i
    have hm := mul_nonpos_of_nonneg_of_nonpos (ha i).le ht
    linarith)
  have hc := hcone i₀
  rw [hy, dotProduct_zero, add_zero] at hc
  have ht0 : t = 0 := le_antisymm ht (nonneg_of_mul_nonneg_right hc (ha i₀))
  exact hne.elim (fun h => h ht0) (fun h => h hy)

theorem affine_normalization {n d : ℕ}
    (a : Fin n → 𝕜) (A : Matrix (Fin n) (Fin d) 𝕜)
    (t : 𝕜) (ht : 0 < t) (y : Fin d → 𝕜)
    (hcone : ∀ i, 0 ≤ a i * t + A i ⬝ᵥ y) :
    AffineFeasible A (fun i => -a i) (fun j => y j / t) ∧
      (∀ i, a i * t + A i ⬝ᵥ y = 0 ↔ A i ⬝ᵥ (fun j => y j / t) = -a i) := by
  have hdot (i : Fin n) : A i ⬝ᵥ (fun j => y j / t) = (A i ⬝ᵥ y) / t := by
    simp only [dotProduct, ← mul_div_assoc, ← Finset.sum_div]
  constructor
  · intro i
    rw [hdot]
    apply (le_div_iff₀ ht).mpr
    have h := hcone i
    change -a i * t ≤ A i ⬝ᵥ y
    nlinarith
  · intro i
    rw [hdot, div_eq_iff ht.ne']
    constructor <;> intro h <;> linarith

/-- Whole-arrangement regularity of the homogeneous source cone follows
    from the finite feasible/simple/neighbor certificate. This theorem
    does not take global cover, boundedness or regularity as hypotheses. -/
theorem certified_source_regularity {n d : ℕ} {V : Type*} [Fintype V] [Nonempty V]
    (a : Fin n → 𝕜) (A : Matrix (Fin n) (Fin d) 𝕜) (i₀ : Fin n) (ha : ∀ i, 0 < a i)
    (p : V → Fin d → 𝕜) (bas : V → Fin d → Fin n)
    (next : V → Fin d → V) (gain : V → Fin d → 𝕜)
    (hvertices : ∀ v, AffineFeasible A (fun i => -a i) (p v))
    (hcount : ∀ v, (activeRows A (fun i => -a i) (p v)).card = d)
    (hgain : ∀ v j, 0 < gain v j)
    (hactive : ∀ v j, A (bas v j) ⬝ᵥ p v = -a (bas v j))
    (hinverse : ∀ v, neighborDirections (p v) (fun j => p (next v j)) (gain v) *
      A.submatrix (bas v) id = 1)
    (t : 𝕜) (y : Fin d → 𝕜) (hne : t ≠ 0 ∨ y ≠ 0)
    (hcone : ∀ i, 0 ≤ a i * t + A i ⬝ᵥ y)
    (hmany : d ≤ (Finset.univ.filter (fun i => a i * t + A i ⬝ᵥ y = 0)).card) :
    ∃ v, 0 < t ∧ (∀ j, y j = t * p v j) ∧
      (Finset.univ.filter (fun i => a i * t + A i ⬝ᵥ y = 0)).card = d ∧
      (A.submatrix (bas v) id).det ≠ 0 := by
  have hmax := certified_list_maximizes A (fun i => -a i) p bas next gain hgain hactive hinverse
  have hrec := no_recession_of_maximizers A (fun i => -a i) p hvertices hmax
  have ht := strict_source_chart a A i₀ ha hrec t y hne hcone
  have hnorm := affine_normalization a A t ht y hcone
  have heq : Finset.univ.filter (fun i => a i * t + A i ⬝ᵥ y = 0) =
      activeRows A (fun i => -a i) (fun j => y j / t) := by
    ext i
    simp only [activeRows, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hnorm.2 i
  rw [heq] at hmany
  obtain ⟨v, hv, hcard⟩ := certified_list_covers_many_active A (fun i => -a i) p bas next gain
    hvertices hcount hgain hactive hinverse (fun j => y j / t) hnorm.1 hmany
  refine ⟨v, ht, ?_, ?_, certified_basis_independent A (bas v) _ (hinverse v)⟩
  · intro j
    have h := congrArg (fun z : Fin d → 𝕜 => z j) hv
    change y j / t = p v j at h
    rw [div_eq_iff ht.ne'] at h
    simpa only [mul_comm] using h
  · rw [heq]
    exact hcard

#print axioms local_max_is_global
#print axioms neighbor_inverse_of_slacks
#print axioms certified_list_maximizes
#print axioms certified_list_covers_faces
#print axioms certified_list_covers_many_active
#print axioms certified_basis_independent
#print axioms no_recession_of_maximizers
#print axioms strict_source_chart
#print axioms affine_normalization
#print axioms certified_source_regularity
end
end ADKZPricing
