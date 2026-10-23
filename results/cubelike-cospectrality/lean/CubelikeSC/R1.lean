import CubelikeSC.Spectrum

/-!
# R1 (the paper): strongly cospectral vertices differ by an element of `K(S)`

The characters `χ_a(x) = (-1)^{a·x}` are eigenvectors of `A` with eigenvalue
`λ_a`. If `λ_a = λ_b = θ` then `χ_a, χ_b` lie in the `θ`-eigenspace, so, `E_θ`
being self-adjoint and fixing them, `⟨E_θ e_u, χ_c⟩ = χ_c(u)` for `c = a, b`.
`E_θ e_u = ε E_θ e_v` then gives `χ_c(u) = ε χ_c(v)`, hence
`χ_a(v - u) = ε = χ_b(v - u)`, i.e. `a·(v-u) = b·(v-u)`.
Only this direction of R1 is needed.
-/

namespace CubelikeSC

open Module.End Matrix

/-- `(-1)^x` for `x ∈ ZMod 2`, in `ℝ`. -/
def sgn (x : ZMod 2) : ℝ := (-1) ^ x.val

lemma sgn_eq (x : ZMod 2) : sgn x = (((-1 : ℤ) ^ x.val : ℤ) : ℝ) := by
  simp [sgn]

lemma sgn_add (x y : ZMod 2) : sgn (x + y) = sgn x * sgn y := by
  rw [sgn_eq, sgn_eq, sgn_eq, neg_one_pow_val_add]; push_cast; ring

lemma sgn_mul_self (x : ZMod 2) : sgn x * sgn x = 1 := by
  unfold sgn; rw [← pow_add, ← two_mul, pow_mul]; norm_num

lemma sgn_inj {x y : ZMod 2} (h : sgn x = sgn y) : x = y := by
  rw [sgn_eq, sgn_eq, Int.cast_inj] at h
  revert x y; decide

lemma sub_eq_add' (x y : V) : x - y = x + y := by
  funext i; simp only [Pi.sub_apply, Pi.add_apply]
  rcases zmod2_cases (y i) with h | h <;> rw [h] <;> ring_nf; rfl

/-- The character `χ_a` as a vector of `ℝ^V`. -/
def chi (a : V) : EuclideanSpace ℝ V := WithLp.toLp 2 fun x => sgn (a ⬝ᵥ x)

lemma chi_apply (a x : V) : chi a x = sgn (a ⬝ᵥ x) := rfl

/-- `A χ_a = λ_a χ_a`. -/
lemma adj_chi (S : Finset V) (a : V) :
    Matrix.toEuclideanLin (adj S) (chi a) = (lam S a : ℝ) • chi a := by
  ext x
  change ∑ y, adj S x y * sgn (a ⬝ᵥ y) = (lam S a : ℝ) * sgn (a ⬝ᵥ x)
  simp only [adj, ite_mul, one_mul, zero_mul]
  have h1 : ∀ y : V, (if x - y ∈ S then sgn (a ⬝ᵥ y) else 0) =
      ∑ s ∈ S, if y = x - s then sgn (a ⬝ᵥ (x - s)) else 0 := by
    intro y
    by_cases hy : x - y ∈ S
    · rw [if_pos hy, Finset.sum_eq_single (x - y)]
      · simp
      · intro s _ hs; rw [if_neg]; intro e; exact hs (by rw [e]; abel)
      · intro h; exact absurd hy h
    · rw [if_neg hy]; symm
      apply Finset.sum_eq_zero
      intro s hs; rw [if_neg]; intro e; exact hy (by rw [e]; simpa using hs)
  simp only [h1]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have h2 : ∀ s, sgn (a ⬝ᵥ (x - s)) = sgn (a ⬝ᵥ x) * sgn (a ⬝ᵥ s) := by
    intro s; rw [sub_eq_add', dotProduct_add, sgn_add]
  simp only [h2, ← Finset.mul_sum, lam]
  push_cast
  rw [mul_comm]
  rfl

lemma chi_ne_zero (a : V) : chi a ≠ 0 := by
  intro h
  have := congrArg (fun f : EuclideanSpace ℝ V => f 0) h
  simp [chi_apply, sgn] at this

lemma chi_mem (S : Finset V) (a : V) :
    chi a ∈ eigenspace (Matrix.toEuclideanLin (adj S)) (lam S a) := by
  rw [mem_eigenspace_iff]; exact adj_chi S a

lemma hasEigenvalue_lam (S : Finset V) (a : V) :
    HasEigenvalue (Matrix.toEuclideanLin (adj S)) (lam S a) :=
  hasEigenvalue_of_hasEigenvector ⟨chi_mem S a, chi_ne_zero a⟩

/-- `⟨E_θ e_u, χ_c⟩ = χ_c(u)` when `λ_c = θ`. -/
lemma inner_proj_chi (S : Finset V) (c u : V) :
    inner ℝ ((eigenspace (Matrix.toEuclideanLin (adj S)) (lam S c)).starProjection
      (EuclideanSpace.single u 1)) (chi c) = sgn (c ⬝ᵥ u) := by
  rw [Submodule.inner_starProjection_left_eq_right,
    (Submodule.starProjection_eq_self_iff).2 (chi_mem S c), EuclideanSpace.inner_single_left]
  simp [chi_apply]

/-- R1, the direction used: strongly cospectral `u, v` have `v - u ∈ K(S)`. -/
theorem sub_mem_K_of_sc {S : Finset V} {u v : V} (h : StronglyCospectral S u v) :
    v - u ∈ K S := by
  rw [mem_K]
  intro a b hab
  have hP := h (lam S a) (hasEigenvalue_lam S a)
  simp only at hP
  -- `χ_c(u) = ε χ_c(v)` for `c = a, b`
  obtain ⟨ε, hε, hε2⟩ : ∃ ε : ℝ, ε * ε = 1 ∧ ∀ c : V, lam S c = lam S a →
      sgn (c ⬝ᵥ u) = ε * sgn (c ⬝ᵥ v) := by
    rcases hP with e | e
    · refine ⟨1, by norm_num, fun c hc => ?_⟩
      have h1 := inner_proj_chi S c u
      have h2 := inner_proj_chi S c v
      rw [hc, e] at h1; rw [hc] at h2
      rw [← h1, h2, one_mul]
    · refine ⟨-1, by norm_num, fun c hc => ?_⟩
      have h1 := inner_proj_chi S c u
      have h2 := inner_proj_chi S c v
      rw [hc, e, inner_neg_left] at h1; rw [hc] at h2
      rw [← h1, h2]; ring
  have key : ∀ c : V, lam S c = lam S a → sgn (c ⬝ᵥ (v - u)) = ε := by
    intro c hc
    rw [sub_eq_add', dotProduct_add, sgn_add, hε2 c hc]
    have := sgn_mul_self (c ⬝ᵥ v)
    linear_combination ε * this
  exact sgn_inj ((key a rfl).trans (key b hab.symm).symm)

end CubelikeSC
