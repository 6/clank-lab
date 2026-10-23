import CubelikeSC.Spectrum

/-!
# The frame `h₀, h₁, h₂` and the coset sums

Instead of a change of basis (Lemmas 3–4) we keep `V` and pick three
independent `h₀, h₁, h₂ ∈ K(S)` spanning a space that contains `σ`. The coset
of `a` is `π(a) = (a·h₀, a·h₁, a·h₂) ∈ (ZMod 2)^3`, which is what the first
three coordinates of `a` are after the change of basis `h_i ↦ e_{i+1}`.
-/

namespace CubelikeSC

/-- `(ZMod 2)^3`, indexing the cosets and the elements of `H = span h`. -/
abbrev W := Fin 3 → ZMod 2

variable (h : Fin 3 → V)

/-- `comb c = Σ_i c_i h_i`. -/
def comb (c : W) : V := ∑ i, c i • h i

/-- The coset of `a`: `π(a) = (a·h_i)_i`. -/
def proj (a : V) : W := fun i => a ⬝ᵥ h i

lemma dot_comb (a : V) (c : W) : a ⬝ᵥ comb h c = c ⬝ᵥ proj h a := by
  rw [comb, dotProduct_sum]
  simp only [dotProduct_smul, smul_eq_mul]
  rfl

lemma comb_sub (c c' : W) : comb h (c - c') = comb h c - comb h c' := by
  simp [comb, sub_smul, Finset.sum_sub_distrib]

lemma comb_zero : comb h 0 = 0 := by simp [comb]

/-- Character sum over a coset: `Σ_{π a = u} χ(a, x) = 16 Σ_{c : comb c = x} χ(c, u)`. -/
lemma fiber_sum (u : W) (x : V) :
    ∑ a ∈ Finset.univ.filter (fun a => proj h a = u), ((-1 : ℤ) ^ (a ⬝ᵥ x).val) =
      16 * ∑ c : W, if comb h c = x then ((-1 : ℤ) ^ (c ⬝ᵥ u).val) else 0 := by
  have key : ∀ a : V, (if proj h a = u then (8 : ℤ) else 0) =
      ∑ c : W, ((-1 : ℤ) ^ (a ⬝ᵥ comb h c).val) * (-1) ^ (c ⬝ᵥ u).val := by
    intro a
    have := sum_char (proj h a + u)
    simp only [dotProduct_add, neg_one_pow_val_add, add_eq_zero_iff_eq'] at this
    simp only [dot_comb]
    rw [this]; norm_num
  have h8 : 8 * ∑ a ∈ Finset.univ.filter (fun a => proj h a = u), ((-1 : ℤ) ^ (a ⬝ᵥ x).val) =
      128 * ∑ c : W, if comb h c = x then ((-1 : ℤ) ^ (c ⬝ᵥ u).val) else 0 := by
    calc 8 * ∑ a ∈ Finset.univ.filter (fun a => proj h a = u), ((-1 : ℤ) ^ (a ⬝ᵥ x).val)
        = ∑ a : V, (if proj h a = u then (8 : ℤ) else 0) * (-1) ^ (a ⬝ᵥ x).val := by
          rw [Finset.sum_filter, Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          split_ifs <;> simp
      _ = ∑ c : W, (-1) ^ (c ⬝ᵥ u).val * ∑ a : V, ((-1 : ℤ) ^ (a ⬝ᵥ (comb h c + x)).val) := by
          simp only [key, Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => ?_
          rw [dotProduct_add, neg_one_pow_val_add]; ring
      _ = ∑ c : W, (-1) ^ (c ⬝ᵥ u).val * (if comb h c = x then (128 : ℤ) else 0) := by
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [sum_char]; simp only [add_eq_zero_iff_eq']; norm_num
      _ = 128 * ∑ c : W, if comb h c = x then ((-1 : ℤ) ^ (c ⬝ᵥ u).val) else 0 := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun c _ => ?_
          split_ifs <;> ring
  linarith

/-- Each coset has 16 elements. -/
lemma fiber_card (hind : ∀ c, comb h c = 0 → c = 0) (u : W) :
    ((Finset.univ.filter (fun a => proj h a = u)).card : ℤ) = 16 := by
  have := fiber_sum h u 0
  simp only [dotProduct_zero] at this
  have h1 : ((-1 : ℤ) ^ (0 : ZMod 2).val) = 1 := by decide
  rw [h1, Finset.sum_const, nsmul_eq_mul, mul_one] at this
  rw [this]
  have : ∀ c : W, (if comb h c = 0 then ((-1 : ℤ) ^ (c ⬝ᵥ u).val) else 0) =
      if c = 0 then 1 else 0 := by
    intro c
    by_cases hc : c = 0
    · subst hc; simp [comb_zero]
    · have : comb h c ≠ 0 := fun h' => hc (hind c h')
      simp [hc, this]
  simp [this]

/-- Lemma 7: `Σ_{π a = u} λ_a = 16 Σ_{c : comb c ∈ S} χ(c, u)`. -/
lemma fiber_lam (S : Finset V) (u : W) :
    ∑ a ∈ Finset.univ.filter (fun a => proj h a = u), lam S a =
      16 * ∑ c ∈ Finset.univ.filter (fun c => comb h c ∈ S), ((-1 : ℤ) ^ (c ⬝ᵥ u).val) := by
  unfold lam
  rw [Finset.sum_comm]
  simp only [fiber_sum, ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm, Finset.sum_filter]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_ite_eq]

/-- Lemma 5 (separation): different cosets have different eigenvalues. -/
lemma proj_eq_of_lam_eq {S : Finset V} (hK : ∀ i, h i ∈ K S) {a b : V}
    (hab : lam S a = lam S b) : proj h a = proj h b := by
  funext i
  exact (mem_K S).1 (hK i) a b hab

end CubelikeSC
