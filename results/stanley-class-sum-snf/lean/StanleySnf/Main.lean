import StanleySnf.Form
import StanleySnf.LemmaA
import StanleySnf.LemmaB
import StanleySnf.LemmaC
import StanleySnf.Assembly

/-!
# The main theorem

Given the classical value of the class-multiplication constants (`bridgeFormula`), the
matrix `M n` of `K_(n)` on the centre of `ℤ[S_n]` has Smith normal form
`diag(stanleyD n 0, …, stanleyD n (n-1), 0, …, 0)`.
-/

open Polynomial

namespace StanleySnf

namespace Mn

variable {n : ℕ}

theorem card_pos (hn : 0 < n) (μ : n.Partition) : 0 < μ.parts.card := by
  rcases Multiset.empty_or_exists_mem μ.parts with h | ⟨a, ha⟩
  · have := μ.parts_sum
    rw [h, Multiset.sum_zero] at this
    omega
  · exact Multiset.card_pos_iff_exists_mem.mpr ⟨a, ha⟩

/-- The integer value of `Γ(μ,s) / δ_{ℓ(μ)-1}` given by Lemma C. -/
noncomputable def zC (hn : 0 < n) (μ : n.Partition) (s : Fin n) : ℤ :=
  Classical.choose
    (lemmaC hn μ (μ.parts.card - 1) (by have := card_pos hn μ; omega) s)

theorem zC_spec (hn : 0 < n) (μ : n.Partition) (s : Fin n) :
    GamQ n μ s = (delta n (μ.parts.card - 1) : ℚ) * zC hn μ s :=
  Classical.choose_spec
    (lemmaC hn μ (μ.parts.card - 1) (by have := card_pos hn μ; omega) s)

/-- The integer matrix `α`. -/
noncomputable def alphaZ (hn : 0 < n) : Matrix (Fin n) n.Partition ℤ :=
  fun s ν => Classical.choose (alpha_int hn s ν)

theorem alphaZ_spec (hn : 0 < n) (s : Fin n) (ν : n.Partition) :
    alphaQ n s ν = (alphaZ hn s ν : ℚ) :=
  Classical.choose_spec (alpha_int hn s ν)

theorem eps_sq {μ : n.Partition} : eps μ * eps μ = 1 := by
  unfold eps
  rw [← pow_add, ← two_mul, pow_mul]
  norm_num

end Mn

open Mn

/-- **Main theorem.** Assuming the classical (Frobenius / Murnaghan–Nakayama) value of the
class-multiplication constants, the Smith normal form of the matrix of `K_(n)` acting on the
centre of `ℤ[S_n]` (class-sum basis) is `diag(d_0, …, d_{n-1}, 0, …, 0)` with `d_0 = 1` and
`d_k = c·k!/gcd(k,n)`, `c = 2` if `k ≡ n (mod 2)` else `1`; and `d_0 ∣ d_1 ∣ ⋯`. -/
theorem main (n : ℕ) (hn : 0 < n)
    (hB : ∀ μ ν : n.Partition, (M n μ ν : ℚ) = bridgeFormula n μ ν) :
    HasStanleySNF n (M n) ∧ (∀ r, r + 1 < n → stanleyD n r ∣ stanleyD n (r + 1)) := by
  refine ⟨?_, fun r hr => stanleyD_dvd r hr⟩
  obtain ⟨W, X, hWsupp, hWlow, hWdiag, hX, hWX⟩ := lemmaB hn
  -- `u r i = ∑_μ W r μ η_μ(i)`
  set u : Fin n → Fin n → ℤ := fun r i => ∑ μ, W r μ * eta μ i with hu
  -- `V r s = ∑_μ W r μ zC μ s`, so that `G r s = δ_r V r s`
  set V : Matrix (Fin n) (Fin n) ℤ := fun r s => ∑ μ, W r μ * zC hn μ s with hV
  set D : Fin n → ℤ := fun r => (delta n r : ℤ) with hD
  set E : Matrix n.Partition n.Partition ℤ := Matrix.diagonal fun μ => eps μ with hE
  -- G r s := (1/e_s) ∑_i u r i Q(i,s) = ∑_μ W r μ Γ(μ,s) = δ_r V r s
  have hG : ∀ r s, (∑ μ, (W r μ : ℚ) * GamQ n μ s) = (delta n r : ℚ) * (V r s : ℚ) := by
    intro r s
    simp only [hV, Int.cast_sum, Int.cast_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    by_cases h0 : W r μ = 0
    · simp [h0]
    · have hc := hWsupp r μ h0
      rw [zC_spec hn μ s, show μ.parts.card - 1 = (r : ℕ) by omega]
      ring
  have hGu : ∀ r s, (∑ μ, (W r μ : ℚ) * GamQ n μ s) =
      (∑ i : Fin n, ((u r i * Qf (n - 1) i s : ℤ) : ℚ)) / (ee n s : ℚ) := by
    intro r s
    simp only [GamQ, hu, Finset.mul_sum, Finset.sum_div, Int.cast_sum, Int.cast_mul,
      Finset.sum_mul, mul_div_assoc]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  -- `Γ = X G`
  have hGam : ∀ μ s, GamQ n μ s = ∑ r, (X μ r : ℚ) * ((delta n r : ℚ) * (V r s : ℚ)) := by
    intro μ s
    simp only [← hG, hGu]
    simp only [GamQ]
    rw [show (∑ i : Fin n, ((eta μ i * Qf (n - 1) i s : ℤ) : ℚ)) =
        ∑ i : Fin n, ((((∑ r, X μ r * u r i) * Qf (n - 1) i s : ℤ)) : ℚ) from by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hX μ i]]
    simp only [Int.cast_mul, Int.cast_sum, Finset.sum_mul, Finset.mul_sum, Finset.sum_div,
      mul_div_assoc]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => ?_
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  -- `M = E X diag(δ) V α`
  have hM : M n = E * X * Matrix.diagonal D * V * alphaZ hn := by
    ext μ ν
    have h1 := M_factor hn hB μ ν
    simp only [hGam, alphaZ_spec hn] at h1
    have hassoc : E * X * Matrix.diagonal D * V * alphaZ hn =
        E * (X * Matrix.diagonal D * V * alphaZ hn) := by
      simp only [Matrix.mul_assoc]
    have h2 : ((E * X * Matrix.diagonal D * V * alphaZ hn) μ ν : ℚ) =
        (eps μ : ℚ) * ∑ s : Fin n, (∑ r, (X μ r : ℚ) * ((delta n r : ℚ) * (V r s : ℚ))) *
          (alphaZ hn s ν : ℚ) := by
      rw [hassoc, hE, Matrix.diagonal_mul, Matrix.mul_apply]
      push_cast
      congr 1
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [Matrix.mul_apply]
      push_cast
      congr 1
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [Matrix.mul_diagonal, hD]
      push_cast
      ring
    exact_mod_cast h1.trans h2.symm
  -- `V` is unimodular
  have hVunit : IsUnit V.det := by
    apply antitriangular_isUnit_det
    · intro r s hrs
      have hzero : (∑ i : Fin n, ((u r i * Qf (n - 1) i s : ℤ) : ℚ)) = 0 := by
        refine Finset.sum_eq_zero fun i _ => ?_
        by_cases hir : i < r
        · simp [hu, hWlow r i hir]
        · rw [Qf_eq_zero (by omega) (by omega) (by
            have : (r : ℕ) ≤ i := by simpa using hir
            omega)]
          simp
      have := (hG r s).symm.trans (hGu r s)
      rw [hzero, zero_div] at this
      have hδ : (delta n r : ℚ) ≠ 0 := by exact_mod_cast (delta_pos hn r r.isLt).ne'
      exact_mod_cast (mul_eq_zero.mp this).resolve_left hδ
    · intro r s hrs
      have hs : (s : ℕ) = n - 1 - r := by omega
      have hsum : (∑ i : Fin n, ((u r i * Qf (n - 1) i s : ℤ) : ℚ)) =
          ((u r r * Qf (n - 1) r s : ℤ) : ℚ) := by
        rw [Finset.sum_eq_single r]
        · intro i _ hir
          rcases lt_or_gt_of_ne hir with h | h
          · simp [hu, hWlow r i h]
          · rw [Qf_eq_zero (by omega) (by omega) (by
              have : (r : ℕ) < i := h
              omega)]
            simp
        · simp
      have key := (hG r s).symm.trans (hGu r s)
      rw [hsum] at key
      have hδ : (delta n r : ℚ) ≠ 0 := by exact_mod_cast (delta_pos hn r r.isLt).ne'
      have had := antidiag hn r r.isLt
      rw [← hs] at had
      have hee : (ee n s : ℚ) ≠ 0 := by
        unfold ee
        have := Nat.gcd_pos_of_pos_right n (Nat.succ_pos s)
        positivity
      set c : ℚ := (aa n r : ℚ) * (Qf (n - 1) r s : ℚ) / (ee n s : ℚ) with hc
      have hδV : (delta n r : ℚ) * V r s = c ∨ (delta n r : ℚ) * V r s = -c := by
        rcases hWdiag r with h | h
        · left
          rw [key, show u r r = ∑ μ, W r μ * eta μ r from rfl, h, hc]
          push_cast; ring
        · right
          rw [key, show u r r = ∑ μ, W r μ * eta μ r from rfl, h, hc]
          push_cast; ring
      have hV1 : (V r s : ℚ) = 1 ∨ (V r s : ℚ) = -1 := by
        rcases had with h' | h' <;> rcases hδV with h'' | h''
        · left; exact mul_left_cancel₀ hδ (by rw [h'', h']; ring)
        · right; exact mul_left_cancel₀ hδ (by rw [h'', h']; ring)
        · right; exact mul_left_cancel₀ hδ (by rw [h'', h']; ring)
        · left; exact mul_left_cancel₀ hδ (by rw [h'', h']; ring)
      rcases hV1 with h | h
      · left; exact_mod_cast h
      · right; exact_mod_cast h
  -- `α` is surjective
  have hαsurj : Function.Surjective (alphaZ hn).mulVec := by
    intro v
    obtain ⟨f, hf⟩ := alpha_surj hn v
    refine ⟨f, funext fun t => ?_⟩
    have := hf t
    simp only [alphaZ_spec hn] at this
    simp only [Matrix.mulVec, dotProduct]
    have h' : ((∑ ν, alphaZ hn t ν * f ν : ℤ) : ℚ) = (v t : ℚ) := by
      rw [← this]; push_cast; exact Finset.sum_congr rfl fun ν _ => by ring
    exact_mod_cast h'
  have hEE : E * E = 1 := by
    rw [hE, Matrix.diagonal_mul_diagonal]
    rw [← Matrix.diagonal_one]
    congr 1
    funext μ
    exact eps_sq
  obtain ⟨κ, hκ, b, hb⟩ := range_of_factor (M n) E hEE X W hWX D V hVunit (alphaZ hn) hαsurj hM
  refine ⟨κ, hκ, b, ?_⟩
  rw [hb]
  congr 1
  ext x
  simp only [Set.mem_range, hD]
  constructor <;> rintro ⟨r, rfl⟩ <;> exact ⟨r, by rw [delta_eq_stanleyD hn r r.isLt]⟩

end StanleySnf
