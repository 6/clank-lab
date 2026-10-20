import EKG.PartAFinite
import EKG.PartALocalization
import EKG.PartACapacity

/-!
The fixed-modulus capacity bound applied to the full actual predecessor
injection. The localization constants precede the choice of capacity
coefficient; the capacity constant precedes every observed prefix and
every controlling prime.
-/

namespace EKG.PartA

/-- Once the finite numerical conditions hold, all upper-half rungs
inject into primes in one uniformly localized cofactor interval.
-/
theorem window_gap_bound :
    ∃ H : ℝ, 0 < H ∧ ∃ X : ℝ,
      ∀ eta : ℝ, 0 < eta → ∃ C : ℝ, 0 ≤ C ∧
      ∀ (t i r M : ℕ) (B : ℝ),
        X ≤ (frontier canonical t : ℝ) →
        9 ≤ frontier canonical t →
        frontier canonical t < nonTickTop canonical t →
        2 ≤ i → i ≤ t →
        nonTickTop canonical t = canonical.a i →
        r.Prime → r ∣ canonical.a (i - 1) →
        2 ≤ M → 3 < B → (M : ℝ) < B →
        4 * B * (earlyEvenCount canonical t + 1 : ℕ) ≤
          (nonTickTop canonical t : ℝ) - (frontier canonical t : ℝ) →
        (nonTickTop canonical t : ℝ) ≤ (2 * r * M : ℕ) * B →
        (nonTickTop canonical t : ℝ) < B ^ 3 →
        (nonTickTop canonical t : ℝ) ≤ (frontier canonical t : ℝ) +
          (4 * 793 ^ 2 + 2 * 793 : ℝ) * logRate (frontier canonical t) →
        (nonTickTop canonical t : ℝ) < 2 * (frontier canonical t : ℝ) →
        (nonTickTop canonical t : ℝ) - (frontier canonical t : ℝ) ≤
          8 * H * eta * (M : ℝ) * logRate (frontier canonical t) +
            4 * (r : ℝ) * (M : ℝ) * (C + 1) := by
  classical
  obtain ⟨A, hA, Xloc, hlocal⟩ := partA_adjacent_localization
  let H : ℝ := A + (4 * 793 ^ 2 + 2 * 793 : ℝ)
  have hH : 0 < H := by dsimp [H]; positivity
  refine ⟨H, hH, max 3 Xloc, ?_⟩
  intro eta heta
  obtain ⟨C, hC, hcapacity⟩ := prime_capacity_real_windows eta heta
  refine ⟨C, hC, ?_⟩
  intro t i r M B heX he hlarge hi hit hval hr hri hM hB hMB
    hscale hstride hcube hspan hv2
  let e : ℝ := frontier canonical t
  let v : ℝ := nonTickTop canonical t
  have he3 : 3 ≤ e := (le_max_left _ _).trans heX
  have heloc : Xloc ≤ e := (le_max_right _ _).trans heX
  have hL : 0 ≤ logRate e := logRate_nonneg (by linarith)
  have hrreal : (0 : ℝ) < r := by exact_mod_cast hr.pos
  have hMpos : 0 < M := by omega
  have hd : 0 < 2 * r * M := by have := hr.pos; positivity
  obtain ⟨index, cofactor, hw, hinj⟩ :=
    many_predecessor_injection he hlarge hi hit hval hr hri hM hB hMB
      hscale hstride hcube
  let F : Finset ℕ := (rungs t r M).image cofactor
  have hcard : F.card = (rungs t r M).card :=
    Finset.card_image_of_injOn hinj
  have hmembers : ∀ q ∈ F,
      q.Prime ∧ (e - H * logRate e) / (r : ℝ) ≤ (q : ℝ) ∧
        (q : ℝ) ≤ (e - H * logRate e) / (r : ℝ) +
          2 * H * logRate e / (r : ℝ) := by
    intro q hq
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hq
    have w := hw j hj
    obtain ⟨hylo, hyhi⟩ := progressionIndices_bounds hd hj
    have hyE_nat : frontier canonical t < canonical.a (index j) := by
      rw [w.value_eq]
      have hymid : frontier canonical t + nonTickTop canonical t <
          2 * (2 * r * M * j) := by omega
      omega
    have hyv_nat : canonical.a (index j) < nonTickTop canonical t := by
      rw [w.value_eq]
      exact hyhi
    have hyE : e < (canonical.a (index j) : ℝ) := by
      dsimp [e]
      exact_mod_cast hyE_nat
    have hyv : (canonical.a (index j) : ℝ) < v := by
      dsimp [v]
      exact_mod_cast hyv_nat
    have hloc := hlocal e heloc (index j) hyE
      (by linarith : (canonical.a (index j) : ℝ) ≤ 2 * e)
      w.smooth_value w.smooth_predecessor
    have hlocbounds := abs_le.mp hloc
    have hC1L : 0 ≤ (4 * 793 ^ 2 + 2 * 793 : ℝ) * logRate e :=
      mul_nonneg (by norm_num) hL
    have hdlo : e - H * logRate e ≤ (canonical.a (index j - 1) : ℝ) := by
      dsimp [H]
      nlinarith only [hlocbounds.1, hyE.le, hC1L]
    have hyspan : (canonical.a (index j) : ℝ) ≤
        e + (4 * 793 ^ 2 + 2 * 793 : ℝ) * logRate e :=
      hyv.le.trans hspan
    have hdhi : (canonical.a (index j - 1) : ℝ) ≤ e + H * logRate e := by
      dsimp [H]
      nlinarith only [hlocbounds.2, hyspan]
    have hpred : (canonical.a (index j - 1) : ℝ) =
        (r : ℝ) * (cofactor j : ℝ) := by
      exact_mod_cast w.predecessor_eq
    refine ⟨w.cofactor_prime, ?_, ?_⟩
    · apply (div_le_iff₀ hrreal).mpr
      nlinarith only [hdlo, hpred]
    · have hright : (e - H * logRate e) / (r : ℝ) +
          2 * H * logRate e / (r : ℝ) =
            (e + H * logRate e) / (r : ℝ) := by ring
      rw [hright]
      apply (le_div_iff₀ hrreal).mpr
      nlinarith only [hdhi, hpred]
  have hz : 0 ≤ 2 * H * logRate e / (r : ℝ) := by positivity
  have hcap := hcapacity F ((e - H * logRate e) / (r : ℝ))
    (2 * H * logRate e / (r : ℝ)) hz hmembers
  rw [hcard] at hcap
  have hcount : v - e ≤ 4 * (r : ℝ) * (M : ℝ) *
      (((rungs t r M).card : ℝ) + 1) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (rungs_count (t := t) hr.pos hMpos)
  have hmulpos : 0 ≤ 4 * (r : ℝ) * (M : ℝ) := by positivity
  change v - e ≤ 8 * H * eta * (M : ℝ) * logRate e +
    4 * (r : ℝ) * (M : ℝ) * (C + 1)
  calc
    v - e ≤ 4 * (r : ℝ) * (M : ℝ) * (((rungs t r M).card : ℝ) + 1) := hcount
    _ ≤ 4 * (r : ℝ) * (M : ℝ) *
        (eta * (2 * H * logRate e / (r : ℝ)) + C + 1) :=
      mul_le_mul_of_nonneg_left (by linarith :
        ((rungs t r M).card : ℝ) + 1 ≤
          eta * (2 * H * logRate e / (r : ℝ)) + C + 1) hmulpos
    _ = 8 * H * eta * (M : ℝ) * logRate e +
        4 * (r : ℝ) * (M : ℝ) * (C + 1) := by
      field_simp [ne_of_gt hrreal]
      <;> ring

end EKG.PartA
