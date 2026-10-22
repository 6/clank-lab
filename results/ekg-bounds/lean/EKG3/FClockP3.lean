import EKG3.FHolesP3
import EKG.CountingExact
import EKG.VerifiedSpans

namespace EKG3.P3.FarTail
open EKG Real EKG.CanonicalCounting

theorem odd_count_half_span {u : ℕ} (hu : 8 ≤ u) :
    2*(O u:ℝ) + (e u:ℝ) ≤ (nonTickTop canonical u:ℝ) + 2 := by
  classical
  let S := Clock.nonTickOddAbove canonical u spanTickValue
  let T := nonTickTop canonical u
  have hspec : ∀ m ∈ S, ¬2 ∣ m ∧ e u < m ∧ m ≤ T := by
    intro m hm
    obtain ⟨hodd, hnt⟩ := Finset.mem_filter.mp hm
    obtain ⟨hused, hmo, hgt⟩ := Finset.mem_filter.mp hodd
    obtain ⟨i, hi, hv⟩ := (Clock.mem_usedValues canonical u m).mp hused
    have htop := nonTick_le_top canonical (by omega : i≤u) (by simpa [hv] using hnt)
    exact ⟨hmo, hgt, by simpa [hv, T] using htop⟩
  have hcard : S.card ≤ (Finset.Ico (e u/2) ((T+1)/2)).card := by
    apply Finset.card_le_card_of_injOn (fun m : ℕ => m/2)
    · intro m hm
      obtain ⟨hodd, hgt, htop⟩ := hspec m hm
      have hmod : m%2=1 := by omega
      change m/2 ∈ Finset.Ico (e u/2) ((T+1)/2)
      exact Finset.mem_Ico.mpr (by omega)
    · intro m hm r hr heq
      have hm' := (hspec m hm).1
      have hr' := (hspec r hr).1
      change m/2=r/2 at heq
      omega
  rw [Nat.card_Ico] at hcard
  have heven := (frontier_spec canonical u).2.1
  have hlow := frontier_le_nonTickTop_add_two canonical (by omega : 1≤u)
  have hn : 2*S.card + e u ≤ T+2 := by dsimp [e] at *; omega
  change 2*((S.card:ℕ):ℝ)+(e u:ℝ) ≤ (T:ℝ)+2
  exact_mod_cast hn

theorem state_bounds (hrs : TailPiBounds) {u : ℕ} (hu : 8 ≤ u)
    (he : (10:ℝ)^153 ≤ e u) :
    (u:ℝ)+4 < 1.0766*(e u:ℝ) ∧
    0.997*(e u:ℝ) < (u:ℝ)+1 ∧
    (nonTickTop canonical u:ℝ) < 1.15288*(e u:ℝ) := by
  let x : ℝ := e u
  let r : ℝ := sqrt x
  let k : ℝ := (K u:ℝ)+1
  obtain ⟨hlog, hroot, hlarge⟩ := large_parameters he
  have hx : 0 < x := by dsimp [x]; linarith
  have hr : 0 < r := by dsimp [r,x]; linarith
  have hr2 : r^2=x := Real.sq_sqrt hx.le
  have hL : 0 < log x := by dsimp [x]; linarith
  have hp := sqrt_prime_bound hrs he
  have hp' : sqrtPrimeCount x ≤ (0.00594:ℝ)*r := by
    apply hp.trans
    have hc : (2*1.045/log x:ℝ) < 0.00594 := by
      apply (div_lt_iff₀ hL).mpr
      dsimp [x]; linarith
    exact mul_le_mul_of_nonneg_right hc.le hr.le
  have hkn := early_even_bound canonical u
  have hk1 : k ≤ 12*sqrtPrimeCount x + 721 := by
    have hn : K u + 1 ≤ 12*Nat.primeCounting (Nat.sqrt (e u))+721 := by
      dsimp [K,e] at *; omega
    have hn' : (K u:ℝ)+1 ≤ 12*(Nat.primeCounting (Nat.sqrt (e u)):ℝ)+721 := by
      exact_mod_cast hn
    simpa only [primeCounting_sqrt_nat_eq] using hn'
  have hk : k ≤ (0.071191:ℝ)*r := by
    have hkb : k ≤ kappa x * r := by
      have hp0 := sqrt_prime_bound hrs he
      have hm := mul_le_mul_of_nonneg_left hp0 (by norm_num : (0:ℝ)≤12)
      have hid : kappa x * r = 12*((2*1.045/log x)*r)+721 := by
        unfold kappa; dsimp [r]; field_simp; ring
      rw [hid]
      change 12*sqrtPrimeCount x ≤ 12*((2*1.045/log x)*r) at hm
      linarith
    have hnum := (numeric_bounds he).1
    have hm := mul_lt_mul_of_pos_right hnum hr
    nlinarith
  have hk0 : 0 ≤ k := by dsimp [k]; positivity
  have hksq : k^2 ≤ (0.071191:ℝ)^2*x := by nlinarith
  have hsqr : Real.sqrt (k^2+x) ≤ (1.002531:ℝ)*r := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · nlinarith
  have hquad := nonTickTop_quadratic canonical hu
  have hquad' : (nonTickTop canonical u:ℝ)-x ≤ 2*k^2+2*k*Real.sqrt (k^2+x) := by
    simpa [x,k,K,e,Nat.cast_add,Nat.cast_one] using hquad
  have hmul := mul_le_mul hk hsqr (sqrt_nonneg _) (by positivity : (0:ℝ)≤0.071191*r)
  have hspan : (nonTickTop canonical u:ℝ)-x < 0.15288*x := by nlinarith
  have hK : (K u:ℝ) < 0.0001*x := by
    have hrr : (10^12:ℝ) ≤ r := hroot
    nlinarith
  have hholes := Clock.holes_card_bound canonical hu
  have hH : (H u:ℝ) < 0.00046*x := by
    have hH0 : (H u:ℝ) ≤ sqrtPrimeCount x*(13*sqrtPrimeCount x+725) := by
      have hc : ((Clock.holes canonical u).card:ℝ) ≤
          (Nat.primeCounting (Nat.sqrt (e u)):ℝ)*
          (13*(Nat.primeCounting (Nat.sqrt (e u)):ℝ)+725) := by
        exact_mod_cast hholes
      simpa only [H, primeCounting_sqrt_nat_eq] using hc
    have hq0 : 0 ≤ sqrtPrimeCount x := by unfold sqrtPrimeCount realPrimeCount; positivity
    have hm := mul_le_mul hp' (by linarith : 13*sqrtPrimeCount x+725 ≤ 13*(0.00594*r)+725)
      (by positivity : (0:ℝ)≤13*sqrtPrimeCount x+725) (by positivity : (0:ℝ)≤0.00594*r)
    have hrr : (10^12:ℝ) ≤ r := hroot
    nlinarith
  have hA := prime_combination_bounds hrs he
  have ha := (numeric_bounds he).2.2.1
  have hAhi : primeCombination (e u) < 0.0013439*x := by
    have hm := mul_lt_mul_of_pos_right ha hx
    exact lt_of_le_of_lt hA.2 hm
  have hclock := exact_integer_clock u hu
  have hc : (e u:ℝ)-((u:ℝ)+1) = primeCombination (e u)+(H u:ℝ)-(K u:ℝ)-(O u:ℝ)+(correction u:ℝ) := by
    have hz : (e u:ℝ)-((u+1:ℕ):ℝ) =
      (Nat.primeCounting (e u):ℝ)-2*(Nat.primeCounting (e u/2):ℝ)+
      (Nat.primeCounting (e u/3):ℝ)+(H u:ℝ)-(K u:ℝ)-(O u:ℝ)+(correction u:ℝ) := by
      exact_mod_cast hclock
    simpa [primeCombination] using hz
  have hcorr := correction_bounds u hu
  have hc1 : (1:ℝ)≤correction u := by exact_mod_cast hcorr.1
  have hc5 : (correction u:ℝ)≤5 := by exact_mod_cast hcorr.2
  have hO := odd_count_half_span hu
  have hH0 : (0:ℝ)≤H u := by positivity
  have hK0 : (0:ℝ)≤K u := by positivity
  have hO0 : (0:ℝ)≤O u := by positivity
  change (u:ℝ)+4 < 1.0766*x ∧ 0.997*x < (u:ℝ)+1 ∧ _
  refine ⟨?_, ?_, by linarith⟩
  · linarith only [hc,hc1,hH0,hO,hspan,hK,hA.1,hlarge]
  · linarith only [hc,hc5,hK0,hO0,hAhi,hH,hlarge]

end EKG3.P3.FarTail
