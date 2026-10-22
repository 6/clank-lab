import EKG3.ArithmeticLargeSieve
import EKG3.TBootstrapP3
import EKG3.LemmaC
import EKG3.LemmaD
import EKG3.FPrimeBounds
import EKG.CountingExact
import EKG.VerifiedSpans

namespace EKG3.P3.Middle
open EKG Real EKG.CanonicalCounting

theorem odd_count_split (u Y : ℕ) :
    O u ≤ (Y+1)/2 + (oddExcess canonical u Y).card := by
  classical
  let A := ((Finset.Ioc (e u) (e u+Y)).filter (fun m => ¬ 2 ∣ m))
  let B := (oddExcess canonical u Y).image actualA
  have hsub : Clock.nonTickOddAbove canonical u spanTickValue ⊆ A ∪ B := by
    intro m hm
    obtain ⟨hodd, hnt⟩ := Finset.mem_filter.mp hm
    obtain ⟨hused, hmo, hgt⟩ := Finset.mem_filter.mp hodd
    by_cases hsmall : m ≤ e u+Y
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr
        ⟨Finset.mem_Ioc.mpr ⟨hgt,hsmall⟩, hmo⟩)
    · obtain ⟨i, hi, hv⟩ := (Clock.mem_usedValues canonical u m).mp hused
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr hi, by simpa [hv, e] using hmo,
          by simpa [hv, e] using (show e u+Y < m by omega), by simpa [hv] using hnt⟩,
        hv⟩
  have hA : A.card ≤ (Y+1)/2 := by
    apply (Finset.card_le_card_of_injOn (fun m : ℕ => (m-e u)/2) (t := Finset.range ((Y+1)/2)) ?_ ?_).trans (by simp)
    · intro m hm
      obtain ⟨hmm, hodd⟩ := Finset.mem_filter.mp hm
      obtain ⟨hlo,hhi⟩ := Finset.mem_Ioc.mp hmm
      have heven := (frontier_spec canonical u).2.1
      change 2 ∣ e u at heven
      apply Finset.mem_range.mpr
      change (m-e u)/2 < (Y+1)/2
      omega
    · intro m hm n hn heq
      obtain ⟨hmm, hmo⟩ := Finset.mem_filter.mp hm
      obtain ⟨hnn, hno⟩ := Finset.mem_filter.mp hn
      obtain ⟨hml,hmu⟩ := Finset.mem_Ioc.mp hmm
      obtain ⟨hnl,hnu⟩ := Finset.mem_Ioc.mp hnn
      change (m-e u)/2=(n-e u)/2 at heq
      have heven := (frontier_spec canonical u).2.1
      change 2 ∣ e u at heven
      omega
  have hB : B.card ≤ (oddExcess canonical u Y).card := Finset.card_image_le
  exact (Finset.card_le_card hsub).trans ((Finset.card_union_le A B).trans (Nat.add_le_add hA hB))

theorem row_span {u : ℕ} {r : CoverRow} (hu : 8 ≤ u)
    (hk : earlyEvenCount canonical u ≤ r.M) (he : frontier canonical u < r.eb) :
    (nonTickTop canonical u : ℝ) - (frontier canonical u : ℝ) ≤ r.S := by
  let k : ℝ := (earlyEvenCount canonical u : ℝ)+1
  let b : ℝ := (r.M : ℝ)+1
  have hk0 : 0 ≤ k := by dsimp [k]; positivity
  have hb0 : 0 ≤ b := by dsimp [b]; positivity
  have hkb : k ≤ b := by dsimp [k,b]; exact_mod_cast Nat.add_le_add_right hk 1
  have hs : k^2+(frontier canonical u : ℝ) ≤ b^2+r.eb := by
    have heR : (frontier canonical u : ℝ) ≤ r.eb := by exact_mod_cast he.le
    nlinarith
  have hsr := Real.sqrt_le_sqrt hs
  have hm := mul_le_mul hkb hsr (sqrt_nonneg _) hb0
  have hq := nonTickTop_quadratic canonical hu
  have hq' : (nonTickTop canonical u : ℝ) - (frontier canonical u : ℝ) ≤
      2*k^2+2*k*sqrt (k^2+frontier canonical u) := by
    simpa [k, Nat.cast_add, Nat.cast_one] using hq
  change _ ≤ 2*b^2+2*b*sqrt (b^2+r.eb)
  nlinarith

theorem row_rough {u : ℕ} {r : CoverRow}
    (hc : r.Conditions) (hk : earlyEvenCount canonical u ≤ r.M)
    (hspan : (nonTickTop canonical u : ℝ)-(frontier canonical u : ℝ) ≤ r.S) :
    ((roughSet canonical u r.Y).card : ℝ) ≤
      (r.S-r.Y+(r.Q : ℝ)^2)/log r.Q := by
  classical
  obtain ⟨hw,hY,hYS,hQ,hQR,hhc,hB,hHc,hP,hTk,hOd,hOl⟩ := hc
  have hdiff : 0 ≤ r.S-r.Y := by linarith
  let N : ℕ := ⌊r.S-r.Y⌋₊
  have hN : (N : ℝ) ≤ r.S-r.Y := Nat.floor_le hdiff
  have hinterval : ∀ m ∈ roughSet canonical u r.Y,
      m ≤ frontier canonical u+r.Y+N := by
    intro m hm
    have hmr := (Finset.mem_filter.mp hm).1
    have hml := (Finset.mem_Ioc.mp hmr).1
    have hmu := (Finset.mem_Ioc.mp hmr).2
    have hmrR : (m : ℝ) ≤ nonTickTop canonical u := by exact_mod_cast hmu
    have hsub : ((m-(frontier canonical u+r.Y) : ℕ) : ℝ) ≤ r.S-r.Y := by
      rw [Nat.cast_sub (by omega)]
      push_cast
      linarith
    have hn : m-(frontier canonical u+r.Y) ≤ N := Nat.le_floor hsub
    omega
  have hQRn : 4*(r.M+1)*r.Q ≤ 2*r.Y+1 := by
    have hden : (0 : ℝ) < 2*((r.M : ℝ)+1) := by positivity
    have hn := (le_div_iff₀ hden).mp hQR
    have hn' : (4 : ℝ)*((r.M : ℝ)+1)*r.Q ≤ 2*(r.Y : ℝ)+1 := by linarith
    exact_mod_cast hn'
  have hav : ∀ m ∈ roughSet canonical u r.Y, ∀ p : ℕ,
      p.Prime → p ≤ r.Q → ¬ p ∣ m := by
    intro m hm p hp hpQ hpd
    have hrough := (Finset.mem_filter.mp hm).2 p hp hpd
    have hmul : 2*(earlyEvenCount canonical u+1)*p ≤ 2*(r.M+1)*r.Q :=
      Nat.mul_le_mul (by omega) hpQ
    nlinarith only [hrough, hmul, hQRn]
  have h := arithmeticLargeSieve_holds u r.Y N r.Q hQ hinterval hav
  apply h.trans
  apply div_le_div_of_nonneg_right (by linarith) (log_pos (by exact_mod_cast (show 1 < r.Q by omega))).le

theorem row_A {e : ℕ} {r : CoverRow}
    (h0 : e0 ≤ r.ea) (hlo : r.ea ≤ e) (hhi : e < r.eb) :
    r.Amin ≤ FarTail.primeCombination e ∧ FarTail.primeCombination e ≤ r.Amax := by
  have hlarge : (13328000000 : ℝ) ≤ r.ea := by exact_mod_cast h0
  have hle : (r.ea : ℝ) ≤ e := by exact_mod_cast hlo
  have hlt : (e : ℝ) < r.eb := by exact_mod_cast hhi
  have c1 := (count_ge_piL (r.ea : ℝ) (by linarith)).trans (count_mono hle)
  have c2 := (count_mono (by linarith : (e : ℝ)/2 ≤ (r.eb : ℝ)/2)).trans
    (count_le_piU (by linarith : (1 : ℝ) < (r.eb : ℝ)/2))
  have c3 := (count_ge_piL ((r.ea : ℝ)/3) (by linarith)).trans
    (count_mono (by linarith : (r.ea : ℝ)/3 ≤ (e : ℝ)/3))
  have d1 := (count_mono hlt.le).trans (count_le_piU (by linarith))
  have d2 := (count_ge_piL ((r.ea : ℝ)/2) (by linarith)).trans
    (count_mono (by linarith : (r.ea : ℝ)/2 ≤ (e : ℝ)/2))
  have d3 := (count_mono (by linarith : (e : ℝ)/3 ≤ (r.eb : ℝ)/3)).trans
    (count_le_piU (by linarith : (1 : ℝ) < (r.eb : ℝ)/3))
  norm_num only [realPrimeCount, Nat.floor_div_ofNat, Nat.floor_natCast] at c1 c2 c3 d1 d2 d3
  dsimp [CoverRow.Amin, CoverRow.Amax, FarTail.primeCombination]
  constructor <;> linarith

end EKG3.P3.Middle
