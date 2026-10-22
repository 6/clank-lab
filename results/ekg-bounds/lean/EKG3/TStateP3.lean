import EKG3.TBoundsP3

namespace EKG3.P3.Middle
open EKG Real EKG.CanonicalCounting

/-- Derived per-state facts, with no additional input hypotheses. -/
structure RowState (u : ℕ) (r : CoverRow) : Prop where
  span : (nonTickTop canonical u : ℝ)-(e u : ℝ) ≤ r.S
  hole : ∀ h : ℕ, 15 ≤ h → ¬ h.Prime → h < e u →
    ¬ UsedBefore actualA (u+1) h → r.hc < h
  upper : (u : ℝ)+1 ≤ (e u : ℝ)-r.Amin+r.M+r.Ostar-1
  lower : (e u : ℝ)-r.Amax-r.Hstar-5 ≤ (u : ℝ)+1
  tprime : (u : ℝ)+3 < 14*(e u : ℝ)/13
  tick : 7*(e u : ℝ)/8 < (u : ℝ)+4

theorem row_state (hf : FiniteFc) {rows : List CoverRow} (hcover : CoverChain e0 Kfin rows)
    {u : ℕ} {r : CoverRow} (hr : r ∈ rows)
    (hlo : r.ea ≤ e u) (hhi : e u < r.eb) (he1 : e u < E1)
    (hrc : r.Conditions) (heq : envelope rows (e u) = r.M) : RowState u r := by
  classical
  have heq' : envelope rows (frontier canonical u) = r.M := heq
  have h0 := chain_lower hcover r hr
  have he0 : e0 ≤ e u := h0.trans hlo
  have hu : 8 ≤ u := by
    have hf := Clock.frontier_le_twice_time_add_two canonical u
    change e u ≤ 2*(u+2) at hf
    dsimp [e0] at he0
    omega
  have hbound := bounded_K hf hcover
  have hpast : ∀ w, w ≤ u → earlyEvenCount canonical w ≤ r.M := by
    intro w hw
    have hfront := frontier_monotone canonical hw
    have h1 : frontier canonical w < E1 := hfront.trans_lt he1
    have hm := (hbound w h1).trans (envelope_mono rows hfront)
    rwa [heq'] at hm
  have hlocal : ∀ w, w < u → earlyEvenCount canonical w ≤ envelope rows (frontier canonical w) := by
    intro w hw
    exact hbound w ((frontier_monotone canonical hw.le).trans_lt he1)
  have hk := hpast u le_rfl
  have hspan := row_span hu hk hhi
  have hrc' := hrc
  obtain ⟨hw,hY,hYS,hQ,hQR,hhc,hB,hHc,hP,hTk,hOd,hOl⟩ := hrc'
  have hp : (Nat.primeCounting (Nat.sqrt (e u)) : ℝ) ≤ r.pU := by
    apply sqrt_count_le (by exact_mod_cast hhi.le)
    apply (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)).mpr
    have hebl : 13328000000 ≤ r.eb := by dsimp [e0] at he0; omega
    exact_mod_cast (show 1 < r.eb by omega)
  have hH : (H u : ℝ) ≤ r.Hstar := by
    have hc := lemmaC2 canonical u (envelope rows) (envelope_mono rows) hlocal
    rw [heq'] at hc
    have hcR : (H u : ℝ) ≤ (Nat.primeCounting (Nat.sqrt (e u)) : ℝ)*
        ((Nat.primeCounting (Nat.sqrt (e u)) : ℝ)+r.M+5) := by exact_mod_cast hc
    apply hcR.trans
    apply mul_le_mul hp (by linarith) (by positivity) (by have := Nat.cast_nonneg (α := ℝ) (Nat.primeCounting (Nat.sqrt (e u))); linarith)
  have hpeak : EKG3.priorPeak canonical u ≤ r.M := by
    apply Finset.sup_le
    intro w hw
    exact hpast w (by have := Finset.mem_range.mp hw; omega)
  have hD := lemmaD canonical u r.Y (by omega)
  change (oddExcess canonical u r.Y).card ≤ Nat.primeCounting (Nat.sqrt (e u+r.Y+1)) + (roughSet canonical u r.Y).card at hD
  have hodd := odd_count_split u r.Y
  have hrough := row_rough hrc hk hspan
  have hbigpi : (Nat.primeCounting (Nat.sqrt (e u+r.Y+1)) : ℝ) ≤
      piU (sqrt ((r.eb : ℝ)+r.Y+1)) := by
    apply sqrt_count_le (by push_cast; exact_mod_cast (by omega : e u+r.Y+1 ≤ r.eb+r.Y+1))
    apply (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)).mpr
    have hebl : (1 : ℝ) < r.eb := by exact_mod_cast (show 1 < r.eb by dsimp [e0] at he0; omega)
    have hYn : (0 : ℝ) ≤ r.Y := by positivity
    nlinarith
  have hO : (O u : ℝ) ≤ r.Ostar := by
    have hn : O u ≤ (r.Y+1)/2 + Nat.primeCounting (Nat.sqrt (e u+r.Y+1)) + (roughSet canonical u r.Y).card := by omega
    have hnR : (O u : ℝ) ≤ ((r.Y+1)/2 : ℕ) +
        (Nat.primeCounting (Nat.sqrt (e u+r.Y+1)) : ℝ) + (roughSet canonical u r.Y).card := by exact_mod_cast hn
    dsimp [CoverRow.Ostar]
    linarith only [hnR, hbigpi, hrough]
  have hhole : ∀ h : ℕ, 15 ≤ h → ¬ h.Prime → h < e u →
      ¬ UsedBefore actualA (u+1) h → r.hc < h := by
    intro h hh hnp hbelow hfree
    by_contra hle
    have hle' : h ≤ r.hc := by omega
    have hraw := lemmaC1 canonical u (envelope rows) (envelope_mono rows) hlocal h hh hnp hbelow hfree
    change e u - h ≤ 2*h.minFac*(Nat.primeCounting (Nat.sqrt h)+envelope rows h+4) at hraw
    have hMh : envelope rows h ≤ r.M := by
      rw [← heq]
      exact envelope_mono rows hbelow.le
    have hn : e u ≤ h+2*h.minFac*(Nat.primeCounting (Nat.sqrt h)+r.M+4) := by
      have hm := Nat.mul_le_mul_left (2*h.minFac) (show Nat.primeCounting (Nat.sqrt h)+envelope rows h+4 ≤ Nat.primeCounting (Nat.sqrt h)+r.M+4 by omega)
      omega
    have hcR : (e u : ℝ) ≤ (h : ℝ)+2*(h.minFac : ℝ)*
        ((Nat.primeCounting (Nat.sqrt h) : ℝ)+r.M+4) := by exact_mod_cast hn
    have hfac : (h.minFac : ℝ) ≤ sqrt r.hc := by
      apply (Real.le_sqrt (by positivity) (by positivity)).mpr
      exact_mod_cast (Nat.minFac_sq_le_self (by omega : 0 < h) hnp).trans hle'
    have hpi : (Nat.primeCounting (Nat.sqrt h) : ℝ) ≤ piU (sqrt r.hc) := by
      apply sqrt_count_le (by exact_mod_cast hle')
      apply (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)).mpr
      exact_mod_cast (by omega : 1 < r.hc)
    have hm := mul_le_mul hfac (by linarith :
      (Nat.primeCounting (Nat.sqrt h) : ℝ)+r.M+4 ≤ piU (sqrt r.hc)+r.M+4)
      (by positivity) (sqrt_nonneg (r.hc : ℝ))
    have hhR : (h : ℝ) ≤ r.hc := by exact_mod_cast hle'
    have heR : (r.ea : ℝ) ≤ e u := by exact_mod_cast hlo
    nlinarith only [hcR, hm, hhR, heR, hHc]
  have hA := row_A h0 hlo hhi
  have hz := exact_integer_clock u hu
  have hclock : (e u : ℝ)-((u : ℝ)+1) = FarTail.primeCombination (e u)+
      (H u : ℝ)-(K u : ℝ)-(O u : ℝ)+(correction u : ℝ) := by
    have hcR : (e u : ℝ)-((u+1 : ℕ) : ℝ) =
        (Nat.primeCounting (e u) : ℝ)-2*(Nat.primeCounting (e u/2) : ℝ)+
        (Nat.primeCounting (e u/3) : ℝ)+(H u : ℝ)-(K u : ℝ)-(O u : ℝ)+(correction u : ℝ) := by exact_mod_cast hz
    simpa [FarTail.primeCombination] using hcR
  have hcorr := correction_bounds u hu
  have hc1 : (1 : ℝ) ≤ correction u := by exact_mod_cast hcorr.1
  have hc5 : (correction u : ℝ) ≤ 5 := by exact_mod_cast hcorr.2
  have hkR : (K u : ℝ) ≤ r.M := by exact_mod_cast hk
  have hH0 : (0 : ℝ) ≤ H u := by positivity
  have hK0 : (0 : ℝ) ≤ K u := by positivity
  have hO0 : (0 : ℝ) ≤ O u := by positivity
  have hupper : (u : ℝ)+1 ≤ (e u : ℝ)-r.Amin+r.M+r.Ostar-1 := by linarith
  have hlower : (e u : ℝ)-r.Amax-r.Hstar-5 ≤ (u : ℝ)+1 := by linarith
  have heaR : (r.ea : ℝ) ≤ e u := by exact_mod_cast hlo
  refine ⟨hspan, hhole, hupper, hlower, ?_, ?_⟩
  · linarith only [hupper, heaR, hP]
  · linarith only [hlower, heaR, hTk]

theorem state (hf : FiniteFc) {rows : List CoverRow} (hc : CoverChain e0 Kfin rows)
    {u : ℕ} (he0 : e0 ≤ e u) (he1 : e u < E1) :
    ∃ r ∈ rows, r.ea ≤ e u ∧ e u < r.eb ∧ r.Conditions ∧ RowState u r := by
  obtain ⟨r,hr,hlo,hhi,hrc,heq⟩ := cover_lookup hc he0 he1
  exact ⟨r,hr,hlo,hhi,hrc,row_state hf hc hr hlo hhi he1 hrc heq⟩

end EKG3.P3.Middle
