import EKG3.TStateP3

namespace EKG3.P3
open EKG Real EKG.CanonicalCounting

namespace Middle

theorem frontier_stays {i : ℕ} (hi : 1 ≤ i)
    (hne : actualA i ≠ e (i-1)) : e i = e (i-1) := by
  apply le_antisymm
  · have hp := frontier_spec canonical (i-1)
    apply frontier_le canonical i _ hp.1 hp.2.1
    rintro ⟨j,hj,hv⟩
    by_cases hji : j=i
    · subst j; exact hne hv
    · exact hp.2.2 ⟨j, by omega, hv⟩
  · exact frontier_monotone canonical (by omega)

theorem bounded_ratios (hfb : FiniteFb) (hfc : FiniteFc) {rows : List CoverRow}
    (hc : CoverChain e0 Kfin rows) (i : ℕ) (hiL : L < i+1) (he1 : e i < E1) :
    13*(i+1) < 28*actualA i ∧ 7*actualA i < 12*(i+1) := by
  have hi9 : 12 ≤ i := by dsimp [L] at hiL; omega
  have good : ∀ u : ℕ, i-3 ≤ u → u ≤ i →
      ∃ r ∈ rows, r.ea ≤ e u ∧ e u < r.eb ∧ r.Conditions ∧ RowState u r := by
    intro u hu hui
    apply state hfc hc
    · exact hfb.trans (frontier_monotone canonical (by dsimp [L] at *; omega))
    · exact (frontier_monotone canonical hui).trans_lt he1
  have hpv : 0 < actualA i := (actualA_properties i).1
  have hne1 : actualA i ≠ 1 := by
    intro h
    have heq : actualA i = actualA 0 := by simpa using h
    have := actualA_injective heq
    omega
  have hne2 : actualA i ≠ 2 := by
    intro h
    have heq : actualA i = actualA 1 := by simpa using h
    have := actualA_injective heq
    omega
  have hfinal : 13*((i : ℝ)+1) < 28*(actualA i : ℝ) ∧
      7*(actualA i : ℝ) < 12*((i : ℝ)+1) := by
    by_cases hp : (actualA i).Prime
    · have hblock := prime_occurrence_block canonical hp hne2 (rfl : canonical.a i=actualA i)
      obtain ⟨r,hr,hlo,hhi,hrc,hst⟩ := good (i-2) (by omega) (by omega)
      have hidxR : ((i-2 : ℕ) : ℝ)+2=(i : ℝ) := by exact_mod_cast (show i-2+2=i by omega)
      have hef : (e (i-2) : ℝ)=2*(actualA i : ℝ) := by exact_mod_cast hblock.2.2.2
      have he0 : (16 : ℝ) ≤ e (i-2) := by
        have hn := (chain_lower hc r hr).trans hlo
        have hn' : (13328000000 : ℝ) ≤ e (i-2) := by exact_mod_cast hn
        linarith
      constructor <;> linarith only [hst.tprime,hst.tick,hef,hidxR,he0]
    · by_cases hv : spanTickValue (actualA i)
      · obtain ⟨p,hp,hp2,hv⟩ := hv
        obtain ⟨j,hj,hij,_⟩ := odd_prime_tick_unique canonical hp hp2 hv
        have he := firstMultiple_frontier canonical hj hp2
        have hidx : j-1=i-3 := by omega
        obtain ⟨r,hr,hlo,hhi,hrc,hst⟩ := good (i-3) (by omega) (by omega)
        have hidxR : ((i-3 : ℕ) : ℝ)+3=(i : ℝ) := by exact_mod_cast (show i-3+3=i by omega)
        have hef : (e (i-3) : ℝ)=2*(p : ℝ) := by rw [hidx] at he; exact_mod_cast he
        have hvR : (actualA i : ℝ)=3*(p : ℝ) := by exact_mod_cast hv
        have he0 : (16 : ℝ) ≤ e (i-3) := by
          have hn := (chain_lower hc r hr).trans hlo
          have hn' : (13328000000 : ℝ) ≤ e (i-3) := by exact_mod_cast hn
          linarith
        constructor <;> linarith only [hst.tprime,hst.tick,hef,hidxR,hvR,he0]
      · have hpre0 : e0 ≤ e (i-1) := hfb.trans (frontier_monotone canonical (by dsimp [L] at *; omega))
        have hpre1 : e (i-1) < E1 := (frontier_monotone canonical (by omega : i-1 ≤ i)).trans_lt he1
        obtain ⟨r,hr,hlo,hhi,hrc,heq⟩ := cover_lookup hc hpre0 hpre1
        have hst := row_state hfc hc hr hlo hhi hpre1 hrc heq
        have hid : ((i-1 : ℕ) : ℝ)+1=(i : ℝ) := by exact_mod_cast (show i-1+1=i by omega)
        have he0 : (16 : ℝ) ≤ e (i-1) := by
          have heR : (13328000000 : ℝ) ≤ e (i-1) := by exact_mod_cast hpre0
          linarith
        by_cases hgt : e (i-1) < actualA i
        · have heqfront := frontier_stays (by omega : 1 ≤ i) (by omega : actualA i ≠ e (i-1))
          have hki := bounded_K hfc hc i he1
          change earlyEvenCount canonical i ≤ envelope rows (e i) at hki
          rw [heqfront, heq] at hki
          have hspan := row_span (by omega : 8 ≤ i) hki (by change e i < r.eb; rwa [heqfront])
          change (nonTickTop canonical i : ℝ)-(e i : ℝ) ≤ r.S at hspan
          rw [heqfront] at hspan
          have htop := nonTick_le_top canonical (le_refl i) hv
          have htopR : (actualA i : ℝ) ≤ nonTickTop canonical i := by exact_mod_cast htop
          have hgtR : (e (i-1) : ℝ) < actualA i := by exact_mod_cast hgt
          have heaR : (r.ea : ℝ) ≤ e (i-1) := by exact_mod_cast hlo
          have hOd := hrc.2.2.2.2.2.2.2.2.2.2.1
          constructor
          · linarith only [hst.tprime,hgtR,hid,he0]
          · linarith only [hspan,htopR,hst.lower,hOd,hid,heaR]
        · by_cases hequal : actualA i = e (i-1)
          · have hvR : (actualA i : ℝ)=e (i-1) := by exact_mod_cast hequal
            constructor <;> linarith only [hst.tprime,hst.tick,hid,hvR,he0]
          · have hlt : actualA i < e (i-1) := by omega
            have hfree : ¬ UsedBefore actualA ((i-1)+1) (actualA i) := by
              rintro ⟨j,hj,hv⟩
              have := actualA_injective hv
              omega
            have h15 := HoleCounting.missing_composite_ge_fifteen canonical
              (t := i-1) (by omega) (by omega : 1 < actualA i) hp hlt hfree
            have hhole := hst.hole (actualA i) h15 hp hlt hfree
            have hhR : (r.hc : ℝ) < actualA i := by exact_mod_cast hhole
            have hltR : (actualA i : ℝ) < e (i-1) := by exact_mod_cast hlt
            have hebR : (e (i-1) : ℝ) < r.eb := by exact_mod_cast hhi
            have hOl := hrc.2.2.2.2.2.2.2.2.2.2.2
            constructor
            · linarith only [hhR,hst.upper,hOl,hid,hebR]
            · linarith only [hltR,hst.tick,hid,he0]
  constructor
  · exact_mod_cast hfinal.1
  · exact_mod_cast hfinal.2

end Middle

theorem theoremT : TheoremTStatement := by
  intro _hfa hfb hfc hcover
  obtain ⟨rows,hc⟩ := hcover
  have hrat := Middle.bounded_ratios hfb hfc hc
  refine ⟨hrat, ?_, ?_⟩
  · intro i hiL hiN
    apply hrat i hiL
    have he := Clock.frontier_le_twice_time_add_two canonical i
    change e i ≤ 2*(i+2) at he
    dsimp [E1]
    omega
  · intro u he0 he1
    obtain ⟨r,hr,hlo,hhi,hrc,hst⟩ := Middle.state hfc hc he0 he1
    exact hst.tprime

end EKG3.P3
