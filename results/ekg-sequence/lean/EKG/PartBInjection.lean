import EKG.PartBFinite
import EKG.PartBRoughness
import EKG.PartBLocalization
import EKG.PartA

/-! Full many-successor injection, including transfer of the proved Part A
at each earlier POST-occurrence frontier. The raw finite-prefix cutoff is
applied before this transfer. The old rate alone localizes the ordinary
successors. No order between the two prime factors is asserted. -/
namespace EKG.PartB

open Real Filter

structure PrimeSuccessorWitness (t h s M : ℕ) (H : ℝ) (j i q : ℕ) : Prop
    extends SuccessorWitness t h s M j i where
  cofactor_prime : q.Prime
  successor_eq : canonical.a (i+1) = s*q
  window_lower : (frontier canonical t : ℝ) - H*logRate (frontier canonical t) <
    (canonical.a (i+1) : ℝ)

/-- Uniform actual injection into prime cofactors in a single old-rate
window. All finite scale hypotheses are discharged by PartBParameters. -/
theorem many_prime_successors :
    ∃ H : ℝ, 0 < H ∧ ∀ delta : ℝ, 0 < delta → ∃ X : ℝ,
      ∀ t h s M : ℕ, ∀ B : ℝ,
      X ≤ (frontier canonical t : ℝ) →
      2 ≤ h → h < frontier canonical t →
      ¬ UsedBefore canonical.a (t+1) h →
      s.Prime → s ∣ h → 2 ≤ M → 3 < B → (M : ℝ) < B →
      delta*logRate (frontier canonical t) ≤ (frontier canonical t : ℝ)-(h : ℝ) →
      (frontier canonical t : ℝ)-(h : ℝ) ≤ 1604*logRate (frontier canonical t) →
      2*B*(13*Nat.primeCounting (Nat.sqrt (frontier canonical t))+724 : ℕ) ≤
        delta/3*logRate (frontier canonical t) →
      (frontier canonical t : ℝ) ≤ (2*s*M : ℕ)*B →
      (frontier canonical t : ℝ) < B^3 →
      ∃ index cofactor : ℕ → ℕ,
        (∀ j ∈ successorRungs t h s M,
          PrimeSuccessorWitness t h s M H j (index j) (cofactor j)) ∧
        Set.InjOn cofactor (successorRungs t h s M : Set ℕ) := by
  obtain ⟨H₀,hH₀,hlocal⟩ := successor_localization
  refine ⟨H₀+802,by linarith,?_⟩
  intro delta hdelta
  obtain ⟨NA,hA⟩ := PartA.canonical_upper_excursion (delta/6) (by positivity)
  have hf : Tendsto (fun i => (frontier canonical i : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (frontier_tendsto_atTop canonical)
  obtain ⟨Nlog,hNlog⟩ := eventually_atTop.mp
    ((Real.tendsto_log_atTop.comp hf).eventually (eventually_ge_atTop (1:ℝ)))
  let N := NA+Nlog+8
  obtain ⟨Xlate,hlate⟩ := occurrence_late N
  obtain ⟨Xloc,hloc⟩ := hlocal N
  refine ⟨max 32 (max Xlate Xloc),?_⟩
  intro t h s M B hX hh hbelow hfree hs hsh hM hB hMB hgap hupper hscale hstride hcube
  classical
  let e : ℝ := frontier canonical t
  have he32 : 32 ≤ e := (le_max_left _ _).trans hX
  have heinner : max Xlate Xloc ≤ e := (le_max_right _ _).trans hX
  have heXlate : Xlate ≤ e := (le_max_left _ _).trans heinner
  have heXloc : Xloc ≤ e := (le_max_right _ _).trans heinner
  have hepos : 0 < e := by linarith
  have hLpos : 0 < logRate e := div_pos hepos (Real.log_pos (by linarith))
  have hd : 0 < 2*s*M := by have := hs.pos; positivity
  obtain ⟨index,hindex,hsuccinj⟩ := many_successors hh hbelow hfree hs hsh hM
  let cofactor : ℕ → ℕ := fun j => canonical.a (index j+1)/s
  have hw : ∀ j ∈ successorRungs t h s M,
      PrimeSuccessorWitness t h s M (H₀+802) j (index j) (cofactor j) := by
    intro j hj
    let n := index j
    let u := canonical.a (n+1)
    have w : SuccessorWitness t h s M j n := hindex j hj
    have hjr := (Finset.mem_filter.mp hj).1
    obtain ⟨hylo,hyhi⟩ := progressionIndices_bounds hd hjr
    have hymid : h+frontier canonical t < 2*(2*s*M*j) := by omega
    have hymidreal : (h : ℝ)+e < 2*(canonical.a n : ℝ) := by
      rw [w.value_eq]
      dsimp [e]
      exact_mod_cast hymid
    have hyhalf : e/2 < (canonical.a n : ℝ) := by
      have hhreal : (0:ℝ) ≤ h := by positivity
      linarith
    have hyupper : (canonical.a n : ℝ) ≤ e := by
      rw [w.value_eq]
      dsimp [e]
      exact_mod_cast hyhi.le
    have hnN : N ≤ n := hlate e heXlate n hyhalf
    have hn8 : 8 ≤ n := by dsimp [N] at hnN; omega
    have hjpos : 0 < j := by
      by_contra hn
      have hz : j=0 := by omega
      rw [hz,Nat.mul_zero] at hylo
      omega
    have heven : 2 ∣ canonical.a n := by
      rw [w.value_eq]
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (Nat.dvd_mul_right 2 s) M) j
    have hybig : 6 < canonical.a n := by
      have hyreal : (6:ℝ) < canonical.a n := by linarith
      exact_mod_cast hyreal
    have hycomp : ¬ (canonical.a n).Prime :=
      Nat.not_prime_of_dvd_of_lt heven (by decide) (by omega)
    have hysmooth : smoothValue (canonical.a n)=canonical.a n :=
      smoothValue_of_ordinary hycomp (even_not_tick heven) (by omega)
    -- The accepted A theorem is applied at n, never at n-1 or at t.
    have hnA : NA ≤ n := by dsimp [N] at hnN; omega
    have hnlog : Nlog ≤ n := by dsimp [N] at hnN; omega
    have hlogf : 1 ≤ Real.log (frontier canonical n : ℝ) := hNlog n hnlog
    have hfpos : (0:ℝ) < frontier canonical n := by
      exact_mod_cast (frontier_spec canonical n).1
    have hfmono : (frontier canonical n : ℝ) ≤ e := by
      dsimp [e]
      exact_mod_cast (frontier_monotone canonical w.index_lt.le)
    have hrate := logRate_mono_of_one_le_log hfpos hlogf hfmono
    have ha : max ((nonTickTop canonical n : ℝ)-(frontier canonical n : ℝ)) 0 ≤
        (delta/6)*logRate (frontier canonical n) := by
      simpa only [logRate,←mul_div_assoc] using hA n hnA
    have hyTop : (canonical.a n : ℝ) ≤ nonTickTop canonical n := by
      exact_mod_cast (nonTick_le_top canonical (le_refl n) (even_not_tick heven))
    have hfdown : (canonical.a n : ℝ)-(frontier canonical n : ℝ) ≤
        (delta/6)*logRate e := by
      have hmul := mul_le_mul_of_nonneg_left hrate (show (0:ℝ) ≤ delta/6 by positivity)
      have hmax := le_max_left ((nonTickTop canonical n : ℝ)-(frontier canonical n : ℝ)) 0
      linarith
    have hult : (u : ℝ) < (h : ℝ) := by exact_mod_cast w.successor_lt
    have hpost : delta/3*logRate e < (frontier canonical n : ℝ)-(u : ℝ) := by
      nlinarith only [hfdown,hymidreal,hult,hgap]
    have hubelow : u < frontier canonical n := by
      have : (u : ℝ) < (frontier canonical n : ℝ) := by
        have : 0 < delta/3*logRate e := by positivity
        linarith
      exact_mod_cast this
    obtain ⟨hucomp,hunottick,husmooth⟩ :=
      successor_ordinary w.index_ge hs hM hjpos w.value_eq hubelow
    have hufree : ¬ UsedBefore canonical.a (n+1) u := term_unused canonical (n+1)
    have huone : 1 < u := by
      have hup := canonical.positive (n+1)
      have hune : u ≠ 1 := by
        intro heq
        have := canonical.injective (heq.trans canonical.seed_zero.symm)
        omega
      omega
    -- The finite-prefix theorem independently establishes u>=15 here.
    have hu15 := HoleCounting.missing_composite_ge_fifteen canonical
      hn8 huone hucomp hubelow hufree
    have hue : u ≤ frontier canonical t := (lt_trans w.successor_lt hbelow).le
    have hrough : ∀ p : ℕ, p.Prime → p ∣ u → B < (p : ℝ) := by
      apply canonical_missing_composite_rough hn8 huone hucomp hubelow hufree hue
      exact hscale.trans_lt hpost
    have hshared : SharedPrime u (2*s*M*j) := by
      obtain ⟨p,hp,hpy,hpu⟩ := canonical.eligible (n+1) (by omega)
      refine ⟨p,hp,hpu,?_⟩
      simpa only [Nat.add_sub_cancel,w.value_eq] using hpy
    have hjreal : (2*s*M : ℕ)*(j : ℝ) < e := by
      dsimp [e]
      exact_mod_cast hyhi
    have hdreal : (0:ℝ) < (2*s*M : ℕ) := by exact_mod_cast hd
    have hjB : (j : ℝ) < B := by nlinarith
    have hsd : s ∣ u := partA_factor_forcing hs hshared hrough hB hM hjpos hMB hjB
    have hprime : (cofactor j).Prime := by
      apply partA_prime_cofactor (canonical.positive (n+1)) hucomp hs hsd hrough
        (by linarith : 0<B)
      have huereal : (u : ℝ) < e := by
        dsimp [e,u]
        exact_mod_cast (lt_of_lt_of_le w.successor_lt hbelow.le)
      exact huereal.trans hcube
    have heq : u=s*cofactor j := (Nat.mul_div_cancel' hsd).symm
    have hlocbound := (hloc e heXloc n hyhalf hyupper hysmooth husmooth).2
    have hlocal_lower := (abs_le.mp hlocbound).1
    have hwindow : e-(H₀+802)*logRate e < (u : ℝ) := by
      nlinarith only [hlocal_lower,hymidreal,hupper]
    exact ⟨w,hprime,heq,hwindow⟩
  refine ⟨index,cofactor,hw,?_⟩
  intro j hj k hk heq
  have wj := hw j hj
  have wk := hw k hk
  apply hsuccinj hj hk
  change canonical.a (index j+1)=canonical.a (index k+1)
  rw [wj.successor_eq,wk.successor_eq,heq]

end EKG.PartB
