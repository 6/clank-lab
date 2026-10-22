import EKG3.P3TailPi
import EKG3.FClockP3

set_option maxRecDepth 10000

namespace EKG3.P3
open EKG EKG.CanonicalCounting

namespace FarTail

theorem tail_frontier (ht : MiddleRangeTPrime) {i u : ℕ}
    (hi : 10^156 ≤ i+1) (hu : i-3 ≤ u) :
    (9:ℝ)*10^155 < e u := by
  have hu0 : 16000000000-3 ≤ u := by omega
  have hbase := frontier_monotone canonical hu0
  have he0 : 13328000000 ≤ frontier canonical u := ht.2.trans hbase
  by_cases he1 : frontier canonical u < 10^205
  · have hm := ht.1 u he0 he1
    have hn : (10:ℝ)^156-1 ≤ (u:ℝ)+3 := by
      have hnat : 10^156 ≤ u+4 := by omega
      have hh : (10:ℝ)^156 ≤ (u:ℝ)+4 := by exact_mod_cast hnat
      linarith
    have hr := FarTail.ratio_checks.2.2.2.2.2
    dsimp [e]; linarith
  · have hn : 10^205 ≤ frontier canonical u := by omega
    have hr : (10:ℝ)^205 ≤ frontier canonical u := by exact_mod_cast hn
    dsimp [e]; norm_num at *; linarith

end FarTail

theorem lemmaF : LemmaFStatement := by
  intro ht i hi
  have hrs := tailPiBounds_holds
  have hi9 : 12 ≤ i := by omega
  have frontier_tail : ∀ {u : ℕ}, i-3 ≤ u → (9:ℝ)*10^155 < e u :=
    fun hu => FarTail.tail_frontier ht hi hu
  have state : ∀ u : ℕ, i-3 ≤ u →
      (u:ℝ)+4 < 1.0766*(e u:ℝ) ∧
      0.997*(e u:ℝ) < (u:ℝ)+1 ∧
      (nonTickTop canonical u:ℝ) < 1.15288*(e u:ℝ) := by
    intro u hu
    have he := frontier_tail hu
    apply FarTail.state_bounds hrs (by omega)
    have hc : (10:ℝ)^153 < 9*10^155 := by norm_num
    linarith
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
  have hfinal :
      13*((i:ℝ)+1) < 28*(actualA i:ℝ) ∧
      7*(actualA i:ℝ) < 12*((i:ℝ)+1) := by
    by_cases hp : (actualA i).Prime
    · have hblock := prime_occurrence_block canonical hp hne2 (rfl : canonical.a i=actualA i)
      have hb := state (i-2) (by omega)
      have hidx : (i-2:ℕ)+2=i := by omega
      have hidxR : ((i-2:ℕ):ℝ)+2=(i:ℝ) := by exact_mod_cast hidx
      have hef : (e (i-2):ℝ)=2*(actualA i:ℝ) := by
        exact_mod_cast hblock.2.2.2
      have hpR : (0:ℝ) < actualA i := by exact_mod_cast hpv
      constructor <;> linarith only [hb.1,hb.2.1,hef,hidxR,hpR]
    · by_cases hv : spanTickValue (actualA i)
      · obtain ⟨p, hp, hp2, hv⟩ := hv
        obtain ⟨j, hj, hij, _⟩ := odd_prime_tick_unique canonical hp hp2 hv
        have he := firstMultiple_frontier canonical hj hp2
        have hidx : j-1=i-3 := by omega
        have hb := state (i-3) (by omega)
        have hidxR : ((i-3:ℕ):ℝ)+3=(i:ℝ) := by exact_mod_cast (show i-3+3=i by omega)
        have hef : (e (i-3):ℝ)=2*(p:ℝ) := by
          rw [hidx] at he
          exact_mod_cast he
        have hvR : (actualA i:ℝ)=3*(p:ℝ) := by exact_mod_cast hv
        have hpR : (0:ℝ)<p := by exact_mod_cast hp.pos
        constructor <;> linarith only [hb.1,hb.2.1,hef,hidxR,hvR,hpR]
      · have hb := state (i-1) (by omega)
        have hb' := state i (by omega)
        have hid : ((i-1:ℕ):ℝ)+1=(i:ℝ) := by exact_mod_cast (show i-1+1=i by omega)
        constructor
        · by_cases hge : frontier canonical (i-1) ≤ actualA i
          · have hgeR : (e (i-1):ℝ) ≤ actualA i := by exact_mod_cast hge
            have hpR : (0:ℝ)<actualA i := by exact_mod_cast hpv
            linarith only [hb.1,hgeR,hpR,hid]
          · have hlt : actualA i < frontier canonical (i-1) := by omega
            have hfree : ¬ UsedBefore actualA ((i-1)+1) (actualA i) := by
              rintro ⟨j,hj,hv⟩
              have := actualA_injective hv
              omega
            have hu : 8 ≤ i - 1 := by omega
            have hvone : 1 < actualA i := by omega
            have h15 := HoleCounting.missing_composite_ge_fifteen canonical
              (t := i-1) hu hvone hp hlt hfree
            have hh := FarTail.large_hole_lower hrs (frontier_tail (u:=i-1) (by omega))
              h15 hp hlt hfree
            have hpR : (0:ℝ)<actualA i := by exact_mod_cast hpv
            have hm := mul_lt_mul_of_pos_left hh (by norm_num : (0:ℝ)<1.0766)
            dsimp [e] at hb
            linarith only [hb.1,hm,hpR,hid]
        · by_cases hlt : actualA i < frontier canonical i
          · have hltR : (actualA i:ℝ)<e i := by exact_mod_cast hlt
            linarith only [hb'.2.1,hltR]
          · have htop := nonTick_le_top canonical (le_refl i) hv
            have htopR : (actualA i:ℝ)≤nonTickTop canonical i := by exact_mod_cast htop
            linarith only [hb'.2.1,hb'.2.2,htopR]
  constructor
  · exact_mod_cast hfinal.1
  · exact_mod_cast hfinal.2

end EKG3.P3
