import ErsConj13.Pieces
import ErsConj13.Telescoping

/-!
# The binomial series satisfies the cubic `K`

Route: the root `S*` of `K` (Hensel) satisfies a third-order linear ODE (derived from
`K, θK, θ²K, θ³K` with a polynomial certificate), hence a second-order P-recurrence; the binomial
coefficients satisfy the same recurrence (`b_rec`, creative telescoping); both series start
`1, 2`, so they are equal.
-/

noncomputable section
set_option linter.unusedSimpArgs false

namespace ErsConj13
open PowerSeries

lemma tD_ofNat' (n : ℕ) [n.AtLeastTwo] : tD (no_index (OfNat.ofNat n : ℚ⟦X⟧)) = 0 := by
  rw [← map_ofNat (PowerSeries.C (R := ℚ)) n]; simp [tD]

/-- From `K S = 0`: the linear ODE `L(S) = 0` (θ = t d/dt, `Sk = θ^k S`). -/
lemma tD_zero' : tD 0 = 0 := by simp [tD]

lemma ode_of_K (S : ℚ⟦X⟧) (hK : K S = 0) :
    let S1 := tD S
    let S2 := tD S1
    let S3 := tD S2
    (-42*S*X^2 + 8*S*X - 213*S1*X^2 - 14*S1*X - 25*S1 - 297*S2*X^2 - 110*S2*X - 5*S2 - 108*S3*X^2 - 88*S3*X + 20*S3 + 12*X) = 0 := by
  intro S1 S2 S3
  have e0 : X^2*S^3 - 2*X*S^2 + (1+X)*S - (1+X) = 0 := hK
  have e1 : 2*S^3*X^2 + 3*S^2*S1*X^2 - 2*S^2*X - 4*S*S1*X + S*X + S1*X + S1 - X = 0 := by
    have h := congrArg tD hK
    simp only [K, pow_succ, pow_zero, one_mul, tD_mul, tD_add, tD_sub, tD_one, tD_X, tD_two,
      tD_ofNat'] at h
    rw [tD_zero'] at h
    linear_combination h
  have e2 : 4*S^3*X^2 + 12*S^2*S1*X^2 + 3*S^2*S2*X^2 - 2*S^2*X + 6*S*S1^2*X^2 - 8*S*S1*X - 4*S*S2*X + S*X - 4*S1^2*X + 2*S1*X + S2*X + S2 - X = 0 := by
    have h := congrArg tD e1
    simp only [pow_succ, pow_zero, one_mul, tD_mul, tD_add, tD_sub, tD_one, tD_X, tD_two,
      tD_ofNat'] at h
    rw [tD_zero'] at h
    linear_combination h
  have e3 : 8*S^3*X^2 + 36*S^2*S1*X^2 + 18*S^2*S2*X^2 + 3*S^2*S3*X^2 - 2*S^2*X + 36*S*S1^2*X^2 + 18*S*S1*S2*X^2 - 12*S*S1*X - 12*S*S2*X - 4*S*S3*X + S*X + 6*S1^3*X^2 - 12*S1^2*X - 12*S1*S2*X + 3*S1*X + 3*S2*X + S3*X + S3 - X = 0 := by
    have h := congrArg tD e2
    simp only [pow_succ, pow_zero, one_mul, tD_mul, tD_add, tD_sub, tD_one, tD_X, tD_two,
      tD_ofNat'] at h
    rw [tD_zero'] at h
    linear_combination h
  have hD : (3*S^2*X^2 - 4*S*X + X + 1 : ℚ⟦X⟧) ≠ 0 := by
    intro h; have := congrArg constantCoeff h; simp at this
  refine (mul_eq_zero.mp ?_).resolve_left (pow_ne_zero 6 hD)
  linear_combination (-3996*S^10*X^11 + 6210*S^10*X^10 + 26640*S^9*X^10 - 41400*S^9*X^9 - 8658*S^8*X^10 - 68358*S^8*X^9 + 119580*S^8*X^8 - 36450*S^7*X^11 - 5616*S^7*X^10 + 47220*S^7*X^9 + 80286*S^7*X^8 - 195300*S^7*X^7 + 170100*S^6*X^10 + 20436*S^6*X^9 - 102984*S^6*X^8 - 26920*S^6*X^7 + 197120*S^6*X^6 - 40338*S^5*X^10 - 348642*S^5*X^9 - 28428*S^5*X^8 + 113058*S^5*X^7 - 37062*S^5*X^6 - 125860*S^5*X^5 + 29160*S^4*X^10 + 147420*S^4*X^9 + 404580*S^4*X^8 + 20340*S^4*X^7 - 62160*S^4*X^6 + 48080*S^4*X^5 + 49700*S^4*X^4 - 88614*S^3*X^9 - 203052*S^3*X^8 - 286106*S^3*X^7 - 10430*S^3*X^6 + 11188*S^3*X^5 - 23502*S^3*X^4 - 11180*S^3*X^3 + 7776*S^2*X^9 + 100332*S^2*X^8 + 131232*S^2*X^7 + 123738*S^2*X^6 + 5476*S^2*X^5 + 4380*S^2*X^4 + 5244*S^2*X^3 + 1150*S^2*X^2 - 10854*S*X^8 - 46290*S*X^7 - 40998*S*X^6 - 30368*S*X^5 - 2186*S*X^4 - 2346*S*X^3 - 410*S*X^2 - 20*S*X - 648*X^8 + 3924*X^7 + 6894*X^6 + 5366*X^5 + 3148*X^4 + 408*X^3 + 302*X^2 - 2*X) * e0 + (-80919*S^10*X^12 - 112698*S^10*X^11 + 38205*S^10*X^10 - 310554*S^9*S1*X^12 - 317196*S^9*S1*X^11 + 86670*S^9*S1*X^10 + 332424*S^9*X^11 + 539856*S^9*X^10 - 196920*S^9*X^9 - 262440*S^8*S1^2*X^12 - 213840*S^8*S1^2*X^11 + 48600*S^8*S1^2*X^10 + 1513404*S^8*S1*X^11 + 1618056*S^8*S1*X^10 - 455220*S^8*S1*X^9 - 76545*S^8*X^11 - 605979*S^8*X^10 - 1002099*S^8*X^9 + 425895*S^8*X^8 + 1399680*S^7*S1^2*X^11 + 1140480*S^7*S1^2*X^10 - 259200*S^7*S1^2*X^9 - 297432*S^7*S1*X^11 - 3354696*S^7*S1*X^10 - 3370248*S^7*S1*X^9 + 1014120*S^7*S1*X^8 + 7290*S^7*X^11 + 194508*S^7*X^10 + 623310*S^7*X^9 + 829224*S^7*X^8 - 495060*S^7*X^7 - 244944*S^6*S1^2*X^11 - 3383856*S^6*S1^2*X^10 - 2549232*S^6*S1^2*X^9 + 589680*S^6*S1^2*X^8 - 87480*S^6*S1*X^11 + 990144*S^6*S1*X^10 + 4403592*S^6*S1*X^9 + 3630576*S^6*S1*X^8 - 1243680*S^6*S1*X^7 - 118584*S^6*X^10 - 169374*S^6*X^9 - 283374*S^6*X^8 - 125266*S^6*X^7 + 321590*S^6*X^6 + 979776*S^5*S1^2*X^10 + 4826304*S^5*S1^2*X^9 + 3100608*S^5*S1^2*X^8 - 745920*S^5*S1^2*X^7 + 247860*S^5*S1*X^10 - 1277424*S^5*S1*X^9 - 3591720*S^5*S1*X^8 - 2043312*S^5*S1*X^7 + 907860*S^5*S1*X^6 + 32562*S^5*X^10 + 334494*S^5*X^9 + 68442*S^5*X^8 - 160530*S^5*X^7 - 319348*S^5*X^6 - 98420*S^5*X^5 - 69984*S^4*S1^2*X^10 - 1643328*S^4*S1^2*X^9 - 4371840*S^4*S1^2*X^8 - 2225856*S^4*S1^2*X^7 + 572640*S^4*S1^2*X^6 - 52488*S^4*S1*X^10 - 361584*S^4*S1*X^9 + 747864*S^4*S1*X^8 + 1683864*S^4*S1*X^7 + 429712*S^4*S1*X^6 - 393800*S^4*S1*X^5 - 29160*S^4*X^10 - 169452*S^4*X^9 - 463434*S^4*X^8 - 37740*S^4*X^7 + 329456*S^4*X^6 + 270376*S^4*X^5 - 7150*S^4*X^4 + 186624*S^3*S1^2*X^9 + 1479168*S^3*S1^2*X^8 + 2519040*S^3*S1^2*X^7 + 953856*S^3*S1^2*X^6 - 272640*S^3*S1^2*X^5 + 125064*S^3*S1*X^9 + 358728*S^3*S1*X^8 - 106608*S^3*S1*X^7 - 304048*S^3*S1*X^6 + 128104*S^3*S1*X^5 + 91880*S^3*S1*X^4 + 89262*S^3*X^9 + 285312*S^3*X^8 + 382672*S^3*X^7 + 35392*S^3*X^6 - 211090*S^3*X^5 - 92432*S^3*X^4 + 16580*S^3*X^3 - 3888*S^2*S1^2*X^9 - 185904*S^2*S1^2*X^8 - 750816*S^2*S1^2*X^7 - 880992*S^2*S1^2*X^6 - 233712*S^2*S1^2*X^5 + 78480*S^2*S1^2*X^4 - 5832*S^2*S1*X^9 - 116208*S^2*S1*X^8 - 224304*S^2*S1*X^7 - 105216*S^2*S1*X^6 - 78216*S^2*S1*X^5 - 93648*S^2*S1*X^4 - 6720*S^2*S1*X^3 - 7776*S^2*X^9 - 107865*S^2*X^8 - 218004*S^2*X^7 - 185945*S^2*X^6 - 20032*S^2*X^5 + 65445*S^2*X^4 + 12052*S^2*X^3 - 5395*S^2*X^2 + 5184*S*S1^2*X^8 + 81984*S*S1^2*X^7 + 202368*S*S1^2*X^6 + 167040*S*S1^2*X^5 + 28992*S*S1^2*X^4 - 12480*S*S1^2*X^3 + 6966*S*S1*X^8 + 47868*S*S1*X^7 + 75938*S*S1*X^6 + 58088*S*S1*X^5 + 43674*S*S1*X^4 + 19292*S*S1*X^3 - 1330*S*S1*X^2 + 10854*S*X^8 + 55566*S*X^7 + 77464*S*X^6 + 48200*S*X^5 + 6550*S*X^4 - 9074*S*X^3 + 524*S*X^2 + 700*S*X + 648*S1^2*X^8 - 2064*S1^2*X^7 - 13896*S1^2*X^6 - 21984*S1^2*X^5 - 12936*S1^2*X^4 - 1296*S1^2*X^3 + 840*S1^2*X^2 + 648*S1*X^8 - 1308*S1*X^7 - 7784*S1*X^6 - 11020*S1*X^5 - 8936*S1*X^4 - 5300*S1*X^3 - 1336*S1*X^2 + 220*S1*X + 648*X^8 - 3195*X^7 - 10167*X^6 - 10247*X^5 - 5379*X^4 - 961*X^3 + 331*X^2 - 189*X - 25) * e1 + (85293*S^10*X^12 + 101574*S^10*X^11 - 30375*S^10*X^10 + 157464*S^9*S1*X^12 + 128304*S^9*S1*X^11 - 29160*S^9*S1*X^10 - 463644*S^9*X^11 - 591624*S^9*X^10 + 183060*S^9*X^9 - 944784*S^8*S1*X^11 - 769824*S^8*S1*X^10 + 174960*S^8*S1*X^9 + 115911*S^8*X^11 + 1194021*S^8*X^10 + 1430325*S^8*X^9 - 477225*S^8*X^8 + 209952*S^7*S1*X^11 + 2620512*S^7*S1*X^10 + 1956960*S^7*S1*X^9 - 453600*S^7*S1*X^8 - 478224*S^7*X^10 - 1915056*S^7*X^9 - 1837872*S^7*X^8 + 704880*S^7*X^7 - 979776*S^6*S1*X^10 - 4390848*S^6*S1*X^9 - 2745792*S^6*S1*X^8 + 665280*S^6*S1*X^7 + 59778*S^6*X^10 + 845424*S^6*X^9 + 2008260*S^6*X^8 + 1310784*S^6*X^7 - 649110*S^6*X^6 + 104976*S^5*S1*X^10 + 1975104*S^5*S1*X^9 + 4797792*S^5*S1*X^8 + 2320704*S^5*S1*X^7 - 606960*S^5*S1*X^6 - 169128*S^5*X^9 - 831168*S^5*X^8 - 1305168*S^5*X^7 - 453376*S^5*X^6 + 386360*S^5*X^5 - 349920*S^4*S1*X^9 - 2229120*S^4*S1*X^8 - 3445056*S^4*S1*X^7 - 1209216*S^4*S1*X^6 + 356640*S^4*S1*X^5 + 14094*S^4*X^9 + 180342*S^4*X^8 + 465228*S^4*X^7 + 444332*S^4*X^6 - 3578*S^4*X^5 - 148930*S^4*X^4 + 23328*S^3*S1*X^9 + 462240*S^3*S1*X^8 + 1505088*S^3*S1*X^7 + 1581888*S^3*S1*X^6 + 380832*S^3*S1*X^5 - 134880*S^3*S1*X^4 - 22032*S^3*X^8 - 86352*S^3*X^7 - 115360*S^3*X^6 - 23712*S^3*X^5 + 63408*S^3*X^4 + 36080*S^3*X^3 - 46656*S^2*S1*X^8 - 302400*S^2*S1*X^7 - 595584*S^2*S1*X^6 - 438912*S^2*S1*X^5 - 67392*S^2*S1*X^4 + 31680*S^2*S1*X^3 + 1377*S^2*X^8 + 9042*S^2*X^7 + 11179*S^2*X^6 - 12020*S^2*X^5 - 33369*S^2*X^4 - 22910*S^2*X^3 - 5075*S^2*X^2 + 1944*S*S1*X^8 + 30096*S*S1*X^7 + 96744*S*S1*X^6 + 124896*S*S1*X^5 + 66024*S*S1*X^4 + 5520*S*S1*X^3 - 4200*S*S1*X^2 - 540*S*X^7 - 56*S*X^6 + 5516*S*X^5 + 11824*S*X^4 + 9916*S*X^3 + 3464*S*X^2 + 340*S*X - 1296*S1*X^7 - 6240*S1*X^6 - 11760*S1*X^5 - 10560*S1*X^4 - 4080*S1*X^3 - 96*S1*X^2 + 240*S1*X + 27*X^7 - 35*X^6 - 585*X^5 - 1455*X^4 - 1615*X^3 - 873*X^2 - 195*X - 5) * e2 + (-26244*S^10*X^12 - 21384*S^10*X^11 + 4860*S^10*X^10 + 174960*S^9*X^11 + 142560*S^9*X^10 - 32400*S^9*X^9 - 43740*S^8*X^11 - 545940*S^8*X^10 - 407700*S^8*X^9 + 94500*S^8*X^8 + 233280*S^7*X^10 + 1045440*S^7*X^9 + 653760*S^7*X^8 - 158400*S^7*X^7 - 29160*S^6*X^10 - 548640*S^6*X^9 - 1332720*S^6*X^8 - 644640*S^6*X^7 + 168600*S^6*X^6 + 116640*S^5*X^9 + 743040*S^5*X^8 + 1148352*S^5*X^7 + 403072*S^5*X^6 - 118880*S^5*X^5 - 9720*S^4*X^9 - 192600*S^4*X^8 - 627120*S^4*X^7 - 659120*S^4*X^6 - 158680*S^4*X^5 + 56200*S^4*X^4 + 25920*S^3*X^8 + 168000*S^3*X^7 + 330880*S^3*X^6 + 243840*S^3*X^5 + 37440*S^3*X^4 - 17600*S^3*X^3 - 1620*S^2*X^8 - 25080*S^2*X^7 - 80620*S^2*X^6 - 104080*S^2*X^5 - 55020*S^2*X^4 - 4600*S^2*X^3 + 3500*S^2*X^2 + 2160*S*X^7 + 10400*S*X^6 + 19600*S*X^5 + 17600*S*X^4 + 6800*S*X^3 + 160*S*X^2 - 400*S*X - 108*X^7 - 628*X^6 - 1500*X^5 - 1860*X^4 - 1220*X^3 - 348*X^2 + 12*X + 20) * e3


lemma coeff_ofNat_mul' (k n : ℕ) [k.AtLeastTwo] (f : ℚ⟦X⟧) :
    coeff n ((no_index (OfNat.ofNat k : ℚ⟦X⟧)) * f) = (OfNat.ofNat k : ℚ) * coeff n f := by
  rw [← map_ofNat (PowerSeries.C (R := ℚ)) k, coeff_C_mul]

lemma coeff_succ_ofNat' (k n : ℕ) [k.AtLeastTwo] :
    coeff (n + 1) (no_index (OfNat.ofNat k : ℚ⟦X⟧)) = 0 := by
  rw [← map_ofNat (PowerSeries.C (R := ℚ)) k, coeff_C]; simp

/-- The P-recurrence read off the linear ODE. -/
lemma rec_of_ode (S : ℚ⟦X⟧)
    (h : (20 * tD (tD (tD S)) - 5 * tD (tD S) - 25 * tD S)
      + X * (8 * S - 14 * tD S - 110 * tD (tD S) - 88 * tD (tD (tD S)) + 12)
      + X * (X * -(42 * S + 213 * tD S + 297 * tD (tD S) + 108 * tD (tD (tD S))) ) = 0)
    (n : ℕ) :
    5 * ((n : ℚ) + 2) * (n + 3) * (4 * n + 3) * coeff (n + 2) S =
      2 * ((n : ℚ) + 2) * (44 * n ^ 2 + 99 * n + 51) * coeff (n + 1) S
        + 3 * (3 * (n : ℚ) + 1) * (3 * n + 2) * (4 * n + 7) * coeff n S := by
  have h' := congrArg (coeff (n + 2)) h
  simp only [map_add, map_sub, map_neg, coeff_succ_X_mul, coeff_ofNat_mul', coeff_tD,
    coeff_succ_ofNat', map_zero] at h'
  push_cast at h'
  linear_combination h'


/-- The P-recurrence `5(n+2)(n+3)(4n+3) s_{n+2} = 2(n+2)(44n²+99n+51) s_{n+1} + 3(3n+1)(3n+2)(4n+7) s_n`. -/
def PRec (s : ℕ → ℚ) : Prop := ∀ n : ℕ,
  5 * ((n : ℚ) + 2) * (n + 3) * (4 * n + 3) * s (n + 2) =
    2 * ((n : ℚ) + 2) * (44 * n ^ 2 + 99 * n + 51) * s (n + 1)
      + 3 * (3 * (n : ℚ) + 1) * (3 * n + 2) * (4 * n + 7) * s n

lemma PRec_unique (s s' : ℕ → ℚ) (h : PRec s) (h' : PRec s') (h0 : s 0 = s' 0)
    (h1 : s 1 = s' 1) : s = s' := by
  have key : ∀ n, s n = s' n ∧ s (n + 1) = s' (n + 1) := by
    intro n
    induction n with
    | zero => exact ⟨h0, h1⟩
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      have e := h n; have e' := h' n
      have hne : 5 * ((n : ℚ) + 2) * (n + 3) * (4 * n + 3) ≠ 0 := by positivity
      apply mul_left_cancel₀ hne
      rw [e, e', ih.1, ih.2]
  funext n; exact (key n).1

lemma coeff_S (n : ℕ) : coeff n S = if n = 0 then 1 else ersCoeff n := by
  rw [S, coeff_mk]

lemma S_PRec : PRec (fun n => coeff n S) := by
  intro n
  simp only [coeff_S]
  rcases n with _ | k
  · have e1 : ersCoeff 1 = 2 := by norm_num [ersCoeff, Finset.sum_range_succ]
    have e2 : ersCoeff 2 = 5 := by norm_num [ersCoeff, Finset.sum_range_succ]
    simp [e1, e2]; norm_num
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), ersCoeff_eq, ersCoeff_eq,
      ersCoeff_eq]
    have hb := b_rec (k + 1) (by omega)
    rw [show k + 1 + 1 = k + 2 by ring, show k + 1 + 2 = k + 3 by ring] at *
    push_cast at hb ⊢
    have h1 : ((k : ℚ) + 1) ≠ 0 := by positivity
    have h2 : ((k : ℚ) + 2) ≠ 0 := by positivity
    have h3 : ((k : ℚ) + 3) ≠ 0 := by positivity
    field_simp
    linear_combination (k + 3 : ℚ) * hb

/-- Hensel: the cubic has a root (in the monic variable `y = 1 − tS`). -/
lemma exists_root_K : ∃ S' : ℚ⟦X⟧, K S' = 0 := by
  set I : Ideal ℚ⟦X⟧ := Ideal.span {PowerSeries.X}
  set f : Polynomial ℚ⟦X⟧ := Polynomial.X ^ 3 - Polynomial.X ^ 2
    + Polynomial.C PowerSeries.X * Polynomial.X + Polynomial.C (PowerSeries.X ^ 2) with hf
  have hmon : f.Monic := by rw [hf]; monicity!
  have h1 : f.eval 1 ∈ I := by
    apply Ideal.mem_span_singleton.mpr
    refine ⟨1 + PowerSeries.X, ?_⟩
    simp [f]; ring
  have h2 : IsUnit (Ideal.Quotient.mk I (f.derivative.eval 1)) := by
    apply IsUnit.map
    rw [PowerSeries.isUnit_iff_constantCoeff]
    have c2 : constantCoeff (2 : ℚ⟦X⟧) = 2 := map_ofNat _ 2
    simp [f, -map_pow, Polynomial.derivative_C, c2]
    norm_num
  obtain ⟨y, hroot, hsub⟩ := HenselianRing.is_henselian f hmon 1 h1 h2
  obtain ⟨g, hg⟩ := Ideal.mem_span_singleton.mp hsub
  refine ⟨-g, ?_⟩
  have hy : y = 1 + PowerSeries.X * g := by rw [← hg]; ring
  have heq : y ^ 3 - y ^ 2 + PowerSeries.X * y + PowerSeries.X ^ 2 = 0 := by
    simpa [f] using hroot
  rw [hy] at heq
  have hX : (PowerSeries.X : ℚ⟦X⟧) ≠ 0 := PowerSeries.X_ne_zero
  refine (mul_eq_zero.mp ?_).resolve_left hX
  rw [K]
  linear_combination (-1 : ℚ⟦X⟧) * heq

lemma root_PRec (S' : ℚ⟦X⟧) (hK : K S' = 0) : PRec (fun n => coeff n S') := by
  intro n
  have h := ode_of_K S' hK
  simp only at h
  exact rec_of_ode S' (by linear_combination h) n

lemma root_coeff01 (S' : ℚ⟦X⟧) (hK : K S' = 0) : coeff 0 S' = 1 ∧ coeff 1 S' = 2 := by
  have hc : constantCoeff S' = 1 := by
    have := congrArg constantCoeff hK
    simp [K] at this
    linear_combination this
  have h0 : coeff 0 S' = 1 := by rw [coeff_zero_eq_constantCoeff_apply, hc]
  refine ⟨h0, ?_⟩
  have e : K S' = X * (X * S' ^ 3 - 2 * S' ^ 2 + S' - 1) + (S' - 1) := by rw [K]; ring
  have h1 := congrArg (coeff 1) (e.symm.trans hK)
  have c2 : constantCoeff (2 : ℚ⟦X⟧) = 2 := map_ofNat _ 2
  simp [coeff_succ_X_mul, coeff_one, hc, c2] at h1
  linear_combination h1

/-- The binomial series satisfies the cubic. -/
lemma S_cubic : K S = 0 := by
  obtain ⟨S', hK⟩ := exists_root_K
  obtain ⟨h0, h1⟩ := root_coeff01 S' hK
  have hseq := PRec_unique _ _ S_PRec (root_PRec S' hK)
    (by rw [coeff_S, if_pos rfl, h0]) (by
      rw [coeff_S, if_neg (by norm_num), h1]; norm_num [ersCoeff, Finset.sum_range_succ])
  have : S = S' := PowerSeries.ext fun n => congrFun hseq n
  rw [this, hK]

end ErsConj13
