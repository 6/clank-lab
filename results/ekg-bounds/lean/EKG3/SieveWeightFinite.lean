import EKG3.SieveWeightFiniteCertificate
import EKG3.SieveWeightFiniteChunk17

namespace EKG3

/-- The kernel-checked chunks chain: each one ends at the running total from
which the next one starts. -/
theorem finiteSieve_small (Q : ℕ) (hQ6 : 6 ≤ Q) (hQ : Q < 1440) :
    rationalLogUpper (Q+1) + 107/100 < (roundedSieveSum Q : ℚ)/1000000 := by
  have h0 : (0 : ℕ) = roundedSieveSum 0 := rfl
  have h1 : 5728076 = roundedSieveSum 80 :=
    finiteSieveCheck_final _ _ _ _ h0 finiteSieveCheck_chunk0
  have h2 : 6397778 = roundedSieveSum 160 :=
    finiteSieveCheck_final _ _ _ _ h1 finiteSieveCheck_chunk1
  have h3 : 6826936 = roundedSieveSum 240 :=
    finiteSieveCheck_final _ _ _ _ h2 finiteSieveCheck_chunk2
  have h4 : 7098247 = roundedSieveSum 320 :=
    finiteSieveCheck_final _ _ _ _ h3 finiteSieveCheck_chunk3
  have h5 : 7316666 = roundedSieveSum 400 :=
    finiteSieveCheck_final _ _ _ _ h4 finiteSieveCheck_chunk4
  have h6 : 7511970 = roundedSieveSum 480 :=
    finiteSieveCheck_final _ _ _ _ h5 finiteSieveCheck_chunk5
  have h7 : 7659199 = roundedSieveSum 560 :=
    finiteSieveCheck_final _ _ _ _ h6 finiteSieveCheck_chunk6
  have h8 : 7793255 = roundedSieveSum 640 :=
    finiteSieveCheck_final _ _ _ _ h7 finiteSieveCheck_chunk7
  have h9 : 7919079 = roundedSieveSum 720 :=
    finiteSieveCheck_final _ _ _ _ h8 finiteSieveCheck_chunk8
  have h10 : 8020151 = roundedSieveSum 800 :=
    finiteSieveCheck_final _ _ _ _ h9 finiteSieveCheck_chunk9
  have h11 : 8109615 = roundedSieveSum 880 :=
    finiteSieveCheck_final _ _ _ _ h10 finiteSieveCheck_chunk10
  have h12 : 8198803 = roundedSieveSum 960 :=
    finiteSieveCheck_final _ _ _ _ h11 finiteSieveCheck_chunk11
  have h13 : 8278093 = roundedSieveSum 1040 :=
    finiteSieveCheck_final _ _ _ _ h12 finiteSieveCheck_chunk12
  have h14 : 8350771 = roundedSieveSum 1120 :=
    finiteSieveCheck_final _ _ _ _ h13 finiteSieveCheck_chunk13
  have h15 : 8421274 = roundedSieveSum 1200 :=
    finiteSieveCheck_final _ _ _ _ h14 finiteSieveCheck_chunk14
  have h16 : 8483305 = roundedSieveSum 1280 :=
    finiteSieveCheck_final _ _ _ _ h15 finiteSieveCheck_chunk15
  have h17 : 8548349 = roundedSieveSum 1360 :=
    finiteSieveCheck_final _ _ _ _ h16 finiteSieveCheck_chunk16
  by_cases c0 : Q ≤ 80
  · exact finiteSieveCheck_sound _ _ _ _ h0 finiteSieveCheck_chunk0 Q (by omega) (by omega) hQ6
  by_cases c1 : Q ≤ 160
  · exact finiteSieveCheck_sound _ _ _ _ h1 finiteSieveCheck_chunk1 Q (by omega) (by omega) hQ6
  by_cases c2 : Q ≤ 240
  · exact finiteSieveCheck_sound _ _ _ _ h2 finiteSieveCheck_chunk2 Q (by omega) (by omega) hQ6
  by_cases c3 : Q ≤ 320
  · exact finiteSieveCheck_sound _ _ _ _ h3 finiteSieveCheck_chunk3 Q (by omega) (by omega) hQ6
  by_cases c4 : Q ≤ 400
  · exact finiteSieveCheck_sound _ _ _ _ h4 finiteSieveCheck_chunk4 Q (by omega) (by omega) hQ6
  by_cases c5 : Q ≤ 480
  · exact finiteSieveCheck_sound _ _ _ _ h5 finiteSieveCheck_chunk5 Q (by omega) (by omega) hQ6
  by_cases c6 : Q ≤ 560
  · exact finiteSieveCheck_sound _ _ _ _ h6 finiteSieveCheck_chunk6 Q (by omega) (by omega) hQ6
  by_cases c7 : Q ≤ 640
  · exact finiteSieveCheck_sound _ _ _ _ h7 finiteSieveCheck_chunk7 Q (by omega) (by omega) hQ6
  by_cases c8 : Q ≤ 720
  · exact finiteSieveCheck_sound _ _ _ _ h8 finiteSieveCheck_chunk8 Q (by omega) (by omega) hQ6
  by_cases c9 : Q ≤ 800
  · exact finiteSieveCheck_sound _ _ _ _ h9 finiteSieveCheck_chunk9 Q (by omega) (by omega) hQ6
  by_cases c10 : Q ≤ 880
  · exact finiteSieveCheck_sound _ _ _ _ h10 finiteSieveCheck_chunk10 Q (by omega) (by omega) hQ6
  by_cases c11 : Q ≤ 960
  · exact finiteSieveCheck_sound _ _ _ _ h11 finiteSieveCheck_chunk11 Q (by omega) (by omega) hQ6
  by_cases c12 : Q ≤ 1040
  · exact finiteSieveCheck_sound _ _ _ _ h12 finiteSieveCheck_chunk12 Q (by omega) (by omega) hQ6
  by_cases c13 : Q ≤ 1120
  · exact finiteSieveCheck_sound _ _ _ _ h13 finiteSieveCheck_chunk13 Q (by omega) (by omega) hQ6
  by_cases c14 : Q ≤ 1200
  · exact finiteSieveCheck_sound _ _ _ _ h14 finiteSieveCheck_chunk14 Q (by omega) (by omega) hQ6
  by_cases c15 : Q ≤ 1280
  · exact finiteSieveCheck_sound _ _ _ _ h15 finiteSieveCheck_chunk15 Q (by omega) (by omega) hQ6
  by_cases c16 : Q ≤ 1360
  · exact finiteSieveCheck_sound _ _ _ _ h16 finiteSieveCheck_chunk16 Q (by omega) (by omega) hQ6
  exact finiteSieveCheck_sound _ _ _ _ h17 finiteSieveCheck_chunk17 Q (by omega) (by omega) hQ6

theorem G_gt_log_add_107_small (Q : ℕ) (hQ6 : 6 ≤ Q) (hQ : Q < 1440) :
    Real.log ((Q : ℝ)+1) + 1.07 < G Q := by
  have hr := finiteSieve_small Q hQ6 hQ
  have hrR : (rationalLogUpper (Q+1) : ℝ) + 1.07 <
      (roundedSieveSum Q : ℝ)/1000000 := by
    have hc := (Rat.cast_lt (K := ℝ)).mpr hr
    norm_num at hc ⊢
    exact hc
  have hl := log_le_rationalLogUpper (Q+1) (by omega)
  push_cast at hl
  linarith [roundedSieveSum_le Q]

/-- An original proof from finite Euler products and harmonic bounds. -/
theorem G_gt_log_add_107 (Q : ℕ) (hQ : 6 ≤ Q) :
    Real.log ((Q : ℝ)+1) + 1.07 < G Q := by
  by_cases hlarge : 1440 ≤ Q
  · exact G_gt_log_add_107_large Q hlarge
  · exact G_gt_log_add_107_small Q hQ (by omega)

end EKG3
