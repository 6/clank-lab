import BaseREhrhart.CertificateChunk0
import BaseREhrhart.CertificateChunk1
import BaseREhrhart.CertificateChunk2
import BaseREhrhart.CertificateChunk3

/-! Exact finite height histogram, checked by
ordinary Lean kernel reduction. All 537,824 residues are covered by
consecutive binary blocks, with no generated axioms or native_decide. -/

set_option maxHeartbeats 0
set_option maxRecDepth 10000

namespace BaseREhrhart


def certificateCover : List ℕ := [14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 13, 12, 10, 7, 6, 5]

lemma certificateCover_size : coverSize certificateCover = D := by decide

def packedValues (start : ℕ) : List ℕ → List ℕ
  | [] => []
  | k :: ks => packedBlock start k :: packedValues (start + 2 ^ k) ks

lemma packedValues_sum (ks : List ℕ) (start : ℕ) :
    (packedValues start ks).sum = packedCover start ks := by
  induction ks generalizing start with
  | nil => rfl
  | cons k ks ih => simp only [packedValues, List.sum_cons, packedCover, ih]

lemma packedCover_checked : packedCover 0 certificateCover =
    Nat.ofDigits radix (List.ofFn weight) := by
  have h000 : packedBlock (0) 14 = _ := packedBlock_000
  have h001 : packedBlock (0 + 2 ^ 14) 14 = _ := packedBlock_001
  have h002 : packedBlock (0 + 2 ^ 14 + 2 ^ 14) 14 = _ := packedBlock_002
  have h003 : packedBlock (0 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14) 14 = _ := packedBlock_003
  have h004 : packedBlock (0 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14) 14 = _ := packedBlock_004
  have h005 : packedBlock (0 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14) 14 = _ := packedBlock_005
  have h006 : packedBlock (0 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14) 14 = _ := packedBlock_006
  have h007 : packedBlock (0 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14) 14 = _ := packedBlock_007
  have h008 : packedBlock (0 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14) 14 = _ := packedBlock_008
  have h009 : packedBlock (0 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14) 14 = _ := packedBlock_009
  have h010 : packedBlock (0 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14) 14 = _ := packedBlock_010
  have h011 : packedBlock (0 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14) 14 = _ := packedBlock_011
  have h012 : packedBlock (0 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14) 14 = _ := packedBlock_012
  have h013 : packedBlock (0 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14) 14 = _ := packedBlock_013
  have h014 : packedBlock (0 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14) 14 = _ := packedBlock_014
  have h015 : packedBlock (0 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14) 14 = _ := packedBlock_015
  have h016 : packedBlock (0 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14) 14 = _ := packedBlock_016
  have h017 : packedBlock (0 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14) 14 = _ := packedBlock_017
  have h018 : packedBlock (0 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14) 14 = _ := packedBlock_018
  have h019 : packedBlock (0 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14) 14 = _ := packedBlock_019
  have h020 : packedBlock (0 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14) 14 = _ := packedBlock_020
  have h021 : packedBlock (0 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14) 14 = _ := packedBlock_021
  have h022 : packedBlock (0 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14) 14 = _ := packedBlock_022
  have h023 : packedBlock (0 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14) 14 = _ := packedBlock_023
  have h024 : packedBlock (0 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14) 14 = _ := packedBlock_024
  have h025 : packedBlock (0 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14) 14 = _ := packedBlock_025
  have h026 : packedBlock (0 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14) 14 = _ := packedBlock_026
  have h027 : packedBlock (0 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14) 14 = _ := packedBlock_027
  have h028 : packedBlock (0 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14) 14 = _ := packedBlock_028
  have h029 : packedBlock (0 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14) 14 = _ := packedBlock_029
  have h030 : packedBlock (0 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14) 14 = _ := packedBlock_030
  have h031 : packedBlock (0 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14) 14 = _ := packedBlock_031
  have h032 : packedBlock (0 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14) 13 = _ := packedBlock_032
  have h033 : packedBlock (0 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 13) 12 = _ := packedBlock_033
  have h034 : packedBlock (0 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 13 + 2 ^ 12) 10 = _ := packedBlock_034
  have h035 : packedBlock (0 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 13 + 2 ^ 12 + 2 ^ 10) 7 = _ := packedBlock_035
  have h036 : packedBlock (0 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 13 + 2 ^ 12 + 2 ^ 10 + 2 ^ 7) 6 = _ := packedBlock_036
  have h037 : packedBlock (0 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 14 + 2 ^ 13 + 2 ^ 12 + 2 ^ 10 + 2 ^ 7 + 2 ^ 6) 5 = _ := packedBlock_037
  have hb := (congrArg₂ List.cons h000 (congrArg₂ List.cons h001 (congrArg₂ List.cons h002 (congrArg₂ List.cons h003 (congrArg₂ List.cons h004 (congrArg₂ List.cons h005 (congrArg₂ List.cons h006 (congrArg₂ List.cons h007 (congrArg₂ List.cons h008 (congrArg₂ List.cons h009 (congrArg₂ List.cons h010 (congrArg₂ List.cons h011 (congrArg₂ List.cons h012 (congrArg₂ List.cons h013 (congrArg₂ List.cons h014 (congrArg₂ List.cons h015 (congrArg₂ List.cons h016 (congrArg₂ List.cons h017 (congrArg₂ List.cons h018 (congrArg₂ List.cons h019 (congrArg₂ List.cons h020 (congrArg₂ List.cons h021 (congrArg₂ List.cons h022 (congrArg₂ List.cons h023 (congrArg₂ List.cons h024 (congrArg₂ List.cons h025 (congrArg₂ List.cons h026 (congrArg₂ List.cons h027 (congrArg₂ List.cons h028 (congrArg₂ List.cons h029 (congrArg₂ List.cons h030 (congrArg₂ List.cons h031 (congrArg₂ List.cons h032 (congrArg₂ List.cons h033 (congrArg₂ List.cons h034 (congrArg₂ List.cons h035 (congrArg₂ List.cons h036 (congrArg₂ List.cons h037 (rfl : ([] : List ℕ) = [])))))))))))))))))))))))))))))))))))))))
  have hs : packedValues 0 certificateCover = _ := hb
  have hsum := congrArg List.sum hs
  exact (packedValues_sum certificateCover 0).symm.trans (hsum.trans (by decide))

/-- The exact encoded sum, over every residue of the actual quotient. -/
lemma packed_height_sum : (∑ b : Fin D, radix ^ rawHeight b.val) =
    Nat.ofDigits radix (List.ofFn weight) := by
  have hc := packedCover_eq_sum certificateCover 0
  simp only [certificateCover_size, Nat.zero_add] at hc
  rw [← Fin.sum_univ_eq_sum_range] at hc
  exact hc.symm.trans packedCover_checked

/-- The finite histogram premise used by the geometric count theorem,
fully discharged by this kernel-checked certificate. -/
theorem height_histogram (h : Fin 6) :
    (Finset.univ.filter (fun b : Fin D => height b = h.val)).card = weight h :=
  histogram_of_packed_sum packed_height_sum h

end BaseREhrhart
