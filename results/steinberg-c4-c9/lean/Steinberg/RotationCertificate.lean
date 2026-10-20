import Mathlib.Tactic.FinCases
import Batteries.Data.List.Perm
import Steinberg.Data
import Steinberg.Rotation

namespace Steinberg
open Rotation
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Explicit face orbits, traced from the exact published cyclic orders.
Each local step and the exhaustive distinct partition are proved below. -/
def sphericalFaces : List (List Dart) :=
  [
   [(0, 1), (1, 6), (6, 0)],
   [(0, 3), (3, 24), (24, 22), (22, 26), (26, 42), (42, 10), (10, 7), (7, 14), (14, 68), (68, 58), (58, 55), (55, 56), (56, 20), (20, 1), (1, 0)],
   [(0, 2), (2, 32), (32, 33), (33, 3), (3, 0)],
   [(0, 5), (5, 29), (29, 27), (27, 31), (31, 46), (46, 38), (38, 25), (25, 22), (22, 23), (23, 2), (2, 0)],
   [(0, 4), (4, 34), (34, 35), (35, 5), (5, 0)],
   [(0, 6), (6, 60), (60, 12), (12, 7), (7, 8), (8, 36), (36, 30), (30, 27), (27, 28), (28, 4), (4, 0)],
   [(1, 19), (19, 52), (52, 50), (50, 54), (54, 74), (74, 16), (16, 7), (7, 13), (13, 61), (61, 6), (6, 1)],
   [(1, 18), (18, 64), (64, 65), (65, 19), (19, 1)],
   [(1, 21), (21, 57), (57, 55), (55, 59), (59, 78), (78, 70), (70, 53), (53, 50), (50, 51), (51, 18), (18, 1)],
   [(1, 20), (20, 66), (66, 67), (67, 21), (21, 1)],
   [(2, 23), (23, 32), (32, 2)],
   [(3, 33), (33, 24), (24, 3)],
   [(4, 28), (28, 34), (34, 4)],
   [(5, 35), (35, 29), (29, 5)],
   [(6, 61), (61, 63), (63, 62), (62, 60), (60, 6)],
   [(7, 12), (12, 62), (62, 63), (63, 13), (13, 7)],
   [(7, 9), (9, 41), (41, 40), (40, 8), (8, 7)],
   [(7, 11), (11, 43), (43, 26), (26, 25), (25, 39), (39, 47), (47, 31), (31, 30), (30, 37), (37, 9), (9, 7)],
   [(7, 10), (10, 44), (44, 45), (45, 11), (11, 7)],
   [(7, 15), (15, 73), (73, 72), (72, 14), (14, 7)],
   [(7, 17), (17, 75), (75, 54), (54, 53), (53, 71), (71, 79), (79, 59), (59, 58), (58, 69), (69, 15), (15, 7)],
   [(7, 16), (16, 76), (76, 77), (77, 17), (17, 7)],
   [(8, 40), (40, 36), (36, 8)],
   [(9, 37), (37, 41), (41, 9)],
   [(10, 42), (42, 44), (44, 10)],
   [(11, 45), (45, 43), (43, 11)],
   [(12, 60), (60, 62), (62, 12)],
   [(13, 63), (63, 61), (61, 13)],
   [(14, 72), (72, 68), (68, 14)],
   [(15, 69), (69, 73), (73, 15)],
   [(16, 74), (74, 76), (76, 16)],
   [(17, 77), (77, 75), (75, 17)],
   [(18, 51), (51, 64), (64, 18)],
   [(19, 65), (65, 52), (52, 19)],
   [(20, 56), (56, 66), (66, 20)],
   [(21, 67), (67, 57), (57, 21)],
   [(22, 25), (25, 26), (26, 22)],
   [(22, 24), (24, 33), (33, 32), (32, 23), (23, 22)],
   [(25, 38), (38, 48), (48, 49), (49, 39), (39, 25)],
   [(26, 43), (43, 45), (45, 44), (44, 42), (42, 26)],
   [(27, 30), (30, 31), (31, 27)],
   [(27, 29), (29, 35), (35, 34), (34, 28), (28, 27)],
   [(30, 36), (36, 40), (40, 41), (41, 37), (37, 30)],
   [(31, 47), (47, 49), (49, 48), (48, 46), (46, 31)],
   [(38, 46), (46, 48), (48, 38)],
   [(39, 49), (49, 47), (47, 39)],
   [(50, 53), (53, 54), (54, 50)],
   [(50, 52), (52, 65), (65, 64), (64, 51), (51, 50)],
   [(53, 70), (70, 80), (80, 81), (81, 71), (71, 53)],
   [(54, 75), (75, 77), (77, 76), (76, 74), (74, 54)],
   [(55, 58), (58, 59), (59, 55)],
   [(55, 57), (57, 67), (67, 66), (66, 56), (56, 55)],
   [(58, 68), (68, 72), (72, 73), (73, 69), (69, 58)],
   [(59, 79), (79, 81), (81, 80), (80, 78), (78, 59)],
   [(70, 78), (78, 80), (80, 70)],
   [(71, 81), (81, 79), (79, 71)]
  ]

private def parentValues : List Nat :=
  [0, 0, 0, 0, 0, 0, 0, 12, 7, 7, 7, 7, 60, 61, 7, 7, 7, 7, 1, 1, 1, 1, 24, 2, 3, 22, 22, 29, 4, 5, 27, 27, 2, 3, 4, 5, 30, 30, 25, 25, 36, 37, 26, 26, 42, 43, 31, 31, 38, 39, 52, 18, 19, 50, 50, 57, 20, 21, 55, 55, 6, 6, 60, 61, 18, 19, 20, 21, 58, 58, 53, 53, 14, 15, 54, 54, 16, 17, 59, 59, 70, 71]

private def rankValues : List Nat :=
  [0, 1, 1, 1, 1, 1, 1, 4, 5, 5, 5, 5, 3, 3, 5, 5, 5, 5, 2, 2, 2, 2, 3, 2, 2, 4, 4, 3, 2, 2, 4, 4, 2, 2, 2, 2, 5, 5, 5, 5, 6, 6, 5, 5, 6, 6, 5, 5, 6, 6, 4, 3, 3, 5, 5, 4, 3, 3, 5, 5, 2, 2, 3, 3, 3, 3, 3, 3, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 7, 7]

private theorem parent_bound : ∀ v : Fin 82, (parentValues[v.val]?.getD 0) < 82 := by
  decide +kernel

private def treeParent (v : Fin 82) : Fin 82 :=
  ⟨parentValues[v.val]?.getD 0, parent_bound v⟩
private def treeRank (v : Fin 82) : Nat := rankValues[v.val]?.getD 0

private theorem tree_step : ∀ v : Fin 82, v ≠ 0 →
    treeRank (treeParent v) < treeRank v ∧ graph.Adj (treeParent v) v := by
  simp only [graph_adj_iff]
  rw [rotation_edgeList_normal_form]
  decide +kernel

/-- Actual connectedness, independent of the face/Euler certificate. -/
theorem rotation_graph_connected : graph.Connected :=
  connected_of_parents graph 0 treeRank treeParent tree_step

private def DartStep (a b : Dart) : Prop :=
  faceNext rotation a = b ∧ a.1 < 82 ∧ a.2 ∈ neighbors rotation a.1

private def dartCheck (a b : Dart) : Bool :=
  (faceNext rotation a == b) &&
    (decide (a.1 < 82) && (neighbors rotation a.1).contains a.2)

private theorem dartCheck_sound (a b : Dart) (h : dartCheck a b = true) : DartStep a b := by
  unfold dartCheck at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.contains_eq_mem] at h
  exact h

/-- Each row is normalized once; atomic decisions use just two short rows. -/
theorem rotationRow_0 : neighbors rotation 0 = [1, 3, 2, 5, 4, 6] := by
  rw [rotation_normal_form]
  decide +kernel

theorem rotationRow_1 : neighbors rotation 1 = [0, 6, 19, 18, 21, 20] := by
  rw [rotation_normal_form]
  decide +kernel

theorem rotationRow_2 : neighbors rotation 2 = [23, 0, 32] := by
  rw [rotation_normal_form]
  decide +kernel

theorem rotationRow_3 : neighbors rotation 3 = [33, 0, 24] := by
  rw [rotation_normal_form]
  decide +kernel

theorem rotationRow_4 : neighbors rotation 4 = [28, 0, 34] := by
  rw [rotation_normal_form]
  decide +kernel

theorem rotationRow_5 : neighbors rotation 5 = [35, 0, 29] := by
  rw [rotation_normal_form]
  decide +kernel

theorem rotationRow_6 : neighbors rotation 6 = [1, 0, 60, 61] := by
  rw [rotation_normal_form]
  decide +kernel

theorem rotationRow_7 : neighbors rotation 7 = [12, 8, 9, 11, 10, 14, 15, 17, 16, 13] := by
  rw [rotation_normal_form]
  decide +kernel

theorem rotationRow_8 : neighbors rotation 8 = [7, 36, 40] := by
  rw [rotation_normal_form]
  decide +kernel

theorem rotationRow_9 : neighbors rotation 9 = [37, 7, 41] := by
  rw [rotation_normal_form]
  decide +kernel

theorem rotationRow_10 : neighbors rotation 10 = [42, 7, 44] := by
  rw [rotation_normal_form]
  decide +kernel

theorem rotationRow_11 : neighbors rotation 11 = [45, 7, 43] := by
  rw [rotation_normal_form]
  decide +kernel

theorem rotationRow_12 : neighbors rotation 12 = [60, 7, 62] := by
  rw [rotation_normal_form]
  decide +kernel

theorem rotationRow_13 : neighbors rotation 13 = [7, 61, 63] := by
  rw [rotation_normal_form]
  decide +kernel

theorem rotationRow_14 : neighbors rotation 14 = [7, 68, 72] := by
  rw [rotation_normal_form]
  decide +kernel

theorem rotationRow_15 : neighbors rotation 15 = [69, 7, 73] := by
  rw [rotation_normal_form]
  decide +kernel

theorem rotationRow_16 : neighbors rotation 16 = [74, 7, 76] := by
  rw [rotation_normal_form]
  decide +kernel

theorem rotationRow_17 : neighbors rotation 17 = [77, 7, 75] := by
  rw [rotation_normal_form]
  decide +kernel

theorem rotationRow_18 : neighbors rotation 18 = [51, 1, 64] := by
  rw [rotation_normal_form]
  decide +kernel

theorem rotationRow_19 : neighbors rotation 19 = [65, 1, 52] := by
  rw [rotation_normal_form]
  decide +kernel

theorem rotationRow_20 : neighbors rotation 20 = [56, 1, 66] := by
  rw [rotation_normal_form]
  decide +kernel

theorem rotationRow_21 : neighbors rotation 21 = [67, 1, 57] := by
  rw [rotation_normal_form]
  decide +kernel

theorem rotationRow_22 : neighbors rotation 22 = [25, 23, 24, 26] := by
  rw [rotation_normal_form]
  decide +kernel

theorem rotationRow_23 : neighbors rotation 23 = [22, 2, 32] := by
  rw [rotation_normal_form]
  decide +kernel

theorem rotationRow_24 : neighbors rotation 24 = [3, 22, 33] := by
  rw [rotation_normal_form]
  decide +kernel

theorem rotationRow_25 : neighbors rotation 25 = [38, 22, 26, 39] := by
  rw [rotation_normal_form]
  decide +kernel

theorem rotationRow_26 : neighbors rotation 26 = [22, 42, 43, 25] := by
  rw [rotation_normal_form]
  decide +kernel

theorem rotationRow_27 : neighbors rotation 27 = [30, 28, 29, 31] := by
  rw [rotation_normal_form]
  decide +kernel

theorem rotationRow_28 : neighbors rotation 28 = [27, 4, 34] := by
  rw [rotation_normal_form]
  decide +kernel

theorem rotationRow_29 : neighbors rotation 29 = [5, 27, 35] := by
  rw [rotation_normal_form]
  decide +kernel

theorem rotationRow_30 : neighbors rotation 30 = [36, 27, 31, 37] := by
  rw [rotation_normal_form]
  decide +kernel

theorem rotationRow_31 : neighbors rotation 31 = [27, 46, 47, 30] := by
  rw [rotation_normal_form]
  decide +kernel

theorem rotationRow_32 : neighbors rotation 32 = [2, 33, 23] := by
  rw [rotation_normal_form]
  decide +kernel

theorem rotationRow_33 : neighbors rotation 33 = [32, 3, 24] := by
  rw [rotation_normal_form]
  decide +kernel

theorem rotationRow_34 : neighbors rotation 34 = [4, 35, 28] := by
  rw [rotation_normal_form]
  decide +kernel

theorem rotationRow_35 : neighbors rotation 35 = [34, 5, 29] := by
  rw [rotation_normal_form]
  decide +kernel

theorem rotationRow_36 : neighbors rotation 36 = [8, 30, 40] := by
  rw [rotation_normal_form]
  decide +kernel

theorem rotationRow_37 : neighbors rotation 37 = [30, 9, 41] := by
  rw [rotation_normal_form]
  decide +kernel

theorem rotationRow_38 : neighbors rotation 38 = [46, 25, 48] := by
  rw [rotation_normal_form]
  decide +kernel

theorem rotationRow_39 : neighbors rotation 39 = [25, 47, 49] := by
  rw [rotation_normal_form]
  decide +kernel

theorem rotationRow_40 : neighbors rotation 40 = [41, 8, 36] := by
  rw [rotation_normal_form]
  decide +kernel

theorem rotationRow_41 : neighbors rotation 41 = [9, 40, 37] := by
  rw [rotation_normal_form]
  decide +kernel

theorem rotationRow_42 : neighbors rotation 42 = [26, 10, 44] := by
  rw [rotation_normal_form]
  decide +kernel

theorem rotationRow_43 : neighbors rotation 43 = [11, 26, 45] := by
  rw [rotation_normal_form]
  decide +kernel

theorem rotationRow_44 : neighbors rotation 44 = [10, 45, 42] := by
  rw [rotation_normal_form]
  decide +kernel

theorem rotationRow_45 : neighbors rotation 45 = [44, 11, 43] := by
  rw [rotation_normal_form]
  decide +kernel

theorem rotationRow_46 : neighbors rotation 46 = [31, 38, 48] := by
  rw [rotation_normal_form]
  decide +kernel

theorem rotationRow_47 : neighbors rotation 47 = [39, 31, 49] := by
  rw [rotation_normal_form]
  decide +kernel

theorem rotationRow_48 : neighbors rotation 48 = [49, 46, 38] := by
  rw [rotation_normal_form]
  decide +kernel

theorem rotationRow_49 : neighbors rotation 49 = [47, 48, 39] := by
  rw [rotation_normal_form]
  decide +kernel

theorem rotationRow_50 : neighbors rotation 50 = [53, 51, 52, 54] := by
  rw [rotation_normal_form]
  decide +kernel

theorem rotationRow_51 : neighbors rotation 51 = [50, 18, 64] := by
  rw [rotation_normal_form]
  decide +kernel

theorem rotationRow_52 : neighbors rotation 52 = [19, 50, 65] := by
  rw [rotation_normal_form]
  decide +kernel

theorem rotationRow_53 : neighbors rotation 53 = [70, 50, 54, 71] := by
  rw [rotation_normal_form]
  decide +kernel

theorem rotationRow_54 : neighbors rotation 54 = [50, 74, 75, 53] := by
  rw [rotation_normal_form]
  decide +kernel

theorem rotationRow_55 : neighbors rotation 55 = [58, 56, 57, 59] := by
  rw [rotation_normal_form]
  decide +kernel

theorem rotationRow_56 : neighbors rotation 56 = [55, 20, 66] := by
  rw [rotation_normal_form]
  decide +kernel

theorem rotationRow_57 : neighbors rotation 57 = [21, 55, 67] := by
  rw [rotation_normal_form]
  decide +kernel

theorem rotationRow_58 : neighbors rotation 58 = [68, 55, 59, 69] := by
  rw [rotation_normal_form]
  decide +kernel

theorem rotationRow_59 : neighbors rotation 59 = [55, 78, 79, 58] := by
  rw [rotation_normal_form]
  decide +kernel

theorem rotationRow_60 : neighbors rotation 60 = [6, 12, 62] := by
  rw [rotation_normal_form]
  decide +kernel

theorem rotationRow_61 : neighbors rotation 61 = [13, 6, 63] := by
  rw [rotation_normal_form]
  decide +kernel

theorem rotationRow_62 : neighbors rotation 62 = [63, 60, 12] := by
  rw [rotation_normal_form]
  decide +kernel

theorem rotationRow_63 : neighbors rotation 63 = [61, 62, 13] := by
  rw [rotation_normal_form]
  decide +kernel

theorem rotationRow_64 : neighbors rotation 64 = [18, 65, 51] := by
  rw [rotation_normal_form]
  decide +kernel

theorem rotationRow_65 : neighbors rotation 65 = [64, 19, 52] := by
  rw [rotation_normal_form]
  decide +kernel

theorem rotationRow_66 : neighbors rotation 66 = [20, 67, 56] := by
  rw [rotation_normal_form]
  decide +kernel

theorem rotationRow_67 : neighbors rotation 67 = [66, 21, 57] := by
  rw [rotation_normal_form]
  decide +kernel

theorem rotationRow_68 : neighbors rotation 68 = [14, 58, 72] := by
  rw [rotation_normal_form]
  decide +kernel

theorem rotationRow_69 : neighbors rotation 69 = [58, 15, 73] := by
  rw [rotation_normal_form]
  decide +kernel

theorem rotationRow_70 : neighbors rotation 70 = [78, 53, 80] := by
  rw [rotation_normal_form]
  decide +kernel

theorem rotationRow_71 : neighbors rotation 71 = [53, 79, 81] := by
  rw [rotation_normal_form]
  decide +kernel

theorem rotationRow_72 : neighbors rotation 72 = [73, 14, 68] := by
  rw [rotation_normal_form]
  decide +kernel

theorem rotationRow_73 : neighbors rotation 73 = [15, 72, 69] := by
  rw [rotation_normal_form]
  decide +kernel

theorem rotationRow_74 : neighbors rotation 74 = [54, 16, 76] := by
  rw [rotation_normal_form]
  decide +kernel

theorem rotationRow_75 : neighbors rotation 75 = [17, 54, 77] := by
  rw [rotation_normal_form]
  decide +kernel

theorem rotationRow_76 : neighbors rotation 76 = [16, 77, 74] := by
  rw [rotation_normal_form]
  decide +kernel

theorem rotationRow_77 : neighbors rotation 77 = [76, 17, 75] := by
  rw [rotation_normal_form]
  decide +kernel

theorem rotationRow_78 : neighbors rotation 78 = [59, 70, 80] := by
  rw [rotation_normal_form]
  decide +kernel

theorem rotationRow_79 : neighbors rotation 79 = [71, 59, 81] := by
  rw [rotation_normal_form]
  decide +kernel

theorem rotationRow_80 : neighbors rotation 80 = [81, 78, 70] := by
  rw [rotation_normal_form]
  decide +kernel

theorem rotationRow_81 : neighbors rotation 81 = [79, 80, 71] := by
  rw [rotation_normal_form]
  decide +kernel

theorem hard_dart_step : DartStep (80, 81) (81, 71) := by
  apply dartCheck_sound
  change (((81, next (neighbors rotation 81) 80) == (81, 71)) &&
    (decide (80 < 82) && (neighbors rotation 80).contains 81)) = true
  rw [rotationRow_81, rotationRow_80]
  decide +kernel

theorem dartStep_0 : DartStep (0, 1) (1, 6) := by
  apply dartCheck_sound
  change (((1, next (neighbors rotation 1) 0) == (1, 6)) &&
    (decide (0 < 82) && (neighbors rotation 0).contains 1)) = true
  rw [rotationRow_1, rotationRow_0]
  decide +kernel

theorem dartStep_1 : DartStep (1, 6) (6, 0) := by
  apply dartCheck_sound
  change (((6, next (neighbors rotation 6) 1) == (6, 0)) &&
    (decide (1 < 82) && (neighbors rotation 1).contains 6)) = true
  rw [rotationRow_6, rotationRow_1]
  decide +kernel

theorem dartStep_2 : DartStep (6, 0) (0, 1) := by
  apply dartCheck_sound
  change (((0, next (neighbors rotation 0) 6) == (0, 1)) &&
    (decide (6 < 82) && (neighbors rotation 6).contains 0)) = true
  rw [rotationRow_0, rotationRow_6]
  decide +kernel

theorem dartStep_3 : DartStep (0, 3) (3, 24) := by
  apply dartCheck_sound
  change (((3, next (neighbors rotation 3) 0) == (3, 24)) &&
    (decide (0 < 82) && (neighbors rotation 0).contains 3)) = true
  rw [rotationRow_3, rotationRow_0]
  decide +kernel

theorem dartStep_4 : DartStep (3, 24) (24, 22) := by
  apply dartCheck_sound
  change (((24, next (neighbors rotation 24) 3) == (24, 22)) &&
    (decide (3 < 82) && (neighbors rotation 3).contains 24)) = true
  rw [rotationRow_24, rotationRow_3]
  decide +kernel

theorem dartStep_5 : DartStep (24, 22) (22, 26) := by
  apply dartCheck_sound
  change (((22, next (neighbors rotation 22) 24) == (22, 26)) &&
    (decide (24 < 82) && (neighbors rotation 24).contains 22)) = true
  rw [rotationRow_22, rotationRow_24]
  decide +kernel

theorem dartStep_6 : DartStep (22, 26) (26, 42) := by
  apply dartCheck_sound
  change (((26, next (neighbors rotation 26) 22) == (26, 42)) &&
    (decide (22 < 82) && (neighbors rotation 22).contains 26)) = true
  rw [rotationRow_26, rotationRow_22]
  decide +kernel

theorem dartStep_7 : DartStep (26, 42) (42, 10) := by
  apply dartCheck_sound
  change (((42, next (neighbors rotation 42) 26) == (42, 10)) &&
    (decide (26 < 82) && (neighbors rotation 26).contains 42)) = true
  rw [rotationRow_42, rotationRow_26]
  decide +kernel

theorem dartStep_8 : DartStep (42, 10) (10, 7) := by
  apply dartCheck_sound
  change (((10, next (neighbors rotation 10) 42) == (10, 7)) &&
    (decide (42 < 82) && (neighbors rotation 42).contains 10)) = true
  rw [rotationRow_10, rotationRow_42]
  decide +kernel

theorem dartStep_9 : DartStep (10, 7) (7, 14) := by
  apply dartCheck_sound
  change (((7, next (neighbors rotation 7) 10) == (7, 14)) &&
    (decide (10 < 82) && (neighbors rotation 10).contains 7)) = true
  rw [rotationRow_7, rotationRow_10]
  decide +kernel

theorem dartStep_10 : DartStep (7, 14) (14, 68) := by
  apply dartCheck_sound
  change (((14, next (neighbors rotation 14) 7) == (14, 68)) &&
    (decide (7 < 82) && (neighbors rotation 7).contains 14)) = true
  rw [rotationRow_14, rotationRow_7]
  decide +kernel

theorem dartStep_11 : DartStep (14, 68) (68, 58) := by
  apply dartCheck_sound
  change (((68, next (neighbors rotation 68) 14) == (68, 58)) &&
    (decide (14 < 82) && (neighbors rotation 14).contains 68)) = true
  rw [rotationRow_68, rotationRow_14]
  decide +kernel

theorem dartStep_12 : DartStep (68, 58) (58, 55) := by
  apply dartCheck_sound
  change (((58, next (neighbors rotation 58) 68) == (58, 55)) &&
    (decide (68 < 82) && (neighbors rotation 68).contains 58)) = true
  rw [rotationRow_58, rotationRow_68]
  decide +kernel

theorem dartStep_13 : DartStep (58, 55) (55, 56) := by
  apply dartCheck_sound
  change (((55, next (neighbors rotation 55) 58) == (55, 56)) &&
    (decide (58 < 82) && (neighbors rotation 58).contains 55)) = true
  rw [rotationRow_55, rotationRow_58]
  decide +kernel

theorem dartStep_14 : DartStep (55, 56) (56, 20) := by
  apply dartCheck_sound
  change (((56, next (neighbors rotation 56) 55) == (56, 20)) &&
    (decide (55 < 82) && (neighbors rotation 55).contains 56)) = true
  rw [rotationRow_56, rotationRow_55]
  decide +kernel

theorem dartStep_15 : DartStep (56, 20) (20, 1) := by
  apply dartCheck_sound
  change (((20, next (neighbors rotation 20) 56) == (20, 1)) &&
    (decide (56 < 82) && (neighbors rotation 56).contains 20)) = true
  rw [rotationRow_20, rotationRow_56]
  decide +kernel

theorem dartStep_16 : DartStep (20, 1) (1, 0) := by
  apply dartCheck_sound
  change (((1, next (neighbors rotation 1) 20) == (1, 0)) &&
    (decide (20 < 82) && (neighbors rotation 20).contains 1)) = true
  rw [rotationRow_1, rotationRow_20]
  decide +kernel

theorem dartStep_17 : DartStep (1, 0) (0, 3) := by
  apply dartCheck_sound
  change (((0, next (neighbors rotation 0) 1) == (0, 3)) &&
    (decide (1 < 82) && (neighbors rotation 1).contains 0)) = true
  rw [rotationRow_0, rotationRow_1]
  decide +kernel

theorem dartStep_18 : DartStep (0, 2) (2, 32) := by
  apply dartCheck_sound
  change (((2, next (neighbors rotation 2) 0) == (2, 32)) &&
    (decide (0 < 82) && (neighbors rotation 0).contains 2)) = true
  rw [rotationRow_2, rotationRow_0]
  decide +kernel

theorem dartStep_19 : DartStep (2, 32) (32, 33) := by
  apply dartCheck_sound
  change (((32, next (neighbors rotation 32) 2) == (32, 33)) &&
    (decide (2 < 82) && (neighbors rotation 2).contains 32)) = true
  rw [rotationRow_32, rotationRow_2]
  decide +kernel

theorem dartStep_20 : DartStep (32, 33) (33, 3) := by
  apply dartCheck_sound
  change (((33, next (neighbors rotation 33) 32) == (33, 3)) &&
    (decide (32 < 82) && (neighbors rotation 32).contains 33)) = true
  rw [rotationRow_33, rotationRow_32]
  decide +kernel

theorem dartStep_21 : DartStep (33, 3) (3, 0) := by
  apply dartCheck_sound
  change (((3, next (neighbors rotation 3) 33) == (3, 0)) &&
    (decide (33 < 82) && (neighbors rotation 33).contains 3)) = true
  rw [rotationRow_3, rotationRow_33]
  decide +kernel

theorem dartStep_22 : DartStep (3, 0) (0, 2) := by
  apply dartCheck_sound
  change (((0, next (neighbors rotation 0) 3) == (0, 2)) &&
    (decide (3 < 82) && (neighbors rotation 3).contains 0)) = true
  rw [rotationRow_0, rotationRow_3]
  decide +kernel

theorem dartStep_23 : DartStep (0, 5) (5, 29) := by
  apply dartCheck_sound
  change (((5, next (neighbors rotation 5) 0) == (5, 29)) &&
    (decide (0 < 82) && (neighbors rotation 0).contains 5)) = true
  rw [rotationRow_5, rotationRow_0]
  decide +kernel

theorem dartStep_24 : DartStep (5, 29) (29, 27) := by
  apply dartCheck_sound
  change (((29, next (neighbors rotation 29) 5) == (29, 27)) &&
    (decide (5 < 82) && (neighbors rotation 5).contains 29)) = true
  rw [rotationRow_29, rotationRow_5]
  decide +kernel

theorem dartStep_25 : DartStep (29, 27) (27, 31) := by
  apply dartCheck_sound
  change (((27, next (neighbors rotation 27) 29) == (27, 31)) &&
    (decide (29 < 82) && (neighbors rotation 29).contains 27)) = true
  rw [rotationRow_27, rotationRow_29]
  decide +kernel

theorem dartStep_26 : DartStep (27, 31) (31, 46) := by
  apply dartCheck_sound
  change (((31, next (neighbors rotation 31) 27) == (31, 46)) &&
    (decide (27 < 82) && (neighbors rotation 27).contains 31)) = true
  rw [rotationRow_31, rotationRow_27]
  decide +kernel

theorem dartStep_27 : DartStep (31, 46) (46, 38) := by
  apply dartCheck_sound
  change (((46, next (neighbors rotation 46) 31) == (46, 38)) &&
    (decide (31 < 82) && (neighbors rotation 31).contains 46)) = true
  rw [rotationRow_46, rotationRow_31]
  decide +kernel

theorem dartStep_28 : DartStep (46, 38) (38, 25) := by
  apply dartCheck_sound
  change (((38, next (neighbors rotation 38) 46) == (38, 25)) &&
    (decide (46 < 82) && (neighbors rotation 46).contains 38)) = true
  rw [rotationRow_38, rotationRow_46]
  decide +kernel

theorem dartStep_29 : DartStep (38, 25) (25, 22) := by
  apply dartCheck_sound
  change (((25, next (neighbors rotation 25) 38) == (25, 22)) &&
    (decide (38 < 82) && (neighbors rotation 38).contains 25)) = true
  rw [rotationRow_25, rotationRow_38]
  decide +kernel

theorem dartStep_30 : DartStep (25, 22) (22, 23) := by
  apply dartCheck_sound
  change (((22, next (neighbors rotation 22) 25) == (22, 23)) &&
    (decide (25 < 82) && (neighbors rotation 25).contains 22)) = true
  rw [rotationRow_22, rotationRow_25]
  decide +kernel

theorem dartStep_31 : DartStep (22, 23) (23, 2) := by
  apply dartCheck_sound
  change (((23, next (neighbors rotation 23) 22) == (23, 2)) &&
    (decide (22 < 82) && (neighbors rotation 22).contains 23)) = true
  rw [rotationRow_23, rotationRow_22]
  decide +kernel

theorem dartStep_32 : DartStep (23, 2) (2, 0) := by
  apply dartCheck_sound
  change (((2, next (neighbors rotation 2) 23) == (2, 0)) &&
    (decide (23 < 82) && (neighbors rotation 23).contains 2)) = true
  rw [rotationRow_2, rotationRow_23]
  decide +kernel

theorem dartStep_33 : DartStep (2, 0) (0, 5) := by
  apply dartCheck_sound
  change (((0, next (neighbors rotation 0) 2) == (0, 5)) &&
    (decide (2 < 82) && (neighbors rotation 2).contains 0)) = true
  rw [rotationRow_0, rotationRow_2]
  decide +kernel

theorem dartStep_34 : DartStep (0, 4) (4, 34) := by
  apply dartCheck_sound
  change (((4, next (neighbors rotation 4) 0) == (4, 34)) &&
    (decide (0 < 82) && (neighbors rotation 0).contains 4)) = true
  rw [rotationRow_4, rotationRow_0]
  decide +kernel

theorem dartStep_35 : DartStep (4, 34) (34, 35) := by
  apply dartCheck_sound
  change (((34, next (neighbors rotation 34) 4) == (34, 35)) &&
    (decide (4 < 82) && (neighbors rotation 4).contains 34)) = true
  rw [rotationRow_34, rotationRow_4]
  decide +kernel

theorem dartStep_36 : DartStep (34, 35) (35, 5) := by
  apply dartCheck_sound
  change (((35, next (neighbors rotation 35) 34) == (35, 5)) &&
    (decide (34 < 82) && (neighbors rotation 34).contains 35)) = true
  rw [rotationRow_35, rotationRow_34]
  decide +kernel

theorem dartStep_37 : DartStep (35, 5) (5, 0) := by
  apply dartCheck_sound
  change (((5, next (neighbors rotation 5) 35) == (5, 0)) &&
    (decide (35 < 82) && (neighbors rotation 35).contains 5)) = true
  rw [rotationRow_5, rotationRow_35]
  decide +kernel

theorem dartStep_38 : DartStep (5, 0) (0, 4) := by
  apply dartCheck_sound
  change (((0, next (neighbors rotation 0) 5) == (0, 4)) &&
    (decide (5 < 82) && (neighbors rotation 5).contains 0)) = true
  rw [rotationRow_0, rotationRow_5]
  decide +kernel

theorem dartStep_39 : DartStep (0, 6) (6, 60) := by
  apply dartCheck_sound
  change (((6, next (neighbors rotation 6) 0) == (6, 60)) &&
    (decide (0 < 82) && (neighbors rotation 0).contains 6)) = true
  rw [rotationRow_6, rotationRow_0]
  decide +kernel

theorem dartStep_40 : DartStep (6, 60) (60, 12) := by
  apply dartCheck_sound
  change (((60, next (neighbors rotation 60) 6) == (60, 12)) &&
    (decide (6 < 82) && (neighbors rotation 6).contains 60)) = true
  rw [rotationRow_60, rotationRow_6]
  decide +kernel

theorem dartStep_41 : DartStep (60, 12) (12, 7) := by
  apply dartCheck_sound
  change (((12, next (neighbors rotation 12) 60) == (12, 7)) &&
    (decide (60 < 82) && (neighbors rotation 60).contains 12)) = true
  rw [rotationRow_12, rotationRow_60]
  decide +kernel

theorem dartStep_42 : DartStep (12, 7) (7, 8) := by
  apply dartCheck_sound
  change (((7, next (neighbors rotation 7) 12) == (7, 8)) &&
    (decide (12 < 82) && (neighbors rotation 12).contains 7)) = true
  rw [rotationRow_7, rotationRow_12]
  decide +kernel

theorem dartStep_43 : DartStep (7, 8) (8, 36) := by
  apply dartCheck_sound
  change (((8, next (neighbors rotation 8) 7) == (8, 36)) &&
    (decide (7 < 82) && (neighbors rotation 7).contains 8)) = true
  rw [rotationRow_8, rotationRow_7]
  decide +kernel

theorem dartStep_44 : DartStep (8, 36) (36, 30) := by
  apply dartCheck_sound
  change (((36, next (neighbors rotation 36) 8) == (36, 30)) &&
    (decide (8 < 82) && (neighbors rotation 8).contains 36)) = true
  rw [rotationRow_36, rotationRow_8]
  decide +kernel

theorem dartStep_45 : DartStep (36, 30) (30, 27) := by
  apply dartCheck_sound
  change (((30, next (neighbors rotation 30) 36) == (30, 27)) &&
    (decide (36 < 82) && (neighbors rotation 36).contains 30)) = true
  rw [rotationRow_30, rotationRow_36]
  decide +kernel

theorem dartStep_46 : DartStep (30, 27) (27, 28) := by
  apply dartCheck_sound
  change (((27, next (neighbors rotation 27) 30) == (27, 28)) &&
    (decide (30 < 82) && (neighbors rotation 30).contains 27)) = true
  rw [rotationRow_27, rotationRow_30]
  decide +kernel

theorem dartStep_47 : DartStep (27, 28) (28, 4) := by
  apply dartCheck_sound
  change (((28, next (neighbors rotation 28) 27) == (28, 4)) &&
    (decide (27 < 82) && (neighbors rotation 27).contains 28)) = true
  rw [rotationRow_28, rotationRow_27]
  decide +kernel

theorem dartStep_48 : DartStep (28, 4) (4, 0) := by
  apply dartCheck_sound
  change (((4, next (neighbors rotation 4) 28) == (4, 0)) &&
    (decide (28 < 82) && (neighbors rotation 28).contains 4)) = true
  rw [rotationRow_4, rotationRow_28]
  decide +kernel

theorem dartStep_49 : DartStep (4, 0) (0, 6) := by
  apply dartCheck_sound
  change (((0, next (neighbors rotation 0) 4) == (0, 6)) &&
    (decide (4 < 82) && (neighbors rotation 4).contains 0)) = true
  rw [rotationRow_0, rotationRow_4]
  decide +kernel

theorem dartStep_50 : DartStep (1, 19) (19, 52) := by
  apply dartCheck_sound
  change (((19, next (neighbors rotation 19) 1) == (19, 52)) &&
    (decide (1 < 82) && (neighbors rotation 1).contains 19)) = true
  rw [rotationRow_19, rotationRow_1]
  decide +kernel

theorem dartStep_51 : DartStep (19, 52) (52, 50) := by
  apply dartCheck_sound
  change (((52, next (neighbors rotation 52) 19) == (52, 50)) &&
    (decide (19 < 82) && (neighbors rotation 19).contains 52)) = true
  rw [rotationRow_52, rotationRow_19]
  decide +kernel

theorem dartStep_52 : DartStep (52, 50) (50, 54) := by
  apply dartCheck_sound
  change (((50, next (neighbors rotation 50) 52) == (50, 54)) &&
    (decide (52 < 82) && (neighbors rotation 52).contains 50)) = true
  rw [rotationRow_50, rotationRow_52]
  decide +kernel

theorem dartStep_53 : DartStep (50, 54) (54, 74) := by
  apply dartCheck_sound
  change (((54, next (neighbors rotation 54) 50) == (54, 74)) &&
    (decide (50 < 82) && (neighbors rotation 50).contains 54)) = true
  rw [rotationRow_54, rotationRow_50]
  decide +kernel

theorem dartStep_54 : DartStep (54, 74) (74, 16) := by
  apply dartCheck_sound
  change (((74, next (neighbors rotation 74) 54) == (74, 16)) &&
    (decide (54 < 82) && (neighbors rotation 54).contains 74)) = true
  rw [rotationRow_74, rotationRow_54]
  decide +kernel

theorem dartStep_55 : DartStep (74, 16) (16, 7) := by
  apply dartCheck_sound
  change (((16, next (neighbors rotation 16) 74) == (16, 7)) &&
    (decide (74 < 82) && (neighbors rotation 74).contains 16)) = true
  rw [rotationRow_16, rotationRow_74]
  decide +kernel

theorem dartStep_56 : DartStep (16, 7) (7, 13) := by
  apply dartCheck_sound
  change (((7, next (neighbors rotation 7) 16) == (7, 13)) &&
    (decide (16 < 82) && (neighbors rotation 16).contains 7)) = true
  rw [rotationRow_7, rotationRow_16]
  decide +kernel

theorem dartStep_57 : DartStep (7, 13) (13, 61) := by
  apply dartCheck_sound
  change (((13, next (neighbors rotation 13) 7) == (13, 61)) &&
    (decide (7 < 82) && (neighbors rotation 7).contains 13)) = true
  rw [rotationRow_13, rotationRow_7]
  decide +kernel

theorem dartStep_58 : DartStep (13, 61) (61, 6) := by
  apply dartCheck_sound
  change (((61, next (neighbors rotation 61) 13) == (61, 6)) &&
    (decide (13 < 82) && (neighbors rotation 13).contains 61)) = true
  rw [rotationRow_61, rotationRow_13]
  decide +kernel

theorem dartStep_59 : DartStep (61, 6) (6, 1) := by
  apply dartCheck_sound
  change (((6, next (neighbors rotation 6) 61) == (6, 1)) &&
    (decide (61 < 82) && (neighbors rotation 61).contains 6)) = true
  rw [rotationRow_6, rotationRow_61]
  decide +kernel

theorem dartStep_60 : DartStep (6, 1) (1, 19) := by
  apply dartCheck_sound
  change (((1, next (neighbors rotation 1) 6) == (1, 19)) &&
    (decide (6 < 82) && (neighbors rotation 6).contains 1)) = true
  rw [rotationRow_1, rotationRow_6]
  decide +kernel

theorem dartStep_61 : DartStep (1, 18) (18, 64) := by
  apply dartCheck_sound
  change (((18, next (neighbors rotation 18) 1) == (18, 64)) &&
    (decide (1 < 82) && (neighbors rotation 1).contains 18)) = true
  rw [rotationRow_18, rotationRow_1]
  decide +kernel

theorem dartStep_62 : DartStep (18, 64) (64, 65) := by
  apply dartCheck_sound
  change (((64, next (neighbors rotation 64) 18) == (64, 65)) &&
    (decide (18 < 82) && (neighbors rotation 18).contains 64)) = true
  rw [rotationRow_64, rotationRow_18]
  decide +kernel

theorem dartStep_63 : DartStep (64, 65) (65, 19) := by
  apply dartCheck_sound
  change (((65, next (neighbors rotation 65) 64) == (65, 19)) &&
    (decide (64 < 82) && (neighbors rotation 64).contains 65)) = true
  rw [rotationRow_65, rotationRow_64]
  decide +kernel

theorem dartStep_64 : DartStep (65, 19) (19, 1) := by
  apply dartCheck_sound
  change (((19, next (neighbors rotation 19) 65) == (19, 1)) &&
    (decide (65 < 82) && (neighbors rotation 65).contains 19)) = true
  rw [rotationRow_19, rotationRow_65]
  decide +kernel

theorem dartStep_65 : DartStep (19, 1) (1, 18) := by
  apply dartCheck_sound
  change (((1, next (neighbors rotation 1) 19) == (1, 18)) &&
    (decide (19 < 82) && (neighbors rotation 19).contains 1)) = true
  rw [rotationRow_1, rotationRow_19]
  decide +kernel

theorem dartStep_66 : DartStep (1, 21) (21, 57) := by
  apply dartCheck_sound
  change (((21, next (neighbors rotation 21) 1) == (21, 57)) &&
    (decide (1 < 82) && (neighbors rotation 1).contains 21)) = true
  rw [rotationRow_21, rotationRow_1]
  decide +kernel

theorem dartStep_67 : DartStep (21, 57) (57, 55) := by
  apply dartCheck_sound
  change (((57, next (neighbors rotation 57) 21) == (57, 55)) &&
    (decide (21 < 82) && (neighbors rotation 21).contains 57)) = true
  rw [rotationRow_57, rotationRow_21]
  decide +kernel

theorem dartStep_68 : DartStep (57, 55) (55, 59) := by
  apply dartCheck_sound
  change (((55, next (neighbors rotation 55) 57) == (55, 59)) &&
    (decide (57 < 82) && (neighbors rotation 57).contains 55)) = true
  rw [rotationRow_55, rotationRow_57]
  decide +kernel

theorem dartStep_69 : DartStep (55, 59) (59, 78) := by
  apply dartCheck_sound
  change (((59, next (neighbors rotation 59) 55) == (59, 78)) &&
    (decide (55 < 82) && (neighbors rotation 55).contains 59)) = true
  rw [rotationRow_59, rotationRow_55]
  decide +kernel

theorem dartStep_70 : DartStep (59, 78) (78, 70) := by
  apply dartCheck_sound
  change (((78, next (neighbors rotation 78) 59) == (78, 70)) &&
    (decide (59 < 82) && (neighbors rotation 59).contains 78)) = true
  rw [rotationRow_78, rotationRow_59]
  decide +kernel

theorem dartStep_71 : DartStep (78, 70) (70, 53) := by
  apply dartCheck_sound
  change (((70, next (neighbors rotation 70) 78) == (70, 53)) &&
    (decide (78 < 82) && (neighbors rotation 78).contains 70)) = true
  rw [rotationRow_70, rotationRow_78]
  decide +kernel

theorem dartStep_72 : DartStep (70, 53) (53, 50) := by
  apply dartCheck_sound
  change (((53, next (neighbors rotation 53) 70) == (53, 50)) &&
    (decide (70 < 82) && (neighbors rotation 70).contains 53)) = true
  rw [rotationRow_53, rotationRow_70]
  decide +kernel

theorem dartStep_73 : DartStep (53, 50) (50, 51) := by
  apply dartCheck_sound
  change (((50, next (neighbors rotation 50) 53) == (50, 51)) &&
    (decide (53 < 82) && (neighbors rotation 53).contains 50)) = true
  rw [rotationRow_50, rotationRow_53]
  decide +kernel

theorem dartStep_74 : DartStep (50, 51) (51, 18) := by
  apply dartCheck_sound
  change (((51, next (neighbors rotation 51) 50) == (51, 18)) &&
    (decide (50 < 82) && (neighbors rotation 50).contains 51)) = true
  rw [rotationRow_51, rotationRow_50]
  decide +kernel

theorem dartStep_75 : DartStep (51, 18) (18, 1) := by
  apply dartCheck_sound
  change (((18, next (neighbors rotation 18) 51) == (18, 1)) &&
    (decide (51 < 82) && (neighbors rotation 51).contains 18)) = true
  rw [rotationRow_18, rotationRow_51]
  decide +kernel

theorem dartStep_76 : DartStep (18, 1) (1, 21) := by
  apply dartCheck_sound
  change (((1, next (neighbors rotation 1) 18) == (1, 21)) &&
    (decide (18 < 82) && (neighbors rotation 18).contains 1)) = true
  rw [rotationRow_1, rotationRow_18]
  decide +kernel

theorem dartStep_77 : DartStep (1, 20) (20, 66) := by
  apply dartCheck_sound
  change (((20, next (neighbors rotation 20) 1) == (20, 66)) &&
    (decide (1 < 82) && (neighbors rotation 1).contains 20)) = true
  rw [rotationRow_20, rotationRow_1]
  decide +kernel

theorem dartStep_78 : DartStep (20, 66) (66, 67) := by
  apply dartCheck_sound
  change (((66, next (neighbors rotation 66) 20) == (66, 67)) &&
    (decide (20 < 82) && (neighbors rotation 20).contains 66)) = true
  rw [rotationRow_66, rotationRow_20]
  decide +kernel

theorem dartStep_79 : DartStep (66, 67) (67, 21) := by
  apply dartCheck_sound
  change (((67, next (neighbors rotation 67) 66) == (67, 21)) &&
    (decide (66 < 82) && (neighbors rotation 66).contains 67)) = true
  rw [rotationRow_67, rotationRow_66]
  decide +kernel

theorem dartStep_80 : DartStep (67, 21) (21, 1) := by
  apply dartCheck_sound
  change (((21, next (neighbors rotation 21) 67) == (21, 1)) &&
    (decide (67 < 82) && (neighbors rotation 67).contains 21)) = true
  rw [rotationRow_21, rotationRow_67]
  decide +kernel

theorem dartStep_81 : DartStep (21, 1) (1, 20) := by
  apply dartCheck_sound
  change (((1, next (neighbors rotation 1) 21) == (1, 20)) &&
    (decide (21 < 82) && (neighbors rotation 21).contains 1)) = true
  rw [rotationRow_1, rotationRow_21]
  decide +kernel

theorem dartStep_82 : DartStep (2, 23) (23, 32) := by
  apply dartCheck_sound
  change (((23, next (neighbors rotation 23) 2) == (23, 32)) &&
    (decide (2 < 82) && (neighbors rotation 2).contains 23)) = true
  rw [rotationRow_23, rotationRow_2]
  decide +kernel

theorem dartStep_83 : DartStep (23, 32) (32, 2) := by
  apply dartCheck_sound
  change (((32, next (neighbors rotation 32) 23) == (32, 2)) &&
    (decide (23 < 82) && (neighbors rotation 23).contains 32)) = true
  rw [rotationRow_32, rotationRow_23]
  decide +kernel

theorem dartStep_84 : DartStep (32, 2) (2, 23) := by
  apply dartCheck_sound
  change (((2, next (neighbors rotation 2) 32) == (2, 23)) &&
    (decide (32 < 82) && (neighbors rotation 32).contains 2)) = true
  rw [rotationRow_2, rotationRow_32]
  decide +kernel

theorem dartStep_85 : DartStep (3, 33) (33, 24) := by
  apply dartCheck_sound
  change (((33, next (neighbors rotation 33) 3) == (33, 24)) &&
    (decide (3 < 82) && (neighbors rotation 3).contains 33)) = true
  rw [rotationRow_33, rotationRow_3]
  decide +kernel

theorem dartStep_86 : DartStep (33, 24) (24, 3) := by
  apply dartCheck_sound
  change (((24, next (neighbors rotation 24) 33) == (24, 3)) &&
    (decide (33 < 82) && (neighbors rotation 33).contains 24)) = true
  rw [rotationRow_24, rotationRow_33]
  decide +kernel

theorem dartStep_87 : DartStep (24, 3) (3, 33) := by
  apply dartCheck_sound
  change (((3, next (neighbors rotation 3) 24) == (3, 33)) &&
    (decide (24 < 82) && (neighbors rotation 24).contains 3)) = true
  rw [rotationRow_3, rotationRow_24]
  decide +kernel

theorem dartStep_88 : DartStep (4, 28) (28, 34) := by
  apply dartCheck_sound
  change (((28, next (neighbors rotation 28) 4) == (28, 34)) &&
    (decide (4 < 82) && (neighbors rotation 4).contains 28)) = true
  rw [rotationRow_28, rotationRow_4]
  decide +kernel

theorem dartStep_89 : DartStep (28, 34) (34, 4) := by
  apply dartCheck_sound
  change (((34, next (neighbors rotation 34) 28) == (34, 4)) &&
    (decide (28 < 82) && (neighbors rotation 28).contains 34)) = true
  rw [rotationRow_34, rotationRow_28]
  decide +kernel

theorem dartStep_90 : DartStep (34, 4) (4, 28) := by
  apply dartCheck_sound
  change (((4, next (neighbors rotation 4) 34) == (4, 28)) &&
    (decide (34 < 82) && (neighbors rotation 34).contains 4)) = true
  rw [rotationRow_4, rotationRow_34]
  decide +kernel

theorem dartStep_91 : DartStep (5, 35) (35, 29) := by
  apply dartCheck_sound
  change (((35, next (neighbors rotation 35) 5) == (35, 29)) &&
    (decide (5 < 82) && (neighbors rotation 5).contains 35)) = true
  rw [rotationRow_35, rotationRow_5]
  decide +kernel

theorem dartStep_92 : DartStep (35, 29) (29, 5) := by
  apply dartCheck_sound
  change (((29, next (neighbors rotation 29) 35) == (29, 5)) &&
    (decide (35 < 82) && (neighbors rotation 35).contains 29)) = true
  rw [rotationRow_29, rotationRow_35]
  decide +kernel

theorem dartStep_93 : DartStep (29, 5) (5, 35) := by
  apply dartCheck_sound
  change (((5, next (neighbors rotation 5) 29) == (5, 35)) &&
    (decide (29 < 82) && (neighbors rotation 29).contains 5)) = true
  rw [rotationRow_5, rotationRow_29]
  decide +kernel

theorem dartStep_94 : DartStep (6, 61) (61, 63) := by
  apply dartCheck_sound
  change (((61, next (neighbors rotation 61) 6) == (61, 63)) &&
    (decide (6 < 82) && (neighbors rotation 6).contains 61)) = true
  rw [rotationRow_61, rotationRow_6]
  decide +kernel

theorem dartStep_95 : DartStep (61, 63) (63, 62) := by
  apply dartCheck_sound
  change (((63, next (neighbors rotation 63) 61) == (63, 62)) &&
    (decide (61 < 82) && (neighbors rotation 61).contains 63)) = true
  rw [rotationRow_63, rotationRow_61]
  decide +kernel

theorem dartStep_96 : DartStep (63, 62) (62, 60) := by
  apply dartCheck_sound
  change (((62, next (neighbors rotation 62) 63) == (62, 60)) &&
    (decide (63 < 82) && (neighbors rotation 63).contains 62)) = true
  rw [rotationRow_62, rotationRow_63]
  decide +kernel

theorem dartStep_97 : DartStep (62, 60) (60, 6) := by
  apply dartCheck_sound
  change (((60, next (neighbors rotation 60) 62) == (60, 6)) &&
    (decide (62 < 82) && (neighbors rotation 62).contains 60)) = true
  rw [rotationRow_60, rotationRow_62]
  decide +kernel

theorem dartStep_98 : DartStep (60, 6) (6, 61) := by
  apply dartCheck_sound
  change (((6, next (neighbors rotation 6) 60) == (6, 61)) &&
    (decide (60 < 82) && (neighbors rotation 60).contains 6)) = true
  rw [rotationRow_6, rotationRow_60]
  decide +kernel

theorem dartStep_99 : DartStep (7, 12) (12, 62) := by
  apply dartCheck_sound
  change (((12, next (neighbors rotation 12) 7) == (12, 62)) &&
    (decide (7 < 82) && (neighbors rotation 7).contains 12)) = true
  rw [rotationRow_12, rotationRow_7]
  decide +kernel

theorem dartStep_100 : DartStep (12, 62) (62, 63) := by
  apply dartCheck_sound
  change (((62, next (neighbors rotation 62) 12) == (62, 63)) &&
    (decide (12 < 82) && (neighbors rotation 12).contains 62)) = true
  rw [rotationRow_62, rotationRow_12]
  decide +kernel

theorem dartStep_101 : DartStep (62, 63) (63, 13) := by
  apply dartCheck_sound
  change (((63, next (neighbors rotation 63) 62) == (63, 13)) &&
    (decide (62 < 82) && (neighbors rotation 62).contains 63)) = true
  rw [rotationRow_63, rotationRow_62]
  decide +kernel

theorem dartStep_102 : DartStep (63, 13) (13, 7) := by
  apply dartCheck_sound
  change (((13, next (neighbors rotation 13) 63) == (13, 7)) &&
    (decide (63 < 82) && (neighbors rotation 63).contains 13)) = true
  rw [rotationRow_13, rotationRow_63]
  decide +kernel

theorem dartStep_103 : DartStep (13, 7) (7, 12) := by
  apply dartCheck_sound
  change (((7, next (neighbors rotation 7) 13) == (7, 12)) &&
    (decide (13 < 82) && (neighbors rotation 13).contains 7)) = true
  rw [rotationRow_7, rotationRow_13]
  decide +kernel

theorem dartStep_104 : DartStep (7, 9) (9, 41) := by
  apply dartCheck_sound
  change (((9, next (neighbors rotation 9) 7) == (9, 41)) &&
    (decide (7 < 82) && (neighbors rotation 7).contains 9)) = true
  rw [rotationRow_9, rotationRow_7]
  decide +kernel

theorem dartStep_105 : DartStep (9, 41) (41, 40) := by
  apply dartCheck_sound
  change (((41, next (neighbors rotation 41) 9) == (41, 40)) &&
    (decide (9 < 82) && (neighbors rotation 9).contains 41)) = true
  rw [rotationRow_41, rotationRow_9]
  decide +kernel

theorem dartStep_106 : DartStep (41, 40) (40, 8) := by
  apply dartCheck_sound
  change (((40, next (neighbors rotation 40) 41) == (40, 8)) &&
    (decide (41 < 82) && (neighbors rotation 41).contains 40)) = true
  rw [rotationRow_40, rotationRow_41]
  decide +kernel

theorem dartStep_107 : DartStep (40, 8) (8, 7) := by
  apply dartCheck_sound
  change (((8, next (neighbors rotation 8) 40) == (8, 7)) &&
    (decide (40 < 82) && (neighbors rotation 40).contains 8)) = true
  rw [rotationRow_8, rotationRow_40]
  decide +kernel

theorem dartStep_108 : DartStep (8, 7) (7, 9) := by
  apply dartCheck_sound
  change (((7, next (neighbors rotation 7) 8) == (7, 9)) &&
    (decide (8 < 82) && (neighbors rotation 8).contains 7)) = true
  rw [rotationRow_7, rotationRow_8]
  decide +kernel

theorem dartStep_109 : DartStep (7, 11) (11, 43) := by
  apply dartCheck_sound
  change (((11, next (neighbors rotation 11) 7) == (11, 43)) &&
    (decide (7 < 82) && (neighbors rotation 7).contains 11)) = true
  rw [rotationRow_11, rotationRow_7]
  decide +kernel

theorem dartStep_110 : DartStep (11, 43) (43, 26) := by
  apply dartCheck_sound
  change (((43, next (neighbors rotation 43) 11) == (43, 26)) &&
    (decide (11 < 82) && (neighbors rotation 11).contains 43)) = true
  rw [rotationRow_43, rotationRow_11]
  decide +kernel

theorem dartStep_111 : DartStep (43, 26) (26, 25) := by
  apply dartCheck_sound
  change (((26, next (neighbors rotation 26) 43) == (26, 25)) &&
    (decide (43 < 82) && (neighbors rotation 43).contains 26)) = true
  rw [rotationRow_26, rotationRow_43]
  decide +kernel

theorem dartStep_112 : DartStep (26, 25) (25, 39) := by
  apply dartCheck_sound
  change (((25, next (neighbors rotation 25) 26) == (25, 39)) &&
    (decide (26 < 82) && (neighbors rotation 26).contains 25)) = true
  rw [rotationRow_25, rotationRow_26]
  decide +kernel

theorem dartStep_113 : DartStep (25, 39) (39, 47) := by
  apply dartCheck_sound
  change (((39, next (neighbors rotation 39) 25) == (39, 47)) &&
    (decide (25 < 82) && (neighbors rotation 25).contains 39)) = true
  rw [rotationRow_39, rotationRow_25]
  decide +kernel

theorem dartStep_114 : DartStep (39, 47) (47, 31) := by
  apply dartCheck_sound
  change (((47, next (neighbors rotation 47) 39) == (47, 31)) &&
    (decide (39 < 82) && (neighbors rotation 39).contains 47)) = true
  rw [rotationRow_47, rotationRow_39]
  decide +kernel

theorem dartStep_115 : DartStep (47, 31) (31, 30) := by
  apply dartCheck_sound
  change (((31, next (neighbors rotation 31) 47) == (31, 30)) &&
    (decide (47 < 82) && (neighbors rotation 47).contains 31)) = true
  rw [rotationRow_31, rotationRow_47]
  decide +kernel

theorem dartStep_116 : DartStep (31, 30) (30, 37) := by
  apply dartCheck_sound
  change (((30, next (neighbors rotation 30) 31) == (30, 37)) &&
    (decide (31 < 82) && (neighbors rotation 31).contains 30)) = true
  rw [rotationRow_30, rotationRow_31]
  decide +kernel

theorem dartStep_117 : DartStep (30, 37) (37, 9) := by
  apply dartCheck_sound
  change (((37, next (neighbors rotation 37) 30) == (37, 9)) &&
    (decide (30 < 82) && (neighbors rotation 30).contains 37)) = true
  rw [rotationRow_37, rotationRow_30]
  decide +kernel

theorem dartStep_118 : DartStep (37, 9) (9, 7) := by
  apply dartCheck_sound
  change (((9, next (neighbors rotation 9) 37) == (9, 7)) &&
    (decide (37 < 82) && (neighbors rotation 37).contains 9)) = true
  rw [rotationRow_9, rotationRow_37]
  decide +kernel

theorem dartStep_119 : DartStep (9, 7) (7, 11) := by
  apply dartCheck_sound
  change (((7, next (neighbors rotation 7) 9) == (7, 11)) &&
    (decide (9 < 82) && (neighbors rotation 9).contains 7)) = true
  rw [rotationRow_7, rotationRow_9]
  decide +kernel

theorem dartStep_120 : DartStep (7, 10) (10, 44) := by
  apply dartCheck_sound
  change (((10, next (neighbors rotation 10) 7) == (10, 44)) &&
    (decide (7 < 82) && (neighbors rotation 7).contains 10)) = true
  rw [rotationRow_10, rotationRow_7]
  decide +kernel

theorem dartStep_121 : DartStep (10, 44) (44, 45) := by
  apply dartCheck_sound
  change (((44, next (neighbors rotation 44) 10) == (44, 45)) &&
    (decide (10 < 82) && (neighbors rotation 10).contains 44)) = true
  rw [rotationRow_44, rotationRow_10]
  decide +kernel

theorem dartStep_122 : DartStep (44, 45) (45, 11) := by
  apply dartCheck_sound
  change (((45, next (neighbors rotation 45) 44) == (45, 11)) &&
    (decide (44 < 82) && (neighbors rotation 44).contains 45)) = true
  rw [rotationRow_45, rotationRow_44]
  decide +kernel

theorem dartStep_123 : DartStep (45, 11) (11, 7) := by
  apply dartCheck_sound
  change (((11, next (neighbors rotation 11) 45) == (11, 7)) &&
    (decide (45 < 82) && (neighbors rotation 45).contains 11)) = true
  rw [rotationRow_11, rotationRow_45]
  decide +kernel

theorem dartStep_124 : DartStep (11, 7) (7, 10) := by
  apply dartCheck_sound
  change (((7, next (neighbors rotation 7) 11) == (7, 10)) &&
    (decide (11 < 82) && (neighbors rotation 11).contains 7)) = true
  rw [rotationRow_7, rotationRow_11]
  decide +kernel

theorem dartStep_125 : DartStep (7, 15) (15, 73) := by
  apply dartCheck_sound
  change (((15, next (neighbors rotation 15) 7) == (15, 73)) &&
    (decide (7 < 82) && (neighbors rotation 7).contains 15)) = true
  rw [rotationRow_15, rotationRow_7]
  decide +kernel

theorem dartStep_126 : DartStep (15, 73) (73, 72) := by
  apply dartCheck_sound
  change (((73, next (neighbors rotation 73) 15) == (73, 72)) &&
    (decide (15 < 82) && (neighbors rotation 15).contains 73)) = true
  rw [rotationRow_73, rotationRow_15]
  decide +kernel

theorem dartStep_127 : DartStep (73, 72) (72, 14) := by
  apply dartCheck_sound
  change (((72, next (neighbors rotation 72) 73) == (72, 14)) &&
    (decide (73 < 82) && (neighbors rotation 73).contains 72)) = true
  rw [rotationRow_72, rotationRow_73]
  decide +kernel

theorem dartStep_128 : DartStep (72, 14) (14, 7) := by
  apply dartCheck_sound
  change (((14, next (neighbors rotation 14) 72) == (14, 7)) &&
    (decide (72 < 82) && (neighbors rotation 72).contains 14)) = true
  rw [rotationRow_14, rotationRow_72]
  decide +kernel

theorem dartStep_129 : DartStep (14, 7) (7, 15) := by
  apply dartCheck_sound
  change (((7, next (neighbors rotation 7) 14) == (7, 15)) &&
    (decide (14 < 82) && (neighbors rotation 14).contains 7)) = true
  rw [rotationRow_7, rotationRow_14]
  decide +kernel

theorem dartStep_130 : DartStep (7, 17) (17, 75) := by
  apply dartCheck_sound
  change (((17, next (neighbors rotation 17) 7) == (17, 75)) &&
    (decide (7 < 82) && (neighbors rotation 7).contains 17)) = true
  rw [rotationRow_17, rotationRow_7]
  decide +kernel

theorem dartStep_131 : DartStep (17, 75) (75, 54) := by
  apply dartCheck_sound
  change (((75, next (neighbors rotation 75) 17) == (75, 54)) &&
    (decide (17 < 82) && (neighbors rotation 17).contains 75)) = true
  rw [rotationRow_75, rotationRow_17]
  decide +kernel

theorem dartStep_132 : DartStep (75, 54) (54, 53) := by
  apply dartCheck_sound
  change (((54, next (neighbors rotation 54) 75) == (54, 53)) &&
    (decide (75 < 82) && (neighbors rotation 75).contains 54)) = true
  rw [rotationRow_54, rotationRow_75]
  decide +kernel

theorem dartStep_133 : DartStep (54, 53) (53, 71) := by
  apply dartCheck_sound
  change (((53, next (neighbors rotation 53) 54) == (53, 71)) &&
    (decide (54 < 82) && (neighbors rotation 54).contains 53)) = true
  rw [rotationRow_53, rotationRow_54]
  decide +kernel

theorem dartStep_134 : DartStep (53, 71) (71, 79) := by
  apply dartCheck_sound
  change (((71, next (neighbors rotation 71) 53) == (71, 79)) &&
    (decide (53 < 82) && (neighbors rotation 53).contains 71)) = true
  rw [rotationRow_71, rotationRow_53]
  decide +kernel

theorem dartStep_135 : DartStep (71, 79) (79, 59) := by
  apply dartCheck_sound
  change (((79, next (neighbors rotation 79) 71) == (79, 59)) &&
    (decide (71 < 82) && (neighbors rotation 71).contains 79)) = true
  rw [rotationRow_79, rotationRow_71]
  decide +kernel

theorem dartStep_136 : DartStep (79, 59) (59, 58) := by
  apply dartCheck_sound
  change (((59, next (neighbors rotation 59) 79) == (59, 58)) &&
    (decide (79 < 82) && (neighbors rotation 79).contains 59)) = true
  rw [rotationRow_59, rotationRow_79]
  decide +kernel

theorem dartStep_137 : DartStep (59, 58) (58, 69) := by
  apply dartCheck_sound
  change (((58, next (neighbors rotation 58) 59) == (58, 69)) &&
    (decide (59 < 82) && (neighbors rotation 59).contains 58)) = true
  rw [rotationRow_58, rotationRow_59]
  decide +kernel

theorem dartStep_138 : DartStep (58, 69) (69, 15) := by
  apply dartCheck_sound
  change (((69, next (neighbors rotation 69) 58) == (69, 15)) &&
    (decide (58 < 82) && (neighbors rotation 58).contains 69)) = true
  rw [rotationRow_69, rotationRow_58]
  decide +kernel

theorem dartStep_139 : DartStep (69, 15) (15, 7) := by
  apply dartCheck_sound
  change (((15, next (neighbors rotation 15) 69) == (15, 7)) &&
    (decide (69 < 82) && (neighbors rotation 69).contains 15)) = true
  rw [rotationRow_15, rotationRow_69]
  decide +kernel

theorem dartStep_140 : DartStep (15, 7) (7, 17) := by
  apply dartCheck_sound
  change (((7, next (neighbors rotation 7) 15) == (7, 17)) &&
    (decide (15 < 82) && (neighbors rotation 15).contains 7)) = true
  rw [rotationRow_7, rotationRow_15]
  decide +kernel

theorem dartStep_141 : DartStep (7, 16) (16, 76) := by
  apply dartCheck_sound
  change (((16, next (neighbors rotation 16) 7) == (16, 76)) &&
    (decide (7 < 82) && (neighbors rotation 7).contains 16)) = true
  rw [rotationRow_16, rotationRow_7]
  decide +kernel

theorem dartStep_142 : DartStep (16, 76) (76, 77) := by
  apply dartCheck_sound
  change (((76, next (neighbors rotation 76) 16) == (76, 77)) &&
    (decide (16 < 82) && (neighbors rotation 16).contains 76)) = true
  rw [rotationRow_76, rotationRow_16]
  decide +kernel

theorem dartStep_143 : DartStep (76, 77) (77, 17) := by
  apply dartCheck_sound
  change (((77, next (neighbors rotation 77) 76) == (77, 17)) &&
    (decide (76 < 82) && (neighbors rotation 76).contains 77)) = true
  rw [rotationRow_77, rotationRow_76]
  decide +kernel

theorem dartStep_144 : DartStep (77, 17) (17, 7) := by
  apply dartCheck_sound
  change (((17, next (neighbors rotation 17) 77) == (17, 7)) &&
    (decide (77 < 82) && (neighbors rotation 77).contains 17)) = true
  rw [rotationRow_17, rotationRow_77]
  decide +kernel

theorem dartStep_145 : DartStep (17, 7) (7, 16) := by
  apply dartCheck_sound
  change (((7, next (neighbors rotation 7) 17) == (7, 16)) &&
    (decide (17 < 82) && (neighbors rotation 17).contains 7)) = true
  rw [rotationRow_7, rotationRow_17]
  decide +kernel

theorem dartStep_146 : DartStep (8, 40) (40, 36) := by
  apply dartCheck_sound
  change (((40, next (neighbors rotation 40) 8) == (40, 36)) &&
    (decide (8 < 82) && (neighbors rotation 8).contains 40)) = true
  rw [rotationRow_40, rotationRow_8]
  decide +kernel

theorem dartStep_147 : DartStep (40, 36) (36, 8) := by
  apply dartCheck_sound
  change (((36, next (neighbors rotation 36) 40) == (36, 8)) &&
    (decide (40 < 82) && (neighbors rotation 40).contains 36)) = true
  rw [rotationRow_36, rotationRow_40]
  decide +kernel

theorem dartStep_148 : DartStep (36, 8) (8, 40) := by
  apply dartCheck_sound
  change (((8, next (neighbors rotation 8) 36) == (8, 40)) &&
    (decide (36 < 82) && (neighbors rotation 36).contains 8)) = true
  rw [rotationRow_8, rotationRow_36]
  decide +kernel

theorem dartStep_149 : DartStep (9, 37) (37, 41) := by
  apply dartCheck_sound
  change (((37, next (neighbors rotation 37) 9) == (37, 41)) &&
    (decide (9 < 82) && (neighbors rotation 9).contains 37)) = true
  rw [rotationRow_37, rotationRow_9]
  decide +kernel

theorem dartStep_150 : DartStep (37, 41) (41, 9) := by
  apply dartCheck_sound
  change (((41, next (neighbors rotation 41) 37) == (41, 9)) &&
    (decide (37 < 82) && (neighbors rotation 37).contains 41)) = true
  rw [rotationRow_41, rotationRow_37]
  decide +kernel

theorem dartStep_151 : DartStep (41, 9) (9, 37) := by
  apply dartCheck_sound
  change (((9, next (neighbors rotation 9) 41) == (9, 37)) &&
    (decide (41 < 82) && (neighbors rotation 41).contains 9)) = true
  rw [rotationRow_9, rotationRow_41]
  decide +kernel

theorem dartStep_152 : DartStep (10, 42) (42, 44) := by
  apply dartCheck_sound
  change (((42, next (neighbors rotation 42) 10) == (42, 44)) &&
    (decide (10 < 82) && (neighbors rotation 10).contains 42)) = true
  rw [rotationRow_42, rotationRow_10]
  decide +kernel

theorem dartStep_153 : DartStep (42, 44) (44, 10) := by
  apply dartCheck_sound
  change (((44, next (neighbors rotation 44) 42) == (44, 10)) &&
    (decide (42 < 82) && (neighbors rotation 42).contains 44)) = true
  rw [rotationRow_44, rotationRow_42]
  decide +kernel

theorem dartStep_154 : DartStep (44, 10) (10, 42) := by
  apply dartCheck_sound
  change (((10, next (neighbors rotation 10) 44) == (10, 42)) &&
    (decide (44 < 82) && (neighbors rotation 44).contains 10)) = true
  rw [rotationRow_10, rotationRow_44]
  decide +kernel

theorem dartStep_155 : DartStep (11, 45) (45, 43) := by
  apply dartCheck_sound
  change (((45, next (neighbors rotation 45) 11) == (45, 43)) &&
    (decide (11 < 82) && (neighbors rotation 11).contains 45)) = true
  rw [rotationRow_45, rotationRow_11]
  decide +kernel

theorem dartStep_156 : DartStep (45, 43) (43, 11) := by
  apply dartCheck_sound
  change (((43, next (neighbors rotation 43) 45) == (43, 11)) &&
    (decide (45 < 82) && (neighbors rotation 45).contains 43)) = true
  rw [rotationRow_43, rotationRow_45]
  decide +kernel

theorem dartStep_157 : DartStep (43, 11) (11, 45) := by
  apply dartCheck_sound
  change (((11, next (neighbors rotation 11) 43) == (11, 45)) &&
    (decide (43 < 82) && (neighbors rotation 43).contains 11)) = true
  rw [rotationRow_11, rotationRow_43]
  decide +kernel

theorem dartStep_158 : DartStep (12, 60) (60, 62) := by
  apply dartCheck_sound
  change (((60, next (neighbors rotation 60) 12) == (60, 62)) &&
    (decide (12 < 82) && (neighbors rotation 12).contains 60)) = true
  rw [rotationRow_60, rotationRow_12]
  decide +kernel

theorem dartStep_159 : DartStep (60, 62) (62, 12) := by
  apply dartCheck_sound
  change (((62, next (neighbors rotation 62) 60) == (62, 12)) &&
    (decide (60 < 82) && (neighbors rotation 60).contains 62)) = true
  rw [rotationRow_62, rotationRow_60]
  decide +kernel

theorem dartStep_160 : DartStep (62, 12) (12, 60) := by
  apply dartCheck_sound
  change (((12, next (neighbors rotation 12) 62) == (12, 60)) &&
    (decide (62 < 82) && (neighbors rotation 62).contains 12)) = true
  rw [rotationRow_12, rotationRow_62]
  decide +kernel

theorem dartStep_161 : DartStep (13, 63) (63, 61) := by
  apply dartCheck_sound
  change (((63, next (neighbors rotation 63) 13) == (63, 61)) &&
    (decide (13 < 82) && (neighbors rotation 13).contains 63)) = true
  rw [rotationRow_63, rotationRow_13]
  decide +kernel

theorem dartStep_162 : DartStep (63, 61) (61, 13) := by
  apply dartCheck_sound
  change (((61, next (neighbors rotation 61) 63) == (61, 13)) &&
    (decide (63 < 82) && (neighbors rotation 63).contains 61)) = true
  rw [rotationRow_61, rotationRow_63]
  decide +kernel

theorem dartStep_163 : DartStep (61, 13) (13, 63) := by
  apply dartCheck_sound
  change (((13, next (neighbors rotation 13) 61) == (13, 63)) &&
    (decide (61 < 82) && (neighbors rotation 61).contains 13)) = true
  rw [rotationRow_13, rotationRow_61]
  decide +kernel

theorem dartStep_164 : DartStep (14, 72) (72, 68) := by
  apply dartCheck_sound
  change (((72, next (neighbors rotation 72) 14) == (72, 68)) &&
    (decide (14 < 82) && (neighbors rotation 14).contains 72)) = true
  rw [rotationRow_72, rotationRow_14]
  decide +kernel

theorem dartStep_165 : DartStep (72, 68) (68, 14) := by
  apply dartCheck_sound
  change (((68, next (neighbors rotation 68) 72) == (68, 14)) &&
    (decide (72 < 82) && (neighbors rotation 72).contains 68)) = true
  rw [rotationRow_68, rotationRow_72]
  decide +kernel

theorem dartStep_166 : DartStep (68, 14) (14, 72) := by
  apply dartCheck_sound
  change (((14, next (neighbors rotation 14) 68) == (14, 72)) &&
    (decide (68 < 82) && (neighbors rotation 68).contains 14)) = true
  rw [rotationRow_14, rotationRow_68]
  decide +kernel

theorem dartStep_167 : DartStep (15, 69) (69, 73) := by
  apply dartCheck_sound
  change (((69, next (neighbors rotation 69) 15) == (69, 73)) &&
    (decide (15 < 82) && (neighbors rotation 15).contains 69)) = true
  rw [rotationRow_69, rotationRow_15]
  decide +kernel

theorem dartStep_168 : DartStep (69, 73) (73, 15) := by
  apply dartCheck_sound
  change (((73, next (neighbors rotation 73) 69) == (73, 15)) &&
    (decide (69 < 82) && (neighbors rotation 69).contains 73)) = true
  rw [rotationRow_73, rotationRow_69]
  decide +kernel

theorem dartStep_169 : DartStep (73, 15) (15, 69) := by
  apply dartCheck_sound
  change (((15, next (neighbors rotation 15) 73) == (15, 69)) &&
    (decide (73 < 82) && (neighbors rotation 73).contains 15)) = true
  rw [rotationRow_15, rotationRow_73]
  decide +kernel

theorem dartStep_170 : DartStep (16, 74) (74, 76) := by
  apply dartCheck_sound
  change (((74, next (neighbors rotation 74) 16) == (74, 76)) &&
    (decide (16 < 82) && (neighbors rotation 16).contains 74)) = true
  rw [rotationRow_74, rotationRow_16]
  decide +kernel

theorem dartStep_171 : DartStep (74, 76) (76, 16) := by
  apply dartCheck_sound
  change (((76, next (neighbors rotation 76) 74) == (76, 16)) &&
    (decide (74 < 82) && (neighbors rotation 74).contains 76)) = true
  rw [rotationRow_76, rotationRow_74]
  decide +kernel

theorem dartStep_172 : DartStep (76, 16) (16, 74) := by
  apply dartCheck_sound
  change (((16, next (neighbors rotation 16) 76) == (16, 74)) &&
    (decide (76 < 82) && (neighbors rotation 76).contains 16)) = true
  rw [rotationRow_16, rotationRow_76]
  decide +kernel

theorem dartStep_173 : DartStep (17, 77) (77, 75) := by
  apply dartCheck_sound
  change (((77, next (neighbors rotation 77) 17) == (77, 75)) &&
    (decide (17 < 82) && (neighbors rotation 17).contains 77)) = true
  rw [rotationRow_77, rotationRow_17]
  decide +kernel

theorem dartStep_174 : DartStep (77, 75) (75, 17) := by
  apply dartCheck_sound
  change (((75, next (neighbors rotation 75) 77) == (75, 17)) &&
    (decide (77 < 82) && (neighbors rotation 77).contains 75)) = true
  rw [rotationRow_75, rotationRow_77]
  decide +kernel

theorem dartStep_175 : DartStep (75, 17) (17, 77) := by
  apply dartCheck_sound
  change (((17, next (neighbors rotation 17) 75) == (17, 77)) &&
    (decide (75 < 82) && (neighbors rotation 75).contains 17)) = true
  rw [rotationRow_17, rotationRow_75]
  decide +kernel

theorem dartStep_176 : DartStep (18, 51) (51, 64) := by
  apply dartCheck_sound
  change (((51, next (neighbors rotation 51) 18) == (51, 64)) &&
    (decide (18 < 82) && (neighbors rotation 18).contains 51)) = true
  rw [rotationRow_51, rotationRow_18]
  decide +kernel

theorem dartStep_177 : DartStep (51, 64) (64, 18) := by
  apply dartCheck_sound
  change (((64, next (neighbors rotation 64) 51) == (64, 18)) &&
    (decide (51 < 82) && (neighbors rotation 51).contains 64)) = true
  rw [rotationRow_64, rotationRow_51]
  decide +kernel

theorem dartStep_178 : DartStep (64, 18) (18, 51) := by
  apply dartCheck_sound
  change (((18, next (neighbors rotation 18) 64) == (18, 51)) &&
    (decide (64 < 82) && (neighbors rotation 64).contains 18)) = true
  rw [rotationRow_18, rotationRow_64]
  decide +kernel

theorem dartStep_179 : DartStep (19, 65) (65, 52) := by
  apply dartCheck_sound
  change (((65, next (neighbors rotation 65) 19) == (65, 52)) &&
    (decide (19 < 82) && (neighbors rotation 19).contains 65)) = true
  rw [rotationRow_65, rotationRow_19]
  decide +kernel

theorem dartStep_180 : DartStep (65, 52) (52, 19) := by
  apply dartCheck_sound
  change (((52, next (neighbors rotation 52) 65) == (52, 19)) &&
    (decide (65 < 82) && (neighbors rotation 65).contains 52)) = true
  rw [rotationRow_52, rotationRow_65]
  decide +kernel

theorem dartStep_181 : DartStep (52, 19) (19, 65) := by
  apply dartCheck_sound
  change (((19, next (neighbors rotation 19) 52) == (19, 65)) &&
    (decide (52 < 82) && (neighbors rotation 52).contains 19)) = true
  rw [rotationRow_19, rotationRow_52]
  decide +kernel

theorem dartStep_182 : DartStep (20, 56) (56, 66) := by
  apply dartCheck_sound
  change (((56, next (neighbors rotation 56) 20) == (56, 66)) &&
    (decide (20 < 82) && (neighbors rotation 20).contains 56)) = true
  rw [rotationRow_56, rotationRow_20]
  decide +kernel

theorem dartStep_183 : DartStep (56, 66) (66, 20) := by
  apply dartCheck_sound
  change (((66, next (neighbors rotation 66) 56) == (66, 20)) &&
    (decide (56 < 82) && (neighbors rotation 56).contains 66)) = true
  rw [rotationRow_66, rotationRow_56]
  decide +kernel

theorem dartStep_184 : DartStep (66, 20) (20, 56) := by
  apply dartCheck_sound
  change (((20, next (neighbors rotation 20) 66) == (20, 56)) &&
    (decide (66 < 82) && (neighbors rotation 66).contains 20)) = true
  rw [rotationRow_20, rotationRow_66]
  decide +kernel

theorem dartStep_185 : DartStep (21, 67) (67, 57) := by
  apply dartCheck_sound
  change (((67, next (neighbors rotation 67) 21) == (67, 57)) &&
    (decide (21 < 82) && (neighbors rotation 21).contains 67)) = true
  rw [rotationRow_67, rotationRow_21]
  decide +kernel

theorem dartStep_186 : DartStep (67, 57) (57, 21) := by
  apply dartCheck_sound
  change (((57, next (neighbors rotation 57) 67) == (57, 21)) &&
    (decide (67 < 82) && (neighbors rotation 67).contains 57)) = true
  rw [rotationRow_57, rotationRow_67]
  decide +kernel

theorem dartStep_187 : DartStep (57, 21) (21, 67) := by
  apply dartCheck_sound
  change (((21, next (neighbors rotation 21) 57) == (21, 67)) &&
    (decide (57 < 82) && (neighbors rotation 57).contains 21)) = true
  rw [rotationRow_21, rotationRow_57]
  decide +kernel

theorem dartStep_188 : DartStep (22, 25) (25, 26) := by
  apply dartCheck_sound
  change (((25, next (neighbors rotation 25) 22) == (25, 26)) &&
    (decide (22 < 82) && (neighbors rotation 22).contains 25)) = true
  rw [rotationRow_25, rotationRow_22]
  decide +kernel

theorem dartStep_189 : DartStep (25, 26) (26, 22) := by
  apply dartCheck_sound
  change (((26, next (neighbors rotation 26) 25) == (26, 22)) &&
    (decide (25 < 82) && (neighbors rotation 25).contains 26)) = true
  rw [rotationRow_26, rotationRow_25]
  decide +kernel

theorem dartStep_190 : DartStep (26, 22) (22, 25) := by
  apply dartCheck_sound
  change (((22, next (neighbors rotation 22) 26) == (22, 25)) &&
    (decide (26 < 82) && (neighbors rotation 26).contains 22)) = true
  rw [rotationRow_22, rotationRow_26]
  decide +kernel

theorem dartStep_191 : DartStep (22, 24) (24, 33) := by
  apply dartCheck_sound
  change (((24, next (neighbors rotation 24) 22) == (24, 33)) &&
    (decide (22 < 82) && (neighbors rotation 22).contains 24)) = true
  rw [rotationRow_24, rotationRow_22]
  decide +kernel

theorem dartStep_192 : DartStep (24, 33) (33, 32) := by
  apply dartCheck_sound
  change (((33, next (neighbors rotation 33) 24) == (33, 32)) &&
    (decide (24 < 82) && (neighbors rotation 24).contains 33)) = true
  rw [rotationRow_33, rotationRow_24]
  decide +kernel

theorem dartStep_193 : DartStep (33, 32) (32, 23) := by
  apply dartCheck_sound
  change (((32, next (neighbors rotation 32) 33) == (32, 23)) &&
    (decide (33 < 82) && (neighbors rotation 33).contains 32)) = true
  rw [rotationRow_32, rotationRow_33]
  decide +kernel

theorem dartStep_194 : DartStep (32, 23) (23, 22) := by
  apply dartCheck_sound
  change (((23, next (neighbors rotation 23) 32) == (23, 22)) &&
    (decide (32 < 82) && (neighbors rotation 32).contains 23)) = true
  rw [rotationRow_23, rotationRow_32]
  decide +kernel

theorem dartStep_195 : DartStep (23, 22) (22, 24) := by
  apply dartCheck_sound
  change (((22, next (neighbors rotation 22) 23) == (22, 24)) &&
    (decide (23 < 82) && (neighbors rotation 23).contains 22)) = true
  rw [rotationRow_22, rotationRow_23]
  decide +kernel

theorem dartStep_196 : DartStep (25, 38) (38, 48) := by
  apply dartCheck_sound
  change (((38, next (neighbors rotation 38) 25) == (38, 48)) &&
    (decide (25 < 82) && (neighbors rotation 25).contains 38)) = true
  rw [rotationRow_38, rotationRow_25]
  decide +kernel

theorem dartStep_197 : DartStep (38, 48) (48, 49) := by
  apply dartCheck_sound
  change (((48, next (neighbors rotation 48) 38) == (48, 49)) &&
    (decide (38 < 82) && (neighbors rotation 38).contains 48)) = true
  rw [rotationRow_48, rotationRow_38]
  decide +kernel

theorem dartStep_198 : DartStep (48, 49) (49, 39) := by
  apply dartCheck_sound
  change (((49, next (neighbors rotation 49) 48) == (49, 39)) &&
    (decide (48 < 82) && (neighbors rotation 48).contains 49)) = true
  rw [rotationRow_49, rotationRow_48]
  decide +kernel

theorem dartStep_199 : DartStep (49, 39) (39, 25) := by
  apply dartCheck_sound
  change (((39, next (neighbors rotation 39) 49) == (39, 25)) &&
    (decide (49 < 82) && (neighbors rotation 49).contains 39)) = true
  rw [rotationRow_39, rotationRow_49]
  decide +kernel

theorem dartStep_200 : DartStep (39, 25) (25, 38) := by
  apply dartCheck_sound
  change (((25, next (neighbors rotation 25) 39) == (25, 38)) &&
    (decide (39 < 82) && (neighbors rotation 39).contains 25)) = true
  rw [rotationRow_25, rotationRow_39]
  decide +kernel

theorem dartStep_201 : DartStep (26, 43) (43, 45) := by
  apply dartCheck_sound
  change (((43, next (neighbors rotation 43) 26) == (43, 45)) &&
    (decide (26 < 82) && (neighbors rotation 26).contains 43)) = true
  rw [rotationRow_43, rotationRow_26]
  decide +kernel

theorem dartStep_202 : DartStep (43, 45) (45, 44) := by
  apply dartCheck_sound
  change (((45, next (neighbors rotation 45) 43) == (45, 44)) &&
    (decide (43 < 82) && (neighbors rotation 43).contains 45)) = true
  rw [rotationRow_45, rotationRow_43]
  decide +kernel

theorem dartStep_203 : DartStep (45, 44) (44, 42) := by
  apply dartCheck_sound
  change (((44, next (neighbors rotation 44) 45) == (44, 42)) &&
    (decide (45 < 82) && (neighbors rotation 45).contains 44)) = true
  rw [rotationRow_44, rotationRow_45]
  decide +kernel

theorem dartStep_204 : DartStep (44, 42) (42, 26) := by
  apply dartCheck_sound
  change (((42, next (neighbors rotation 42) 44) == (42, 26)) &&
    (decide (44 < 82) && (neighbors rotation 44).contains 42)) = true
  rw [rotationRow_42, rotationRow_44]
  decide +kernel

theorem dartStep_205 : DartStep (42, 26) (26, 43) := by
  apply dartCheck_sound
  change (((26, next (neighbors rotation 26) 42) == (26, 43)) &&
    (decide (42 < 82) && (neighbors rotation 42).contains 26)) = true
  rw [rotationRow_26, rotationRow_42]
  decide +kernel

theorem dartStep_206 : DartStep (27, 30) (30, 31) := by
  apply dartCheck_sound
  change (((30, next (neighbors rotation 30) 27) == (30, 31)) &&
    (decide (27 < 82) && (neighbors rotation 27).contains 30)) = true
  rw [rotationRow_30, rotationRow_27]
  decide +kernel

theorem dartStep_207 : DartStep (30, 31) (31, 27) := by
  apply dartCheck_sound
  change (((31, next (neighbors rotation 31) 30) == (31, 27)) &&
    (decide (30 < 82) && (neighbors rotation 30).contains 31)) = true
  rw [rotationRow_31, rotationRow_30]
  decide +kernel

theorem dartStep_208 : DartStep (31, 27) (27, 30) := by
  apply dartCheck_sound
  change (((27, next (neighbors rotation 27) 31) == (27, 30)) &&
    (decide (31 < 82) && (neighbors rotation 31).contains 27)) = true
  rw [rotationRow_27, rotationRow_31]
  decide +kernel

theorem dartStep_209 : DartStep (27, 29) (29, 35) := by
  apply dartCheck_sound
  change (((29, next (neighbors rotation 29) 27) == (29, 35)) &&
    (decide (27 < 82) && (neighbors rotation 27).contains 29)) = true
  rw [rotationRow_29, rotationRow_27]
  decide +kernel

theorem dartStep_210 : DartStep (29, 35) (35, 34) := by
  apply dartCheck_sound
  change (((35, next (neighbors rotation 35) 29) == (35, 34)) &&
    (decide (29 < 82) && (neighbors rotation 29).contains 35)) = true
  rw [rotationRow_35, rotationRow_29]
  decide +kernel

theorem dartStep_211 : DartStep (35, 34) (34, 28) := by
  apply dartCheck_sound
  change (((34, next (neighbors rotation 34) 35) == (34, 28)) &&
    (decide (35 < 82) && (neighbors rotation 35).contains 34)) = true
  rw [rotationRow_34, rotationRow_35]
  decide +kernel

theorem dartStep_212 : DartStep (34, 28) (28, 27) := by
  apply dartCheck_sound
  change (((28, next (neighbors rotation 28) 34) == (28, 27)) &&
    (decide (34 < 82) && (neighbors rotation 34).contains 28)) = true
  rw [rotationRow_28, rotationRow_34]
  decide +kernel

theorem dartStep_213 : DartStep (28, 27) (27, 29) := by
  apply dartCheck_sound
  change (((27, next (neighbors rotation 27) 28) == (27, 29)) &&
    (decide (28 < 82) && (neighbors rotation 28).contains 27)) = true
  rw [rotationRow_27, rotationRow_28]
  decide +kernel

theorem dartStep_214 : DartStep (30, 36) (36, 40) := by
  apply dartCheck_sound
  change (((36, next (neighbors rotation 36) 30) == (36, 40)) &&
    (decide (30 < 82) && (neighbors rotation 30).contains 36)) = true
  rw [rotationRow_36, rotationRow_30]
  decide +kernel

theorem dartStep_215 : DartStep (36, 40) (40, 41) := by
  apply dartCheck_sound
  change (((40, next (neighbors rotation 40) 36) == (40, 41)) &&
    (decide (36 < 82) && (neighbors rotation 36).contains 40)) = true
  rw [rotationRow_40, rotationRow_36]
  decide +kernel

theorem dartStep_216 : DartStep (40, 41) (41, 37) := by
  apply dartCheck_sound
  change (((41, next (neighbors rotation 41) 40) == (41, 37)) &&
    (decide (40 < 82) && (neighbors rotation 40).contains 41)) = true
  rw [rotationRow_41, rotationRow_40]
  decide +kernel

theorem dartStep_217 : DartStep (41, 37) (37, 30) := by
  apply dartCheck_sound
  change (((37, next (neighbors rotation 37) 41) == (37, 30)) &&
    (decide (41 < 82) && (neighbors rotation 41).contains 37)) = true
  rw [rotationRow_37, rotationRow_41]
  decide +kernel

theorem dartStep_218 : DartStep (37, 30) (30, 36) := by
  apply dartCheck_sound
  change (((30, next (neighbors rotation 30) 37) == (30, 36)) &&
    (decide (37 < 82) && (neighbors rotation 37).contains 30)) = true
  rw [rotationRow_30, rotationRow_37]
  decide +kernel

theorem dartStep_219 : DartStep (31, 47) (47, 49) := by
  apply dartCheck_sound
  change (((47, next (neighbors rotation 47) 31) == (47, 49)) &&
    (decide (31 < 82) && (neighbors rotation 31).contains 47)) = true
  rw [rotationRow_47, rotationRow_31]
  decide +kernel

theorem dartStep_220 : DartStep (47, 49) (49, 48) := by
  apply dartCheck_sound
  change (((49, next (neighbors rotation 49) 47) == (49, 48)) &&
    (decide (47 < 82) && (neighbors rotation 47).contains 49)) = true
  rw [rotationRow_49, rotationRow_47]
  decide +kernel

theorem dartStep_221 : DartStep (49, 48) (48, 46) := by
  apply dartCheck_sound
  change (((48, next (neighbors rotation 48) 49) == (48, 46)) &&
    (decide (49 < 82) && (neighbors rotation 49).contains 48)) = true
  rw [rotationRow_48, rotationRow_49]
  decide +kernel

theorem dartStep_222 : DartStep (48, 46) (46, 31) := by
  apply dartCheck_sound
  change (((46, next (neighbors rotation 46) 48) == (46, 31)) &&
    (decide (48 < 82) && (neighbors rotation 48).contains 46)) = true
  rw [rotationRow_46, rotationRow_48]
  decide +kernel

theorem dartStep_223 : DartStep (46, 31) (31, 47) := by
  apply dartCheck_sound
  change (((31, next (neighbors rotation 31) 46) == (31, 47)) &&
    (decide (46 < 82) && (neighbors rotation 46).contains 31)) = true
  rw [rotationRow_31, rotationRow_46]
  decide +kernel

theorem dartStep_224 : DartStep (38, 46) (46, 48) := by
  apply dartCheck_sound
  change (((46, next (neighbors rotation 46) 38) == (46, 48)) &&
    (decide (38 < 82) && (neighbors rotation 38).contains 46)) = true
  rw [rotationRow_46, rotationRow_38]
  decide +kernel

theorem dartStep_225 : DartStep (46, 48) (48, 38) := by
  apply dartCheck_sound
  change (((48, next (neighbors rotation 48) 46) == (48, 38)) &&
    (decide (46 < 82) && (neighbors rotation 46).contains 48)) = true
  rw [rotationRow_48, rotationRow_46]
  decide +kernel

theorem dartStep_226 : DartStep (48, 38) (38, 46) := by
  apply dartCheck_sound
  change (((38, next (neighbors rotation 38) 48) == (38, 46)) &&
    (decide (48 < 82) && (neighbors rotation 48).contains 38)) = true
  rw [rotationRow_38, rotationRow_48]
  decide +kernel

theorem dartStep_227 : DartStep (39, 49) (49, 47) := by
  apply dartCheck_sound
  change (((49, next (neighbors rotation 49) 39) == (49, 47)) &&
    (decide (39 < 82) && (neighbors rotation 39).contains 49)) = true
  rw [rotationRow_49, rotationRow_39]
  decide +kernel

theorem dartStep_228 : DartStep (49, 47) (47, 39) := by
  apply dartCheck_sound
  change (((47, next (neighbors rotation 47) 49) == (47, 39)) &&
    (decide (49 < 82) && (neighbors rotation 49).contains 47)) = true
  rw [rotationRow_47, rotationRow_49]
  decide +kernel

theorem dartStep_229 : DartStep (47, 39) (39, 49) := by
  apply dartCheck_sound
  change (((39, next (neighbors rotation 39) 47) == (39, 49)) &&
    (decide (47 < 82) && (neighbors rotation 47).contains 39)) = true
  rw [rotationRow_39, rotationRow_47]
  decide +kernel

theorem dartStep_230 : DartStep (50, 53) (53, 54) := by
  apply dartCheck_sound
  change (((53, next (neighbors rotation 53) 50) == (53, 54)) &&
    (decide (50 < 82) && (neighbors rotation 50).contains 53)) = true
  rw [rotationRow_53, rotationRow_50]
  decide +kernel

theorem dartStep_231 : DartStep (53, 54) (54, 50) := by
  apply dartCheck_sound
  change (((54, next (neighbors rotation 54) 53) == (54, 50)) &&
    (decide (53 < 82) && (neighbors rotation 53).contains 54)) = true
  rw [rotationRow_54, rotationRow_53]
  decide +kernel

theorem dartStep_232 : DartStep (54, 50) (50, 53) := by
  apply dartCheck_sound
  change (((50, next (neighbors rotation 50) 54) == (50, 53)) &&
    (decide (54 < 82) && (neighbors rotation 54).contains 50)) = true
  rw [rotationRow_50, rotationRow_54]
  decide +kernel

theorem dartStep_233 : DartStep (50, 52) (52, 65) := by
  apply dartCheck_sound
  change (((52, next (neighbors rotation 52) 50) == (52, 65)) &&
    (decide (50 < 82) && (neighbors rotation 50).contains 52)) = true
  rw [rotationRow_52, rotationRow_50]
  decide +kernel

theorem dartStep_234 : DartStep (52, 65) (65, 64) := by
  apply dartCheck_sound
  change (((65, next (neighbors rotation 65) 52) == (65, 64)) &&
    (decide (52 < 82) && (neighbors rotation 52).contains 65)) = true
  rw [rotationRow_65, rotationRow_52]
  decide +kernel

theorem dartStep_235 : DartStep (65, 64) (64, 51) := by
  apply dartCheck_sound
  change (((64, next (neighbors rotation 64) 65) == (64, 51)) &&
    (decide (65 < 82) && (neighbors rotation 65).contains 64)) = true
  rw [rotationRow_64, rotationRow_65]
  decide +kernel

theorem dartStep_236 : DartStep (64, 51) (51, 50) := by
  apply dartCheck_sound
  change (((51, next (neighbors rotation 51) 64) == (51, 50)) &&
    (decide (64 < 82) && (neighbors rotation 64).contains 51)) = true
  rw [rotationRow_51, rotationRow_64]
  decide +kernel

theorem dartStep_237 : DartStep (51, 50) (50, 52) := by
  apply dartCheck_sound
  change (((50, next (neighbors rotation 50) 51) == (50, 52)) &&
    (decide (51 < 82) && (neighbors rotation 51).contains 50)) = true
  rw [rotationRow_50, rotationRow_51]
  decide +kernel

theorem dartStep_238 : DartStep (53, 70) (70, 80) := by
  apply dartCheck_sound
  change (((70, next (neighbors rotation 70) 53) == (70, 80)) &&
    (decide (53 < 82) && (neighbors rotation 53).contains 70)) = true
  rw [rotationRow_70, rotationRow_53]
  decide +kernel

theorem dartStep_239 : DartStep (70, 80) (80, 81) := by
  apply dartCheck_sound
  change (((80, next (neighbors rotation 80) 70) == (80, 81)) &&
    (decide (70 < 82) && (neighbors rotation 70).contains 80)) = true
  rw [rotationRow_80, rotationRow_70]
  decide +kernel

theorem dartStep_240 : DartStep (80, 81) (81, 71) := hard_dart_step

theorem dartStep_241 : DartStep (81, 71) (71, 53) := by
  apply dartCheck_sound
  change (((71, next (neighbors rotation 71) 81) == (71, 53)) &&
    (decide (81 < 82) && (neighbors rotation 81).contains 71)) = true
  rw [rotationRow_71, rotationRow_81]
  decide +kernel

theorem dartStep_242 : DartStep (71, 53) (53, 70) := by
  apply dartCheck_sound
  change (((53, next (neighbors rotation 53) 71) == (53, 70)) &&
    (decide (71 < 82) && (neighbors rotation 71).contains 53)) = true
  rw [rotationRow_53, rotationRow_71]
  decide +kernel

theorem dartStep_243 : DartStep (54, 75) (75, 77) := by
  apply dartCheck_sound
  change (((75, next (neighbors rotation 75) 54) == (75, 77)) &&
    (decide (54 < 82) && (neighbors rotation 54).contains 75)) = true
  rw [rotationRow_75, rotationRow_54]
  decide +kernel

theorem dartStep_244 : DartStep (75, 77) (77, 76) := by
  apply dartCheck_sound
  change (((77, next (neighbors rotation 77) 75) == (77, 76)) &&
    (decide (75 < 82) && (neighbors rotation 75).contains 77)) = true
  rw [rotationRow_77, rotationRow_75]
  decide +kernel

theorem dartStep_245 : DartStep (77, 76) (76, 74) := by
  apply dartCheck_sound
  change (((76, next (neighbors rotation 76) 77) == (76, 74)) &&
    (decide (77 < 82) && (neighbors rotation 77).contains 76)) = true
  rw [rotationRow_76, rotationRow_77]
  decide +kernel

theorem dartStep_246 : DartStep (76, 74) (74, 54) := by
  apply dartCheck_sound
  change (((74, next (neighbors rotation 74) 76) == (74, 54)) &&
    (decide (76 < 82) && (neighbors rotation 76).contains 74)) = true
  rw [rotationRow_74, rotationRow_76]
  decide +kernel

theorem dartStep_247 : DartStep (74, 54) (54, 75) := by
  apply dartCheck_sound
  change (((54, next (neighbors rotation 54) 74) == (54, 75)) &&
    (decide (74 < 82) && (neighbors rotation 74).contains 54)) = true
  rw [rotationRow_54, rotationRow_74]
  decide +kernel

theorem dartStep_248 : DartStep (55, 58) (58, 59) := by
  apply dartCheck_sound
  change (((58, next (neighbors rotation 58) 55) == (58, 59)) &&
    (decide (55 < 82) && (neighbors rotation 55).contains 58)) = true
  rw [rotationRow_58, rotationRow_55]
  decide +kernel

theorem dartStep_249 : DartStep (58, 59) (59, 55) := by
  apply dartCheck_sound
  change (((59, next (neighbors rotation 59) 58) == (59, 55)) &&
    (decide (58 < 82) && (neighbors rotation 58).contains 59)) = true
  rw [rotationRow_59, rotationRow_58]
  decide +kernel

theorem dartStep_250 : DartStep (59, 55) (55, 58) := by
  apply dartCheck_sound
  change (((55, next (neighbors rotation 55) 59) == (55, 58)) &&
    (decide (59 < 82) && (neighbors rotation 59).contains 55)) = true
  rw [rotationRow_55, rotationRow_59]
  decide +kernel

theorem dartStep_251 : DartStep (55, 57) (57, 67) := by
  apply dartCheck_sound
  change (((57, next (neighbors rotation 57) 55) == (57, 67)) &&
    (decide (55 < 82) && (neighbors rotation 55).contains 57)) = true
  rw [rotationRow_57, rotationRow_55]
  decide +kernel

theorem dartStep_252 : DartStep (57, 67) (67, 66) := by
  apply dartCheck_sound
  change (((67, next (neighbors rotation 67) 57) == (67, 66)) &&
    (decide (57 < 82) && (neighbors rotation 57).contains 67)) = true
  rw [rotationRow_67, rotationRow_57]
  decide +kernel

theorem dartStep_253 : DartStep (67, 66) (66, 56) := by
  apply dartCheck_sound
  change (((66, next (neighbors rotation 66) 67) == (66, 56)) &&
    (decide (67 < 82) && (neighbors rotation 67).contains 66)) = true
  rw [rotationRow_66, rotationRow_67]
  decide +kernel

theorem dartStep_254 : DartStep (66, 56) (56, 55) := by
  apply dartCheck_sound
  change (((56, next (neighbors rotation 56) 66) == (56, 55)) &&
    (decide (66 < 82) && (neighbors rotation 66).contains 56)) = true
  rw [rotationRow_56, rotationRow_66]
  decide +kernel

theorem dartStep_255 : DartStep (56, 55) (55, 57) := by
  apply dartCheck_sound
  change (((55, next (neighbors rotation 55) 56) == (55, 57)) &&
    (decide (56 < 82) && (neighbors rotation 56).contains 55)) = true
  rw [rotationRow_55, rotationRow_56]
  decide +kernel

theorem dartStep_256 : DartStep (58, 68) (68, 72) := by
  apply dartCheck_sound
  change (((68, next (neighbors rotation 68) 58) == (68, 72)) &&
    (decide (58 < 82) && (neighbors rotation 58).contains 68)) = true
  rw [rotationRow_68, rotationRow_58]
  decide +kernel

theorem dartStep_257 : DartStep (68, 72) (72, 73) := by
  apply dartCheck_sound
  change (((72, next (neighbors rotation 72) 68) == (72, 73)) &&
    (decide (68 < 82) && (neighbors rotation 68).contains 72)) = true
  rw [rotationRow_72, rotationRow_68]
  decide +kernel

theorem dartStep_258 : DartStep (72, 73) (73, 69) := by
  apply dartCheck_sound
  change (((73, next (neighbors rotation 73) 72) == (73, 69)) &&
    (decide (72 < 82) && (neighbors rotation 72).contains 73)) = true
  rw [rotationRow_73, rotationRow_72]
  decide +kernel

theorem dartStep_259 : DartStep (73, 69) (69, 58) := by
  apply dartCheck_sound
  change (((69, next (neighbors rotation 69) 73) == (69, 58)) &&
    (decide (73 < 82) && (neighbors rotation 73).contains 69)) = true
  rw [rotationRow_69, rotationRow_73]
  decide +kernel

theorem dartStep_260 : DartStep (69, 58) (58, 68) := by
  apply dartCheck_sound
  change (((58, next (neighbors rotation 58) 69) == (58, 68)) &&
    (decide (69 < 82) && (neighbors rotation 69).contains 58)) = true
  rw [rotationRow_58, rotationRow_69]
  decide +kernel

theorem dartStep_261 : DartStep (59, 79) (79, 81) := by
  apply dartCheck_sound
  change (((79, next (neighbors rotation 79) 59) == (79, 81)) &&
    (decide (59 < 82) && (neighbors rotation 59).contains 79)) = true
  rw [rotationRow_79, rotationRow_59]
  decide +kernel

theorem dartStep_262 : DartStep (79, 81) (81, 80) := by
  apply dartCheck_sound
  change (((81, next (neighbors rotation 81) 79) == (81, 80)) &&
    (decide (79 < 82) && (neighbors rotation 79).contains 81)) = true
  rw [rotationRow_81, rotationRow_79]
  decide +kernel

theorem dartStep_263 : DartStep (81, 80) (80, 78) := by
  apply dartCheck_sound
  change (((80, next (neighbors rotation 80) 81) == (80, 78)) &&
    (decide (81 < 82) && (neighbors rotation 81).contains 80)) = true
  rw [rotationRow_80, rotationRow_81]
  decide +kernel

theorem dartStep_264 : DartStep (80, 78) (78, 59) := by
  apply dartCheck_sound
  change (((78, next (neighbors rotation 78) 80) == (78, 59)) &&
    (decide (80 < 82) && (neighbors rotation 80).contains 78)) = true
  rw [rotationRow_78, rotationRow_80]
  decide +kernel

theorem dartStep_265 : DartStep (78, 59) (59, 79) := by
  apply dartCheck_sound
  change (((59, next (neighbors rotation 59) 78) == (59, 79)) &&
    (decide (78 < 82) && (neighbors rotation 78).contains 59)) = true
  rw [rotationRow_59, rotationRow_78]
  decide +kernel

theorem dartStep_266 : DartStep (70, 78) (78, 80) := by
  apply dartCheck_sound
  change (((78, next (neighbors rotation 78) 70) == (78, 80)) &&
    (decide (70 < 82) && (neighbors rotation 70).contains 78)) = true
  rw [rotationRow_78, rotationRow_70]
  decide +kernel

theorem dartStep_267 : DartStep (78, 80) (80, 70) := by
  apply dartCheck_sound
  change (((80, next (neighbors rotation 80) 78) == (80, 70)) &&
    (decide (78 < 82) && (neighbors rotation 78).contains 80)) = true
  rw [rotationRow_80, rotationRow_78]
  decide +kernel

theorem dartStep_268 : DartStep (80, 70) (70, 78) := by
  apply dartCheck_sound
  change (((70, next (neighbors rotation 70) 80) == (70, 78)) &&
    (decide (80 < 82) && (neighbors rotation 80).contains 70)) = true
  rw [rotationRow_70, rotationRow_80]
  decide +kernel

theorem dartStep_269 : DartStep (71, 81) (81, 79) := by
  apply dartCheck_sound
  change (((81, next (neighbors rotation 81) 71) == (81, 79)) &&
    (decide (71 < 82) && (neighbors rotation 71).contains 81)) = true
  rw [rotationRow_81, rotationRow_71]
  decide +kernel

theorem dartStep_270 : DartStep (81, 79) (79, 71) := by
  apply dartCheck_sound
  change (((79, next (neighbors rotation 79) 81) == (79, 71)) &&
    (decide (81 < 82) && (neighbors rotation 81).contains 79)) = true
  rw [rotationRow_79, rotationRow_81]
  decide +kernel

theorem dartStep_271 : DartStep (79, 71) (71, 81) := by
  apply dartCheck_sound
  change (((71, next (neighbors rotation 71) 79) == (71, 81)) &&
    (decide (79 < 82) && (neighbors rotation 79).contains 71)) = true
  rw [rotationRow_71, rotationRow_79]
  decide +kernel

private def FaceLocal (l : List Dart) : Prop :=
  IsOrbit (faceNext rotation) l ∧
  ∀ d ∈ l, d.1 < 82 ∧ d.2 ∈ neighbors rotation d.1

private theorem faceLocal_0 : FaceLocal (sphericalFaces[0]?.getD []) := by
  change FaceLocal [(0, 1), (1, 6), (6, 0)]
  unfold FaceLocal IsOrbit
  refine ⟨⟨by decide +kernel, by decide +kernel, ?_⟩, ?_⟩
  · change [faceNext rotation (0, 1), faceNext rotation (1, 6), faceNext rotation (6, 0)] = [(1, 6), (6, 0), (0, 1)]
    rw [(dartStep_0).1, (dartStep_1).1, (dartStep_2).1]
  · intro d hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
    rcases hd with rfl | rfl | rfl
    · exact (dartStep_0).2
    · exact (dartStep_1).2
    · exact (dartStep_2).2

private theorem faceLocal_1 : FaceLocal (sphericalFaces[1]?.getD []) := by
  change FaceLocal [(0, 3), (3, 24), (24, 22), (22, 26), (26, 42), (42, 10), (10, 7), (7, 14), (14, 68), (68, 58), (58, 55), (55, 56), (56, 20), (20, 1), (1, 0)]
  unfold FaceLocal IsOrbit
  refine ⟨⟨by decide +kernel, by decide +kernel, ?_⟩, ?_⟩
  · change [faceNext rotation (0, 3), faceNext rotation (3, 24), faceNext rotation (24, 22), faceNext rotation (22, 26), faceNext rotation (26, 42), faceNext rotation (42, 10), faceNext rotation (10, 7), faceNext rotation (7, 14), faceNext rotation (14, 68), faceNext rotation (68, 58), faceNext rotation (58, 55), faceNext rotation (55, 56), faceNext rotation (56, 20), faceNext rotation (20, 1), faceNext rotation (1, 0)] = [(3, 24), (24, 22), (22, 26), (26, 42), (42, 10), (10, 7), (7, 14), (14, 68), (68, 58), (58, 55), (55, 56), (56, 20), (20, 1), (1, 0), (0, 3)]
    rw [(dartStep_3).1, (dartStep_4).1, (dartStep_5).1, (dartStep_6).1, (dartStep_7).1, (dartStep_8).1, (dartStep_9).1, (dartStep_10).1, (dartStep_11).1, (dartStep_12).1, (dartStep_13).1, (dartStep_14).1, (dartStep_15).1, (dartStep_16).1, (dartStep_17).1]
  · intro d hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (dartStep_3).2
    · exact (dartStep_4).2
    · exact (dartStep_5).2
    · exact (dartStep_6).2
    · exact (dartStep_7).2
    · exact (dartStep_8).2
    · exact (dartStep_9).2
    · exact (dartStep_10).2
    · exact (dartStep_11).2
    · exact (dartStep_12).2
    · exact (dartStep_13).2
    · exact (dartStep_14).2
    · exact (dartStep_15).2
    · exact (dartStep_16).2
    · exact (dartStep_17).2

private theorem faceLocal_2 : FaceLocal (sphericalFaces[2]?.getD []) := by
  change FaceLocal [(0, 2), (2, 32), (32, 33), (33, 3), (3, 0)]
  unfold FaceLocal IsOrbit
  refine ⟨⟨by decide +kernel, by decide +kernel, ?_⟩, ?_⟩
  · change [faceNext rotation (0, 2), faceNext rotation (2, 32), faceNext rotation (32, 33), faceNext rotation (33, 3), faceNext rotation (3, 0)] = [(2, 32), (32, 33), (33, 3), (3, 0), (0, 2)]
    rw [(dartStep_18).1, (dartStep_19).1, (dartStep_20).1, (dartStep_21).1, (dartStep_22).1]
  · intro d hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl
    · exact (dartStep_18).2
    · exact (dartStep_19).2
    · exact (dartStep_20).2
    · exact (dartStep_21).2
    · exact (dartStep_22).2

private theorem faceLocal_3 : FaceLocal (sphericalFaces[3]?.getD []) := by
  change FaceLocal [(0, 5), (5, 29), (29, 27), (27, 31), (31, 46), (46, 38), (38, 25), (25, 22), (22, 23), (23, 2), (2, 0)]
  unfold FaceLocal IsOrbit
  refine ⟨⟨by decide +kernel, by decide +kernel, ?_⟩, ?_⟩
  · change [faceNext rotation (0, 5), faceNext rotation (5, 29), faceNext rotation (29, 27), faceNext rotation (27, 31), faceNext rotation (31, 46), faceNext rotation (46, 38), faceNext rotation (38, 25), faceNext rotation (25, 22), faceNext rotation (22, 23), faceNext rotation (23, 2), faceNext rotation (2, 0)] = [(5, 29), (29, 27), (27, 31), (31, 46), (46, 38), (38, 25), (25, 22), (22, 23), (23, 2), (2, 0), (0, 5)]
    rw [(dartStep_23).1, (dartStep_24).1, (dartStep_25).1, (dartStep_26).1, (dartStep_27).1, (dartStep_28).1, (dartStep_29).1, (dartStep_30).1, (dartStep_31).1, (dartStep_32).1, (dartStep_33).1]
  · intro d hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (dartStep_23).2
    · exact (dartStep_24).2
    · exact (dartStep_25).2
    · exact (dartStep_26).2
    · exact (dartStep_27).2
    · exact (dartStep_28).2
    · exact (dartStep_29).2
    · exact (dartStep_30).2
    · exact (dartStep_31).2
    · exact (dartStep_32).2
    · exact (dartStep_33).2

private theorem faceLocal_4 : FaceLocal (sphericalFaces[4]?.getD []) := by
  change FaceLocal [(0, 4), (4, 34), (34, 35), (35, 5), (5, 0)]
  unfold FaceLocal IsOrbit
  refine ⟨⟨by decide +kernel, by decide +kernel, ?_⟩, ?_⟩
  · change [faceNext rotation (0, 4), faceNext rotation (4, 34), faceNext rotation (34, 35), faceNext rotation (35, 5), faceNext rotation (5, 0)] = [(4, 34), (34, 35), (35, 5), (5, 0), (0, 4)]
    rw [(dartStep_34).1, (dartStep_35).1, (dartStep_36).1, (dartStep_37).1, (dartStep_38).1]
  · intro d hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl
    · exact (dartStep_34).2
    · exact (dartStep_35).2
    · exact (dartStep_36).2
    · exact (dartStep_37).2
    · exact (dartStep_38).2

private theorem faceLocal_5 : FaceLocal (sphericalFaces[5]?.getD []) := by
  change FaceLocal [(0, 6), (6, 60), (60, 12), (12, 7), (7, 8), (8, 36), (36, 30), (30, 27), (27, 28), (28, 4), (4, 0)]
  unfold FaceLocal IsOrbit
  refine ⟨⟨by decide +kernel, by decide +kernel, ?_⟩, ?_⟩
  · change [faceNext rotation (0, 6), faceNext rotation (6, 60), faceNext rotation (60, 12), faceNext rotation (12, 7), faceNext rotation (7, 8), faceNext rotation (8, 36), faceNext rotation (36, 30), faceNext rotation (30, 27), faceNext rotation (27, 28), faceNext rotation (28, 4), faceNext rotation (4, 0)] = [(6, 60), (60, 12), (12, 7), (7, 8), (8, 36), (36, 30), (30, 27), (27, 28), (28, 4), (4, 0), (0, 6)]
    rw [(dartStep_39).1, (dartStep_40).1, (dartStep_41).1, (dartStep_42).1, (dartStep_43).1, (dartStep_44).1, (dartStep_45).1, (dartStep_46).1, (dartStep_47).1, (dartStep_48).1, (dartStep_49).1]
  · intro d hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (dartStep_39).2
    · exact (dartStep_40).2
    · exact (dartStep_41).2
    · exact (dartStep_42).2
    · exact (dartStep_43).2
    · exact (dartStep_44).2
    · exact (dartStep_45).2
    · exact (dartStep_46).2
    · exact (dartStep_47).2
    · exact (dartStep_48).2
    · exact (dartStep_49).2

private theorem faceLocal_6 : FaceLocal (sphericalFaces[6]?.getD []) := by
  change FaceLocal [(1, 19), (19, 52), (52, 50), (50, 54), (54, 74), (74, 16), (16, 7), (7, 13), (13, 61), (61, 6), (6, 1)]
  unfold FaceLocal IsOrbit
  refine ⟨⟨by decide +kernel, by decide +kernel, ?_⟩, ?_⟩
  · change [faceNext rotation (1, 19), faceNext rotation (19, 52), faceNext rotation (52, 50), faceNext rotation (50, 54), faceNext rotation (54, 74), faceNext rotation (74, 16), faceNext rotation (16, 7), faceNext rotation (7, 13), faceNext rotation (13, 61), faceNext rotation (61, 6), faceNext rotation (6, 1)] = [(19, 52), (52, 50), (50, 54), (54, 74), (74, 16), (16, 7), (7, 13), (13, 61), (61, 6), (6, 1), (1, 19)]
    rw [(dartStep_50).1, (dartStep_51).1, (dartStep_52).1, (dartStep_53).1, (dartStep_54).1, (dartStep_55).1, (dartStep_56).1, (dartStep_57).1, (dartStep_58).1, (dartStep_59).1, (dartStep_60).1]
  · intro d hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (dartStep_50).2
    · exact (dartStep_51).2
    · exact (dartStep_52).2
    · exact (dartStep_53).2
    · exact (dartStep_54).2
    · exact (dartStep_55).2
    · exact (dartStep_56).2
    · exact (dartStep_57).2
    · exact (dartStep_58).2
    · exact (dartStep_59).2
    · exact (dartStep_60).2

private theorem faceLocal_7 : FaceLocal (sphericalFaces[7]?.getD []) := by
  change FaceLocal [(1, 18), (18, 64), (64, 65), (65, 19), (19, 1)]
  unfold FaceLocal IsOrbit
  refine ⟨⟨by decide +kernel, by decide +kernel, ?_⟩, ?_⟩
  · change [faceNext rotation (1, 18), faceNext rotation (18, 64), faceNext rotation (64, 65), faceNext rotation (65, 19), faceNext rotation (19, 1)] = [(18, 64), (64, 65), (65, 19), (19, 1), (1, 18)]
    rw [(dartStep_61).1, (dartStep_62).1, (dartStep_63).1, (dartStep_64).1, (dartStep_65).1]
  · intro d hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl
    · exact (dartStep_61).2
    · exact (dartStep_62).2
    · exact (dartStep_63).2
    · exact (dartStep_64).2
    · exact (dartStep_65).2

private theorem faceLocal_8 : FaceLocal (sphericalFaces[8]?.getD []) := by
  change FaceLocal [(1, 21), (21, 57), (57, 55), (55, 59), (59, 78), (78, 70), (70, 53), (53, 50), (50, 51), (51, 18), (18, 1)]
  unfold FaceLocal IsOrbit
  refine ⟨⟨by decide +kernel, by decide +kernel, ?_⟩, ?_⟩
  · change [faceNext rotation (1, 21), faceNext rotation (21, 57), faceNext rotation (57, 55), faceNext rotation (55, 59), faceNext rotation (59, 78), faceNext rotation (78, 70), faceNext rotation (70, 53), faceNext rotation (53, 50), faceNext rotation (50, 51), faceNext rotation (51, 18), faceNext rotation (18, 1)] = [(21, 57), (57, 55), (55, 59), (59, 78), (78, 70), (70, 53), (53, 50), (50, 51), (51, 18), (18, 1), (1, 21)]
    rw [(dartStep_66).1, (dartStep_67).1, (dartStep_68).1, (dartStep_69).1, (dartStep_70).1, (dartStep_71).1, (dartStep_72).1, (dartStep_73).1, (dartStep_74).1, (dartStep_75).1, (dartStep_76).1]
  · intro d hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (dartStep_66).2
    · exact (dartStep_67).2
    · exact (dartStep_68).2
    · exact (dartStep_69).2
    · exact (dartStep_70).2
    · exact (dartStep_71).2
    · exact (dartStep_72).2
    · exact (dartStep_73).2
    · exact (dartStep_74).2
    · exact (dartStep_75).2
    · exact (dartStep_76).2

private theorem faceLocal_9 : FaceLocal (sphericalFaces[9]?.getD []) := by
  change FaceLocal [(1, 20), (20, 66), (66, 67), (67, 21), (21, 1)]
  unfold FaceLocal IsOrbit
  refine ⟨⟨by decide +kernel, by decide +kernel, ?_⟩, ?_⟩
  · change [faceNext rotation (1, 20), faceNext rotation (20, 66), faceNext rotation (66, 67), faceNext rotation (67, 21), faceNext rotation (21, 1)] = [(20, 66), (66, 67), (67, 21), (21, 1), (1, 20)]
    rw [(dartStep_77).1, (dartStep_78).1, (dartStep_79).1, (dartStep_80).1, (dartStep_81).1]
  · intro d hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl
    · exact (dartStep_77).2
    · exact (dartStep_78).2
    · exact (dartStep_79).2
    · exact (dartStep_80).2
    · exact (dartStep_81).2

private theorem faceLocal_10 : FaceLocal (sphericalFaces[10]?.getD []) := by
  change FaceLocal [(2, 23), (23, 32), (32, 2)]
  unfold FaceLocal IsOrbit
  refine ⟨⟨by decide +kernel, by decide +kernel, ?_⟩, ?_⟩
  · change [faceNext rotation (2, 23), faceNext rotation (23, 32), faceNext rotation (32, 2)] = [(23, 32), (32, 2), (2, 23)]
    rw [(dartStep_82).1, (dartStep_83).1, (dartStep_84).1]
  · intro d hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
    rcases hd with rfl | rfl | rfl
    · exact (dartStep_82).2
    · exact (dartStep_83).2
    · exact (dartStep_84).2

private theorem faceLocal_11 : FaceLocal (sphericalFaces[11]?.getD []) := by
  change FaceLocal [(3, 33), (33, 24), (24, 3)]
  unfold FaceLocal IsOrbit
  refine ⟨⟨by decide +kernel, by decide +kernel, ?_⟩, ?_⟩
  · change [faceNext rotation (3, 33), faceNext rotation (33, 24), faceNext rotation (24, 3)] = [(33, 24), (24, 3), (3, 33)]
    rw [(dartStep_85).1, (dartStep_86).1, (dartStep_87).1]
  · intro d hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
    rcases hd with rfl | rfl | rfl
    · exact (dartStep_85).2
    · exact (dartStep_86).2
    · exact (dartStep_87).2

private theorem faceLocal_12 : FaceLocal (sphericalFaces[12]?.getD []) := by
  change FaceLocal [(4, 28), (28, 34), (34, 4)]
  unfold FaceLocal IsOrbit
  refine ⟨⟨by decide +kernel, by decide +kernel, ?_⟩, ?_⟩
  · change [faceNext rotation (4, 28), faceNext rotation (28, 34), faceNext rotation (34, 4)] = [(28, 34), (34, 4), (4, 28)]
    rw [(dartStep_88).1, (dartStep_89).1, (dartStep_90).1]
  · intro d hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
    rcases hd with rfl | rfl | rfl
    · exact (dartStep_88).2
    · exact (dartStep_89).2
    · exact (dartStep_90).2

private theorem faceLocal_13 : FaceLocal (sphericalFaces[13]?.getD []) := by
  change FaceLocal [(5, 35), (35, 29), (29, 5)]
  unfold FaceLocal IsOrbit
  refine ⟨⟨by decide +kernel, by decide +kernel, ?_⟩, ?_⟩
  · change [faceNext rotation (5, 35), faceNext rotation (35, 29), faceNext rotation (29, 5)] = [(35, 29), (29, 5), (5, 35)]
    rw [(dartStep_91).1, (dartStep_92).1, (dartStep_93).1]
  · intro d hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
    rcases hd with rfl | rfl | rfl
    · exact (dartStep_91).2
    · exact (dartStep_92).2
    · exact (dartStep_93).2

private theorem faceLocal_14 : FaceLocal (sphericalFaces[14]?.getD []) := by
  change FaceLocal [(6, 61), (61, 63), (63, 62), (62, 60), (60, 6)]
  unfold FaceLocal IsOrbit
  refine ⟨⟨by decide +kernel, by decide +kernel, ?_⟩, ?_⟩
  · change [faceNext rotation (6, 61), faceNext rotation (61, 63), faceNext rotation (63, 62), faceNext rotation (62, 60), faceNext rotation (60, 6)] = [(61, 63), (63, 62), (62, 60), (60, 6), (6, 61)]
    rw [(dartStep_94).1, (dartStep_95).1, (dartStep_96).1, (dartStep_97).1, (dartStep_98).1]
  · intro d hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl
    · exact (dartStep_94).2
    · exact (dartStep_95).2
    · exact (dartStep_96).2
    · exact (dartStep_97).2
    · exact (dartStep_98).2

private theorem faceLocal_15 : FaceLocal (sphericalFaces[15]?.getD []) := by
  change FaceLocal [(7, 12), (12, 62), (62, 63), (63, 13), (13, 7)]
  unfold FaceLocal IsOrbit
  refine ⟨⟨by decide +kernel, by decide +kernel, ?_⟩, ?_⟩
  · change [faceNext rotation (7, 12), faceNext rotation (12, 62), faceNext rotation (62, 63), faceNext rotation (63, 13), faceNext rotation (13, 7)] = [(12, 62), (62, 63), (63, 13), (13, 7), (7, 12)]
    rw [(dartStep_99).1, (dartStep_100).1, (dartStep_101).1, (dartStep_102).1, (dartStep_103).1]
  · intro d hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl
    · exact (dartStep_99).2
    · exact (dartStep_100).2
    · exact (dartStep_101).2
    · exact (dartStep_102).2
    · exact (dartStep_103).2

private theorem faceLocal_16 : FaceLocal (sphericalFaces[16]?.getD []) := by
  change FaceLocal [(7, 9), (9, 41), (41, 40), (40, 8), (8, 7)]
  unfold FaceLocal IsOrbit
  refine ⟨⟨by decide +kernel, by decide +kernel, ?_⟩, ?_⟩
  · change [faceNext rotation (7, 9), faceNext rotation (9, 41), faceNext rotation (41, 40), faceNext rotation (40, 8), faceNext rotation (8, 7)] = [(9, 41), (41, 40), (40, 8), (8, 7), (7, 9)]
    rw [(dartStep_104).1, (dartStep_105).1, (dartStep_106).1, (dartStep_107).1, (dartStep_108).1]
  · intro d hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl
    · exact (dartStep_104).2
    · exact (dartStep_105).2
    · exact (dartStep_106).2
    · exact (dartStep_107).2
    · exact (dartStep_108).2

private theorem faceLocal_17 : FaceLocal (sphericalFaces[17]?.getD []) := by
  change FaceLocal [(7, 11), (11, 43), (43, 26), (26, 25), (25, 39), (39, 47), (47, 31), (31, 30), (30, 37), (37, 9), (9, 7)]
  unfold FaceLocal IsOrbit
  refine ⟨⟨by decide +kernel, by decide +kernel, ?_⟩, ?_⟩
  · change [faceNext rotation (7, 11), faceNext rotation (11, 43), faceNext rotation (43, 26), faceNext rotation (26, 25), faceNext rotation (25, 39), faceNext rotation (39, 47), faceNext rotation (47, 31), faceNext rotation (31, 30), faceNext rotation (30, 37), faceNext rotation (37, 9), faceNext rotation (9, 7)] = [(11, 43), (43, 26), (26, 25), (25, 39), (39, 47), (47, 31), (31, 30), (30, 37), (37, 9), (9, 7), (7, 11)]
    rw [(dartStep_109).1, (dartStep_110).1, (dartStep_111).1, (dartStep_112).1, (dartStep_113).1, (dartStep_114).1, (dartStep_115).1, (dartStep_116).1, (dartStep_117).1, (dartStep_118).1, (dartStep_119).1]
  · intro d hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (dartStep_109).2
    · exact (dartStep_110).2
    · exact (dartStep_111).2
    · exact (dartStep_112).2
    · exact (dartStep_113).2
    · exact (dartStep_114).2
    · exact (dartStep_115).2
    · exact (dartStep_116).2
    · exact (dartStep_117).2
    · exact (dartStep_118).2
    · exact (dartStep_119).2

private theorem faceLocal_18 : FaceLocal (sphericalFaces[18]?.getD []) := by
  change FaceLocal [(7, 10), (10, 44), (44, 45), (45, 11), (11, 7)]
  unfold FaceLocal IsOrbit
  refine ⟨⟨by decide +kernel, by decide +kernel, ?_⟩, ?_⟩
  · change [faceNext rotation (7, 10), faceNext rotation (10, 44), faceNext rotation (44, 45), faceNext rotation (45, 11), faceNext rotation (11, 7)] = [(10, 44), (44, 45), (45, 11), (11, 7), (7, 10)]
    rw [(dartStep_120).1, (dartStep_121).1, (dartStep_122).1, (dartStep_123).1, (dartStep_124).1]
  · intro d hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl
    · exact (dartStep_120).2
    · exact (dartStep_121).2
    · exact (dartStep_122).2
    · exact (dartStep_123).2
    · exact (dartStep_124).2

private theorem faceLocal_19 : FaceLocal (sphericalFaces[19]?.getD []) := by
  change FaceLocal [(7, 15), (15, 73), (73, 72), (72, 14), (14, 7)]
  unfold FaceLocal IsOrbit
  refine ⟨⟨by decide +kernel, by decide +kernel, ?_⟩, ?_⟩
  · change [faceNext rotation (7, 15), faceNext rotation (15, 73), faceNext rotation (73, 72), faceNext rotation (72, 14), faceNext rotation (14, 7)] = [(15, 73), (73, 72), (72, 14), (14, 7), (7, 15)]
    rw [(dartStep_125).1, (dartStep_126).1, (dartStep_127).1, (dartStep_128).1, (dartStep_129).1]
  · intro d hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl
    · exact (dartStep_125).2
    · exact (dartStep_126).2
    · exact (dartStep_127).2
    · exact (dartStep_128).2
    · exact (dartStep_129).2

private theorem faceLocal_20 : FaceLocal (sphericalFaces[20]?.getD []) := by
  change FaceLocal [(7, 17), (17, 75), (75, 54), (54, 53), (53, 71), (71, 79), (79, 59), (59, 58), (58, 69), (69, 15), (15, 7)]
  unfold FaceLocal IsOrbit
  refine ⟨⟨by decide +kernel, by decide +kernel, ?_⟩, ?_⟩
  · change [faceNext rotation (7, 17), faceNext rotation (17, 75), faceNext rotation (75, 54), faceNext rotation (54, 53), faceNext rotation (53, 71), faceNext rotation (71, 79), faceNext rotation (79, 59), faceNext rotation (59, 58), faceNext rotation (58, 69), faceNext rotation (69, 15), faceNext rotation (15, 7)] = [(17, 75), (75, 54), (54, 53), (53, 71), (71, 79), (79, 59), (59, 58), (58, 69), (69, 15), (15, 7), (7, 17)]
    rw [(dartStep_130).1, (dartStep_131).1, (dartStep_132).1, (dartStep_133).1, (dartStep_134).1, (dartStep_135).1, (dartStep_136).1, (dartStep_137).1, (dartStep_138).1, (dartStep_139).1, (dartStep_140).1]
  · intro d hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (dartStep_130).2
    · exact (dartStep_131).2
    · exact (dartStep_132).2
    · exact (dartStep_133).2
    · exact (dartStep_134).2
    · exact (dartStep_135).2
    · exact (dartStep_136).2
    · exact (dartStep_137).2
    · exact (dartStep_138).2
    · exact (dartStep_139).2
    · exact (dartStep_140).2

private theorem faceLocal_21 : FaceLocal (sphericalFaces[21]?.getD []) := by
  change FaceLocal [(7, 16), (16, 76), (76, 77), (77, 17), (17, 7)]
  unfold FaceLocal IsOrbit
  refine ⟨⟨by decide +kernel, by decide +kernel, ?_⟩, ?_⟩
  · change [faceNext rotation (7, 16), faceNext rotation (16, 76), faceNext rotation (76, 77), faceNext rotation (77, 17), faceNext rotation (17, 7)] = [(16, 76), (76, 77), (77, 17), (17, 7), (7, 16)]
    rw [(dartStep_141).1, (dartStep_142).1, (dartStep_143).1, (dartStep_144).1, (dartStep_145).1]
  · intro d hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl
    · exact (dartStep_141).2
    · exact (dartStep_142).2
    · exact (dartStep_143).2
    · exact (dartStep_144).2
    · exact (dartStep_145).2

private theorem faceLocal_22 : FaceLocal (sphericalFaces[22]?.getD []) := by
  change FaceLocal [(8, 40), (40, 36), (36, 8)]
  unfold FaceLocal IsOrbit
  refine ⟨⟨by decide +kernel, by decide +kernel, ?_⟩, ?_⟩
  · change [faceNext rotation (8, 40), faceNext rotation (40, 36), faceNext rotation (36, 8)] = [(40, 36), (36, 8), (8, 40)]
    rw [(dartStep_146).1, (dartStep_147).1, (dartStep_148).1]
  · intro d hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
    rcases hd with rfl | rfl | rfl
    · exact (dartStep_146).2
    · exact (dartStep_147).2
    · exact (dartStep_148).2

private theorem faceLocal_23 : FaceLocal (sphericalFaces[23]?.getD []) := by
  change FaceLocal [(9, 37), (37, 41), (41, 9)]
  unfold FaceLocal IsOrbit
  refine ⟨⟨by decide +kernel, by decide +kernel, ?_⟩, ?_⟩
  · change [faceNext rotation (9, 37), faceNext rotation (37, 41), faceNext rotation (41, 9)] = [(37, 41), (41, 9), (9, 37)]
    rw [(dartStep_149).1, (dartStep_150).1, (dartStep_151).1]
  · intro d hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
    rcases hd with rfl | rfl | rfl
    · exact (dartStep_149).2
    · exact (dartStep_150).2
    · exact (dartStep_151).2

private theorem faceLocal_24 : FaceLocal (sphericalFaces[24]?.getD []) := by
  change FaceLocal [(10, 42), (42, 44), (44, 10)]
  unfold FaceLocal IsOrbit
  refine ⟨⟨by decide +kernel, by decide +kernel, ?_⟩, ?_⟩
  · change [faceNext rotation (10, 42), faceNext rotation (42, 44), faceNext rotation (44, 10)] = [(42, 44), (44, 10), (10, 42)]
    rw [(dartStep_152).1, (dartStep_153).1, (dartStep_154).1]
  · intro d hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
    rcases hd with rfl | rfl | rfl
    · exact (dartStep_152).2
    · exact (dartStep_153).2
    · exact (dartStep_154).2

private theorem faceLocal_25 : FaceLocal (sphericalFaces[25]?.getD []) := by
  change FaceLocal [(11, 45), (45, 43), (43, 11)]
  unfold FaceLocal IsOrbit
  refine ⟨⟨by decide +kernel, by decide +kernel, ?_⟩, ?_⟩
  · change [faceNext rotation (11, 45), faceNext rotation (45, 43), faceNext rotation (43, 11)] = [(45, 43), (43, 11), (11, 45)]
    rw [(dartStep_155).1, (dartStep_156).1, (dartStep_157).1]
  · intro d hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
    rcases hd with rfl | rfl | rfl
    · exact (dartStep_155).2
    · exact (dartStep_156).2
    · exact (dartStep_157).2

private theorem faceLocal_26 : FaceLocal (sphericalFaces[26]?.getD []) := by
  change FaceLocal [(12, 60), (60, 62), (62, 12)]
  unfold FaceLocal IsOrbit
  refine ⟨⟨by decide +kernel, by decide +kernel, ?_⟩, ?_⟩
  · change [faceNext rotation (12, 60), faceNext rotation (60, 62), faceNext rotation (62, 12)] = [(60, 62), (62, 12), (12, 60)]
    rw [(dartStep_158).1, (dartStep_159).1, (dartStep_160).1]
  · intro d hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
    rcases hd with rfl | rfl | rfl
    · exact (dartStep_158).2
    · exact (dartStep_159).2
    · exact (dartStep_160).2

private theorem faceLocal_27 : FaceLocal (sphericalFaces[27]?.getD []) := by
  change FaceLocal [(13, 63), (63, 61), (61, 13)]
  unfold FaceLocal IsOrbit
  refine ⟨⟨by decide +kernel, by decide +kernel, ?_⟩, ?_⟩
  · change [faceNext rotation (13, 63), faceNext rotation (63, 61), faceNext rotation (61, 13)] = [(63, 61), (61, 13), (13, 63)]
    rw [(dartStep_161).1, (dartStep_162).1, (dartStep_163).1]
  · intro d hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
    rcases hd with rfl | rfl | rfl
    · exact (dartStep_161).2
    · exact (dartStep_162).2
    · exact (dartStep_163).2

private theorem faceLocal_28 : FaceLocal (sphericalFaces[28]?.getD []) := by
  change FaceLocal [(14, 72), (72, 68), (68, 14)]
  unfold FaceLocal IsOrbit
  refine ⟨⟨by decide +kernel, by decide +kernel, ?_⟩, ?_⟩
  · change [faceNext rotation (14, 72), faceNext rotation (72, 68), faceNext rotation (68, 14)] = [(72, 68), (68, 14), (14, 72)]
    rw [(dartStep_164).1, (dartStep_165).1, (dartStep_166).1]
  · intro d hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
    rcases hd with rfl | rfl | rfl
    · exact (dartStep_164).2
    · exact (dartStep_165).2
    · exact (dartStep_166).2

private theorem faceLocal_29 : FaceLocal (sphericalFaces[29]?.getD []) := by
  change FaceLocal [(15, 69), (69, 73), (73, 15)]
  unfold FaceLocal IsOrbit
  refine ⟨⟨by decide +kernel, by decide +kernel, ?_⟩, ?_⟩
  · change [faceNext rotation (15, 69), faceNext rotation (69, 73), faceNext rotation (73, 15)] = [(69, 73), (73, 15), (15, 69)]
    rw [(dartStep_167).1, (dartStep_168).1, (dartStep_169).1]
  · intro d hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
    rcases hd with rfl | rfl | rfl
    · exact (dartStep_167).2
    · exact (dartStep_168).2
    · exact (dartStep_169).2

private theorem faceLocal_30 : FaceLocal (sphericalFaces[30]?.getD []) := by
  change FaceLocal [(16, 74), (74, 76), (76, 16)]
  unfold FaceLocal IsOrbit
  refine ⟨⟨by decide +kernel, by decide +kernel, ?_⟩, ?_⟩
  · change [faceNext rotation (16, 74), faceNext rotation (74, 76), faceNext rotation (76, 16)] = [(74, 76), (76, 16), (16, 74)]
    rw [(dartStep_170).1, (dartStep_171).1, (dartStep_172).1]
  · intro d hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
    rcases hd with rfl | rfl | rfl
    · exact (dartStep_170).2
    · exact (dartStep_171).2
    · exact (dartStep_172).2

private theorem faceLocal_31 : FaceLocal (sphericalFaces[31]?.getD []) := by
  change FaceLocal [(17, 77), (77, 75), (75, 17)]
  unfold FaceLocal IsOrbit
  refine ⟨⟨by decide +kernel, by decide +kernel, ?_⟩, ?_⟩
  · change [faceNext rotation (17, 77), faceNext rotation (77, 75), faceNext rotation (75, 17)] = [(77, 75), (75, 17), (17, 77)]
    rw [(dartStep_173).1, (dartStep_174).1, (dartStep_175).1]
  · intro d hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
    rcases hd with rfl | rfl | rfl
    · exact (dartStep_173).2
    · exact (dartStep_174).2
    · exact (dartStep_175).2

private theorem faceLocal_32 : FaceLocal (sphericalFaces[32]?.getD []) := by
  change FaceLocal [(18, 51), (51, 64), (64, 18)]
  unfold FaceLocal IsOrbit
  refine ⟨⟨by decide +kernel, by decide +kernel, ?_⟩, ?_⟩
  · change [faceNext rotation (18, 51), faceNext rotation (51, 64), faceNext rotation (64, 18)] = [(51, 64), (64, 18), (18, 51)]
    rw [(dartStep_176).1, (dartStep_177).1, (dartStep_178).1]
  · intro d hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
    rcases hd with rfl | rfl | rfl
    · exact (dartStep_176).2
    · exact (dartStep_177).2
    · exact (dartStep_178).2

private theorem faceLocal_33 : FaceLocal (sphericalFaces[33]?.getD []) := by
  change FaceLocal [(19, 65), (65, 52), (52, 19)]
  unfold FaceLocal IsOrbit
  refine ⟨⟨by decide +kernel, by decide +kernel, ?_⟩, ?_⟩
  · change [faceNext rotation (19, 65), faceNext rotation (65, 52), faceNext rotation (52, 19)] = [(65, 52), (52, 19), (19, 65)]
    rw [(dartStep_179).1, (dartStep_180).1, (dartStep_181).1]
  · intro d hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
    rcases hd with rfl | rfl | rfl
    · exact (dartStep_179).2
    · exact (dartStep_180).2
    · exact (dartStep_181).2

private theorem faceLocal_34 : FaceLocal (sphericalFaces[34]?.getD []) := by
  change FaceLocal [(20, 56), (56, 66), (66, 20)]
  unfold FaceLocal IsOrbit
  refine ⟨⟨by decide +kernel, by decide +kernel, ?_⟩, ?_⟩
  · change [faceNext rotation (20, 56), faceNext rotation (56, 66), faceNext rotation (66, 20)] = [(56, 66), (66, 20), (20, 56)]
    rw [(dartStep_182).1, (dartStep_183).1, (dartStep_184).1]
  · intro d hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
    rcases hd with rfl | rfl | rfl
    · exact (dartStep_182).2
    · exact (dartStep_183).2
    · exact (dartStep_184).2

private theorem faceLocal_35 : FaceLocal (sphericalFaces[35]?.getD []) := by
  change FaceLocal [(21, 67), (67, 57), (57, 21)]
  unfold FaceLocal IsOrbit
  refine ⟨⟨by decide +kernel, by decide +kernel, ?_⟩, ?_⟩
  · change [faceNext rotation (21, 67), faceNext rotation (67, 57), faceNext rotation (57, 21)] = [(67, 57), (57, 21), (21, 67)]
    rw [(dartStep_185).1, (dartStep_186).1, (dartStep_187).1]
  · intro d hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
    rcases hd with rfl | rfl | rfl
    · exact (dartStep_185).2
    · exact (dartStep_186).2
    · exact (dartStep_187).2

private theorem faceLocal_36 : FaceLocal (sphericalFaces[36]?.getD []) := by
  change FaceLocal [(22, 25), (25, 26), (26, 22)]
  unfold FaceLocal IsOrbit
  refine ⟨⟨by decide +kernel, by decide +kernel, ?_⟩, ?_⟩
  · change [faceNext rotation (22, 25), faceNext rotation (25, 26), faceNext rotation (26, 22)] = [(25, 26), (26, 22), (22, 25)]
    rw [(dartStep_188).1, (dartStep_189).1, (dartStep_190).1]
  · intro d hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
    rcases hd with rfl | rfl | rfl
    · exact (dartStep_188).2
    · exact (dartStep_189).2
    · exact (dartStep_190).2

private theorem faceLocal_37 : FaceLocal (sphericalFaces[37]?.getD []) := by
  change FaceLocal [(22, 24), (24, 33), (33, 32), (32, 23), (23, 22)]
  unfold FaceLocal IsOrbit
  refine ⟨⟨by decide +kernel, by decide +kernel, ?_⟩, ?_⟩
  · change [faceNext rotation (22, 24), faceNext rotation (24, 33), faceNext rotation (33, 32), faceNext rotation (32, 23), faceNext rotation (23, 22)] = [(24, 33), (33, 32), (32, 23), (23, 22), (22, 24)]
    rw [(dartStep_191).1, (dartStep_192).1, (dartStep_193).1, (dartStep_194).1, (dartStep_195).1]
  · intro d hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl
    · exact (dartStep_191).2
    · exact (dartStep_192).2
    · exact (dartStep_193).2
    · exact (dartStep_194).2
    · exact (dartStep_195).2

private theorem faceLocal_38 : FaceLocal (sphericalFaces[38]?.getD []) := by
  change FaceLocal [(25, 38), (38, 48), (48, 49), (49, 39), (39, 25)]
  unfold FaceLocal IsOrbit
  refine ⟨⟨by decide +kernel, by decide +kernel, ?_⟩, ?_⟩
  · change [faceNext rotation (25, 38), faceNext rotation (38, 48), faceNext rotation (48, 49), faceNext rotation (49, 39), faceNext rotation (39, 25)] = [(38, 48), (48, 49), (49, 39), (39, 25), (25, 38)]
    rw [(dartStep_196).1, (dartStep_197).1, (dartStep_198).1, (dartStep_199).1, (dartStep_200).1]
  · intro d hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl
    · exact (dartStep_196).2
    · exact (dartStep_197).2
    · exact (dartStep_198).2
    · exact (dartStep_199).2
    · exact (dartStep_200).2

private theorem faceLocal_39 : FaceLocal (sphericalFaces[39]?.getD []) := by
  change FaceLocal [(26, 43), (43, 45), (45, 44), (44, 42), (42, 26)]
  unfold FaceLocal IsOrbit
  refine ⟨⟨by decide +kernel, by decide +kernel, ?_⟩, ?_⟩
  · change [faceNext rotation (26, 43), faceNext rotation (43, 45), faceNext rotation (45, 44), faceNext rotation (44, 42), faceNext rotation (42, 26)] = [(43, 45), (45, 44), (44, 42), (42, 26), (26, 43)]
    rw [(dartStep_201).1, (dartStep_202).1, (dartStep_203).1, (dartStep_204).1, (dartStep_205).1]
  · intro d hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl
    · exact (dartStep_201).2
    · exact (dartStep_202).2
    · exact (dartStep_203).2
    · exact (dartStep_204).2
    · exact (dartStep_205).2

private theorem faceLocal_40 : FaceLocal (sphericalFaces[40]?.getD []) := by
  change FaceLocal [(27, 30), (30, 31), (31, 27)]
  unfold FaceLocal IsOrbit
  refine ⟨⟨by decide +kernel, by decide +kernel, ?_⟩, ?_⟩
  · change [faceNext rotation (27, 30), faceNext rotation (30, 31), faceNext rotation (31, 27)] = [(30, 31), (31, 27), (27, 30)]
    rw [(dartStep_206).1, (dartStep_207).1, (dartStep_208).1]
  · intro d hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
    rcases hd with rfl | rfl | rfl
    · exact (dartStep_206).2
    · exact (dartStep_207).2
    · exact (dartStep_208).2

private theorem faceLocal_41 : FaceLocal (sphericalFaces[41]?.getD []) := by
  change FaceLocal [(27, 29), (29, 35), (35, 34), (34, 28), (28, 27)]
  unfold FaceLocal IsOrbit
  refine ⟨⟨by decide +kernel, by decide +kernel, ?_⟩, ?_⟩
  · change [faceNext rotation (27, 29), faceNext rotation (29, 35), faceNext rotation (35, 34), faceNext rotation (34, 28), faceNext rotation (28, 27)] = [(29, 35), (35, 34), (34, 28), (28, 27), (27, 29)]
    rw [(dartStep_209).1, (dartStep_210).1, (dartStep_211).1, (dartStep_212).1, (dartStep_213).1]
  · intro d hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl
    · exact (dartStep_209).2
    · exact (dartStep_210).2
    · exact (dartStep_211).2
    · exact (dartStep_212).2
    · exact (dartStep_213).2

private theorem faceLocal_42 : FaceLocal (sphericalFaces[42]?.getD []) := by
  change FaceLocal [(30, 36), (36, 40), (40, 41), (41, 37), (37, 30)]
  unfold FaceLocal IsOrbit
  refine ⟨⟨by decide +kernel, by decide +kernel, ?_⟩, ?_⟩
  · change [faceNext rotation (30, 36), faceNext rotation (36, 40), faceNext rotation (40, 41), faceNext rotation (41, 37), faceNext rotation (37, 30)] = [(36, 40), (40, 41), (41, 37), (37, 30), (30, 36)]
    rw [(dartStep_214).1, (dartStep_215).1, (dartStep_216).1, (dartStep_217).1, (dartStep_218).1]
  · intro d hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl
    · exact (dartStep_214).2
    · exact (dartStep_215).2
    · exact (dartStep_216).2
    · exact (dartStep_217).2
    · exact (dartStep_218).2

private theorem faceLocal_43 : FaceLocal (sphericalFaces[43]?.getD []) := by
  change FaceLocal [(31, 47), (47, 49), (49, 48), (48, 46), (46, 31)]
  unfold FaceLocal IsOrbit
  refine ⟨⟨by decide +kernel, by decide +kernel, ?_⟩, ?_⟩
  · change [faceNext rotation (31, 47), faceNext rotation (47, 49), faceNext rotation (49, 48), faceNext rotation (48, 46), faceNext rotation (46, 31)] = [(47, 49), (49, 48), (48, 46), (46, 31), (31, 47)]
    rw [(dartStep_219).1, (dartStep_220).1, (dartStep_221).1, (dartStep_222).1, (dartStep_223).1]
  · intro d hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl
    · exact (dartStep_219).2
    · exact (dartStep_220).2
    · exact (dartStep_221).2
    · exact (dartStep_222).2
    · exact (dartStep_223).2

private theorem faceLocal_44 : FaceLocal (sphericalFaces[44]?.getD []) := by
  change FaceLocal [(38, 46), (46, 48), (48, 38)]
  unfold FaceLocal IsOrbit
  refine ⟨⟨by decide +kernel, by decide +kernel, ?_⟩, ?_⟩
  · change [faceNext rotation (38, 46), faceNext rotation (46, 48), faceNext rotation (48, 38)] = [(46, 48), (48, 38), (38, 46)]
    rw [(dartStep_224).1, (dartStep_225).1, (dartStep_226).1]
  · intro d hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
    rcases hd with rfl | rfl | rfl
    · exact (dartStep_224).2
    · exact (dartStep_225).2
    · exact (dartStep_226).2

private theorem faceLocal_45 : FaceLocal (sphericalFaces[45]?.getD []) := by
  change FaceLocal [(39, 49), (49, 47), (47, 39)]
  unfold FaceLocal IsOrbit
  refine ⟨⟨by decide +kernel, by decide +kernel, ?_⟩, ?_⟩
  · change [faceNext rotation (39, 49), faceNext rotation (49, 47), faceNext rotation (47, 39)] = [(49, 47), (47, 39), (39, 49)]
    rw [(dartStep_227).1, (dartStep_228).1, (dartStep_229).1]
  · intro d hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
    rcases hd with rfl | rfl | rfl
    · exact (dartStep_227).2
    · exact (dartStep_228).2
    · exact (dartStep_229).2

private theorem faceLocal_46 : FaceLocal (sphericalFaces[46]?.getD []) := by
  change FaceLocal [(50, 53), (53, 54), (54, 50)]
  unfold FaceLocal IsOrbit
  refine ⟨⟨by decide +kernel, by decide +kernel, ?_⟩, ?_⟩
  · change [faceNext rotation (50, 53), faceNext rotation (53, 54), faceNext rotation (54, 50)] = [(53, 54), (54, 50), (50, 53)]
    rw [(dartStep_230).1, (dartStep_231).1, (dartStep_232).1]
  · intro d hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
    rcases hd with rfl | rfl | rfl
    · exact (dartStep_230).2
    · exact (dartStep_231).2
    · exact (dartStep_232).2

private theorem faceLocal_47 : FaceLocal (sphericalFaces[47]?.getD []) := by
  change FaceLocal [(50, 52), (52, 65), (65, 64), (64, 51), (51, 50)]
  unfold FaceLocal IsOrbit
  refine ⟨⟨by decide +kernel, by decide +kernel, ?_⟩, ?_⟩
  · change [faceNext rotation (50, 52), faceNext rotation (52, 65), faceNext rotation (65, 64), faceNext rotation (64, 51), faceNext rotation (51, 50)] = [(52, 65), (65, 64), (64, 51), (51, 50), (50, 52)]
    rw [(dartStep_233).1, (dartStep_234).1, (dartStep_235).1, (dartStep_236).1, (dartStep_237).1]
  · intro d hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl
    · exact (dartStep_233).2
    · exact (dartStep_234).2
    · exact (dartStep_235).2
    · exact (dartStep_236).2
    · exact (dartStep_237).2

private theorem faceLocal_48 : FaceLocal (sphericalFaces[48]?.getD []) := by
  change FaceLocal [(53, 70), (70, 80), (80, 81), (81, 71), (71, 53)]
  unfold FaceLocal IsOrbit
  refine ⟨⟨by decide +kernel, by decide +kernel, ?_⟩, ?_⟩
  · change [faceNext rotation (53, 70), faceNext rotation (70, 80), faceNext rotation (80, 81), faceNext rotation (81, 71), faceNext rotation (71, 53)] = [(70, 80), (80, 81), (81, 71), (71, 53), (53, 70)]
    rw [(dartStep_238).1, (dartStep_239).1, (dartStep_240).1, (dartStep_241).1, (dartStep_242).1]
  · intro d hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl
    · exact (dartStep_238).2
    · exact (dartStep_239).2
    · exact (dartStep_240).2
    · exact (dartStep_241).2
    · exact (dartStep_242).2

private theorem faceLocal_49 : FaceLocal (sphericalFaces[49]?.getD []) := by
  change FaceLocal [(54, 75), (75, 77), (77, 76), (76, 74), (74, 54)]
  unfold FaceLocal IsOrbit
  refine ⟨⟨by decide +kernel, by decide +kernel, ?_⟩, ?_⟩
  · change [faceNext rotation (54, 75), faceNext rotation (75, 77), faceNext rotation (77, 76), faceNext rotation (76, 74), faceNext rotation (74, 54)] = [(75, 77), (77, 76), (76, 74), (74, 54), (54, 75)]
    rw [(dartStep_243).1, (dartStep_244).1, (dartStep_245).1, (dartStep_246).1, (dartStep_247).1]
  · intro d hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl
    · exact (dartStep_243).2
    · exact (dartStep_244).2
    · exact (dartStep_245).2
    · exact (dartStep_246).2
    · exact (dartStep_247).2

private theorem faceLocal_50 : FaceLocal (sphericalFaces[50]?.getD []) := by
  change FaceLocal [(55, 58), (58, 59), (59, 55)]
  unfold FaceLocal IsOrbit
  refine ⟨⟨by decide +kernel, by decide +kernel, ?_⟩, ?_⟩
  · change [faceNext rotation (55, 58), faceNext rotation (58, 59), faceNext rotation (59, 55)] = [(58, 59), (59, 55), (55, 58)]
    rw [(dartStep_248).1, (dartStep_249).1, (dartStep_250).1]
  · intro d hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
    rcases hd with rfl | rfl | rfl
    · exact (dartStep_248).2
    · exact (dartStep_249).2
    · exact (dartStep_250).2

private theorem faceLocal_51 : FaceLocal (sphericalFaces[51]?.getD []) := by
  change FaceLocal [(55, 57), (57, 67), (67, 66), (66, 56), (56, 55)]
  unfold FaceLocal IsOrbit
  refine ⟨⟨by decide +kernel, by decide +kernel, ?_⟩, ?_⟩
  · change [faceNext rotation (55, 57), faceNext rotation (57, 67), faceNext rotation (67, 66), faceNext rotation (66, 56), faceNext rotation (56, 55)] = [(57, 67), (67, 66), (66, 56), (56, 55), (55, 57)]
    rw [(dartStep_251).1, (dartStep_252).1, (dartStep_253).1, (dartStep_254).1, (dartStep_255).1]
  · intro d hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl
    · exact (dartStep_251).2
    · exact (dartStep_252).2
    · exact (dartStep_253).2
    · exact (dartStep_254).2
    · exact (dartStep_255).2

private theorem faceLocal_52 : FaceLocal (sphericalFaces[52]?.getD []) := by
  change FaceLocal [(58, 68), (68, 72), (72, 73), (73, 69), (69, 58)]
  unfold FaceLocal IsOrbit
  refine ⟨⟨by decide +kernel, by decide +kernel, ?_⟩, ?_⟩
  · change [faceNext rotation (58, 68), faceNext rotation (68, 72), faceNext rotation (72, 73), faceNext rotation (73, 69), faceNext rotation (69, 58)] = [(68, 72), (72, 73), (73, 69), (69, 58), (58, 68)]
    rw [(dartStep_256).1, (dartStep_257).1, (dartStep_258).1, (dartStep_259).1, (dartStep_260).1]
  · intro d hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl
    · exact (dartStep_256).2
    · exact (dartStep_257).2
    · exact (dartStep_258).2
    · exact (dartStep_259).2
    · exact (dartStep_260).2

private theorem faceLocal_53 : FaceLocal (sphericalFaces[53]?.getD []) := by
  change FaceLocal [(59, 79), (79, 81), (81, 80), (80, 78), (78, 59)]
  unfold FaceLocal IsOrbit
  refine ⟨⟨by decide +kernel, by decide +kernel, ?_⟩, ?_⟩
  · change [faceNext rotation (59, 79), faceNext rotation (79, 81), faceNext rotation (81, 80), faceNext rotation (80, 78), faceNext rotation (78, 59)] = [(79, 81), (81, 80), (80, 78), (78, 59), (59, 79)]
    rw [(dartStep_261).1, (dartStep_262).1, (dartStep_263).1, (dartStep_264).1, (dartStep_265).1]
  · intro d hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl
    · exact (dartStep_261).2
    · exact (dartStep_262).2
    · exact (dartStep_263).2
    · exact (dartStep_264).2
    · exact (dartStep_265).2

private theorem faceLocal_54 : FaceLocal (sphericalFaces[54]?.getD []) := by
  change FaceLocal [(70, 78), (78, 80), (80, 70)]
  unfold FaceLocal IsOrbit
  refine ⟨⟨by decide +kernel, by decide +kernel, ?_⟩, ?_⟩
  · change [faceNext rotation (70, 78), faceNext rotation (78, 80), faceNext rotation (80, 70)] = [(78, 80), (80, 70), (70, 78)]
    rw [(dartStep_266).1, (dartStep_267).1, (dartStep_268).1]
  · intro d hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
    rcases hd with rfl | rfl | rfl
    · exact (dartStep_266).2
    · exact (dartStep_267).2
    · exact (dartStep_268).2

private theorem faceLocal_55 : FaceLocal (sphericalFaces[55]?.getD []) := by
  change FaceLocal [(71, 81), (81, 79), (79, 71)]
  unfold FaceLocal IsOrbit
  refine ⟨⟨by decide +kernel, by decide +kernel, ?_⟩, ?_⟩
  · change [faceNext rotation (71, 81), faceNext rotation (81, 79), faceNext rotation (79, 71)] = [(81, 79), (79, 71), (71, 81)]
    rw [(dartStep_269).1, (dartStep_270).1, (dartStep_271).1]
  · intro d hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
    rcases hd with rfl | rfl | rfl
    · exact (dartStep_269).2
    · exact (dartStep_270).2
    · exact (dartStep_271).2

private theorem face_local_all : ∀ i : Fin 56,
    FaceLocal (sphericalFaces[i.val]?.getD []) := by
  intro i
  fin_cases i
  · exact faceLocal_0
  · exact faceLocal_1
  · exact faceLocal_2
  · exact faceLocal_3
  · exact faceLocal_4
  · exact faceLocal_5
  · exact faceLocal_6
  · exact faceLocal_7
  · exact faceLocal_8
  · exact faceLocal_9
  · exact faceLocal_10
  · exact faceLocal_11
  · exact faceLocal_12
  · exact faceLocal_13
  · exact faceLocal_14
  · exact faceLocal_15
  · exact faceLocal_16
  · exact faceLocal_17
  · exact faceLocal_18
  · exact faceLocal_19
  · exact faceLocal_20
  · exact faceLocal_21
  · exact faceLocal_22
  · exact faceLocal_23
  · exact faceLocal_24
  · exact faceLocal_25
  · exact faceLocal_26
  · exact faceLocal_27
  · exact faceLocal_28
  · exact faceLocal_29
  · exact faceLocal_30
  · exact faceLocal_31
  · exact faceLocal_32
  · exact faceLocal_33
  · exact faceLocal_34
  · exact faceLocal_35
  · exact faceLocal_36
  · exact faceLocal_37
  · exact faceLocal_38
  · exact faceLocal_39
  · exact faceLocal_40
  · exact faceLocal_41
  · exact faceLocal_42
  · exact faceLocal_43
  · exact faceLocal_44
  · exact faceLocal_45
  · exact faceLocal_46
  · exact faceLocal_47
  · exact faceLocal_48
  · exact faceLocal_49
  · exact faceLocal_50
  · exact faceLocal_51
  · exact faceLocal_52
  · exact faceLocal_53
  · exact faceLocal_54
  · exact faceLocal_55

private theorem face_local_mem (l : List Dart) (hl : l ∈ sphericalFaces) : FaceLocal l := by
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hl
  have hp := face_local_all ⟨i.val, i.isLt⟩
  have hs : sphericalFaces[i.val]?.getD [] = l := by
    rw [List.getElem?_eq_getElem i.isLt]
    exact hi
  exact hs ▸ hp

/-- Each face is a genuine simple successor orbit, including its closing step. -/
theorem sphericalFaces_orbits : ∀ l ∈ sphericalFaces, IsOrbit (faceNext rotation) l :=
  fun l hl => (face_local_mem l hl).1

theorem sphericalFaces_distinct : sphericalFaces.flatten.Nodup := by decide +kernel

private theorem sphericalFaces_incident : ∀ d ∈ sphericalFaces.flatten,
    d.1 < 82 ∧ d.2 ∈ neighbors rotation d.1 := by
  intro d hd
  obtain ⟨l, hl, hdl⟩ := List.mem_flatten.mp hd
  exact (face_local_mem l hl).2 d hdl

private theorem sphericalFaces_dart_count : sphericalFaces.flatten.length = 272 := by
  decide +kernel

private theorem source_dart_count : (darts 82 rotation).length = 272 := by
  rw [rotation_normal_form]
  decide +kernel

/-- Exact exhaustive coverage, obtained from a distinct subset of the actual
darts and equal cardinalities by a general proved sub-permutation theorem. -/
theorem sphericalFaces_cover : sphericalFaces.flatten.Perm (darts 82 rotation) := by
  have hs : sphericalFaces.flatten ⊆ darts 82 rotation := by
    intro d hd
    exact (mem_darts_iff 82 rotation d.1 d.2).mpr (sphericalFaces_incident d hd)
  exact (List.subperm_of_subset sphericalFaces_distinct hs).perm_of_length_le
    (by simpa only [source_dart_count, sphericalFaces_dart_count] using Nat.le_refl 272)

theorem sphericalFaces_partition : FacePartition 82 rotation sphericalFaces :=
  ⟨sphericalFaces_orbits, sphericalFaces_distinct, sphericalFaces_cover⟩

theorem spherical_rotation_counts :
    (darts 82 rotation).length = 272 ∧ sphericalFaces.length = 56 := by
  exact ⟨source_dart_count, by decide +kernel⟩

theorem spherical_rotation_euler :
    82 + sphericalFaces.length = (darts 82 rotation).length / 2 + 2 := by
  rw [spherical_rotation_counts.1, spherical_rotation_counts.2]

/-- Deleting a face fails exact coverage, independently of Euler. -/
theorem missing_face_rejected : ¬ FacePartition 82 rotation sphericalFaces.tail := by
  intro h
  have he := h.2.2.length_eq
  have hn : sphericalFaces.tail.flatten.length = 269 := by decide +kernel
  rw [hn, spherical_rotation_counts.1] at he
  contradiction

#print axioms rotation_graph_connected
#print axioms hard_dart_step
#print axioms faceLocal_0
#print axioms sphericalFaces_cover
#print axioms sphericalFaces_partition
#print axioms missing_face_rejected
end Steinberg
