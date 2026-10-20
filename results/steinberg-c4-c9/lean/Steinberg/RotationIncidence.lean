import Mathlib.Tactic.FinCases
import Steinberg.Data
import Steinberg.Rotation

namespace Steinberg
open Rotation
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem rotation_first_row : neighbors rotation 0 = [1, 3, 2, 5, 4, 6] := by
  rw [rotation_normal_form]
  decide +kernel

theorem rotation_first_face : IsOrbit (faceNext rotation) [(0, 1), (1, 6), (6, 0)] := by
  rw [rotation_normal_form]
  decide +kernel

private def vertexRowValid (v : Fin 82) : Prop :=
    (neighbors rotation v).Nodup ∧ neighbors rotation v ≠ [] ∧
    (∀ w ∈ neighbors rotation v, w < 82) ∧
    (∀ w : Fin 82, w.val ∈ neighbors rotation v ↔ graph.Adj v w)

private theorem vertexRow_0 : vertexRowValid 0 := by
  unfold vertexRowValid
  simp only [graph_adj_iff]
  rw [rotation_normal_form, rotation_edgeList_normal_form]
  decide +kernel

private theorem vertexRow_1 : vertexRowValid 1 := by
  unfold vertexRowValid
  simp only [graph_adj_iff]
  rw [rotation_normal_form, rotation_edgeList_normal_form]
  decide +kernel

private theorem vertexRow_2 : vertexRowValid 2 := by
  unfold vertexRowValid
  simp only [graph_adj_iff]
  rw [rotation_normal_form, rotation_edgeList_normal_form]
  decide +kernel

private theorem vertexRow_3 : vertexRowValid 3 := by
  unfold vertexRowValid
  simp only [graph_adj_iff]
  rw [rotation_normal_form, rotation_edgeList_normal_form]
  decide +kernel

private theorem vertexRow_4 : vertexRowValid 4 := by
  unfold vertexRowValid
  simp only [graph_adj_iff]
  rw [rotation_normal_form, rotation_edgeList_normal_form]
  decide +kernel

private theorem vertexRow_5 : vertexRowValid 5 := by
  unfold vertexRowValid
  simp only [graph_adj_iff]
  rw [rotation_normal_form, rotation_edgeList_normal_form]
  decide +kernel

private theorem vertexRow_6 : vertexRowValid 6 := by
  unfold vertexRowValid
  simp only [graph_adj_iff]
  rw [rotation_normal_form, rotation_edgeList_normal_form]
  decide +kernel

private theorem vertexRow_7 : vertexRowValid 7 := by
  unfold vertexRowValid
  simp only [graph_adj_iff]
  rw [rotation_normal_form, rotation_edgeList_normal_form]
  decide +kernel

private theorem vertexRow_8 : vertexRowValid 8 := by
  unfold vertexRowValid
  simp only [graph_adj_iff]
  rw [rotation_normal_form, rotation_edgeList_normal_form]
  decide +kernel

private theorem vertexRow_9 : vertexRowValid 9 := by
  unfold vertexRowValid
  simp only [graph_adj_iff]
  rw [rotation_normal_form, rotation_edgeList_normal_form]
  decide +kernel

private theorem vertexRow_10 : vertexRowValid 10 := by
  unfold vertexRowValid
  simp only [graph_adj_iff]
  rw [rotation_normal_form, rotation_edgeList_normal_form]
  decide +kernel

private theorem vertexRow_11 : vertexRowValid 11 := by
  unfold vertexRowValid
  simp only [graph_adj_iff]
  rw [rotation_normal_form, rotation_edgeList_normal_form]
  decide +kernel

private theorem vertexRow_12 : vertexRowValid 12 := by
  unfold vertexRowValid
  simp only [graph_adj_iff]
  rw [rotation_normal_form, rotation_edgeList_normal_form]
  decide +kernel

private theorem vertexRow_13 : vertexRowValid 13 := by
  unfold vertexRowValid
  simp only [graph_adj_iff]
  rw [rotation_normal_form, rotation_edgeList_normal_form]
  decide +kernel

private theorem vertexRow_14 : vertexRowValid 14 := by
  unfold vertexRowValid
  simp only [graph_adj_iff]
  rw [rotation_normal_form, rotation_edgeList_normal_form]
  decide +kernel

private theorem vertexRow_15 : vertexRowValid 15 := by
  unfold vertexRowValid
  simp only [graph_adj_iff]
  rw [rotation_normal_form, rotation_edgeList_normal_form]
  decide +kernel

private theorem vertexRow_16 : vertexRowValid 16 := by
  unfold vertexRowValid
  simp only [graph_adj_iff]
  rw [rotation_normal_form, rotation_edgeList_normal_form]
  decide +kernel

private theorem vertexRow_17 : vertexRowValid 17 := by
  unfold vertexRowValid
  simp only [graph_adj_iff]
  rw [rotation_normal_form, rotation_edgeList_normal_form]
  decide +kernel

private theorem vertexRow_18 : vertexRowValid 18 := by
  unfold vertexRowValid
  simp only [graph_adj_iff]
  rw [rotation_normal_form, rotation_edgeList_normal_form]
  decide +kernel

private theorem vertexRow_19 : vertexRowValid 19 := by
  unfold vertexRowValid
  simp only [graph_adj_iff]
  rw [rotation_normal_form, rotation_edgeList_normal_form]
  decide +kernel

private theorem vertexRow_20 : vertexRowValid 20 := by
  unfold vertexRowValid
  simp only [graph_adj_iff]
  rw [rotation_normal_form, rotation_edgeList_normal_form]
  decide +kernel

private theorem vertexRow_21 : vertexRowValid 21 := by
  unfold vertexRowValid
  simp only [graph_adj_iff]
  rw [rotation_normal_form, rotation_edgeList_normal_form]
  decide +kernel

private theorem vertexRow_22 : vertexRowValid 22 := by
  unfold vertexRowValid
  simp only [graph_adj_iff]
  rw [rotation_normal_form, rotation_edgeList_normal_form]
  decide +kernel

private theorem vertexRow_23 : vertexRowValid 23 := by
  unfold vertexRowValid
  simp only [graph_adj_iff]
  rw [rotation_normal_form, rotation_edgeList_normal_form]
  decide +kernel

private theorem vertexRow_24 : vertexRowValid 24 := by
  unfold vertexRowValid
  simp only [graph_adj_iff]
  rw [rotation_normal_form, rotation_edgeList_normal_form]
  decide +kernel

private theorem vertexRow_25 : vertexRowValid 25 := by
  unfold vertexRowValid
  simp only [graph_adj_iff]
  rw [rotation_normal_form, rotation_edgeList_normal_form]
  decide +kernel

private theorem vertexRow_26 : vertexRowValid 26 := by
  unfold vertexRowValid
  simp only [graph_adj_iff]
  rw [rotation_normal_form, rotation_edgeList_normal_form]
  decide +kernel

private theorem vertexRow_27 : vertexRowValid 27 := by
  unfold vertexRowValid
  simp only [graph_adj_iff]
  rw [rotation_normal_form, rotation_edgeList_normal_form]
  decide +kernel

private theorem vertexRow_28 : vertexRowValid 28 := by
  unfold vertexRowValid
  simp only [graph_adj_iff]
  rw [rotation_normal_form, rotation_edgeList_normal_form]
  decide +kernel

private theorem vertexRow_29 : vertexRowValid 29 := by
  unfold vertexRowValid
  simp only [graph_adj_iff]
  rw [rotation_normal_form, rotation_edgeList_normal_form]
  decide +kernel

private theorem vertexRow_30 : vertexRowValid 30 := by
  unfold vertexRowValid
  simp only [graph_adj_iff]
  rw [rotation_normal_form, rotation_edgeList_normal_form]
  decide +kernel

private theorem vertexRow_31 : vertexRowValid 31 := by
  unfold vertexRowValid
  simp only [graph_adj_iff]
  rw [rotation_normal_form, rotation_edgeList_normal_form]
  decide +kernel

private theorem vertexRow_32 : vertexRowValid 32 := by
  unfold vertexRowValid
  simp only [graph_adj_iff]
  rw [rotation_normal_form, rotation_edgeList_normal_form]
  decide +kernel

private theorem vertexRow_33 : vertexRowValid 33 := by
  unfold vertexRowValid
  simp only [graph_adj_iff]
  rw [rotation_normal_form, rotation_edgeList_normal_form]
  decide +kernel

private theorem vertexRow_34 : vertexRowValid 34 := by
  unfold vertexRowValid
  simp only [graph_adj_iff]
  rw [rotation_normal_form, rotation_edgeList_normal_form]
  decide +kernel

private theorem vertexRow_35 : vertexRowValid 35 := by
  unfold vertexRowValid
  simp only [graph_adj_iff]
  rw [rotation_normal_form, rotation_edgeList_normal_form]
  decide +kernel

private theorem vertexRow_36 : vertexRowValid 36 := by
  unfold vertexRowValid
  simp only [graph_adj_iff]
  rw [rotation_normal_form, rotation_edgeList_normal_form]
  decide +kernel

private theorem vertexRow_37 : vertexRowValid 37 := by
  unfold vertexRowValid
  simp only [graph_adj_iff]
  rw [rotation_normal_form, rotation_edgeList_normal_form]
  decide +kernel

private theorem vertexRow_38 : vertexRowValid 38 := by
  unfold vertexRowValid
  simp only [graph_adj_iff]
  rw [rotation_normal_form, rotation_edgeList_normal_form]
  decide +kernel

private theorem vertexRow_39 : vertexRowValid 39 := by
  unfold vertexRowValid
  simp only [graph_adj_iff]
  rw [rotation_normal_form, rotation_edgeList_normal_form]
  decide +kernel

private theorem vertexRow_40 : vertexRowValid 40 := by
  unfold vertexRowValid
  simp only [graph_adj_iff]
  rw [rotation_normal_form, rotation_edgeList_normal_form]
  decide +kernel

private theorem vertexRow_41 : vertexRowValid 41 := by
  unfold vertexRowValid
  simp only [graph_adj_iff]
  rw [rotation_normal_form, rotation_edgeList_normal_form]
  decide +kernel

private theorem vertexRow_42 : vertexRowValid 42 := by
  unfold vertexRowValid
  simp only [graph_adj_iff]
  rw [rotation_normal_form, rotation_edgeList_normal_form]
  decide +kernel

private theorem vertexRow_43 : vertexRowValid 43 := by
  unfold vertexRowValid
  simp only [graph_adj_iff]
  rw [rotation_normal_form, rotation_edgeList_normal_form]
  decide +kernel

private theorem vertexRow_44 : vertexRowValid 44 := by
  unfold vertexRowValid
  simp only [graph_adj_iff]
  rw [rotation_normal_form, rotation_edgeList_normal_form]
  decide +kernel

private theorem vertexRow_45 : vertexRowValid 45 := by
  unfold vertexRowValid
  simp only [graph_adj_iff]
  rw [rotation_normal_form, rotation_edgeList_normal_form]
  decide +kernel

private theorem vertexRow_46 : vertexRowValid 46 := by
  unfold vertexRowValid
  simp only [graph_adj_iff]
  rw [rotation_normal_form, rotation_edgeList_normal_form]
  decide +kernel

private theorem vertexRow_47 : vertexRowValid 47 := by
  unfold vertexRowValid
  simp only [graph_adj_iff]
  rw [rotation_normal_form, rotation_edgeList_normal_form]
  decide +kernel

private theorem vertexRow_48 : vertexRowValid 48 := by
  unfold vertexRowValid
  simp only [graph_adj_iff]
  rw [rotation_normal_form, rotation_edgeList_normal_form]
  decide +kernel

private theorem vertexRow_49 : vertexRowValid 49 := by
  unfold vertexRowValid
  simp only [graph_adj_iff]
  rw [rotation_normal_form, rotation_edgeList_normal_form]
  decide +kernel

private theorem vertexRow_50 : vertexRowValid 50 := by
  unfold vertexRowValid
  simp only [graph_adj_iff]
  rw [rotation_normal_form, rotation_edgeList_normal_form]
  decide +kernel

private theorem vertexRow_51 : vertexRowValid 51 := by
  unfold vertexRowValid
  simp only [graph_adj_iff]
  rw [rotation_normal_form, rotation_edgeList_normal_form]
  decide +kernel

private theorem vertexRow_52 : vertexRowValid 52 := by
  unfold vertexRowValid
  simp only [graph_adj_iff]
  rw [rotation_normal_form, rotation_edgeList_normal_form]
  decide +kernel

private theorem vertexRow_53 : vertexRowValid 53 := by
  unfold vertexRowValid
  simp only [graph_adj_iff]
  rw [rotation_normal_form, rotation_edgeList_normal_form]
  decide +kernel

private theorem vertexRow_54 : vertexRowValid 54 := by
  unfold vertexRowValid
  simp only [graph_adj_iff]
  rw [rotation_normal_form, rotation_edgeList_normal_form]
  decide +kernel

private theorem vertexRow_55 : vertexRowValid 55 := by
  unfold vertexRowValid
  simp only [graph_adj_iff]
  rw [rotation_normal_form, rotation_edgeList_normal_form]
  decide +kernel

private theorem vertexRow_56 : vertexRowValid 56 := by
  unfold vertexRowValid
  simp only [graph_adj_iff]
  rw [rotation_normal_form, rotation_edgeList_normal_form]
  decide +kernel

private theorem vertexRow_57 : vertexRowValid 57 := by
  unfold vertexRowValid
  simp only [graph_adj_iff]
  rw [rotation_normal_form, rotation_edgeList_normal_form]
  decide +kernel

private theorem vertexRow_58 : vertexRowValid 58 := by
  unfold vertexRowValid
  simp only [graph_adj_iff]
  rw [rotation_normal_form, rotation_edgeList_normal_form]
  decide +kernel

private theorem vertexRow_59 : vertexRowValid 59 := by
  unfold vertexRowValid
  simp only [graph_adj_iff]
  rw [rotation_normal_form, rotation_edgeList_normal_form]
  decide +kernel

private theorem vertexRow_60 : vertexRowValid 60 := by
  unfold vertexRowValid
  simp only [graph_adj_iff]
  rw [rotation_normal_form, rotation_edgeList_normal_form]
  decide +kernel

private theorem vertexRow_61 : vertexRowValid 61 := by
  unfold vertexRowValid
  simp only [graph_adj_iff]
  rw [rotation_normal_form, rotation_edgeList_normal_form]
  decide +kernel

private theorem vertexRow_62 : vertexRowValid 62 := by
  unfold vertexRowValid
  simp only [graph_adj_iff]
  rw [rotation_normal_form, rotation_edgeList_normal_form]
  decide +kernel

private theorem vertexRow_63 : vertexRowValid 63 := by
  unfold vertexRowValid
  simp only [graph_adj_iff]
  rw [rotation_normal_form, rotation_edgeList_normal_form]
  decide +kernel

private theorem vertexRow_64 : vertexRowValid 64 := by
  unfold vertexRowValid
  simp only [graph_adj_iff]
  rw [rotation_normal_form, rotation_edgeList_normal_form]
  decide +kernel

private theorem vertexRow_65 : vertexRowValid 65 := by
  unfold vertexRowValid
  simp only [graph_adj_iff]
  rw [rotation_normal_form, rotation_edgeList_normal_form]
  decide +kernel

private theorem vertexRow_66 : vertexRowValid 66 := by
  unfold vertexRowValid
  simp only [graph_adj_iff]
  rw [rotation_normal_form, rotation_edgeList_normal_form]
  decide +kernel

private theorem vertexRow_67 : vertexRowValid 67 := by
  unfold vertexRowValid
  simp only [graph_adj_iff]
  rw [rotation_normal_form, rotation_edgeList_normal_form]
  decide +kernel

private theorem vertexRow_68 : vertexRowValid 68 := by
  unfold vertexRowValid
  simp only [graph_adj_iff]
  rw [rotation_normal_form, rotation_edgeList_normal_form]
  decide +kernel

private theorem vertexRow_69 : vertexRowValid 69 := by
  unfold vertexRowValid
  simp only [graph_adj_iff]
  rw [rotation_normal_form, rotation_edgeList_normal_form]
  decide +kernel

private theorem vertexRow_70 : vertexRowValid 70 := by
  unfold vertexRowValid
  simp only [graph_adj_iff]
  rw [rotation_normal_form, rotation_edgeList_normal_form]
  decide +kernel

private theorem vertexRow_71 : vertexRowValid 71 := by
  unfold vertexRowValid
  simp only [graph_adj_iff]
  rw [rotation_normal_form, rotation_edgeList_normal_form]
  decide +kernel

private theorem vertexRow_72 : vertexRowValid 72 := by
  unfold vertexRowValid
  simp only [graph_adj_iff]
  rw [rotation_normal_form, rotation_edgeList_normal_form]
  decide +kernel

private theorem vertexRow_73 : vertexRowValid 73 := by
  unfold vertexRowValid
  simp only [graph_adj_iff]
  rw [rotation_normal_form, rotation_edgeList_normal_form]
  decide +kernel

private theorem vertexRow_74 : vertexRowValid 74 := by
  unfold vertexRowValid
  simp only [graph_adj_iff]
  rw [rotation_normal_form, rotation_edgeList_normal_form]
  decide +kernel

private theorem vertexRow_75 : vertexRowValid 75 := by
  unfold vertexRowValid
  simp only [graph_adj_iff]
  rw [rotation_normal_form, rotation_edgeList_normal_form]
  decide +kernel

private theorem vertexRow_76 : vertexRowValid 76 := by
  unfold vertexRowValid
  simp only [graph_adj_iff]
  rw [rotation_normal_form, rotation_edgeList_normal_form]
  decide +kernel

private theorem vertexRow_77 : vertexRowValid 77 := by
  unfold vertexRowValid
  simp only [graph_adj_iff]
  rw [rotation_normal_form, rotation_edgeList_normal_form]
  decide +kernel

private theorem vertexRow_78 : vertexRowValid 78 := by
  unfold vertexRowValid
  simp only [graph_adj_iff]
  rw [rotation_normal_form, rotation_edgeList_normal_form]
  decide +kernel

private theorem vertexRow_79 : vertexRowValid 79 := by
  unfold vertexRowValid
  simp only [graph_adj_iff]
  rw [rotation_normal_form, rotation_edgeList_normal_form]
  decide +kernel

private theorem vertexRow_80 : vertexRowValid 80 := by
  unfold vertexRowValid
  simp only [graph_adj_iff]
  rw [rotation_normal_form, rotation_edgeList_normal_form]
  decide +kernel

private theorem vertexRow_81 : vertexRowValid 81 := by
  unfold vertexRowValid
  simp only [graph_adj_iff]
  rw [rotation_normal_form, rotation_edgeList_normal_form]
  decide +kernel

/-- Complete, distinct, bounded neighbor cycles, with exact graph incidence.
Each of the 82 independently kernel-checked rows is composed here. -/
theorem rotation_orders : ∀ v : Fin 82, (neighbors rotation v).Nodup ∧
    neighbors rotation v ≠ [] ∧
    (∀ w ∈ neighbors rotation v, w < 82) ∧
    (∀ w : Fin 82, w.val ∈ neighbors rotation v ↔ graph.Adj v w) := by
  change ∀ v, vertexRowValid v
  intro v
  fin_cases v
  · exact vertexRow_0
  · exact vertexRow_1
  · exact vertexRow_2
  · exact vertexRow_3
  · exact vertexRow_4
  · exact vertexRow_5
  · exact vertexRow_6
  · exact vertexRow_7
  · exact vertexRow_8
  · exact vertexRow_9
  · exact vertexRow_10
  · exact vertexRow_11
  · exact vertexRow_12
  · exact vertexRow_13
  · exact vertexRow_14
  · exact vertexRow_15
  · exact vertexRow_16
  · exact vertexRow_17
  · exact vertexRow_18
  · exact vertexRow_19
  · exact vertexRow_20
  · exact vertexRow_21
  · exact vertexRow_22
  · exact vertexRow_23
  · exact vertexRow_24
  · exact vertexRow_25
  · exact vertexRow_26
  · exact vertexRow_27
  · exact vertexRow_28
  · exact vertexRow_29
  · exact vertexRow_30
  · exact vertexRow_31
  · exact vertexRow_32
  · exact vertexRow_33
  · exact vertexRow_34
  · exact vertexRow_35
  · exact vertexRow_36
  · exact vertexRow_37
  · exact vertexRow_38
  · exact vertexRow_39
  · exact vertexRow_40
  · exact vertexRow_41
  · exact vertexRow_42
  · exact vertexRow_43
  · exact vertexRow_44
  · exact vertexRow_45
  · exact vertexRow_46
  · exact vertexRow_47
  · exact vertexRow_48
  · exact vertexRow_49
  · exact vertexRow_50
  · exact vertexRow_51
  · exact vertexRow_52
  · exact vertexRow_53
  · exact vertexRow_54
  · exact vertexRow_55
  · exact vertexRow_56
  · exact vertexRow_57
  · exact vertexRow_58
  · exact vertexRow_59
  · exact vertexRow_60
  · exact vertexRow_61
  · exact vertexRow_62
  · exact vertexRow_63
  · exact vertexRow_64
  · exact vertexRow_65
  · exact vertexRow_66
  · exact vertexRow_67
  · exact vertexRow_68
  · exact vertexRow_69
  · exact vertexRow_70
  · exact vertexRow_71
  · exact vertexRow_72
  · exact vertexRow_73
  · exact vertexRow_74
  · exact vertexRow_75
  · exact vertexRow_76
  · exact vertexRow_77
  · exact vertexRow_78
  · exact vertexRow_79
  · exact vertexRow_80
  · exact vertexRow_81

theorem rotation_cyclic_orders : ∀ v : Fin 82,
    (neighbors rotation v).map (next (neighbors rotation v)) =
      (neighbors rotation v).rotateLeft 1 := by
  rw [rotation_normal_form]
  decide +kernel

theorem rotation_darts_distinct : (darts 82 rotation).Nodup := by
  rw [rotation_normal_form]
  decide +kernel

theorem rotation_reversal : ((darts 82 rotation).map reverse).Perm (darts 82 rotation) := by
  rw [rotation_normal_form]
  decide +kernel

theorem rotation_face_permutation :
    ((darts 82 rotation).map (faceNext rotation)).Perm (darts 82 rotation) := by
  rw [rotation_normal_form]
  decide +kernel

#print axioms rotation_first_face
end Steinberg
