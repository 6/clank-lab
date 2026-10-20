import Steinberg.Data

namespace Steinberg

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- A proved cache of the parsed edges, for finite kernel computations. -/
theorem edgeList_value : edgeList = [
  (0, 1),
  (0, 2),
  (0, 3),
  (0, 4),
  (0, 5),
  (0, 6),
  (1, 6),
  (1, 18),
  (1, 19),
  (1, 20),
  (1, 21),
  (2, 23),
  (2, 32),
  (3, 24),
  (3, 33),
  (4, 28),
  (4, 34),
  (5, 29),
  (5, 35),
  (6, 60),
  (6, 61),
  (7, 8),
  (7, 9),
  (7, 10),
  (7, 11),
  (7, 12),
  (7, 13),
  (7, 14),
  (7, 15),
  (7, 16),
  (7, 17),
  (8, 36),
  (8, 40),
  (9, 37),
  (9, 41),
  (10, 42),
  (10, 44),
  (11, 43),
  (11, 45),
  (12, 60),
  (12, 62),
  (13, 61),
  (13, 63),
  (14, 68),
  (14, 72),
  (15, 69),
  (15, 73),
  (16, 74),
  (16, 76),
  (17, 75),
  (17, 77),
  (18, 51),
  (18, 64),
  (19, 52),
  (19, 65),
  (20, 56),
  (20, 66),
  (21, 57),
  (21, 67),
  (22, 23),
  (22, 24),
  (22, 25),
  (22, 26),
  (23, 32),
  (24, 33),
  (25, 26),
  (25, 38),
  (25, 39),
  (26, 42),
  (26, 43),
  (27, 28),
  (27, 29),
  (27, 30),
  (27, 31),
  (28, 34),
  (29, 35),
  (30, 31),
  (30, 36),
  (30, 37),
  (31, 46),
  (31, 47),
  (32, 33),
  (34, 35),
  (36, 40),
  (37, 41),
  (38, 46),
  (38, 48),
  (39, 47),
  (39, 49),
  (40, 41),
  (42, 44),
  (43, 45),
  (44, 45),
  (46, 48),
  (47, 49),
  (48, 49),
  (50, 51),
  (50, 52),
  (50, 53),
  (50, 54),
  (51, 64),
  (52, 65),
  (53, 54),
  (53, 70),
  (53, 71),
  (54, 74),
  (54, 75),
  (55, 56),
  (55, 57),
  (55, 58),
  (55, 59),
  (56, 66),
  (57, 67),
  (58, 59),
  (58, 68),
  (58, 69),
  (59, 78),
  (59, 79),
  (60, 62),
  (61, 63),
  (62, 63),
  (64, 65),
  (66, 67),
  (68, 72),
  (69, 73),
  (70, 78),
  (70, 80),
  (71, 79),
  (71, 81),
  (72, 73),
  (74, 76),
  (75, 77),
  (76, 77),
  (78, 80),
  (79, 81),
  (80, 81)] := by decide +kernel

/-- A proved cache of the parsed cyclic neighbor lists. -/
theorem rotation_value : rotation = [
  [1, 3, 2, 5, 4, 6],
  [0, 6, 19, 18, 21, 20],
  [23, 0, 32],
  [33, 0, 24],
  [28, 0, 34],
  [35, 0, 29],
  [1, 0, 60, 61],
  [12, 8, 9, 11, 10, 14, 15, 17, 16, 13],
  [7, 36, 40],
  [37, 7, 41],
  [42, 7, 44],
  [45, 7, 43],
  [60, 7, 62],
  [7, 61, 63],
  [7, 68, 72],
  [69, 7, 73],
  [74, 7, 76],
  [77, 7, 75],
  [51, 1, 64],
  [65, 1, 52],
  [56, 1, 66],
  [67, 1, 57],
  [25, 23, 24, 26],
  [22, 2, 32],
  [3, 22, 33],
  [38, 22, 26, 39],
  [22, 42, 43, 25],
  [30, 28, 29, 31],
  [27, 4, 34],
  [5, 27, 35],
  [36, 27, 31, 37],
  [27, 46, 47, 30],
  [2, 33, 23],
  [32, 3, 24],
  [4, 35, 28],
  [34, 5, 29],
  [8, 30, 40],
  [30, 9, 41],
  [46, 25, 48],
  [25, 47, 49],
  [41, 8, 36],
  [9, 40, 37],
  [26, 10, 44],
  [11, 26, 45],
  [10, 45, 42],
  [44, 11, 43],
  [31, 38, 48],
  [39, 31, 49],
  [49, 46, 38],
  [47, 48, 39],
  [53, 51, 52, 54],
  [50, 18, 64],
  [19, 50, 65],
  [70, 50, 54, 71],
  [50, 74, 75, 53],
  [58, 56, 57, 59],
  [55, 20, 66],
  [21, 55, 67],
  [68, 55, 59, 69],
  [55, 78, 79, 58],
  [6, 12, 62],
  [13, 6, 63],
  [63, 60, 12],
  [61, 62, 13],
  [18, 65, 51],
  [64, 19, 52],
  [20, 67, 56],
  [66, 21, 57],
  [14, 58, 72],
  [58, 15, 73],
  [78, 53, 80],
  [53, 79, 81],
  [73, 14, 68],
  [15, 72, 69],
  [54, 16, 76],
  [17, 54, 77],
  [16, 77, 74],
  [76, 17, 75],
  [59, 70, 80],
  [71, 59, 81],
  [81, 78, 70],
  [79, 80, 71]] := by decide +kernel

theorem edgeList_bounds (e : Nat × Nat) (he : e ∈ edgeList) : e.1 < 82 ∧ e.2 < 82 := by
  have h := edgeList_canonical e he
  exact ⟨Nat.lt_trans h.1 h.2, h.2⟩

theorem rotation_bounds (row : List Nat) (hr : row ∈ rotation) : ∀ v ∈ row, v < 82 := by
  change row ∈ rotationRows.map List.tail at hr
  obtain ⟨r, hmem, heq⟩ := List.mem_map.mp hr
  subst row
  have h := rotation_checked
  simp only [rotationOK, Bool.and_eq_true, beq_iff_eq] at h
  have hrow := List.all_eq_true.mp h.2.2 r hmem
  simp only [Bool.and_eq_true] at hrow
  intro v hv
  exact of_decide_eq_true (List.all_eq_true.mp hrow.2.1 v hv)

theorem rotation_nodup (row : List Nat) (hr : row ∈ rotation) : row.Nodup := by
  change row ∈ rotationRows.map List.tail at hr
  obtain ⟨r, hmem, heq⟩ := List.mem_map.mp hr
  subst row
  have h := rotation_checked
  simp only [rotationOK, Bool.and_eq_true, beq_iff_eq] at h
  have hrow := List.all_eq_true.mp h.2.2 r hmem
  simp only [Bool.and_eq_true] at hrow
  exact of_decide_eq_true hrow.2.2.1

theorem edge_adj (e : Nat × Nat) (he : e ∈ edgeList) :
    graph.Adj ⟨e.1, (edgeList_bounds e he).1⟩ ⟨e.2, (edgeList_bounds e he).2⟩ := by
  rw [graph_adj_iff]
  constructor
  · intro eq
    exact (Nat.ne_of_lt (edgeList_canonical e he).1) (congrArg Fin.val eq)
  · exact Or.inl he

/-- Replace an actual edge by a loop; validation must mathematically reject it. -/
def loopCorruption : GraphData := { graphData with edges := (0, 0) :: edgeList.tail }

theorem corrupt_graph_false : graphOK loopCorruption = false := by
  simp [graphOK, loopCorruption]

/-- info: 'Steinberg.edgeList_value' depends on axioms: [propext] -/
#guard_msgs in
#print axioms edgeList_value
/-- info: 'Steinberg.rotation_value' does not depend on any axioms -/
#guard_msgs in
#print axioms rotation_value
/-- info: 'Steinberg.corrupt_graph_false' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms corrupt_graph_false

end Steinberg
