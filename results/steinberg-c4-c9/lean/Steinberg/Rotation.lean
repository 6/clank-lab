import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Steinberg.Data

namespace Steinberg

namespace Rotation

abbrev Dart := Nat × Nat

/-- The outgoing neighbors of a vertex, in the supplied order. -/
def neighbors (r : List (List Nat)) (v : Nat) : List Nat := r[v]?.getD []

/-- Advance exactly one place in a cyclic list. On members of a nonempty
nodup list this is the single cycle specified by the list, not an arbitrary
permutation. The default is immaterial on valid darts. -/
def next (l : List Nat) (v : Nat) : Nat :=
  l[(l.idxOf v + 1) % l.length]?.getD 0

/-- All outgoing darts, in vertex and then neighbor order. -/
def darts (n : Nat) (r : List (List Nat)) : List Dart :=
  (List.range n).flatMap fun v => (neighbors r v).map fun w => (v, w)

theorem mem_darts_iff (n : Nat) (r : List (List Nat)) (u v : Nat) :
    (u, v) ∈ darts n r ↔ u < n ∧ v ∈ neighbors r u := by
  simp [darts, List.mem_flatMap, List.mem_map]

/-- Reverse an oriented edge. -/
def reverse (d : Dart) : Dart := (d.2, d.1)

theorem reverse_reverse (d : Dart) : reverse (reverse d) = d := rfl

/-- First reverse the dart, then advance in the rotation at its new origin. -/
def faceNext (r : List (List Nat)) (d : Dart) : Dart :=
  let e := reverse d
  (e.1, next (neighbors r e.1) e.2)

/-- An explicitly listed, nonempty, simple orbit of `f`. The map equality
checks the closing step too. Distinctness excludes repeated traversals. -/
def IsOrbit (f : Dart → Dart) (l : List Dart) : Prop :=
  l ≠ [] ∧ l.Nodup ∧ l.map f = l.rotateLeft 1

instance (f : Dart → Dart) (l : List Dart) : Decidable (IsOrbit f l) := by
  unfold IsOrbit
  infer_instance

/-- The lists are actual orbits and partition every dart exactly once. -/
def FacePartition (n : Nat) (r : List (List Nat)) (faces : List (List Dart)) : Prop :=
  (∀ l ∈ faces, IsOrbit (faceNext r) l) ∧
  faces.flatten.Nodup ∧ faces.flatten.Perm (darts n r)

instance (n : Nat) (r : List (List Nat)) (faces : List (List Dart)) :
    Decidable (FacePartition n r faces) := by
  unfold FacePartition
  infer_instance

/-- A finite rooted spanning-tree certificate gives genuine Mathlib
connectedness. The decreasing rank excludes cycles of parent pointers. -/
theorem connected_of_parents {n : Nat} (G : SimpleGraph (Fin n))
    (root : Fin n) (rank : Fin n → Nat) (parent : Fin n → Fin n)
    (step : ∀ v, v ≠ root → rank (parent v) < rank v ∧ G.Adj (parent v) v) :
    G.Connected := by
  apply G.connected_iff_exists_forall_reachable.mpr
  refine ⟨root, ?_⟩
  have reach : ∀ k v, rank v = k → G.Reachable root v := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro v hv
      by_cases he : v = root
      · subst v
        exact SimpleGraph.Reachable.refl _
      · have hs := step v he
        exact (ih (rank (parent v)) (hv ▸ hs.1) (parent v) rfl).trans hs.2.reachable
  exact fun v => reach (rank v) v rfl

end Rotation

/-- A spherical combinatorial rotation certificate. Darts are precisely
ordered adjacent vertex pairs. Each complete distinct neighbor list specifies
one cyclic vertex order. Reversal and the derived face successor permute the
darts, whose explicit face orbits partition them. The graph is connected and
V + F = E + 2, with two darts per undirected edge. This predicate is the
combinatorial sphere criterion; no topological realization theorem is claimed. -/
structure HasSphericalRotation {n : Nat} (G : SimpleGraph (Fin n))
    (r : List (List Nat)) : Prop where
  vertex_count : r.length = n
  orders : ∀ v : Fin n, (Rotation.neighbors r v).Nodup ∧
    Rotation.neighbors r v ≠ [] ∧
    (∀ w ∈ Rotation.neighbors r v, w < n) ∧
    (∀ w : Fin n, w.val ∈ Rotation.neighbors r v ↔ G.Adj v w)
  cyclic_orders : ∀ v : Fin n,
    (Rotation.neighbors r v).map (Rotation.next (Rotation.neighbors r v)) =
      (Rotation.neighbors r v).rotateLeft 1
  connected : G.Connected
  dart_distinct : (Rotation.darts n r).Nodup
  reversal : ((Rotation.darts n r).map Rotation.reverse).Perm (Rotation.darts n r)
  face_permutation : ((Rotation.darts n r).map (Rotation.faceNext r)).Perm
    (Rotation.darts n r)
  spherical_faces : ∃ faces : List (List Rotation.Dart),
    Rotation.FacePartition n r faces ∧ n + faces.length = (Rotation.darts n r).length / 2 + 2

/-- No extraneous or missing darts: the natural pair representation is
exactly the ordered adjacent finite vertices. -/
theorem HasSphericalRotation.dart_iff {n : Nat} {G : SimpleGraph (Fin n)}
    {r : List (List Nat)} (h : HasSphericalRotation G r) (u v : Nat) :
    (u, v) ∈ Rotation.darts n r ↔
      ∃ (hu : u < n) (hv : v < n), G.Adj ⟨u, hu⟩ ⟨v, hv⟩ := by
  rw [Rotation.mem_darts_iff]
  constructor
  · rintro ⟨hu, hm⟩
    have hv := (h.orders ⟨u, hu⟩).2.2.1 v hm
    exact ⟨hu, hv, (h.orders ⟨u, hu⟩).2.2.2 ⟨v, hv⟩ |>.mp hm⟩
  · rintro ⟨hu, hv, ha⟩
    exact ⟨hu, (h.orders ⟨u, hu⟩).2.2.2 ⟨v, hv⟩ |>.mpr ha⟩

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- A kernel-proved small List normal form of the exact parsed rotation.
This is a rewrite theorem, not an alternative graph or an assumed input. -/
theorem rotation_normal_form : rotation =
  [
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
   [79, 80, 71]
  ] := by decide +kernel

/-- The analogous proved List normal form of the exact parsed edge lines. -/
theorem rotation_edgeList_normal_form : edgeList =
  [
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
   (80, 81)
  ] := by decide +kernel

end Steinberg
