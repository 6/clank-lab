import Steinberg.RotationIncidence
import Steinberg.RotationCertificate

namespace Steinberg.Rotation.Controls

private def triangleRotation : List (List Nat) := [[1, 2], [0, 2], [0, 1]]
private def triangleFaces : List (List Dart) :=
  [[(0, 1), (1, 2), (2, 0)], [(0, 2), (2, 1), (1, 0)]]

theorem triangle_spherical : HasSphericalRotation (⊤ : SimpleGraph (Fin 3))
    triangleRotation where
  vertex_count := by decide
  orders := by decide
  cyclic_orders := by decide
  connected := connected_of_parents _ 0 Fin.val (fun _ => 0) (by decide)
  dart_distinct := by decide
  reversal := by decide
  face_permutation := by decide
  spherical_faces := ⟨triangleFaces, by decide, by decide⟩

private def planarK4Rotation : List (List Nat) :=
  [[1, 2, 3], [0, 3, 2], [0, 1, 3], [0, 2, 1]]
private def planarK4Faces : List (List Dart) :=
  [[(0, 1), (1, 3), (3, 0)], [(0, 2), (2, 1), (1, 0)],
   [(0, 3), (3, 2), (2, 0)], [(1, 2), (2, 3), (3, 1)]]

/-- The same abstract K4 has a spherical rotation with four triangular faces. -/
theorem k4_spherical : HasSphericalRotation (⊤ : SimpleGraph (Fin 4))
    planarK4Rotation where
  vertex_count := by decide +kernel
  orders := by decide +kernel
  cyclic_orders := by decide +kernel
  connected := connected_of_parents _ 0 Fin.val (fun _ => 0) (by decide +kernel)
  dart_distinct := by decide +kernel
  reversal := by decide +kernel
  face_permutation := by decide +kernel
  spherical_faces := ⟨planarK4Faces, by decide +kernel, by decide +kernel⟩

/-- Sorted cyclic orders at K4 give a torus, with two faces and Euler
characteristic zero. All incidence, orbit and partition checks succeed. -/
private def torusRotation : List (List Nat) :=
  [[1, 2, 3], [0, 2, 3], [0, 1, 3], [0, 1, 2]]
private def torusFaces : List (List Dart) :=
  [[(0, 1), (1, 2), (2, 3), (3, 0)],
   [(0, 2), (2, 1), (1, 3), (3, 2), (2, 0), (0, 3), (3, 1), (1, 0)]]

theorem torus_partition : FacePartition 4 torusRotation torusFaces := by decide

/-- Refutes this exact exhaustive face certificate, not a quantified
negation of `HasSphericalRotation` over all possible face lists. -/
theorem torus_not_spherical_certificate :
    ¬ (FacePartition 4 torusRotation torusFaces ∧
      4 + torusFaces.length = (darts 4 torusRotation).length / 2 + 2) := by decide

/-- A duplicate neighbor is a mathematical incidence/rotation error. -/
theorem duplicate_neighbor_rejected :
    ¬ HasSphericalRotation (⊤ : SimpleGraph (Fin 3)) [[1, 1, 2], [0, 2], [0, 1]] := by
  intro h
  have hn := (h.orders 0).1
  exact (by decide : ¬ ([1, 1, 2] : List Nat).Nodup) hn

/-- First seven actual published rows, used only for the initial timed slice;
not a definition of the common graph or the full rotation. -/
private def actualSlice : List (List Nat) :=
  [[1, 3, 2, 5, 4, 6], [0, 6, 19, 18, 21, 20], [23, 0, 32],
   [33, 0, 24], [28, 0, 34], [35, 0, 29], [1, 0, 60, 61]]

theorem first_actual_face : IsOrbit (faceNext actualSlice) [(0, 1), (1, 6), (6, 0)] := by
  decide

theorem first_actual_row : (neighbors actualSlice 0).Nodup ∧
    ∀ i : Fin 6, next (neighbors actualSlice 0) ((neighbors actualSlice 0)[i.val]?.getD 0) =
      (neighbors actualSlice 0)[(i.val + 1) % 6]?.getD 0 := by decide

#print axioms triangle_spherical
#print axioms k4_spherical
#print axioms torus_not_spherical_certificate
#print axioms duplicate_neighbor_rejected
#print axioms first_actual_face

end Steinberg.Rotation.Controls

namespace Steinberg

/-- The exact parsed published graph has the exact published spherical
rotation: complete vertex cycles, connectedness, a partition into 56 actual
face orbits of successor after reversal, and 82 + 56 = 136 + 2. -/
theorem has_spherical_rotation : HasSphericalRotation graph rotation where
  vertex_count := rotation_length
  orders := rotation_orders
  cyclic_orders := rotation_cyclic_orders
  connected := rotation_graph_connected
  dart_distinct := rotation_darts_distinct
  reversal := rotation_reversal
  face_permutation := rotation_face_permutation
  spherical_faces := ⟨sphericalFaces, sphericalFaces_partition, spherical_rotation_euler⟩

/-- The actual numeric Euler identity, using the parsed edge-list count. -/
theorem spherical_rotation_euler_numbers : 82 + 56 = edgeList.length + 2 := by
  rw [edgeList_length]

/-- info: 'Steinberg.has_spherical_rotation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms has_spherical_rotation

example : HasSphericalRotation graph rotation := has_spherical_rotation

end Steinberg
