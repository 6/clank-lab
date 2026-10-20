import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.InnerProductSpace.Convex
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Logic.Relation

/-!
# The common cell-transport core of Case B

This module formalizes the product lemma in the type-(i) proof of `thm:s1`,
the type-(ii) cell partition, and the translate arguments in `thm:paired`
(the manuscript, sections `sec:s1` and the paired theorem).

A `CellSystem` supplies only a finite vertex set, cells containing their
indexing vertices and contained in that set, connectedness, and an edgewise
transport rule. Perpendicularity in that rule is measured against differences
of points of the *current* cell. No fixed global direction, global translation
set, product, or case-specific classification is an input.

The missing geometric instantiations are the paper's uniqueness of the
selected large face / antiprism cell / duoprism facet, construction of the
lateral translate from an actual prism or duoprism, exhaustion of neighbours,
and connectivity of the polytope graph. These are not proved here. Cells are
sets of vertices, rather than filled polygons; their convex hulls are taken
only after the vertex-set factorization has been proved.

The extension proves extremality of both factors from extremality or
cosphericity of the original vertices. `CellSymmetry` supplies only an ambient
affine isometry preserving vertices and the selected cells. Its action on the
normal subspace, offsets, and their convex hull is derived; ambient vertex
transitivity then descends to the offsets. Factor dimension, edge/face
inheritance and uniform/regular-polygon classification are not asserted.
-/

namespace Uniform5.CaseB

open Set
open scoped Pointwise RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Vectors perpendicular to every difference of two points of a cell. -/
noncomputable def normals (C : Set E) : Submodule ℝ E where
  carrier := {d | ∀ a ∈ C, ∀ b ∈ C, ⟪a - b, d⟫ = 0}
  zero_mem' := by simp
  add_mem' := by
    intro d e hd he a ha b hb
    simp only [inner_add_right, hd a ha b hb, he a ha b hb, add_zero]
  smul_mem' := by
    intro c d hd a ha b hb
    simp only [inner_smul_right, hd a ha b hb, mul_zero]

/-- Translation of a set of cell vertices. -/
noncomputable def translate (C : Set E) (d : E) : Set E := (fun a => a + d) '' C

omit [InnerProductSpace ℝ E] in
@[simp] theorem translate_zero (C : Set E) : translate C 0 = C := by
  simp [translate]

omit [InnerProductSpace ℝ E] in
theorem translate_translate (C : Set E) (d e : E) :
    translate (translate C d) e = translate C (d + e) := by
  simp only [translate, image_image, Function.comp_def, add_assoc]

@[simp] theorem normals_translate (C : Set E) (d : E) :
    normals (translate C d) = normals C := by
  ext e
  change (∀ a ∈ translate C d, ∀ b ∈ translate C d, ⟪a - b, e⟫ = 0) ↔ _
  constructor
  · intro h a ha b hb
    have h' := h (a + d) ⟨a, ha, rfl⟩ (b + d) ⟨b, hb, rfl⟩
    simpa only [add_sub_add_right_eq_sub] using h'
  · rintro h _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    simpa only [add_sub_add_right_eq_sub] using h a ha b hb

/-- A linear functional constant on a set is constant on its convex hull. -/
theorem inner_constant_on_convexHull {C : Set E} {d : E} {c : ℝ}
    (h : ∀ a ∈ C, ⟪a, d⟫ = c) :
    ∀ a ∈ convexHull ℝ C, ⟪a, d⟫ = c := by
  apply convexHull_min h
  intro a ha b hb s t _ _ hst
  change ⟪s • a + t • b, d⟫ = c
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, ha, hb,
    ← add_mul, hst, one_mul]

/-- Taking the convex hull does not change the cell's perpendicular vectors. -/
@[simp] theorem normals_convexHull (C : Set E) :
    normals (convexHull ℝ C) = normals C := by
  ext d
  constructor
  · intro hd a ha b hb
    exact hd a (subset_convexHull ℝ C ha) b (subset_convexHull ℝ C hb)
  · intro hd
    rcases C.eq_empty_or_nonempty with hC | ⟨r, hr⟩
    · subst C
      simp only [convexHull_empty]
      exact hd
    · have hc : ∀ a ∈ convexHull ℝ C, ⟪a, d⟫ = ⟪r, d⟫ :=
        inner_constant_on_convexHull (fun a ha => by
          have h := hd a ha r hr
          rw [inner_sub_left, sub_eq_zero] at h
          exact h)
      intro a ha b hb
      rw [inner_sub_left, hc a ha, hc b hb, sub_self]

/-- Orthogonality makes addition injective on the Cartesian product of the
cell with any set of normal offsets. This is an affine product: the cell
need not have been centered at the origin. -/
theorem sum_injOn {C X : Set E} (hX : X ⊆ normals C) :
    Set.InjOn (fun p : E × E => p.1 + p.2) (C ×ˢ X) := by
  rintro ⟨a, d⟩ had ⟨b, e⟩ hbe h
  change a + d = b + e at h
  have hsub : a - b = e - d := by
    calc
      a - b = (a + d) - (b + d) := by abel
      _ = (b + e) - (b + d) := by rw [h]
      _ = e - d := by abel
  have hn : a - b ∈ normals C := by
    rw [hsub]
    exact (normals C).sub_mem (hX hbe.2) (hX had.2)
  have hab : a = b := sub_eq_zero.mp (inner_self_eq_zero.mp (hn a had.1 b hbe.1))
  have hde : d = e := by simpa only [hab, add_left_cancel_iff] using h
  exact Prod.ext hab hde

/-- Addition identifies the Cartesian product with the Minkowski sum. -/
theorem sum_bijOn {C X : Set E} (hX : X ⊆ normals C) :
    Set.BijOn (fun p : E × E => p.1 + p.2) (C ×ˢ X) (C + X) := by
  refine ⟨?_, sum_injOn hX, ?_⟩
  · intro p hp
    exact Set.mem_add.mpr ⟨p.1, hp.1, p.2, hp.2, rfl⟩
  · intro z hz
    obtain ⟨a, ha, d, hd, h⟩ := Set.mem_add.mp hz
    exact ⟨(a, d), ⟨ha, hd⟩, h⟩

/-- A nonempty cell has a unique offset among its normal translates. -/
theorem normal_translate_eq_iff {C : Set E} (hC : C.Nonempty)
    {d e : E} (hd : d ∈ normals C) (he : e ∈ normals C) :
    translate C d = translate C e ↔ d = e := by
  refine ⟨?_, fun h => h ▸ rfl⟩
  intro h
  obtain ⟨a, ha⟩ := hC
  have ha' : a + d ∈ translate C e := by
    rw [← h]
    exact ⟨a, ha, rfl⟩
  obtain ⟨b, hb, hb'⟩ := ha'
  have hp := sum_injOn (C := C) (X := (normals C : Set E)) (fun _ h => h)
    (show (a, d) ∈ _ from ⟨ha, hd⟩) (show (b, e) ∈ _ from ⟨hb, he⟩) hb'.symm
  exact congrArg Prod.snd hp

/-- If a point of the root cell occurs in the sum, its offset must be zero. -/
theorem zero_mem_offsets {C X : Set E} (hX : X ⊆ normals C)
    {r : E} (hr : r ∈ C) (hrsum : r ∈ C + X) : 0 ∈ X := by
  obtain ⟨a, ha, d, hd, had⟩ := Set.mem_add.mp hrsum
  have hp := sum_injOn (C := C) (X := (normals C : Set E)) (fun _ h => h)
    (show (a, d) ∈ _ from ⟨ha, hX hd⟩)
    (show (r, 0) ∈ _ from ⟨hr, (normals C).zero_mem⟩)
    (by simpa only [add_zero] using had)
  have hd0 : d = 0 := congrArg Prod.snd hp
  exact hd0 ▸ hd

/-- The product identification also has the Euclidean product distance law.
The ordinary Lean product norm is a maximum norm, so this squared-distance
identity states the intended orthogonal metric identification explicitly. -/
theorem sum_dist_sq {C X : Set E} (hX : X ⊆ normals C)
    {a b d e : E} (ha : a ∈ C) (hb : b ∈ C) (hd : d ∈ X) (he : e ∈ X) :
    dist (a + d) (b + e) ^ 2 = dist a b ^ 2 + dist d e ^ 2 := by
  simp only [dist_eq_norm]
  have hsub : (a + d) - (b + e) = (a - b) + (d - e) := by abel
  rw [hsub]
  simpa only [pow_two] using
    norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _
      ((normals C).sub_mem (hX hd) (hX he) a ha b hb)

/-- A concrete equivalence of the two factors with their orthogonal sum. -/
noncomputable def sumEquiv (C X : Set E) (hX : X ⊆ normals C) :
    (C × X) ≃ (C + X : Set E) :=
  Equiv.ofBijective
    (fun p => ⟨p.1.1 + p.2.1, Set.mem_add.mpr ⟨_, p.1.2, _, p.2.2, rfl⟩⟩)
    ⟨by
      intro p q hpq
      have h := sum_injOn hX (show (p.1.1, p.2.1) ∈ C ×ˢ X from ⟨p.1.2, p.2.2⟩)
        (show (q.1.1, q.2.1) ∈ C ×ˢ X from ⟨q.1.2, q.2.2⟩) (congrArg Subtype.val hpq)
      exact Prod.ext (Subtype.ext (congrArg Prod.fst h))
        (Subtype.ext (congrArg Prod.snd h)), by
      intro z
      obtain ⟨a, ha, d, hd, h⟩ := Set.mem_add.mp z.2
      exact ⟨(⟨a, ha⟩, ⟨d, hd⟩), Subtype.ext h⟩⟩

/-- Convex combinations of normal offsets are still normal to the filled
cell. No dimension or completeness assumptions are needed. -/
theorem convexHull_normal_subset {C X : Set E} (hX : X ⊆ normals C) :
    convexHull ℝ X ⊆ normals (convexHull ℝ C) := by
  rw [normals_convexHull]
  exact convexHull_min hX (normals C).convex

/-- The hull of a Minkowski sum is an orthogonal Cartesian product of hulls. -/
theorem convexHull_product {C X : Set E} (hX : X ⊆ normals C) :
    Set.BijOn (fun p : E × E => p.1 + p.2)
      (convexHull ℝ C ×ˢ convexHull ℝ X) (convexHull ℝ (C + X)) := by
  rw [convexHull_add]
  exact sum_bijOn (convexHull_normal_subset hX)

/-- A cospherical set consists of extreme points of its own convex hull.
This includes radius zero and needs neither finiteness nor a specified center
inside the hull. -/
theorem cospherical_extremePoints {V : Set E} {c : E} {R : ℝ}
    (hsphere : V ⊆ Metric.sphere c R) :
    V ⊆ (convexHull ℝ V).extremePoints ℝ := by
  have hball : convexHull ℝ V ⊆ Metric.closedBall c R :=
    convexHull_min (hsphere.trans Metric.sphere_subset_closedBall) (convex_closedBall c R)
  intro x hx
  apply mem_extremePoints_iff_left.mpr
  refine ⟨subset_convexHull ℝ V hx, ?_⟩
  intro u hu v hv hseg
  by_cases huv : u = v
  · subst v
    have hxu : x = u := by simpa only [openSegment_same, mem_singleton_iff] using hseg
    exact hxu.symm
  · have hin := openSegment_subset_ball_of_ne (hball hu) (hball hv) huv hseg
    have heq := Metric.mem_sphere.mp (hsphere hx)
    have hlt := Metric.mem_ball.mp hin
    rw [heq] at hlt
    exact False.elim ((lt_irrefl R) hlt)

/-- Extremality of every original vertex forces extremality of every offset.
The hypothesis concerns the full vertex set `C + X`, never X itself. This
lemma is also useful without orthogonality. -/
theorem right_factor_extremePoints {C X : Set E} (hC : C.Nonempty)
    (hvertices : C + X ⊆ (convexHull ℝ (C + X)).extremePoints ℝ) :
    X ⊆ (convexHull ℝ X).extremePoints ℝ := by
  obtain ⟨a, ha⟩ := hC
  intro d hd
  have hext := hvertices (Set.mem_add.mpr ⟨a, ha, d, hd, rfl⟩)
  apply mem_extremePoints_iff_left.mpr
  refine ⟨subset_convexHull ℝ X hd, ?_⟩
  intro u hu v hv hseg
  have hsum (z : E) (hz : z ∈ convexHull ℝ X) : a + z ∈ convexHull ℝ (C + X) := by
    rw [convexHull_add]
    exact Set.mem_add.mpr ⟨a, subset_convexHull ℝ C ha, z, hz, rfl⟩
  have hseg' : a + d ∈ openSegment ℝ (a + u) (a + v) :=
    (mem_openSegment_translate ℝ a).mpr hseg
  exact add_left_cancel (hext.2 (hsum u hu) (hsum v hv) hseg').1

/-- Both factor sets are exactly the vertices (extreme points) of their hulls,
provided the original vertices are extreme. -/
theorem factor_extremePoints {C X : Set E} (hC : C.Nonempty) (hX : X.Nonempty)
    (hvertices : C + X ⊆ (convexHull ℝ (C + X)).extremePoints ℝ) :
    (convexHull ℝ C).extremePoints ℝ = C ∧
      (convexHull ℝ X).extremePoints ℝ = X := by
  refine ⟨Subset.antisymm extremePoints_convexHull_subset ?_,
    Subset.antisymm extremePoints_convexHull_subset (right_factor_extremePoints hC hvertices)⟩
  apply right_factor_extremePoints hX
  simpa only [add_comm X C] using hvertices

/-- Local geometric interface shared by the polygon, antiprism and duoprism
arguments. The graph can be oriented: only the stated directed paths are used.
Finiteness of each cell follows from `cell_subset` and `finite_vertices`. -/
structure CellSystem (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  vertices : Set E
  finite_vertices : vertices.Finite
  cell : E → Set E
  self_mem : ∀ t ∈ vertices, t ∈ cell t
  cell_subset : ∀ t ∈ vertices, cell t ⊆ vertices
  edge : E → E → Prop
  connected : ∀ r ∈ vertices, ∀ t ∈ vertices, Relation.ReflTransGen edge r t
  local_transport : ∀ {t u}, edge t u →
    cell u = cell t ∨ ∃ d ∈ normals (cell t), cell u = translate (cell t) d

namespace CellSystem

variable (D : CellSystem E)

theorem finite_cell {t : E} (ht : t ∈ D.vertices) : (D.cell t).Finite :=
  D.finite_vertices.subset (D.cell_subset t ht)

/-- The genuine propagation step: local normal spaces are transported too,
so the successive displacements sum in the root cell's normal subspace. -/
theorem translate_of_path {r t : E} (h : Relation.ReflTransGen D.edge r t) :
    ∃ d ∈ normals (D.cell r), D.cell t = translate (D.cell r) d := by
  induction h with
  | refl => exact ⟨0, (normals _).zero_mem, (translate_zero _).symm⟩
  | @tail t u _ htu ih =>
    obtain ⟨d, hd, ht⟩ := ih
    rcases D.local_transport htu with heq | ⟨e, he, hu⟩
    · exact ⟨d, hd, heq.trans ht⟩
    · have he' : e ∈ normals (D.cell r) := by
        simpa only [ht, normals_translate] using he
      exact ⟨d + e, (normals _).add_mem hd he', by
        rw [hu, ht, translate_translate]⟩

/-- Every cell is a normal translate of the root cell, proved from edges. -/
theorem global_translate {r : E} (hr : r ∈ D.vertices) {t : E}
    (ht : t ∈ D.vertices) :
    ∃ d ∈ normals (D.cell r), D.cell t = translate (D.cell r) d :=
  D.translate_of_path (D.connected r hr t ht)

/-- The normal displacement is independent of the chosen graph path. -/
theorem global_translate_unique {r : E} (hr : r ∈ D.vertices) {t : E}
    (ht : t ∈ D.vertices) :
    ∃! d, d ∈ normals (D.cell r) ∧ D.cell t = translate (D.cell r) d := by
  obtain ⟨d, hd, htd⟩ := D.global_translate hr ht
  refine ⟨d, ⟨hd, htd⟩, ?_⟩
  intro e he
  exact (normal_translate_eq_iff ⟨r, D.self_mem r hr⟩ he.1 hd).mp
    (he.2.symm.trans htd)

/-- The unique proved displacement of an indexed cell from the root. -/
noncomputable def offset {r : E} (hr : r ∈ D.vertices) (t : D.vertices) : E :=
  Classical.choose (D.global_translate hr t.2)

theorem offset_mem {r : E} (hr : r ∈ D.vertices) (t : D.vertices) :
    D.offset hr t ∈ normals (D.cell r) :=
  (Classical.choose_spec (D.global_translate hr t.2)).1

theorem cell_eq_translate_offset {r : E} (hr : r ∈ D.vertices) (t : D.vertices) :
    D.cell t = translate (D.cell r) (D.offset hr t) :=
  (Classical.choose_spec (D.global_translate hr t.2)).2

/-- The canonical finite offset set. Its construction uses the proved local
transport theorem, rather than a global product hypothesis. -/
noncomputable def offsets {r : E} (hr : r ∈ D.vertices) : Set E := range (D.offset hr)

theorem offsets_finite {r : E} (hr : r ∈ D.vertices) : (D.offsets hr).Finite := by
  classical
  letI := D.finite_vertices.fintype
  exact finite_range _

theorem offsets_nonempty {r : E} (hr : r ∈ D.vertices) : (D.offsets hr).Nonempty :=
  ⟨D.offset hr ⟨r, hr⟩, mem_range_self _⟩

theorem offsets_normal {r : E} (hr : r ∈ D.vertices) :
    D.offsets hr ⊆ normals (D.cell r) := by
  rintro _ ⟨t, rfl⟩
  exact D.offset_mem hr t

/-- The propagated cells really form a partition: intersecting cells agree.
This is derived from local transport and orthogonality, not postulated. -/
theorem cell_eq_of_common_point {r t u z : E} (hr : r ∈ D.vertices)
    (ht : t ∈ D.vertices) (hu : u ∈ D.vertices)
    (hzt : z ∈ D.cell t) (hzu : z ∈ D.cell u) : D.cell t = D.cell u := by
  obtain ⟨d, hd, htd⟩ := D.global_translate hr ht
  obtain ⟨e, he, hue⟩ := D.global_translate hr hu
  rw [htd] at hzt
  rw [hue] at hzu
  obtain ⟨a, ha, haz⟩ := hzt
  obtain ⟨b, hb, hbz⟩ := hzu
  have h := sum_injOn (C := D.cell r) (X := (normals (D.cell r) : Set E))
    (fun _ h => h) (show (a, d) ∈ _ from ⟨ha, hd⟩)
    (show (b, e) ∈ _ from ⟨hb, he⟩) (haz.trans hbz.symm)
  have hde : d = e := congrArg Prod.snd h
  rw [htd, hue, hde]

/-- The usual cell-partition statement at an indexing vertex. -/
theorem cell_eq_of_mem {r t u : E} (hr : r ∈ D.vertices)
    (ht : t ∈ D.vertices) (hu : u ∈ D.cell t) : D.cell u = D.cell t :=
  D.cell_eq_of_common_point hr (D.cell_subset t ht hu) ht
    (D.self_mem u (D.cell_subset t ht hu)) hu

/-- A finite translation set is constructed by choosing one proved offset per
vertex. Both inclusions in the Minkowski equality use the local cell coverage
facts, rather than an assumed global factorization. -/
theorem finite_minkowski_factorization {r : E} (hr : r ∈ D.vertices) :
    ∃ X : Set E, X.Finite ∧ X.Nonempty ∧ X ⊆ normals (D.cell r) ∧
      D.vertices = D.cell r + X ∧
      (∀ t ∈ D.vertices, ∃ d ∈ X, D.cell t = translate (D.cell r) d) := by
  classical
  letI := D.finite_vertices.fintype
  let f : D.vertices → E := fun t => Classical.choose (D.global_translate hr t.2)
  have hf (t : D.vertices) : f t ∈ normals (D.cell r) ∧
      D.cell t = translate (D.cell r) (f t) :=
    Classical.choose_spec (D.global_translate hr t.2)
  refine ⟨range f, finite_range f, ⟨f ⟨r, hr⟩, mem_range_self _⟩, ?_, ?_, ?_⟩
  · rintro _ ⟨t, rfl⟩
    exact (hf t).1
  · apply Subset.antisymm
    · intro t ht
      have hmem : t ∈ translate (D.cell r) (f ⟨t, ht⟩) := by
        rw [← (hf ⟨t, ht⟩).2]
        exact D.self_mem t ht
      obtain ⟨a, ha, hat⟩ := hmem
      exact Set.mem_add.mpr ⟨a, ha, f ⟨t, ht⟩, mem_range_self _, hat⟩
    · intro t ht
      obtain ⟨a, ha, d, ⟨u, rfl⟩, rfl⟩ := Set.mem_add.mp ht
      apply D.cell_subset u u.2
      rw [(hf u).2]
      exact ⟨a, ha, rfl⟩
  · intro t ht
    exact ⟨f ⟨t, ht⟩, mem_range_self _, (hf ⟨t, ht⟩).2⟩

/-- The convex hull is the sum of the two convex hulls; the finite offset set
and its perpendicularity are conclusions, not fields of `CellSystem`. -/
theorem convexHull_factorization {r : E} (hr : r ∈ D.vertices) :
    ∃ X : Set E, X.Finite ∧ X.Nonempty ∧ X ⊆ normals (D.cell r) ∧
      D.vertices = D.cell r + X ∧
      convexHull ℝ D.vertices = convexHull ℝ (D.cell r) + convexHull ℝ X := by
  obtain ⟨X, hfin, hne, hn, hsum, _⟩ := D.finite_minkowski_factorization hr
  exact ⟨X, hfin, hne, hn, hsum, by rw [hsum, convexHull_add]⟩

/-- The entire convex hull is a genuine orthogonal product: addition is
bijective on the Cartesian product of the two hulls and obeys the squared
Euclidean distance law. This is the common conclusion of the paper's
translate arguments before classifying the remaining factor. -/
theorem orthogonal_product {r : E} (hr : r ∈ D.vertices) :
    ∃ X : Set E, X.Finite ∧ X.Nonempty ∧ 0 ∈ X ∧ X ⊆ normals (D.cell r) ∧
      D.vertices = D.cell r + X ∧
      convexHull ℝ D.vertices = convexHull ℝ (D.cell r) + convexHull ℝ X ∧
      Set.BijOn (fun p : E × E => p.1 + p.2)
        (convexHull ℝ (D.cell r) ×ˢ convexHull ℝ X) (convexHull ℝ D.vertices) ∧
      (∀ a ∈ convexHull ℝ (D.cell r), ∀ b ∈ convexHull ℝ (D.cell r),
        ∀ d ∈ convexHull ℝ X, ∀ e ∈ convexHull ℝ X,
        dist (a + d) (b + e) ^ 2 = dist a b ^ 2 + dist d e ^ 2) := by
  obtain ⟨X, hfin, hne, hn, hsum, hhull⟩ := D.convexHull_factorization hr
  have hz : 0 ∈ X := zero_mem_offsets hn (D.self_mem r hr) (hsum ▸ hr)
  refine ⟨X, hfin, hne, hz, hn, hsum, hhull, ?_, ?_⟩
  · rw [hsum]
    exact convexHull_product hn
  · intro a ha b hb d hd e he
    exact sum_dist_sq (convexHull_normal_subset hn) ha hb hd he

/-- The canonical offsets give the same proved factorization. -/
theorem vertices_eq_cell_add_offsets {r : E} (hr : r ∈ D.vertices) :
    D.vertices = D.cell r + D.offsets hr := by
  apply Subset.antisymm
  · intro t ht
    have hmem : t ∈ translate (D.cell r) (D.offset hr ⟨t, ht⟩) := by
      rw [← D.cell_eq_translate_offset hr ⟨t, ht⟩]
      exact D.self_mem t ht
    obtain ⟨a, ha, hat⟩ := hmem
    exact Set.mem_add.mpr ⟨a, ha, _, mem_range_self _, hat⟩
  · intro z hz
    obtain ⟨a, ha, _, ⟨t, rfl⟩, rfl⟩ := Set.mem_add.mp hz
    apply D.cell_subset t t.2
    rw [D.cell_eq_translate_offset hr t]
    exact ⟨a, ha, rfl⟩

theorem convexHull_eq_cell_add_offsets {r : E} (hr : r ∈ D.vertices) :
    convexHull ℝ D.vertices = convexHull ℝ (D.cell r) + convexHull ℝ (D.offsets hr) := by
  rw [D.vertices_eq_cell_add_offsets hr, convexHull_add]

/-- The canonical offset of the root cell is zero. -/
theorem offsets_zero {r : E} (hr : r ∈ D.vertices) : 0 ∈ D.offsets hr :=
  zero_mem_offsets (D.offsets_normal hr) (D.self_mem r hr)
    (D.vertices_eq_cell_add_offsets hr ▸ hr)

/-- The same canonical factors used for extremality and symmetry carry the
proved orthogonal convex-hull product identification. -/
theorem offsets_hull_product {r : E} (hr : r ∈ D.vertices) :
    Set.BijOn (fun p : E × E => p.1 + p.2)
      (convexHull ℝ (D.cell r) ×ˢ convexHull ℝ (D.offsets hr)) (convexHull ℝ D.vertices) := by
  rw [D.vertices_eq_cell_add_offsets hr]
  exact convexHull_product (D.offsets_normal hr)

/-- The actual-extreme-vertex version of the factor vertex theorem. -/
theorem cell_offsets_extremePoints {r : E} (hr : r ∈ D.vertices)
    (hvertices : D.vertices ⊆ (convexHull ℝ D.vertices).extremePoints ℝ) :
    (convexHull ℝ (D.cell r)).extremePoints ℝ = D.cell r ∧
      (convexHull ℝ (D.offsets hr)).extremePoints ℝ = D.offsets hr := by
  apply factor_extremePoints ⟨r, D.self_mem r hr⟩ (D.offsets_nonempty hr)
  rwa [← D.vertices_eq_cell_add_offsets hr]

/-- In particular, cosphericity of the original vertices proves that all
points of both factors are vertices. No extremality assumption on X occurs. -/
theorem cell_offsets_extremePoints_of_cospherical {r : E} (hr : r ∈ D.vertices)
    {c : E} {R : ℝ} (hsphere : D.vertices ⊆ Metric.sphere c R) :
    (convexHull ℝ (D.cell r)).extremePoints ℝ = D.cell r ∧
      (convexHull ℝ (D.offsets hr)).extremePoints ℝ = D.offsets hr :=
  D.cell_offsets_extremePoints hr (cospherical_extremePoints hsphere)

end CellSystem

/-- An ambient symmetry preserving the actual selected cells. There is no
assumed offset action or preserved global direction in this interface. -/
structure CellSymmetry (D : CellSystem E) where
  point : E ≃ᵃⁱ[ℝ] E
  vertices_image : point '' D.vertices = D.vertices
  cells_image : ∀ t ∈ D.vertices, point '' D.cell t = D.cell (point t)

namespace CellSymmetry

variable {D : CellSystem E} (g : CellSymmetry D)

theorem point_mem {t : E} (ht : t ∈ D.vertices) : g.point t ∈ D.vertices := by
  rw [← g.vertices_image]
  exact mem_image_of_mem _ ht

/-- The induced permutation on the original vertices, before taking offsets. -/
noncomputable def vertexMap (t : D.vertices) : D.vertices := ⟨g.point t, g.point_mem t.2⟩

/-- Affine isometries take translated cells to translates by the linear part. -/
theorem image_translate (C : Set E) (d : E) :
    g.point '' translate C d = translate (g.point '' C) (g.point.linearIsometryEquiv d) := by
  unfold translate
  rw [image_image, image_image]
  apply congrArg (fun f : E → E => f '' C)
  funext a
  have h := g.point.map_vadd a d
  change g.point (d + a) = g.point.linearIsometryEquiv d + g.point a at h
  simpa only [Function.comp_apply, add_comm] using h

/-- Normal directions transform by the ambient linear isometry. -/
theorem linear_normal_iff (C : Set E) (d : E) :
    g.point.linearIsometryEquiv d ∈ normals (g.point '' C) ↔ d ∈ normals C := by
  constructor
  · intro hd a ha b hb
    have h := hd (g.point a) ⟨a, ha, rfl⟩ (g.point b) ⟨b, hb, rfl⟩
    have hmap : g.point.linearIsometryEquiv (a - b) = g.point a - g.point b :=
      g.point.map_vsub a b
    rw [← hmap, g.point.linearIsometryEquiv.inner_map_map] at h
    exact h
  · intro hd
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have hmap : g.point.linearIsometryEquiv (a - b) = g.point a - g.point b :=
      g.point.map_vsub a b
    rw [← hmap, g.point.linearIsometryEquiv.inner_map_map]
    exact hd a ha b hb

/-- Preserving cells forces preservation of the root normal subspace. -/
theorem linear_preserves_normal {r : E} (hr : r ∈ D.vertices) (d : E) :
    g.point.linearIsometryEquiv d ∈ normals (D.cell r) ↔ d ∈ normals (D.cell r) := by
  have hcell : g.point '' D.cell r =
      translate (D.cell r) (D.offset hr (g.vertexMap ⟨r, hr⟩)) :=
    (g.cells_image r hr).trans (D.cell_eq_translate_offset hr (g.vertexMap ⟨r, hr⟩))
  have h := g.linear_normal_iff (D.cell r) d
  rwa [hcell, normals_translate] at h

/-- The actual descended ambient affine isometry on offset coordinates. Its
translation is the proved offset of the image root cell, and its linear part
is inherited from the original ambient symmetry. -/
noncomputable def offsetAction {r : E} (hr : r ∈ D.vertices) : E ≃ᵃⁱ[ℝ] E :=
  g.point.linearIsometryEquiv.toAffineIsometryEquiv.trans
    (AffineIsometryEquiv.constVAdd ℝ E (D.offset hr (g.vertexMap ⟨r, hr⟩)))

theorem offsetAction_apply {r : E} (hr : r ∈ D.vertices) (d : E) :
    g.offsetAction hr d =
      D.offset hr (g.vertexMap ⟨r, hr⟩) + g.point.linearIsometryEquiv d := rfl

/-- Offset transport is proved from cell transport, with no hypothesized
factor symmetry. -/
theorem offset_vertexMap {r : E} (hr : r ∈ D.vertices) (t : D.vertices) :
    D.offset hr (g.vertexMap t) = g.offsetAction hr (D.offset hr t) := by
  have hn : g.offsetAction hr (D.offset hr t) ∈ normals (D.cell r) := by
    rw [g.offsetAction_apply]
    exact (normals _).add_mem (D.offset_mem hr _)
      ((g.linear_preserves_normal hr _).mpr (D.offset_mem hr t))
  have ht : D.cell (g.vertexMap t) =
      translate (D.cell r) (g.offsetAction hr (D.offset hr t)) := by
    change D.cell (g.point t) = _
    have hroot : D.cell (g.point r) =
        translate (D.cell r) (D.offset hr (g.vertexMap ⟨r, hr⟩)) :=
      D.cell_eq_translate_offset hr (g.vertexMap ⟨r, hr⟩)
    rw [← g.cells_image t t.2, D.cell_eq_translate_offset hr t,
      g.image_translate, g.cells_image r hr, hroot,
      translate_translate, g.offsetAction_apply]
  exact (normal_translate_eq_iff ⟨r, D.self_mem r hr⟩
    (D.offset_mem hr (g.vertexMap t)) hn).mp
      ((D.cell_eq_translate_offset hr (g.vertexMap t)).symm.trans ht)

/-- The descended isometry bijects the canonical offset set with itself. -/
theorem offsetAction_bijOn {r : E} (hr : r ∈ D.vertices) :
    Set.BijOn (g.offsetAction hr) (D.offsets hr) (D.offsets hr) := by
  refine ⟨?_, (g.offsetAction hr).injective.injOn, ?_⟩
  · rintro _ ⟨t, rfl⟩
    exact ⟨g.vertexMap t, g.offset_vertexMap hr t⟩
  · rintro _ ⟨t, rfl⟩
    obtain ⟨u, hu, hut⟩ : ∃ u ∈ D.vertices, g.point u = t := by
      have ht : (t : E) ∈ g.point '' D.vertices := by
        rw [g.vertices_image]
        exact t.2
      exact ht
    refine ⟨D.offset hr ⟨u, hu⟩, mem_range_self _, ?_⟩
    rw [← g.offset_vertexMap hr]
    congr 1
    exact Subtype.ext hut

/-- The same ambient affine isometry preserves the remaining convex factor. -/
theorem offsetAction_hull_image {r : E} (hr : r ∈ D.vertices) :
    g.offsetAction hr '' convexHull ℝ (D.offsets hr) = convexHull ℝ (D.offsets hr) := by
  have h := (g.offsetAction hr).toAffineEquiv.toAffineMap.image_convexHull (D.offsets hr)
  change g.offsetAction hr '' convexHull ℝ (D.offsets hr) =
    convexHull ℝ (g.offsetAction hr '' D.offsets hr) at h
  rw [(g.offsetAction_bijOn hr).image_eq] at h
  exact h

/-- An actual isometry equivalence on the finite offset set. -/
noncomputable def offsetsIsometry {r : E} (hr : r ∈ D.vertices) :
    D.offsets hr ≃ᵢ D.offsets hr where
  toEquiv := Equiv.ofBijective
    (fun x => ⟨g.offsetAction hr x, (g.offsetAction_bijOn hr).mapsTo x.2⟩)
    ⟨by
      intro x y h
      apply Subtype.ext
      exact (g.offsetAction hr).injective (congrArg Subtype.val h), by
      intro y
      obtain ⟨x, hx, hxy⟩ := (g.offsetAction_bijOn hr).surjOn y.2
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩⟩
  isometry_toFun := by
    intro x y
    exact (g.offsetAction hr).edist_map x y

end CellSymmetry

namespace CellSystem

variable (D : CellSystem E)

/-- Vertex transitivity by ambient cell-preserving symmetries descends to
transitivity on the offset vertices by ambient affine isometries preserving
both the offset set and its hull. This asserts no uniformity classification. -/
theorem offsets_transitive {r : E} (hr : r ∈ D.vertices)
    (htrans : ∀ t ∈ D.vertices, ∀ u ∈ D.vertices,
      ∃ g : CellSymmetry D, g.point t = u) :
    ∀ x ∈ D.offsets hr, ∀ y ∈ D.offsets hr,
      ∃ f : E ≃ᵃⁱ[ℝ] E, f '' D.offsets hr = D.offsets hr ∧
        f '' convexHull ℝ (D.offsets hr) = convexHull ℝ (D.offsets hr) ∧ f x = y := by
  rintro _ ⟨t, rfl⟩ _ ⟨u, rfl⟩
  obtain ⟨g, htu⟩ := htrans t t.2 u u.2
  refine ⟨g.offsetAction hr, (g.offsetAction_bijOn hr).image_eq,
    g.offsetAction_hull_image hr, ?_⟩
  rw [← g.offset_vertexMap hr]
  congr 1
  exact Subtype.ext htu

end CellSystem

end Uniform5.CaseB
