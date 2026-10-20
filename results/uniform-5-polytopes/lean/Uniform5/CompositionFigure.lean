import Uniform5.CompositionSection
import Uniform5.CompositionDimension
import Uniform5.CompositionSymmetry

/-!
# Vertex figures of actual unit-edge polytopes

These statements quantify over the geometric hull and its actual vertices.
The defining hyperplane section is proved equal to the neighbor hull.
-/

noncomputable section
namespace Uniform5.Composition
open Set Classical

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual unit-edge vertex-figure section at `v`, for sphere center `c`.
The height functional on displacements has value one at each neighbor. -/
noncomputable def vertexFigure (P : Set E) (v c : E) : Set E :=
  {x ∈ P | sphereHeight (c - v) (x - v) = 1}

/-- Ambient Euclidean isometries carry the actual section to the
corresponding section at the transported center and vertex. -/
theorem vertexFigure_image (g : E ≃ᵃⁱ[ℝ] E) (P : Set E) (v c : E) :
    g '' vertexFigure P v c = vertexFigure (g '' P) (g v) (g c) := by
  have hh (x : E) : sphereHeight (g c - g v) (g x - g v) =
      sphereHeight (c - v) (x - v) := by
    change (2 : ℝ) * inner (g c - g v) (g x - g v) = (2 : ℝ) * inner (c - v) (x - v)
    have hc : g c - g v = g.linearIsometryEquiv (c - v) := (g.map_vsub c v).symm
    have hx : g x - g v = g.linearIsometryEquiv (x - v) := (g.map_vsub x v).symm
    rw [hc, hx, g.linearIsometryEquiv.inner_map_map]
  ext x
  constructor
  · rintro ⟨y, ⟨hy, hyL⟩, rfl⟩
    exact ⟨mem_image_of_mem g hy, (hh y).trans hyL⟩
  · rintro ⟨⟨y, hy, rfl⟩, hyL⟩
    exact ⟨y, ⟨hy, (hh y).symm.trans hyL⟩, rfl⟩

/-- The section at the origin is the hull of actual edge neighbors. -/
theorem finitePolytope_unit_figure_zero {P : Set E} (hP : FinitePolytope P)
    (hzero : (0 : E) ∈ P.extremePoints ℝ) (c : E) (R : ℝ)
    (hsphere : ∀ x ∈ P.extremePoints ℝ, ‖x - c‖ ^ 2 = R ^ 2)
    (hunit : UnitEdges P) :
    vertexFigure P 0 c = convexHull ℝ {z | Edge P 0 z} := by
  have hV := cospherical_unit_section (vertices P hP)
    ((mem_vertices hP 0).mpr hzero)
    (fun x hx => by simpa only [convexHull_vertices] using (mem_vertices hP x).mp hx)
    c R (fun x hx => hsphere x ((mem_vertices hP x).mp hx))
    (fun x y hxy => hunit x y ((edge_iff_vertices_isEdge hP x y).mpr hxy))
  simpa only [vertexFigure, sub_zero, convexHull_vertices,
    ← edge_iff_vertices_isEdge hP] using hV

/-- The same section identity at every actual vertex, with arbitrary
sphere center. Translation supplies the origin normalization. -/
theorem finitePolytope_unit_vertexFigure {P : Set E} (hP : FinitePolytope P)
    {v : E} (hv : v ∈ P.extremePoints ℝ) (c : E) (R : ℝ)
    (hsphere : ∀ x ∈ P.extremePoints ℝ, ‖x - c‖ ^ 2 = R ^ 2)
    (hunit : UnitEdges P) :
    vertexFigure P v c = convexHull ℝ {z | Edge P v z} := by
  let g := AffineIsometryEquiv.constVAdd ℝ E (-v)
  have hg (x : E) : g x = x - v := by simp [g, sub_eq_add_neg, add_comm]
  have hgv : g v = 0 := by rw [hg, sub_self]
  have hz : (0 : E) ∈ (g '' P).extremePoints ℝ := by
    rw [← affineIsometry_image_extremePoints, ← hgv]
    exact mem_image_of_mem g hv
  have hs : ∀ x ∈ (g '' P).extremePoints ℝ, ‖x - (c - v)‖ ^ 2 = R ^ 2 := by
    rw [← affineIsometry_image_extremePoints]
    rintro x ⟨y, hy, rfl⟩
    have heq : g y - (c - v) = y - c := by rw [hg]; abel
    rw [heq]
    exact hsphere y hy
  have hf := finitePolytope_unit_figure_zero (finitePolytope_image g hP)
    hz (c - v) R hs (unitEdges_image g hunit)
  have himage : g '' vertexFigure P v c = vertexFigure (g '' P) 0 (c - v) := by
    ext x
    constructor
    · rintro ⟨y, ⟨hy, hyL⟩, rfl⟩
      exact ⟨mem_image_of_mem g hy, by simpa only [sub_zero, hg] using hyL⟩
    · rintro ⟨⟨y, hy, rfl⟩, hyL⟩
      exact ⟨y, ⟨hy, by simpa only [sub_zero, hg] using hyL⟩, rfl⟩
  have hedges : g '' {z | Edge P v z} = {z | Edge (g '' P) 0 z} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa only [hgv] using edge_image g hy
    · intro hx
      refine ⟨g.symm x, ?_, g.apply_symm_apply x⟩
      apply (edge_image_iff g P v (g.symm x)).mp
      simpa only [hgv, g.apply_symm_apply] using hx
  apply g.injective.image_injective
  rw [himage, hf, ← hedges]
  exact (g.toAffineMap.image_convexHull {z | Edge P v z}).symm

/-- No spurious vertices appear in the section: its actual extreme points
are exactly the actual edge neighbors of the distinguished vertex. -/
theorem finitePolytope_unit_vertexFigure_extremePoints {P : Set E}
    (hP : FinitePolytope P) {v : E} (hv : v ∈ P.extremePoints ℝ) (c : E) (R : ℝ)
    (hsphere : ∀ x ∈ P.extremePoints ℝ, ‖x - c‖ ^ 2 = R ^ 2)
    (hunit : UnitEdges P) :
    (vertexFigure P v c).extremePoints ℝ = {z | Edge P v z} := by
  have hf := finitePolytope_unit_vertexFigure hP hv c R hsphere hunit
  apply Set.Subset.antisymm
  · rw [hf]
    exact extremePoints_convexHull_subset
  · intro z hz
    apply inter_extremePoints_subset_extremePoints_of_subset (A := P)
      (show vertexFigure P v c ⊆ P from fun _ hx => hx.1)
    refine ⟨?_, hz.2.1⟩
    rw [hf]
    exact subset_convexHull ℝ _ hz

/-- A full-dimensional unit-edge polytope's actual vertex figure has
codimension one. The proof derives the spanning and nonemptiness facts. -/
theorem finitePolytope_unit_vertexFigure_dimension [FiniteDimensional ℝ E]
    {P : Set E} (hP : FinitePolytope P) {v : E} (hv : v ∈ P.extremePoints ℝ)
    (c : E) (R : ℝ) (hsphere : ∀ x ∈ P.extremePoints ℝ, ‖x - c‖ ^ 2 = R ^ 2)
    (hunit : UnitEdges P) (hfull : affineDimension P = Module.finrank ℝ E)
    (hpos : 0 < Module.finrank ℝ E) :
    affineDimension (vertexFigure P v c) + 1 = Module.finrank ℝ E := by
  have zero_case {Q : Set E} (hQ : FinitePolytope Q)
      (hz : (0 : E) ∈ Q.extremePoints ℝ) (d : E)
      (hs : ∀ x ∈ Q.extremePoints ℝ, ‖x - d‖ ^ 2 = R ^ 2)
      (hu : UnitEdges Q) (hdim : affineDimension Q = Module.finrank ℝ E) :
      affineDimension (vertexFigure Q 0 d) + 1 = Module.finrank ℝ E := by
    let V := vertices Q hQ
    have hzero : (0 : E) ∈ V := (mem_vertices hQ 0).mpr hz
    have hVs : ∀ x ∈ V, ‖x - d‖ ^ 2 = R ^ 2 :=
      fun x hx => hs x ((mem_vertices hQ x).mp hx)
    have hd : ‖d‖ ^ 2 = R ^ 2 := by simpa using hs 0 hz
    have hheight : ∀ x ∈ V.erase 0, 1 ≤ sphereHeight d x := by
      intro x hx
      have hxV := (Finset.mem_erase.mp hx).2
      rw [sphereHeight_eq_norm_sq ((hVs x hxV).trans hd.symm)]
      have hsep := unit_edges_separated V hVs
        (fun a b hab => hu a b ((edge_iff_vertices_isEdge hQ a b).mpr hab))
        hzero hxV (Finset.mem_erase.mp hx).1.symm
      simp only [dist_zero_left] at hsep
      nlinarith
    have hsection := finiteHull_radial_section V hzero (sphereHeight d) hheight
    have hsection' : vertexFigure Q 0 d = convexHull ℝ
        ((fun x => (sphereHeight d x)⁻¹ • x) '' (V.erase 0 : Set E)) := by
      simpa only [vertexFigure, sub_zero, V, convexHull_vertices] using hsection
    rw [hsection']
    exact finiteHull_radialHull_dimension V hzero (sphereHeight d).toLinearMap
      (fun x hx => ne_of_gt (lt_of_lt_of_le zero_lt_one (hheight x hx)))
      (by simpa only [V, convexHull_vertices] using hdim) hpos
  let g := AffineIsometryEquiv.constVAdd ℝ E (-v)
  have hg (x : E) : g x = x - v := by simp [g, sub_eq_add_neg, add_comm]
  have hz : g v = 0 := by rw [hg, sub_self]
  have hvertex : (0 : E) ∈ (g '' P).extremePoints ℝ := by
    rw [← affineIsometry_image_extremePoints, ← hz]
    exact mem_image_of_mem g hv
  have hs : ∀ x ∈ (g '' P).extremePoints ℝ, ‖x - g c‖ ^ 2 = R ^ 2 := by
    rw [← affineIsometry_image_extremePoints]
    rintro x ⟨y, hy, rfl⟩
    have heq : g y - g c = y - c := by simp only [hg]; abel
    rw [heq]
    exact hsphere y hy
  have hdim := zero_case (finitePolytope_image g hP) hvertex (g c) hs
    (unitEdges_image g hunit) (by rw [affineDimension_image]; exact hfull)
  rw [← hz, ← vertexFigure_image, affineDimension_image] at hdim
  exact hdim

/-- The actual section is a finite polytope whenever it has a neighbor. -/
theorem finitePolytope_vertexFigure {P : Set E} (hP : FinitePolytope P)
    {v : E} (hv : v ∈ P.extremePoints ℝ) (c : E) (R : ℝ)
    (hsphere : ∀ x ∈ P.extremePoints ℝ, ‖x - c‖ ^ 2 = R ^ 2)
    (hunit : UnitEdges P) (hne : ∃ z, Edge P v z) :
    FinitePolytope (vertexFigure P v c) := by
  have hfin : {z | Edge P v z}.Finite :=
    (finitePolytope_extremePoints_finite hP).subset (fun _ hz => hz.2.1)
  refine ⟨hfin.toFinset, hfin.toFinset_nonempty.mpr hne, ?_⟩
  simpa only [Set.Finite.coe_toFinset] using
    finitePolytope_unit_vertexFigure hP hv c R hsphere hunit

/-- The geometric vertex-figure conclusions for the objects quantified over
by the classification theorem. The sphere and dimension premises are derived
from unit uniformity, rather than supplied by a model record. -/
theorem unitUniform5_vertexFigures {P : Set (Space 5)} (hP : UnitUniform 5 P) :
    ∃ c : Space 5, ∃ R : ℝ, 0 < R ∧
      (∀ x ∈ P.extremePoints ℝ, ‖x - c‖ ^ 2 = R ^ 2) ∧
      ∀ v ∈ P.extremePoints ℝ,
        vertexFigure P v c = convexHull ℝ {z | Edge P v z} ∧
        (vertexFigure P v c).extremePoints ℝ = {z | Edge P v z} ∧
        affineDimension (vertexFigure P v c) = 4 := by
  obtain ⟨c, R, hR, hs⟩ := uniform_cospherical_pos hP.1
  refine ⟨c, R, hR, hs, ?_⟩
  intro v hv
  refine ⟨finitePolytope_unit_vertexFigure (uniform_finitePolytope hP.1) hv c R hs hP.2,
    finitePolytope_unit_vertexFigure_extremePoints (uniform_finitePolytope hP.1) hv c R hs hP.2, ?_⟩
  have hd := finitePolytope_unit_vertexFigure_dimension (uniform_finitePolytope hP.1)
    hv c R hs hP.2
    (by simpa using uniform_dimension hP.1) (by simp)
  have hn : Module.finrank ℝ (Space 5) = 5 := by simp [Space]
  rw [hn] at hd
  omega

/-- Sanity check: the vertex figure of the unit real segment at zero is
its other endpoint, with the segment's genuine midpoint as sphere center. -/
theorem vertexFigure_unit_real_segment :
    vertexFigure (segment ℝ (0 : ℝ) 1) 0 (1 / 2) = {1} := by
  ext x
  have hh : sphereHeight ((1 / 2 : ℝ) - 0) (x - 0) = x := by
    simp only [sphereHeight, sub_zero, ContinuousLinearMap.smul_apply, innerSL_apply, smul_eq_mul, RCLike.inner_apply, conj_trivial]
    ring
  simp only [vertexFigure, Set.mem_setOf_eq, hh, Set.mem_singleton_iff]
  constructor
  · exact fun h => h.2
  · intro hx
    exact ⟨hx ▸ right_mem_segment ℝ (0 : ℝ) 1, hx⟩

end Uniform5.Composition
