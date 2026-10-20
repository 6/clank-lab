import Uniform5.CompositionFigureMetric

/-! Intrinsic vertex-figure centers without a full ambient span assumption. -/
noncomputable section
namespace Uniform5.Composition
open Set
open scoped BigOperators RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The corrected centroid argument also holds in a proper affine span.
Its full-span version is applied in the span of the centered generators. -/
theorem figureCenter_mem_intrinsicInterior_in_span
    (V : Finset E) {v : E} {R : ℝ} (hv : v ∈ V) (hcard : 1 < V.card)
    (hsum : ∑ x ∈ V, x = 0) (hsphere : ∀ x ∈ V, ‖x‖ = R)
    (hR : R ≠ 0) (hsep : ∀ x ∈ V, x ≠ v → 1 ≤ dist x v) :
    figureCenter v R ∈ intrinsicInterior ℝ
      (convexHull ℝ (V : Set E) ∩ figureHyperplane v R) := by
  classical
  let S := Submodule.span ℝ (V : Set E)
  let q : V → S := fun i => ⟨i, Submodule.subset_span i.property⟩
  let W : Finset S := Finset.univ.image q
  let w : S := ⟨v, Submodule.subset_span hv⟩
  have hqinj : Function.Injective q := by
    intro i j hh
    exact Subtype.ext (congrArg (fun x : S => (x : E)) hh)
  have hWset : (W : Set S) = range q := by simp [W]
  have himage : S.subtype '' range q = (V : Set E) := by
    ext x
    constructor
    · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
      exact i.property
    · intro hx
      exact ⟨q ⟨x, hx⟩, mem_range_self _, rfl⟩
  have hw : w ∈ W := Finset.mem_image.mpr ⟨⟨v, hv⟩, Finset.mem_univ _, rfl⟩
  have hcardW : 1 < W.card := by
    simpa only [W, Finset.card_image_of_injective _ hqinj, Finset.card_univ,
      Fintype.card_coe] using hcard
  have hsumq : ∑ i, q i = 0 := by
    apply Subtype.ext
    simpa only [q, Submodule.coe_sum, ZeroMemClass.coe_zero,
      Finset.univ_eq_attach, Finset.sum_attach V (fun x : E => x)] using hsum
  have hsumW : ∑ x ∈ W, x = 0 := by
    rw [Finset.sum_image (fun a _ b _ hh => hqinj hh)]
    exact hsumq
  have hspan : Submodule.span ℝ (range q) = ⊤ := by
    apply Submodule.map_injective_of_injective S.injective_subtype
    rw [Submodule.map_span, Submodule.map_subtype_top, himage]
  have hzero : (0 : S) ∈ convexHull ℝ (range q) := by
    have h := W.centerMass_mem_convexHull (w := fun _ => (1 : ℝ)) (z := id)
      (fun _ _ => zero_le_one)
      (by simpa using (show (0 : ℝ) < W.card by exact_mod_cast (by omega : 0 < W.card)))
      (fun x hx => hx)
    have hzW : (0 : S) ∈ convexHull ℝ (W : Set S) := by
      simpa [Finset.centerMass, hsumW] using h
    rwa [hWset] at hzW
  have haffine : affineSpan ℝ (W : Set S) = ⊤ := by
    rw [hWset]
    apply SetLike.coe_injective
    rw [← affineSpan_insert_eq_affineSpan ℝ
      ((affineSpan_convexHull (𝕜 := ℝ) (range q)) ▸ subset_affineSpan ℝ _ hzero),
      affineSpan_insert_zero, hspan]
    rfl
  have hs : ∀ x ∈ W, ‖x‖ = R := by
    rintro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact hsphere i i.property
  have hdist : ∀ x ∈ W, x ≠ w → 1 ≤ dist x w := by
    rintro x hx hne
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact hsep i i.property (fun hh => hne (Subtype.ext hh))
  have hint := figureCenter_mem_intrinsicInterior W hw hcardW haffine hsumW hs hR hdist
  let f := S.subtypeₗᵢ.toAffineIsometry
  have hmap := Set.mem_image_of_mem f hint
  rw [← f.image_intrinsicInterior] at hmap
  have hH : f '' convexHull ℝ (W : Set S) = convexHull ℝ (V : Set E) := by
    change S.subtype '' convexHull ℝ (W : Set S) = _
    rw [S.subtype.image_convexHull, hWset, himage]
  have hsection : f '' (convexHull ℝ (W : Set S) ∩ figureHyperplane w R) =
      convexHull ℝ (V : Set E) ∩ figureHyperplane v R := by
    ext x
    constructor
    · rintro ⟨y, ⟨hy, hh⟩, rfl⟩
      exact ⟨hH ▸ mem_image_of_mem f hy, hh⟩
    · rintro ⟨hx, hh⟩
      rw [← hH] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact ⟨y, ⟨hy, hh⟩, rfl⟩
  rw [hsection] at hmap
  exact hmap

/-- Positive-dimensional uniform polytopes have at least two actual vertices. -/
theorem uniform_vertices_card_gt_one {n : ℕ} {P : Set E} (hP : Uniform (n + 3) P) :
    1 < (vertices P (uniform_finitePolytope hP)).card := by
  classical
  let V := vertices P (uniform_finitePolytope hP)
  have hVne : V.Nonempty := vertices_nonempty _
  change 1 < V.card
  by_contra hcard
  have heq : V.card = 1 := by have hh := Finset.card_pos.mpr hVne; omega
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp heq
  have hHull := convexHull_vertices (uniform_finitePolytope hP)
  change convexHull ℝ (V : Set E) = P at hHull
  rw [hv] at hHull
  simp only [Finset.coe_singleton, convexHull_singleton] at hHull
  have hd := uniform_dimension hP
  rw [← hHull, affineDimension_singleton] at hd
  omega


/-- The actual figure center is relatively interior in every dimension,
including uniform facets embedded in a larger Euclidean space. -/
theorem unitUniform_centroid_figureCenter_mem_intrinsicInterior
    {n : ℕ} {P : Set E} (hP : UnitUniform (n + 3) P) (R : ℝ) (hR : 0 < R)
    (hsphere : ∀ x ∈ P.extremePoints ℝ,
      ‖x - vertexCentroid (vertices P (uniform_finitePolytope hP.1))‖ ^ 2 = R ^ 2)
    {v : E} (hv : v ∈ P.extremePoints ℝ) :
    let c := vertexCentroid (vertices P (uniform_finitePolytope hP.1))
    c + figureCenter (v - c) R ∈ intrinsicInterior ℝ (vertexFigure P v c) := by
  classical
  let V := vertices P (uniform_finitePolytope hP.1)
  let c := vertexCentroid V
  let g := (AffineIsometryEquiv.vaddConst ℝ c).symm
  let W := V.image g
  have hg (x : E) : g x = x - c := rfl
  have hV : convexHull ℝ (V : Set (E)) = P := convexHull_vertices _
  have hW : convexHull ℝ (W : Set (E)) = g '' P := by
    rw [← hV]
    simpa only [W, Finset.coe_image] using
      (g.toAffineMap.image_convexHull (V : Set (E))).symm
  have hvV : v ∈ V := (mem_vertices _ v).mpr hv
  have hvW : g v ∈ W := Finset.mem_image.mpr ⟨v, hvV, rfl⟩
  have hcard : 1 < W.card := by
    rw [Finset.card_image_of_injective V g.injective]
    exact uniform_vertices_card_gt_one hP.1
  have hsum : ∑ x ∈ W, x = 0 := by
    rw [Finset.sum_image (fun a _ b _ hab => g.injective hab)]
    simp only [hg]
    exact sum_sub_vertexCentroid V (vertices_nonempty _)
  have hs : ∀ x ∈ W, ‖x‖ = R := by
    rintro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    have hh := hsphere y ((mem_vertices _ y).mp hy)
    change ‖y - c‖ ^ 2 = R ^ 2 at hh
    exact (sq_eq_sq₀ (norm_nonneg _) hR.le).mp hh
  have hsep : ∀ x ∈ W, x ≠ g v → 1 ≤ dist x (g v) := by
    rintro x hx hne
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    rw [g.dist_map]
    exact unitUniform_separated hP ((mem_vertices _ y).mp hy) hv
      (fun heq => hne (congrArg g heq))
  have hint := figureCenter_mem_intrinsicInterior_in_span W hvW hcard hsum hs hR.ne' hsep
  have hsection : convexHull ℝ (W : Set (E)) ∩ figureHyperplane (g v) R =
      g '' vertexFigure P v c := by
    rw [hW, ← vertexFigure_zero_center_eq _ _ _ (hs _ hvW), vertexFigure_image]
    have hgc : g c = 0 := by rw [hg, sub_self]
    rw [hgc]
  rw [hsection] at hint
  have hint' : figureCenter (g v) R ∈ g '' intrinsicInterior ℝ (vertexFigure P v c) := by
    have hi := g.toAffineIsometry.image_intrinsicInterior (vertexFigure P v c)
    change intrinsicInterior ℝ (g '' vertexFigure P v c) =
      g '' intrinsicInterior ℝ (vertexFigure P v c) at hi
    rwa [hi] at hint
  obtain ⟨x, hx, hxeq⟩ := hint'
  have hxc : x = c + figureCenter (v - c) R := by
    rw [hg] at hxeq
    rw [hg] at hxeq
    exact (sub_eq_iff_eq_add.mp hxeq).trans (add_comm _ _)
  simpa only [hxc] using hx


end Uniform5.Composition
