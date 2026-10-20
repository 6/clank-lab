import Uniform5.CompositionVertices

/-!
# Transport of geometric uniformity by ambient Euclidean symmetries

Every transport below follows from the concrete geometric definitions.
-/
noncomputable section
namespace Uniform5.Composition
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

@[simp] theorem affineIsometry_symm_image_image (g : E ≃ᵃⁱ[ℝ] E) (P : Set E) :
    g.symm '' (g '' P) = P := by ext x; simp

@[simp] theorem affineIsometry_image_symm_image (g : E ≃ᵃⁱ[ℝ] E) (P : Set E) :
    g '' (g.symm '' P) = P := by ext x; simp

theorem finitePolytope_image (g : E ≃ᵃⁱ[ℝ] E) {P : Set E} (h : FinitePolytope P) :
    FinitePolytope (g '' P) := by
  classical
  obtain ⟨V, hV, rfl⟩ := h
  refine ⟨V.image g, hV.image g, ?_⟩
  simpa only [Finset.coe_image] using g.toAffineMap.image_convexHull (V : Set E)

@[simp] theorem affineDimension_image (g : E ≃ᵃⁱ[ℝ] E) (P : Set E) :
    affineDimension (g '' P) = affineDimension P := by
  unfold affineDimension Uniform5.affineDimension
  change Module.finrank ℝ (affineSpan ℝ (g.toAffineMap '' P)).direction = _
  rw [← AffineSubspace.map_span, AffineSubspace.map_direction]
  exact g.toAffineEquiv.linear.finrank_map_eq _

theorem isConvexFace_image (g : E ≃ᵃⁱ[ℝ] E) {P F : Set E}
    (h : IsConvexFace P F) : IsConvexFace (g '' P) (g '' F) := by
  refine ⟨h.1.affine_image g.toAffineMap, Set.image_mono h.2.1, ?_⟩
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ _ ⟨x, hx, rfl⟩ hs
  have hi : g '' openSegment ℝ a b = openSegment ℝ (g a) (g b) :=
    image_openSegment ℝ g.toAffineMap a b
  rw [← hi] at hs
  obtain ⟨haF, hbF⟩ := h.2.2 ha hb hx (g.injective.mem_set_image.mp hs)
  exact ⟨⟨a, haF, rfl⟩, ⟨b, hbF, rfl⟩⟩

theorem facet_image (g : E ≃ᵃⁱ[ℝ] E) {P F : Set E} (h : Facet P F) :
    Facet (g '' P) (g '' F) := by
  exact ⟨isConvexFace_image g h.1, h.2.1.image g, by simpa using h.2.2⟩

/-- The exposing functional is pulled back by the inverse linear part;
the translation contributes the same constant to both sides. -/
theorem isExposed_image (g : E ≃ᵃⁱ[ℝ] E) {P F : Set E}
    (h : IsExposed ℝ P F) : IsExposed ℝ (g '' P) (g '' F) := by
  intro hF
  obtain ⟨l, hl⟩ := h (Set.Nonempty.of_image hF)
  let m := l.comp g.symm.linearIsometryEquiv.toContinuousLinearEquiv.toContinuousLinearMap
  have hm (a : E) : m (g a) = l a - l (g.symm 0) := by
    have hg := g.symm.map_vsub (g a) 0
    simp only [vsub_eq_sub, sub_zero, g.symm_apply_apply] at hg
    change l (g.symm.linearIsometryEquiv (g a)) = _
    rw [hg, map_sub]
  refine ⟨m, ?_⟩
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [hl] at ha
    refine ⟨⟨a, ha.1, rfl⟩, ?_⟩
    rintro _ ⟨b, hb, rfl⟩
    rw [hm, hm]
    exact sub_le_sub_right (ha.2 b hb) _
  · rintro ⟨⟨a, ha, rfl⟩, hx⟩
    refine ⟨a, ?_, rfl⟩
    rw [hl]
    refine ⟨ha, fun b hb => ?_⟩
    have hh := hx (g b) ⟨b, hb, rfl⟩
    simpa only [hm, sub_le_sub_iff_right] using hh

theorem edge_image (g : E ≃ᵃⁱ[ℝ] E) {P : Set E} {v w : E} (h : Edge P v w) :
    Edge (g '' P) (g v) (g w) := by
  refine ⟨?_, ?_, fun he => h.2.2.1 (g.injective he), ?_⟩
  · rw [← affineIsometry_image_extremePoints]
    exact ⟨v, h.1, rfl⟩
  · rw [← affineIsometry_image_extremePoints]
    exact ⟨w, h.2.1, rfl⟩
  · have hh := isExposed_image g h.2.2.2
    have hs : g '' segment ℝ v w = segment ℝ (g v) (g w) :=
      image_segment ℝ g.toAffineMap v w
    rwa [hs] at hh

theorem unitEdges_image (g : E ≃ᵃⁱ[ℝ] E) {P : Set E} (h : UnitEdges P) :
    UnitEdges (g '' P) := by
  intro v w he
  have hi := edge_image g.symm he
  rw [affineIsometry_symm_image_image] at hi
  simpa only [g.symm.dist_map] using h _ _ hi

theorem vertexTransitive_image (g : E ≃ᵃⁱ[ℝ] E) {P : Set E}
    (h : VertexTransitive P) : VertexTransitive (g '' P) := by
  intro v hv w hw
  rw [← affineIsometry_image_extremePoints] at hv hw
  obtain ⟨a, ha, rfl⟩ := hv
  obtain ⟨b, hb, rfl⟩ := hw
  obtain ⟨f, hf, hab⟩ := h a ha b hb
  refine ⟨(g.symm.trans f).trans g, ?_, by simpa using congrArg g hab⟩
  change (fun x => g (f (g.symm x))) '' (g '' P) = g '' P
  calc
    _ = g '' (f '' (g.symm '' (g '' P))) := by simp only [Set.image_image]
    _ = g '' P := by rw [affineIsometry_symm_image_image, hf]

/-- Recursive uniformity is preserved in every dimension, including its
point, segment and regular-polygon base cases. -/
theorem uniform_image (g : E ≃ᵃⁱ[ℝ] E) {n : ℕ} {P : Set E} (h : Uniform n P) :
    Uniform n (g '' P) := by
  induction n using Nat.strong_induction_on generalizing P with
  | h n ih =>
    rcases n with _ | n
    · rw [Uniform] at h ⊢
      obtain ⟨x, rfl⟩ := h
      exact ⟨g x, Set.image_singleton⟩
    rcases n with _ | n
    · rw [Uniform] at h ⊢
      obtain ⟨x, y, hxy, rfl⟩ := h
      exact ⟨g x, g y, fun he => hxy (g.injective he),
        image_segment ℝ g.toAffineMap x y⟩
    rcases n with _ | n
    · rw [Uniform] at h ⊢
      obtain ⟨k, hk, r, hr, f, rfl⟩ := h
      refine ⟨k, hk, r, hr, g.toAffineIsometry.comp f, ?_⟩
      exact Set.image_image _ _ _
    rw [Uniform] at h ⊢
    refine ⟨finitePolytope_image g h.1, ?_, vertexTransitive_image g h.2.2.1, ?_⟩
    · simpa only [affineDimension_image] using h.2.1
    · intro F hF
      have hpre : Facet P (g.symm '' F) := by
        simpa only [affineIsometry_symm_image_image] using facet_image g.symm hF
      have hh := ih (n + 2) (by omega) (h.2.2.2 _ hpre)
      simpa only [affineIsometry_image_symm_image] using hh

theorem unitUniform_image (g : E ≃ᵃⁱ[ℝ] E) {n : ℕ} {P : Set E}
    (h : UnitUniform n P) : UnitUniform n (g '' P) :=
  ⟨uniform_image g h.1, unitEdges_image g h.2⟩

@[simp] theorem finitePolytope_image_iff (g : E ≃ᵃⁱ[ℝ] E) (P : Set E) :
    FinitePolytope (g '' P) ↔ FinitePolytope P :=
  ⟨fun h => by simpa using finitePolytope_image g.symm h, finitePolytope_image g⟩

@[simp] theorem facet_image_iff (g : E ≃ᵃⁱ[ℝ] E) (P F : Set E) :
    Facet (g '' P) (g '' F) ↔ Facet P F :=
  ⟨fun h => by simpa using facet_image g.symm h, facet_image g⟩

@[simp] theorem edge_image_iff (g : E ≃ᵃⁱ[ℝ] E) (P : Set E) (v w : E) :
    Edge (g '' P) (g v) (g w) ↔ Edge P v w :=
  ⟨fun h => by simpa using edge_image g.symm h, edge_image g⟩

@[simp] theorem unitEdges_image_iff (g : E ≃ᵃⁱ[ℝ] E) (P : Set E) :
    UnitEdges (g '' P) ↔ UnitEdges P :=
  ⟨fun h => by simpa using unitEdges_image g.symm h, unitEdges_image g⟩

@[simp] theorem vertexTransitive_image_iff (g : E ≃ᵃⁱ[ℝ] E) (P : Set E) :
    VertexTransitive (g '' P) ↔ VertexTransitive P :=
  ⟨fun h => by simpa using vertexTransitive_image g.symm h, vertexTransitive_image g⟩

@[simp] theorem uniform_image_iff (g : E ≃ᵃⁱ[ℝ] E) (n : ℕ) (P : Set E) :
    Uniform n (g '' P) ↔ Uniform n P :=
  ⟨fun h => by simpa using uniform_image g.symm h, uniform_image g⟩

@[simp] theorem unitUniform_image_iff (g : E ≃ᵃⁱ[ℝ] E) (n : ℕ) (P : Set E) :
    UnitUniform n (g '' P) ↔ UnitUniform n P :=
  ⟨fun h => by simpa using unitUniform_image g.symm h, unitUniform_image g⟩

/-- Actual five-dimensional unit uniform hulls in Euclidean five-space. -/
noncomputable def UnitUniform5 := {P : Set (Space 5) // UnitUniform 5 P}

/-- Transport of actual geometric objects, rather than of symbolic labels. -/
noncomputable def UnitUniform5.image (g : Space 5 ≃ᵃⁱ[ℝ] Space 5)
    (P : UnitUniform5) : UnitUniform5 :=
  ⟨g '' P.val, unitUniform_image g P.property⟩

@[simp] theorem UnitUniform5.image_val (g : Space 5 ≃ᵃⁱ[ℝ] Space 5)
    (P : UnitUniform5) : (P.image g).val = g '' P.val := rfl

@[ext] theorem UnitUniform5.ext {P Q : UnitUniform5} (h : P.val = Q.val) : P = Q :=
  Subtype.ext h

@[simp] theorem UnitUniform5.image_refl (P : UnitUniform5) :
    P.image (AffineIsometryEquiv.refl ℝ (Space 5)) = P := by
  apply UnitUniform5.ext
  exact Set.image_id _

theorem UnitUniform5.image_trans (g h : Space 5 ≃ᵃⁱ[ℝ] Space 5)
    (P : UnitUniform5) : (P.image g).image h = P.image (g.trans h) := by
  apply UnitUniform5.ext
  exact Set.image_image _ _ _

@[simp] theorem UnitUniform5.image_symm (g : Space 5 ≃ᵃⁱ[ℝ] Space 5)
    (P : UnitUniform5) : (P.image g).image g.symm = P := by
  apply UnitUniform5.ext
  exact affineIsometry_symm_image_image g P.val

/-- The image operation is a genuine invertible action on the class of
unit uniform five-polytopes. -/
noncomputable def UnitUniform5.imageEquiv (g : Space 5 ≃ᵃⁱ[ℝ] Space 5) :
    UnitUniform5 ≃ UnitUniform5 where
  toFun := UnitUniform5.image g
  invFun := UnitUniform5.image g.symm
  left_inv := UnitUniform5.image_symm g
  right_inv P := by
    apply UnitUniform5.ext
    exact affineIsometry_image_symm_image g P.val

noncomputable instance : MulAction (Space 5 ≃ᵃⁱ[ℝ] Space 5) UnitUniform5 where
  smul g P := P.image g
  one_smul := UnitUniform5.image_refl
  mul_smul g h P := (UnitUniform5.image_trans h g P).symm

/-- The finite vertex sets determine the actual hulls, so they also
separate elements of the geometric model type. -/
theorem UnitUniform5.ext_vertices {P Q : UnitUniform5}
    (h : P.val.extremePoints ℝ = Q.val.extremePoints ℝ) : P = Q := by
  apply UnitUniform5.ext
  rw [finitePolytope_eq_convexHull_extremePoints (uniform_finitePolytope P.property.1),
    finitePolytope_eq_convexHull_extremePoints (uniform_finitePolytope Q.property.1), h]

@[simp] theorem UnitUniform5.image_vertices (g : Space 5 ≃ᵃⁱ[ℝ] Space 5)
    (P : UnitUniform5) :
    (P.image g).val.extremePoints ℝ = g '' P.val.extremePoints ℝ :=
  (affineIsometry_image_extremePoints g P.val).symm

@[simp] theorem UnitUniform5.image_mem_vertices (g : Space 5 ≃ᵃⁱ[ℝ] Space 5)
    (P : UnitUniform5) (v : Space 5) :
    g v ∈ (P.image g).val.extremePoints ℝ ↔ v ∈ P.val.extremePoints ℝ := by
  rw [UnitUniform5.image_vertices]
  exact g.injective.mem_set_image

end Uniform5.Composition
