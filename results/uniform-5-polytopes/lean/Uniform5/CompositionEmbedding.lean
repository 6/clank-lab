import Uniform5.CompositionIntrinsicModel
import Uniform5.CompositionSymmetry
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Transport through Euclidean affine embeddings

Faces, extreme points, exposed edges and ambient symmetry witnesses are
transported through actual affine isometric embeddings. Symmetries on the
image hull extend to its ambient Euclidean space by the intrinsic extension
theorem, so no ambient symmetry extension is postulated.
-/

noncomputable section
namespace Uniform5.Composition
open Set

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The actual restricted isometry, retaining its pointwise action. -/
noncomputable def embeddingSetEquiv (f : E →ᵃⁱ[ℝ] F) (P : Set E) : P ≃ᵢ (f '' P) :=
  { toEquiv := Equiv.Set.image f P f.injective
    isometry_toFun := fun x y => f.isometry x y }

@[simp] theorem embeddingSetEquiv_apply (f : E →ᵃⁱ[ℝ] F) (P : Set E) (x : P) :
    (embeddingSetEquiv f P x : F) = f x := rfl

@[simp] theorem embeddingSetEquiv_apply_symm (f : E →ᵃⁱ[ℝ] F) (P : Set E)
    (x : f '' P) : f (embeddingSetEquiv f P |>.symm x) = x :=
  congrArg Subtype.val ((embeddingSetEquiv f P).apply_symm_apply x)

theorem embedding_extremePoints (f : E →ᵃⁱ[ℝ] F) (P : Set E) :
    f '' P.extremePoints ℝ = (f '' P).extremePoints ℝ := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨x, hx.1, rfl⟩, ?_⟩
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hs
    have hi : f '' openSegment ℝ a b = openSegment ℝ (f a) (f b) :=
      image_openSegment ℝ f.toAffineMap a b
    rw [← hi] at hs
    obtain ⟨hax, hbx⟩ := hx.2 ha hb (f.injective.mem_set_image.mp hs)
    exact ⟨congrArg f hax, congrArg f hbx⟩
  · intro hy
    obtain ⟨x, hx, rfl⟩ := hy.1
    refine ⟨x, ⟨hx, ?_⟩, rfl⟩
    intro a ha b hb hs
    have hi : f '' openSegment ℝ a b = openSegment ℝ (f a) (f b) :=
      image_openSegment ℝ f.toAffineMap a b
    have hs' : f x ∈ openSegment ℝ (f a) (f b) := by
      rw [← hi]
      exact ⟨x, hs, rfl⟩
    obtain ⟨hax, hbx⟩ := hy.2 ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩ hs'
    exact ⟨f.injective hax, f.injective hbx⟩

theorem embedding_face_image (f : E →ᵃⁱ[ℝ] F) {P A : Set E}
    (h : IsConvexFace P A) : IsConvexFace (f '' P) (f '' A) := by
  refine ⟨h.1.affine_image f.toAffineMap, Set.image_mono h.2.1, ?_⟩
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ _ ⟨x, hx, rfl⟩ hs
  have hi : f '' openSegment ℝ a b = openSegment ℝ (f a) (f b) :=
    image_openSegment ℝ f.toAffineMap a b
  rw [← hi] at hs
  obtain ⟨ha', hb'⟩ := h.2.2 ha hb hx (f.injective.mem_set_image.mp hs)
  exact ⟨⟨a, ha', rfl⟩, ⟨b, hb', rfl⟩⟩

theorem embedding_face_preimage (f : E →ᵃⁱ[ℝ] F) {P : Set E} {A : Set F}
    (h : IsConvexFace (f '' P) A) : IsConvexFace P (f ⁻¹' A) := by
  refine ⟨h.1.affine_preimage f.toAffineMap, ?_, ?_⟩
  · intro x hx
    exact f.injective.mem_set_image.mp (h.2.1 hx)
  · intro a ha b hb x hx hs
    have hi : f '' openSegment ℝ a b = openSegment ℝ (f a) (f b) :=
      image_openSegment ℝ f.toAffineMap a b
    have hs' : f x ∈ openSegment ℝ (f a) (f b) := by
      rw [← hi]
      exact ⟨x, hs, rfl⟩
    exact h.2.2 ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩ hx hs'

theorem embedding_face_image_preimage (f : E →ᵃⁱ[ℝ] F) {P : Set E} {A : Set F}
    (h : IsConvexFace (f '' P) A) : f '' (f ⁻¹' A) = A :=
  Set.image_preimage_eq_of_subset (h.2.1.trans (Set.image_subset_range _ _))

theorem embedding_facet_image (f : E →ᵃⁱ[ℝ] F) {P A : Set E} (h : Facet P A) :
    Facet (f '' P) (f '' A) :=
  ⟨embedding_face_image f h.1, h.2.1.image f, by
    simpa only [affineDimension_affineIsometry_image] using h.2.2⟩

theorem embedding_facet_preimage (f : E →ᵃⁱ[ℝ] F) {P : Set E} {A : Set F}
    (h : Facet (f '' P) A) : Facet P (f ⁻¹' A) := by
  have hi := embedding_face_image_preimage f h.1
  refine ⟨embedding_face_preimage f h.1, ?_, ?_⟩
  · rw [← hi] at h
    exact Set.Nonempty.of_image h.2.1
  · have hd := affineDimension_affineIsometry_image f (f ⁻¹' A)
    rw [hi] at hd
    rw [← affineDimension_affineIsometry_image f P, ← hd]
    exact h.2.2

/-- Restrict an ambient symmetry to the actual hull. -/
noncomputable def symmetrySetEquiv (g : E ≃ᵃⁱ[ℝ] E) (P : Set E)
    (hg : g '' P = P) : P ≃ᵢ P :=
  { toEquiv := (Equiv.image g.toEquiv P).trans (Equiv.setCongr hg)
    isometry_toFun := fun x y => g.isometry x y }

@[simp] theorem symmetrySetEquiv_apply (g : E ≃ᵃⁱ[ℝ] E) (P : Set E)
    (hg : g '' P = P) (x : P) : (symmetrySetEquiv g P hg x : E) = g x := rfl

/-- An intrinsic symmetry extends while preserving its whole hull. -/
theorem intrinsicSymmetry_extension [FiniteDimensional ℝ E] {P : Set E} (e : P ≃ᵢ P) :
    ∃ g : E ≃ᵃⁱ[ℝ] E, g '' P = P ∧ ∀ x : P, g x = e x := by
  obtain ⟨g, hg⟩ := isometryEquiv_extends_affineIsometryEquiv e
  refine ⟨g, ?_, hg⟩
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [hg ⟨x, hx⟩]
    exact (e ⟨x, hx⟩).property
  · intro hy
    refine ⟨e.symm ⟨y, hy⟩, (e.symm ⟨y, hy⟩).property, ?_⟩
    rw [hg]
    exact congrArg Subtype.val (e.apply_symm_apply ⟨y, hy⟩)

/-- Source hull symmetries induce genuine ambient symmetries of an
isometrically embedded hull. -/
theorem embedding_vertexTransitive_image [FiniteDimensional ℝ F]
    (f : E →ᵃⁱ[ℝ] F) {P : Set E} (hP : VertexTransitive P) :
    VertexTransitive (f '' P) := by
  intro y hy z hz
  rw [← embedding_extremePoints f P] at hy hz
  obtain ⟨v, hv, rfl⟩ := hy
  obtain ⟨w, hw, rfl⟩ := hz
  obtain ⟨g, hg, hgw⟩ := hP v hv w hw
  let e := embeddingSetEquiv f P
  let t := (e.symm.trans (symmetrySetEquiv g P hg)).trans e
  obtain ⟨k, hk, hkt⟩ := intrinsicSymmetry_extension t
  refine ⟨k, hk, ?_⟩
  let v₀ : P := ⟨v, hv.1⟩
  have hk' := hkt (e v₀)
  change k (f v) = _ at hk'
  have ht : (t (e v₀) : F) = f (g v) := by
    change (e (symmetrySetEquiv g P hg (e.symm (e v₀))) : F) = _
    rw [e.symm_apply_apply]
    rfl
  rw [ht, hgw] at hk'
  exact hk'

/-- Symmetry transport also reflects vertex transitivity. -/
theorem embedding_vertexTransitive_preimage [FiniteDimensional ℝ E]
    (f : E →ᵃⁱ[ℝ] F) {P : Set E} (hP : VertexTransitive (f '' P)) :
    VertexTransitive P := by
  intro v hv w hw
  have hv' : f v ∈ (f '' P).extremePoints ℝ := by
    rw [← embedding_extremePoints f P]
    exact ⟨v, hv, rfl⟩
  have hw' : f w ∈ (f '' P).extremePoints ℝ := by
    rw [← embedding_extremePoints f P]
    exact ⟨w, hw, rfl⟩
  obtain ⟨g, hg, hgw⟩ := hP (f v) hv' (f w) hw'
  let e := embeddingSetEquiv f P
  let t := (e.trans (symmetrySetEquiv g (f '' P) hg)).trans e.symm
  obtain ⟨k, hk, hkt⟩ := intrinsicSymmetry_extension t
  refine ⟨k, hk, ?_⟩
  let v₀ : P := ⟨v, hv.1⟩
  let w₀ : P := ⟨w, hw.1⟩
  have heq : symmetrySetEquiv g (f '' P) hg (e v₀) = e w₀ := Subtype.ext hgw
  have ht : t v₀ = w₀ := by
    change e.symm (symmetrySetEquiv g (f '' P) hg (e v₀)) = w₀
    rw [heq, e.symm_apply_apply]
  have hk' := hkt v₀
  rw [ht] at hk'
  exact hk'

/-- Recursive geometric uniformity is preserved by affine isometric
embedding, including regular-polygon base cases. -/
theorem embedding_uniform_image [FiniteDimensional ℝ F]
    (f : E →ᵃⁱ[ℝ] F) {n : ℕ} {P : Set E} (h : Uniform n P) :
    Uniform n (f '' P) := by
  induction n using Nat.strong_induction_on generalizing P with
  | h n ih =>
    rcases n with _ | n
    · rw [Uniform] at h ⊢
      obtain ⟨x, rfl⟩ := h
      exact ⟨f x, Set.image_singleton⟩
    rcases n with _ | n
    · rw [Uniform] at h ⊢
      obtain ⟨x, y, hxy, rfl⟩ := h
      exact ⟨f x, f y, fun he => hxy (f.injective he), image_segment ℝ f.toAffineMap x y⟩
    rcases n with _ | n
    · rw [Uniform] at h ⊢
      obtain ⟨k, hk, r, hr, g, rfl⟩ := h
      exact ⟨k, hk, r, hr, f.comp g, Set.image_image _ _ _⟩
    rw [Uniform] at h ⊢
    refine ⟨(finitePolytope_affineIsometry_image_iff f P).mpr h.1, ?_,
      embedding_vertexTransitive_image f h.2.2.1, ?_⟩
    · rw [affineDimension_affineIsometry_image]
      exact h.2.1
    · intro A hA
      have hh := ih (n + 2) (by omega)
        (h.2.2.2 _ (embedding_facet_preimage f hA))
      rwa [embedding_face_image_preimage f hA.1] at hh

/-- Exposed faces reflect through any affine isometric embedding by
pulling their exposing functional back along its linear part. -/
theorem embedding_isExposed_reflect (f : E →ᵃⁱ[ℝ] F) {P A : Set E}
    (h : IsExposed ℝ (f '' P) (f '' A)) : IsExposed ℝ P A := by
  intro hA
  obtain ⟨l, hl⟩ := h (hA.image f)
  let m := l.comp f.linearIsometry.toContinuousLinearMap
  have hm (x : E) : l (f x) = m x + l (f 0) := by
    have hh : f x = f.linear x + f 0 := by simpa using f.map_vadd 0 x
    rw [hh, map_add]
    rfl
  refine ⟨m, ?_⟩
  ext x
  constructor
  · intro hx
    have hx' : f x ∈ f '' A := ⟨x, hx, rfl⟩
    rw [hl] at hx'
    refine ⟨f.injective.mem_set_image.mp hx'.1, ?_⟩
    intro y hy
    have hh := hx'.2 (f y) ⟨y, hy, rfl⟩
    simpa only [hm y, hm x, add_le_add_iff_right] using hh
  · rintro ⟨hx, hxmax⟩
    apply f.injective.mem_set_image.mp
    rw [hl]
    refine ⟨⟨x, hx, rfl⟩, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    rw [hm y, hm x]
    exact add_le_add_right (hxmax y hy) _

/-- Extending an exposing functional by the adjoint of the linear isometry
preserves its maximizers on the embedded hull. -/
theorem embedding_isExposed_image [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (f : E →ᵃⁱ[ℝ] F) {P A : Set E} (h : IsExposed ℝ P A) :
    IsExposed ℝ (f '' P) (f '' A) := by
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  letI : CompleteSpace F := FiniteDimensional.complete ℝ F
  let T := f.linearIsometry.toContinuousLinearMap
  have hinv (x : E) : T.adjoint (T x) = x := by
    have hh := T.norm_map_iff_adjoint_comp_self.mp f.linearIsometry.norm_map
    have hv := congrArg (fun k : E →L[ℝ] E => k x) hh
    exact hv
  intro hA
  obtain ⟨l, hl⟩ := h (Set.Nonempty.of_image hA)
  let m := l.comp T.adjoint
  have hm (x : E) : m (f x) = l x + m (f 0) := by
    have hh : f x = T x + f 0 := by simpa using f.map_vadd 0 x
    rw [hh, map_add]
    change l (T.adjoint (T x)) + m (f 0) = _
    rw [hinv]
  refine ⟨m, ?_⟩
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [hl] at hx
    refine ⟨⟨x, hx.1, rfl⟩, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    rw [hm y, hm x]
    exact add_le_add_right (hx.2 y hy) _
  · rintro ⟨⟨x, hx, rfl⟩, hxmax⟩
    refine ⟨x, ?_, rfl⟩
    rw [hl]
    refine ⟨hx, fun y hy => ?_⟩
    have hh := hxmax (f y) ⟨y, hy, rfl⟩
    simpa only [hm y, hm x, add_le_add_iff_right] using hh

/-- Actual exposed edges reflect through affine isometric embedding. -/
theorem embedding_edge_reflect (f : E →ᵃⁱ[ℝ] F) {P : Set E} {x y : E}
    (h : Edge (f '' P) (f x) (f y)) : Edge P x y := by
  have hext := embedding_extremePoints f P
  refine ⟨?_, ?_, fun hxy => h.2.2.1 (congrArg f hxy), ?_⟩
  · have hv := h.1
    rw [← hext] at hv
    exact f.injective.mem_set_image.mp hv
  · have hv := h.2.1
    rw [← hext] at hv
    exact f.injective.mem_set_image.mp hv
  · apply embedding_isExposed_reflect f
    have hi : f '' segment ℝ x y = segment ℝ (f x) (f y) :=
      image_segment ℝ f.toAffineMap x y
    rw [hi]
    exact h.2.2.2

theorem embedding_edge_image [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (f : E →ᵃⁱ[ℝ] F) {P : Set E} {x y : E} (h : Edge P x y) :
    Edge (f '' P) (f x) (f y) := by
  refine ⟨?_, ?_, fun hxy => h.2.2.1 (f.injective hxy), ?_⟩
  · rw [← embedding_extremePoints f P]
    exact ⟨x, h.1, rfl⟩
  · rw [← embedding_extremePoints f P]
    exact ⟨y, h.2.1, rfl⟩
  · have hh := embedding_isExposed_image f h.2.2.2
    have hi : f '' segment ℝ x y = segment ℝ (f x) (f y) :=
      image_segment ℝ f.toAffineMap x y
    rwa [hi] at hh

theorem embedding_unitEdges_image (f : E →ᵃⁱ[ℝ] F) {P : Set E} (h : UnitEdges P) :
    UnitEdges (f '' P) := by
  intro v w he
  obtain ⟨x, hx, rfl⟩ := he.1.1
  obtain ⟨y, hy, rfl⟩ := he.2.1.1
  rw [f.dist_map]
  exact h x y (embedding_edge_reflect f he)

theorem embedding_unitEdges_reflect [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (f : E →ᵃⁱ[ℝ] F) {P : Set E} (h : UnitEdges (f '' P)) : UnitEdges P := by
  intro x y he
  simpa only [f.dist_map] using h _ _ (embedding_edge_image f he)

/-- Forward transport of the paper's entire unit-uniform predicate. -/
theorem embedding_unitUniform_image [FiniteDimensional ℝ F]
    (f : E →ᵃⁱ[ℝ] F) {n : ℕ} {P : Set E} (h : UnitUniform n P) :
    UnitUniform n (f '' P) :=
  ⟨embedding_uniform_image f h.1, embedding_unitEdges_image f h.2⟩

end Uniform5.Composition
