import Uniform5.CompositionRadiusTransport
import Uniform5.CompositionEmbeddingReverse
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-! Intrinsic geometric predicates are independent of the chosen Euclidean
ambient dimension. The two ambient spaces embed into their Euclidean direct
sum, where the already proved extension theorem applies. -/
noncomputable section
namespace Uniform5.Composition
open Set
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Inclusion in the first summand of the Euclidean direct sum. -/
noncomputable def euclideanInl : E →ᵃⁱ[ℝ] WithLp 2 (E × F) :=
  LinearIsometry.toAffineIsometry
    { toLinearMap := (WithLp.linearEquiv 2 ℝ (E × F)).symm.toLinearMap.comp
        (LinearMap.inl ℝ E F)
      norm_map' := fun x => WithLp.norm_equiv_symm_fst 2 E F x }

/-- Inclusion in the second summand of the Euclidean direct sum. -/
noncomputable def euclideanInr : F →ᵃⁱ[ℝ] WithLp 2 (E × F) :=
  LinearIsometry.toAffineIsometry
    { toLinearMap := (WithLp.linearEquiv 2 ℝ (E × F)).symm.toLinearMap.comp
        (LinearMap.inr ℝ E F)
      norm_map' := fun x => WithLp.norm_equiv_symm_snd 2 E F x }

theorem HasIntrinsicRadius.of_embedding {P : Set E} {r : ℝ}
    (f : E →ᵃⁱ[ℝ] F) (hr : HasIntrinsicRadius (f '' P) r) :
    HasIntrinsicRadius P r := by
  obtain ⟨himage, hr, hs⟩ := hr
  have hP := (finitePolytope_affineIsometry_image_iff f P).mp himage
  refine ⟨hP, hr, ?_⟩
  intro x hx
  have hfx : f x ∈ (f '' P).extremePoints ℝ := by
    rw [← embedding_extremePoints f P]
    exact mem_image_of_mem f hx
  have h := hs (f x) hfx
  rw [← embedding_vertexCentroid f hP, ← dist_eq_norm, f.isometry.dist_eq,
    dist_eq_norm] at h
  exact h

theorem hasIntrinsicRadius_embedding_iff (f : E →ᵃⁱ[ℝ] F) (P : Set E) (r : ℝ) :
    HasIntrinsicRadius (f '' P) r ↔ HasIntrinsicRadius P r :=
  ⟨fun h => h.of_embedding f, fun h => h.embedding f⟩

/-- Any intrinsic congruence becomes an actual ambient isometry after
embedding both spaces into their Euclidean direct sum. -/
theorem congruent_euclidean_sum {P : Set E} {Q : Set F} (h : Congruent P Q) :
    Congruent (euclideanInl (F := F) '' P) (euclideanInr (E := E) '' Q) :=
  congruent_trans (congruent_symm (congruent_affineIsometry_image (euclideanInl (F := F)) P))
    (congruent_trans h (congruent_affineIsometry_image (euclideanInr (E := E)) Q))

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

theorem HasIntrinsicRadius.cross_congruent {P : Set E} {Q : Set F} {r : ℝ}
    (hr : HasIntrinsicRadius P r) (h : Congruent P Q) : HasIntrinsicRadius Q r := by
  have hs := (hr.embedding (euclideanInl (F := F))).congruent
    (congruent_euclidean_sum h)
  exact hs.of_embedding (euclideanInr (E := E))

theorem hasIntrinsicRadius_cross_congruent_iff {P : Set E} {Q : Set F}
    (h : Congruent P Q) (r : ℝ) : HasIntrinsicRadius P r ↔ HasIntrinsicRadius Q r :=
  ⟨fun hr => hr.cross_congruent h, fun hr => hr.cross_congruent (congruent_symm h)⟩

/-- The total intrinsic-radius definition is invariant as well: its zero
fallback agrees on congruent sets, including sets without a vertex sphere. -/
theorem intrinsicRadius_cross_congruent {P : Set E} {Q : Set F}
    (h : Congruent P Q) : intrinsicRadius P = intrinsicRadius Q := by
  classical
  by_cases hP : ∃ r, HasIntrinsicRadius P r
  · obtain ⟨r, hr⟩ := hP
    exact hr.eq_intrinsicRadius.symm.trans (hr.cross_congruent h).eq_intrinsicRadius
  · have hQ : ¬ ∃ r, HasIntrinsicRadius Q r := by
      rintro ⟨r, hr⟩
      exact hP ⟨r, hr.cross_congruent (congruent_symm h)⟩
    simp only [intrinsicRadius, dif_neg hP, dif_neg hQ]

theorem uniform_intrinsicRadius_cross_congruent {n : ℕ} {P : Set E} {Q : Set F}
    (hP : Uniform (n + 3) P) (h : Congruent P Q) : intrinsicRadius P = intrinsicRadius Q :=
  ((uniform_hasIntrinsicRadius hP).cross_congruent h).eq_intrinsicRadius

theorem affineDimension_cross_congruent {P : Set E} {Q : Set F}
    (h : Congruent P Q) : affineDimension P = affineDimension Q := by
  have hs := affineDimension_congruent (congruent_euclidean_sum h)
  simpa only [affineDimension_affineIsometry_image] using hs

theorem finitePolytope_cross_congruent_iff {P : Set E} {Q : Set F}
    (h : Congruent P Q) : FinitePolytope P ↔ FinitePolytope Q := by
  have hs := finitePolytope_congruent_iff (congruent_euclidean_sum h)
  simpa only [finitePolytope_affineIsometry_image_iff] using hs

theorem uniform_cross_congruent_iff {P : Set E} {Q : Set F}
    (h : Congruent P Q) (n : ℕ) : Uniform n P ↔ Uniform n Q := by
  have hs := uniform_congruent_iff (congruent_euclidean_sum h) n
  simpa only [embedding_uniform_iff] using hs

theorem unitUniform_cross_congruent_iff {P : Set E} {Q : Set F}
    (h : Congruent P Q) (n : ℕ) : UnitUniform n P ↔ UnitUniform n Q := by
  have hs := unitUniform_congruent_iff (congruent_euclidean_sum h) n
  simpa only [embedding_unitUniform_iff] using hs

/-- Radius-based word angles can be evaluated in intrinsic coordinate
models even when the parent facet and its cells use different dimensions. -/
theorem facetWordAngle_cross_congruent {G H : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    {P A B : Set E} {Q : Set F} {A' : Set G} {B' : Set H} (k : ℕ)
    (hP : Uniform 4 P) (hA : Uniform 3 A) (hB : Uniform 3 B)
    (hPQ : Congruent P Q) (hAA : Congruent A A') (hBB : Congruent B B') :
    facetWordAngle k (intrinsicRadius P) (intrinsicRadius A) (intrinsicRadius B) =
      facetWordAngle k (intrinsicRadius Q) (intrinsicRadius A') (intrinsicRadius B') := by
  rw [uniform_intrinsicRadius_cross_congruent hP hPQ,
    uniform_intrinsicRadius_cross_congruent hA hAA,
    uniform_intrinsicRadius_cross_congruent hB hBB]

end Uniform5.Composition
