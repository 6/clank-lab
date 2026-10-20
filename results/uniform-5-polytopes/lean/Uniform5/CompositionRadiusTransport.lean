import Uniform5.CompositionCycleWords
import Uniform5.CompositionKnownTransport

/-! Intrinsic radii and facet-word angles respect actual geometric model
identification. No library completeness or numerical containment is assumed. -/
noncomputable section
namespace Uniform5.Composition
open Set
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Actual vertex centroids commute with Euclidean affine embeddings. -/
theorem embedding_vertexCentroid (f : E →ᵃⁱ[ℝ] F) {P : Set E} (hP : FinitePolytope P) :
    f (vertexCentroid (vertices P hP)) =
      vertexCentroid (vertices (f '' P) ((finitePolytope_affineIsometry_image_iff f P).mpr hP)) := by
  let V := vertices P hP
  let W := vertices (f '' P) ((finitePolytope_affineIsometry_image_iff f P).mpr hP)
  have hmap := V.map_affineCombination id (V.centroidWeights ℝ)
    (V.sum_centroidWeights_eq_one_of_nonempty ℝ (vertices_nonempty hP)) f.toAffineMap
  change f (V.centroid ℝ id) = W.centroid ℝ id
  calc
    f (V.centroid ℝ id) = V.centroid ℝ f := hmap
    _ = W.centroid ℝ id := by
      apply V.centroid_eq_of_inj_on_of_image_eq ℝ W
      · exact f.injective.injOn
      · exact Function.injective_id.injOn
      · simpa only [V, W, coe_vertices, Set.image_id] using embedding_extremePoints f P

theorem HasIntrinsicRadius.embedding {P : Set E} {r : ℝ}
    (hr : HasIntrinsicRadius P r) (f : E →ᵃⁱ[ℝ] F) : HasIntrinsicRadius (f '' P) r := by
  obtain ⟨hP, hr, hs⟩ := hr
  refine ⟨(finitePolytope_affineIsometry_image_iff f P).mpr hP, hr, ?_⟩
  intro y hy
  rw [← embedding_extremePoints f P] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  rw [← embedding_vertexCentroid f hP, ← dist_eq_norm, f.isometry.dist_eq, dist_eq_norm]
  exact hs x hx

theorem intrinsicRadius_embedding {P : Set E} {r : ℝ}
    (hr : HasIntrinsicRadius P r) (f : E →ᵃⁱ[ℝ] F) :
    intrinsicRadius (f '' P) = intrinsicRadius P :=
  (hr.embedding f).eq_intrinsicRadius.symm.trans hr.eq_intrinsicRadius

variable [FiniteDimensional ℝ E]

/-- In a common Euclidean ambient space, intrinsic congruence transports
actual radii through its proved ambient extension. -/
theorem HasIntrinsicRadius.congruent {P Q : Set E} {r : ℝ}
    (hr : HasIntrinsicRadius P r) (h : Congruent P Q) : HasIntrinsicRadius Q r := by
  obtain ⟨g, rfl⟩ := (congruent_iff_affineIsometryEquiv_image P Q).mp h
  exact hr.embedding g.toAffineIsometry

theorem uniform_intrinsicRadius_congruent {n : ℕ} {P Q : Set E}
    (hP : Uniform (n + 3) P) (h : Congruent P Q) : intrinsicRadius P = intrinsicRadius Q :=
  ((uniform_hasIntrinsicRadius hP).congruent h).eq_intrinsicRadius

omit [FiniteDimensional ℝ E] in
/-- A concrete check: translations do not change the actual radius. -/
theorem uniform_intrinsicRadius_translation {n : ℕ} {P : Set E}
    (hP : Uniform (n + 3) P) (v : E) :
    intrinsicRadius ((fun x => v + x) '' P) = intrinsicRadius P := by
  exact intrinsicRadius_embedding (uniform_hasIntrinsicRadius hP)
    (AffineIsometryEquiv.constVAdd ℝ E v).toAffineIsometry

/-- The exact geometric meaning of identical facet/cell labels: two
polygon occurrences with congruent parent and cell models have equal
word angles, without any same-orbit assumption. -/
theorem facetWordAngle_congruent {P Q A A' B B' : Set E} (k : ℕ)
    (hP : Uniform 4 P) (hA : Uniform 3 A) (hB : Uniform 3 B)
    (hPQ : Congruent P Q) (hAA : Congruent A A') (hBB : Congruent B B') :
    facetWordAngle k (intrinsicRadius P) (intrinsicRadius A) (intrinsicRadius B) =
      facetWordAngle k (intrinsicRadius Q) (intrinsicRadius A') (intrinsicRadius B') := by
  rw [uniform_intrinsicRadius_congruent hP hPQ, uniform_intrinsicRadius_congruent hA hAA,
    uniform_intrinsicRadius_congruent hB hBB]

/-- Every actual nonempty proper face has smaller intrinsic radius. This
uses the proved centroid projection and strict face-interior separation. -/
theorem uniform_proper_face_intrinsicRadius_lt {n : ℕ} {P F : Set E}
    (hP : Uniform (n + 3) P) (hF : IsConvexFace P F) (hne : F.Nonempty)
    (hproper : F ≠ P) : intrinsicRadius F < intrinsicRadius P := by
  obtain ⟨_, hR, hs⟩ := uniform_hasIntrinsicRadius hP
  obtain ⟨r, hr, hlt, hsr, _, _, _, _⟩ :=
    uniform_proper_face_radius_lt hP hF hne (hproper) (intrinsicRadius P) hR hs
  have hf : HasIntrinsicRadius F r := ⟨_, hr, hsr⟩
  rwa [hf.eq_intrinsicRadius] at hlt

/-- The strict reciprocal-radius domain used in S1 is derived for any
nonempty finite selection of actual facets. Degenerate endpoint equality
is excluded without an interval hypothesis. -/
theorem unitUniform5_facet_radius_domain {P : Set E} (hP : UnitUniform 5 P)
    {ι : Type*} [Fintype ι] [Nonempty ι] (A : ι → Set E) (hA : ∀ i, Facet P (A i)) :
    let Rmax := Finset.univ.sup' Finset.univ_nonempty (fun i => intrinsicRadius (A i))
    0 < Rmax ∧ Rmax < intrinsicRadius P ∧
      0 < 1 / intrinsicRadius P ∧ 1 / intrinsicRadius P < 1 / Rmax := by
  classical
  let Rmax := Finset.univ.sup' Finset.univ_nonempty (fun i => intrinsicRadius (A i))
  have hpos (i : ι) : 0 < intrinsicRadius (A i) :=
    uniform_intrinsicRadius_pos (uniform_facets hP.1 (hA i))
  have hproper (i : ι) : A i ≠ P := by
    intro he
    have hh := (hA i).2.2
    rw [he] at hh
    omega
  have hlt (i : ι) : intrinsicRadius (A i) < intrinsicRadius P :=
    uniform_proper_face_intrinsicRadius_lt hP.1 (hA i).1 (hA i).2.1 (hproper i)
  have hmax : Rmax < intrinsicRadius P :=
    (Finset.sup'_lt_iff Finset.univ_nonempty).mpr (fun i _ => hlt i)
  obtain ⟨i⟩ := ‹Nonempty ι›
  have hmaxpos : 0 < Rmax := (hpos i).trans_le
    (Finset.le_sup' (fun i => intrinsicRadius (A i)) (Finset.mem_univ i))
  exact ⟨hmaxpos, hmax, one_div_pos.mpr (uniform_intrinsicRadius_pos hP.1),
    one_div_lt_one_div_of_lt hmaxpos hmax⟩

end Uniform5.Composition
