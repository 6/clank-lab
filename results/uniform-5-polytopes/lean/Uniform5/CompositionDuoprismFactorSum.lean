import Uniform5.CompositionDuoprismFactorPair

/-! A duoprism is the affine sum of its two complementary factor polygons
through a root. The statement concerns whole faces, not just root neighbors. -/
noncomputable section
namespace Uniform5.Composition
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def rootedFaceSum (G H : Set E) (v : E) : Set E :=
  {z | ∃ x ∈ G, ∃ y ∈ H, z = x + y - v}

theorem rootedFaceSum_comm (G H : Set E) (v : E) :
    rootedFaceSum G H v = rootedFaceSum H G v := by
  ext z
  constructor <;> rintro ⟨x, hx, y, hy, rfl⟩ <;>
    exact ⟨y, hy, x, hx, by simp only [sub_eq_add_neg, neg_add_rev]; abel⟩

theorem embedding_product_eq_rootedFaceSum {a b : ℕ}
    (f : EuclideanSpace ℝ (Fin a ⊕ Fin b) →ᵃⁱ[ℝ] E)
    (A : Set (Space a)) (B : Set (Space b)) (x₀ : Space a) (y₀ : Space b) :
    f '' product A B = rootedFaceSum (f '' product A {y₀}) (f '' product {x₀} B)
      (f (productPoint x₀ y₀)) := by
  have he (x : Space a) (y : Space b) :
      f (productPoint x y) = f (productPoint x y₀) + f (productPoint x₀ y) -
        f (productPoint x₀ y₀) := by
    have hh := f.map_vadd (productPoint x y₀) (productPoint x₀ y - productPoint x₀ y₀)
    have hlin : f.linearIsometry (productPoint x₀ y - productPoint x₀ y₀) =
        f (productPoint x₀ y) - f (productPoint x₀ y₀) :=
      f.map_vsub (productPoint x₀ y) (productPoint x₀ y₀)
    rw [hlin] at hh
    have hh0 : (productPoint x₀ y - productPoint x₀ y₀) +ᵥ productPoint x y₀ =
        productPoint x y := by
      ext i
      cases i <;> simp [productPoint, vadd_eq_add]
    rw [hh0] at hh
    simp only [vsub_eq_sub, vadd_eq_add] at hh
    rw [hh]
    abel
  ext z
  constructor
  · rintro ⟨_, ⟨x, hx, y, hy, rfl⟩, rfl⟩
    exact ⟨f (productPoint x y₀), ⟨_, ⟨x, hx, y₀, rfl, rfl⟩, rfl⟩,
      f (productPoint x₀ y), ⟨_, ⟨x₀, rfl, y, hy, rfl⟩, rfl⟩, he x y⟩
  · rintro ⟨_, ⟨_, ⟨x, hx, y, hy, rfl⟩, rfl⟩,
      _, ⟨_, ⟨x', hx', y', hy', rfl⟩, rfl⟩, rfl⟩
    have hy0 : y = y₀ := hy
    have hx0 : x' = x₀ := hx'
    subst y
    subst x'
    exact ⟨productPoint x y', ⟨x, hx, y', hy', rfl⟩, he x y'⟩

/-- Rooted sums commute with simultaneous translation of both faces. -/
theorem rootedFaceSum_translate (G H : Set E) (v d : E) :
    rootedFaceSum (CaseB.translate G d) (CaseB.translate H d) (v + d) =
      CaseB.translate (rootedFaceSum G H v) d := by
  ext z
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨x + y - v, ⟨x, hx, y, hy, rfl⟩, by simp only [sub_eq_add_neg, neg_add_rev]; abel⟩
  · rintro ⟨_, ⟨x, hx, y, hy, rfl⟩, rfl⟩
    exact ⟨x + d, ⟨x, hx, rfl⟩, y + d, ⟨y, hy, rfl⟩, by simp only [sub_eq_add_neg, neg_add_rev]; abel⟩

private theorem embedded_duoprism_rooted_sum {p q n m : ℕ}
    (hp : 3 ≤ p) (hq : 3 ≤ q)
    (f : EuclideanSpace ℝ (Fin 2 ⊕ Fin 2) →ᵃⁱ[ℝ] E)
    {G H : Set (EuclideanSpace ℝ (Fin 2 ⊕ Fin 2))}
    (hG : PolygonFace (duoprismModel p q) G n) (hn : n ≠ 4)
    (hH : PolygonFace (duoprismModel p q) H m) (hm : m ≠ 4)
    {v : EuclideanSpace ℝ (Fin 2 ⊕ Fin 2)} (hvG : v ∈ G) (hvH : v ∈ H)
    (hne : G ≠ H) :
    f '' duoprismModel p q = rootedFaceSum (f '' G) (f '' H) (f v) := by
  obtain ⟨x₀, hx₀, y₀, hy₀, rfl⟩ := hG.1.2.1 hvG
  rcases duoprism_nonquadrilateral_polygon_slices hp hq hG hn with
    ⟨_, y, hy, hgs⟩ | ⟨_, x, hx, hgs⟩ <;>
    rcases duoprism_nonquadrilateral_polygon_slices hp hq hH hm with
    ⟨_, y', hy', hhs⟩ | ⟨_, x', hx', hhs⟩
  · have h1 : y₀ = y := ((productPoint_mem_product (x := x₀) (y := y₀) (P := unitPolygon p) (Q := {y})).mp (hgs ▸ hvG)).2
    have h2 : y₀ = y' := ((productPoint_mem_product (x := x₀) (y := y₀) (P := unitPolygon p) (Q := {y'})).mp (hhs ▸ hvH)).2
    exact (hne (hgs.trans (by rw [hhs, ← h1, ← h2]))).elim
  · have h1 : y₀ = y := ((productPoint_mem_product (x := x₀) (y := y₀) (P := unitPolygon p) (Q := {y})).mp (hgs ▸ hvG)).2
    have h2 : x₀ = x' := ((productPoint_mem_product (x := x₀) (y := y₀) (P := {x'}) (Q := unitPolygon q)).mp (hhs ▸ hvH)).1
    rw [hgs, hhs, ← h1, ← h2]
    exact embedding_product_eq_rootedFaceSum f _ _ _ _
  · have h1 : x₀ = x := ((productPoint_mem_product (x := x₀) (y := y₀) (P := {x}) (Q := unitPolygon q)).mp (hgs ▸ hvG)).1
    have h2 : y₀ = y' := ((productPoint_mem_product (x := x₀) (y := y₀) (P := unitPolygon p) (Q := {y'})).mp (hhs ▸ hvH)).2
    rw [rootedFaceSum_comm, hgs, hhs, ← h1, ← h2]
    exact embedding_product_eq_rootedFaceSum f _ _ _ _
  · have h1 : x₀ = x := ((productPoint_mem_product (x := x₀) (y := y₀) (P := {x}) (Q := unitPolygon q)).mp (hgs ▸ hvG)).1
    have h2 : x₀ = x' := ((productPoint_mem_product (x := x₀) (y := y₀) (P := {x'}) (Q := unitPolygon q)).mp (hhs ▸ hvH)).1
    exact (hne (hgs.trans (by rw [hhs, ← h1, ← h2]))).elim

/-- Any two distinct nonquadrilateral polygons of an actual duoprism
through one root determine its entire set. -/
theorem unitUniform4_duoprism_eq_rootedFaceSum {K G H : Set E} {p q n m : ℕ}
    (hK : UnitUniform 4 K) (hp : 3 ≤ p) (hq : 3 ≤ q)
    (hmodel : Congruent K (duoprismModel p q))
    (hG : PolygonFace K G n) (hn : n ≠ 4)
    (hH : PolygonFace K H m) (hm : m ≠ 4)
    {v : E} (hvG : v ∈ G) (hvH : v ∈ H) (hne : G ≠ H) :
    K = rootedFaceSum G H v := by
  have hKN := congruent_trans hmodel
    (congruent_affineIsometry_image (flattenProduct 2 2).toAffineIsometry _)
  obtain ⟨f, hf⟩ := exists_embedding_of_congruent_model (uniform_finitePolytope hK.1)
    (uniform_dimension hK.1) hKN
  let j := f.comp (flattenProduct 2 2).toAffineIsometry
  have hj : j '' duoprismModel p q = K := by
    change (f ∘ flattenProduct 2 2) '' duoprismModel p q = K
    rw [Set.image_comp]
    exact hf
  have hM := (unitUniform_cross_congruent_iff hmodel 4).mp hK
  have hG' : PolygonFace (j '' duoprismModel p q) G n := hj ▸ hG
  have hH' : PolygonFace (j '' duoprismModel p q) H m := hj ▸ hH
  have hG₀ := embedding_polygonFace_preimage j (uniform_finitePolytope hM.1) hG'
  have hH₀ := embedding_polygonFace_preimage j (uniform_finitePolytope hM.1) hH'
  have hGi := embedding_face_image_preimage j hG'.1
  have hHi := embedding_face_image_preimage j hH'.1
  have hvK : v ∈ j '' duoprismModel p q := hj.symm ▸ hG.1.2.1 hvG
  obtain ⟨v₀, hv₀, rfl⟩ := hvK
  have hne₀ : j ⁻¹' G ≠ j ⁻¹' H := by
    intro he
    exact hne (hGi.symm.trans ((congrArg (fun A => j '' A) he).trans hHi))
  have hh := embedded_duoprism_rooted_sum hp hq j hG₀ hn hH₀ hm hvG hvH hne₀
  rwa [hj, hGi, hHi] at hh

end Uniform5.Composition
