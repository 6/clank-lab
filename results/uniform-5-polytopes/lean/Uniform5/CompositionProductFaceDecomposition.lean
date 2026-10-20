import Uniform5.CompositionProductAssociativity

/-! Every nonempty actual convex face of an orthogonal product is itself
the product of two actual factor faces. The proof uses rectangle midpoints
and extremity, with no assumed face enumeration or exposing functional. -/
noncomputable section
namespace Uniform5.Composition
open Set

noncomputable def productLeftProjection {a b : ℕ} :
    EuclideanSpace ℝ (Fin a ⊕ Fin b) →ₗ[ℝ] Space a where
  toFun z := fun i => z (Sum.inl i)
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

noncomputable def productRightProjection {a b : ℕ} :
    EuclideanSpace ℝ (Fin a ⊕ Fin b) →ₗ[ℝ] Space b where
  toFun z := fun i => z (Sum.inr i)
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

@[simp] theorem productLeftProjection_point {a b : ℕ} (x : Space a) (y : Space b) :
    productLeftProjection (productPoint x y) = x := rfl

@[simp] theorem productRightProjection_point {a b : ℕ} (x : Space a) (y : Space b) :
    productRightProjection (productPoint x y) = y := rfl

theorem productPoint_projections {a b : ℕ} (z : EuclideanSpace ℝ (Fin a ⊕ Fin b)) :
    productPoint (productLeftProjection z) (productRightProjection z) = z := by
  ext i
  cases i <;> rfl

/-- A face containing opposite corners of a rectangle contains both cross corners. -/
theorem product_face_cross {a b : ℕ} {P : Set (Space a)} {Q : Set (Space b)}
    {F : Set (EuclideanSpace ℝ (Fin a ⊕ Fin b))} (hF : IsConvexFace (product P Q) F)
    {x x' : Space a} {y y' : Space b}
    (hz : productPoint x y ∈ F) (hw : productPoint x' y' ∈ F) :
    productPoint x y' ∈ F ∧ productPoint x' y ∈ F := by
  have hp (u : Space a) (v : Space b) (h : productPoint u v ∈ product P Q) : u ∈ P ∧ v ∈ Q := by
    obtain ⟨u', hu', v', hv', he⟩ := h
    have hu := congrArg productLeftProjection he
    have hv := congrArg productRightProjection he
    simp only [productLeftProjection_point, productRightProjection_point] at hu hv
    exact ⟨hu.symm ▸ hu', hv.symm ▸ hv'⟩
  have hxy := hp x y (hF.2.1 hz)
  have hxy' := hp x' y' (hF.2.1 hw)
  let m := (1 / 2 : ℝ) • productPoint x y + (1 / 2 : ℝ) • productPoint x' y'
  have hm : m ∈ F := hF.1 hz hw (by norm_num) (by norm_num) (by norm_num)
  apply hF.2.2 ⟨x, hxy.1, y', hxy'.2, rfl⟩ ⟨x', hxy'.1, y, hxy.2, rfl⟩ hm
  refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
  ext i
  cases i <;> simp [m, productPoint, add_comm]

/-- The product description is exact, for the actual projection images. -/
theorem product_face_eq_projections {a b : ℕ} {P : Set (Space a)} {Q : Set (Space b)}
    {F : Set (EuclideanSpace ℝ (Fin a ⊕ Fin b))} (hF : IsConvexFace (product P Q) F) :
    F = product (productLeftProjection '' F) (productRightProjection '' F) := by
  apply Subset.antisymm
  · intro z hz
    exact ⟨_, mem_image_of_mem _ hz, _, mem_image_of_mem _ hz, (productPoint_projections z).symm⟩
  · rintro _ ⟨x, ⟨z, hz, rfl⟩, y, ⟨w, hw, rfl⟩, rfl⟩
    exact (product_face_cross hF (x := productLeftProjection z) (y := productRightProjection z)
      (x' := productLeftProjection w) (y' := productRightProjection w)
      (by simpa only [productPoint_projections] using hz)
      (by simpa only [productPoint_projections] using hw)).1

/-- The projection onto the first factor is an actual convex face. -/
theorem product_face_left_projection {a b : ℕ} {P : Set (Space a)} {Q : Set (Space b)}
    {F : Set (EuclideanSpace ℝ (Fin a ⊕ Fin b))} (hF : IsConvexFace (product P Q) F)
    (hne : F.Nonempty) : IsConvexFace P (productLeftProjection '' F) := by
  obtain ⟨w, hw⟩ := hne
  have hy : productRightProjection w ∈ Q := by
    obtain ⟨x, hx, y, hy, rfl⟩ := hF.2.1 hw
    exact hy
  refine ⟨hF.1.linear_image productLeftProjection, ?_, ?_⟩
  · rintro x ⟨z, hz, rfl⟩
    obtain ⟨u, hu, v, hv, rfl⟩ := hF.2.1 hz
    exact hu
  · intro x hx x' hx' z hz hs
    obtain ⟨u, hu, rfl⟩ := hz
    have hzw : productPoint (productLeftProjection u) (productRightProjection w) ∈ F :=
      (product_face_cross hF (x := productLeftProjection u) (y := productRightProjection u)
        (x' := productLeftProjection w) (y' := productRightProjection w)
        (by simpa only [productPoint_projections] using hu)
        (by simpa only [productPoint_projections] using hw)).1
    have hseg : productPoint (productLeftProjection u) (productRightProjection w) ∈
        openSegment ℝ (productPoint x (productRightProjection w))
          (productPoint x' (productRightProjection w)) := by
      obtain ⟨s, t, hs, ht, hst, he⟩ := hs
      refine ⟨s, t, hs, ht, hst, ?_⟩
      ext i
      cases i with
      | inl i => exact congrArg (fun v : Space a => v i) he
      | inr i => simp [productPoint]; linear_combination congrArg (fun r : ℝ => r * (productRightProjection w) i) hst
    have hh := hF.2.2 ⟨x, hx, _, hy, rfl⟩ ⟨x', hx', _, hy, rfl⟩ hzw hseg
    exact ⟨⟨_, hh.1, rfl⟩, ⟨_, hh.2, rfl⟩⟩

/-- The projection onto the second factor is an actual convex face. -/
theorem product_face_right_projection {a b : ℕ} {P : Set (Space a)} {Q : Set (Space b)}
    {F : Set (EuclideanSpace ℝ (Fin a ⊕ Fin b))} (hF : IsConvexFace (product P Q) F)
    (hne : F.Nonempty) : IsConvexFace Q (productRightProjection '' F) := by
  obtain ⟨w, hw⟩ := hne
  have hx : productLeftProjection w ∈ P := by
    obtain ⟨x, hx, y, hy, rfl⟩ := hF.2.1 hw
    exact hx
  refine ⟨hF.1.linear_image productRightProjection, ?_, ?_⟩
  · rintro y ⟨z, hz, rfl⟩
    obtain ⟨u, hu, v, hv, rfl⟩ := hF.2.1 hz
    exact hv
  · intro y hy y' hy' z hz hs
    obtain ⟨u, hu, rfl⟩ := hz
    have hwz : productPoint (productLeftProjection w) (productRightProjection u) ∈ F :=
      (product_face_cross hF (x := productLeftProjection w) (y := productRightProjection w)
        (x' := productLeftProjection u) (y' := productRightProjection u)
        (by simpa only [productPoint_projections] using hw)
        (by simpa only [productPoint_projections] using hu)).1
    have hseg : productPoint (productLeftProjection w) (productRightProjection u) ∈
        openSegment ℝ (productPoint (productLeftProjection w) y)
          (productPoint (productLeftProjection w) y') := by
      obtain ⟨s, t, hs, ht, hst, he⟩ := hs
      refine ⟨s, t, hs, ht, hst, ?_⟩
      ext i
      cases i with
      | inl i => simp [productPoint]; linear_combination congrArg (fun r : ℝ => r * (productLeftProjection w) i) hst
      | inr i => exact congrArg (fun v : Space b => v i) he
    have hh := hF.2.2 ⟨_, hx, y, hy, rfl⟩ ⟨_, hx, y', hy', rfl⟩ hwz hseg
    exact ⟨⟨_, hh.1, rfl⟩, ⟨_, hh.2, rfl⟩⟩

/-- No exposing-hyperplane or product-face completeness premise is required. -/
theorem product_face_decomposition {a b : ℕ} {P : Set (Space a)} {Q : Set (Space b)}
    {F : Set (EuclideanSpace ℝ (Fin a ⊕ Fin b))} (hF : IsConvexFace (product P Q) F)
    (hne : F.Nonempty) :
    ∃ A : Set (Space a), ∃ B : Set (Space b),
      IsConvexFace P A ∧ IsConvexFace Q B ∧ A.Nonempty ∧ B.Nonempty ∧ F = product A B :=
  ⟨_, _, product_face_left_projection hF hne, product_face_right_projection hF hne,
    hne.image _, hne.image _, product_face_eq_projections hF⟩

end Uniform5.Composition
