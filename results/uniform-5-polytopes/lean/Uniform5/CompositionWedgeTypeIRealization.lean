import Uniform5.CompositionWedgeTypeIShape

/-! Every actual Type I chart, with its cyclic labels, realizes precisely
the finite geometric fan supplied to W. The sphere and halfspace premises
are proved here from the actual parent. -/
noncomputable section
namespace Uniform5.Composition.TypeIFanChart
open Set
variable {P G : Set (Space 5)} {D : ActualPolygonCycle P G} {v : Space 5} {n : ℕ}
    (T : TypeIFanChart D v n)
variable {c : List Wedge.Parameter} {q : Fin D.length → ℕ}

theorem wedgeShape_realizes (hP : UnitUniform 5 P) (hG : PolygonFace P G n)
    (hn : 17 ≤ n) (hvG : v ∈ G.extremePoints ℝ)
    (hlen : D.length ≤ 5) (hq : ∀ i, 3 ≤ q i)
    (hmodel : ∀ i, Congruent (D.facet i) (duoprismModel n (q i)))
    (hcell : ∀ i : Fin D.length, Congruent (D.cell i) (polygonPrismModel n))
    (L : CyclicLabels (D := D) c q)
    (ends : Finset (Space 5)) (special : Space 5 → Space 5 → Prop)
    {f : CaseB.WFan} (hfinite : Wedge.finiteParameters (some (n : ℝ)) f) :
    let S := T.wedgeShape hP hG (by omega) (by omega) hvG hlen hq hmodel hcell L
    Wedge.Realizes (some (n : ℝ)) f
      (Wedge.actualGeometry hP v S.points ends special S.facets)
      S.points S.facets ends special := by
  dsimp only
  apply Wedge.actualGeometry_realizes hP (hG.1.2.extremePoints_subset_extremePoints hvG)
    _ _ _ _ hfinite
  · exact T.wedgeShape_points hP hG (by omega) (by omega) hvG hlen hq hmodel hcell L
  · refine ⟨T.a, ?_, T.b, ?_, ?_⟩
    · simp [Wedge.TypeIShape.points, wedgeShape]
    · simp [Wedge.TypeIShape.points, wedgeShape]
    · rw [T.chord_ab]
      have hm := CaseB.chord_mono (by norm_num : (3 : ℝ) ≤ 17)
        (by exact_mod_cast hn : (17 : ℝ) ≤ n)
      linarith [CaseB.chord_seventeen_gt]
  · exact T.wedgeShape_facets hP hG (by omega) (by omega) hvG hlen hq hmodel hcell L

/-- The unpaired Type I realization includes exactly the two protected
endpoints and the paper's lateral diagonal exception. -/
theorem wedge_unpaired_realizes (hP : UnitUniform 5 P) (hG : PolygonFace P G n)
    (hn : 17 ≤ n) (hvG : v ∈ G.extremePoints ℝ)
    (hlen : D.length ≤ 5) (hq : ∀ i, 3 ≤ q i)
    (hmodel : ∀ i, Congruent (D.facet i) (duoprismModel n (q i)))
    (hcell : ∀ i : Fin D.length, Congruent (D.cell i) (polygonPrismModel n))
    {cs : List ℕ} (L : CyclicLabels (D := D) (cs.map fun q => some (q : ℝ)) q) :
    let S := T.wedgeShape hP hG (by omega) (by omega) hvG hlen hq hmodel hcell L
    let F := Wedge.actualGeometry hP v S.points {S.a, S.b}
      (fun x y => Wedge.pair S.a S.b x y ∨ S.diagonal x y) S.facets
    Wedge.RealizesFiniteFan (some (n : ℝ)) (.unpairedI cs) F := by
  dsimp only
  refine ⟨_, T.wedgeShape_realizes hP hG hn hvG hlen hq hmodel hcell L _ _ ?_⟩
  simp [Wedge.finiteParameters, Wedge.atInfinity]

/-- The paired Type I realization protects the actual first lateral edge
as well as the original polygon edge. -/
theorem wedge_paired_realizes (hP : UnitUniform 5 P) (hG : PolygonFace P G n)
    (hn : 17 ≤ n) (hvG : v ∈ G.extremePoints ℝ)
    (hlen : D.length ≤ 5) (hq : ∀ i, 3 ≤ q i)
    (hmodel : ∀ i, Congruent (D.facet i) (duoprismModel n (q i)))
    (hcell : ∀ i : Fin D.length, Congruent (D.cell i) (polygonPrismModel n))
    {m : ℕ} {cs : List ℕ}
    (L : CyclicLabels (D := D) (some (m : ℝ) :: cs.map fun q => some (q : ℝ)) q) :
    let S := T.wedgeShape hP hG (by omega) (by omega) hvG hlen hq hmodel hcell L
    let F := Wedge.actualGeometry hP v S.points
      {S.a, S.b, S.x S.first, S.x (finRotate _ S.first)}
      (fun x y => Wedge.pair S.a S.b x y ∨ S.partner x y ∨ S.diagonal x y) S.facets
    Wedge.RealizesFiniteFan (some (n : ℝ)) (.pairedI (some (m : ℝ)) cs) F := by
  dsimp only
  refine ⟨_, T.wedgeShape_realizes hP hG hn hvG hlen hq hmodel hcell L _ _ ?_⟩
  simp [Wedge.finiteParameters, Wedge.atInfinity]

end Uniform5.Composition.TypeIFanChart
