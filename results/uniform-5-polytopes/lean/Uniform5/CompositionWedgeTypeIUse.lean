import Uniform5.CompositionWedgeTypeIDiagonals
import Uniform5.CompositionWedgeActualUse

/-! W's complete actual Type I consequence. All geometric, admissibility,
endpoint, and diagonal premises are discharged from actual incidence. -/
noncomputable section
namespace Uniform5.Composition.TypeIFanChart
open Set
variable {P G : Set (Space 5)} {D : ActualPolygonCycle P G} {v : Space 5} {n : ℕ}
    (T : TypeIFanChart D v n) {q : Fin D.length → ℕ}

theorem wedge_unpaired_only_edge (p1 : CaseB.P1) (hW : Wedge.W p1)
    (hP : UnitUniform 5 P) (hG : PolygonFace P G n)
    (hn : 17 ≤ n) (hvG : v ∈ G.extremePoints ℝ)
    (hlen : D.length ≤ 5) (hq : ∀ i, 3 ≤ q i)
    (hmodel : ∀ i, Congruent (D.facet i) (duoprismModel n (q i)))
    (hcell : ∀ i : Fin D.length, Congruent (D.cell i) (polygonPrismModel n))
    {cs : List ℕ} (L : CyclicLabels (D := D) (cs.map fun q => some (q : ℝ)) q)
    (hlisted : CaseB.WListed p1 (some (n : ℝ)) (.unpairedI cs))
    {x y : Space 5} (he : Edge (vertexFigure P v
      (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))) x y)
    (hlong : CaseB.chord 17 ≤ dist x y) : Wedge.pair T.a T.b x y := by
  let S := T.wedgeShape hP hG (by omega) (by omega) hvG hlen hq hmodel hcell L
  let F := Wedge.actualGeometry hP v S.points {S.a, S.b}
    (fun x y => Wedge.pair S.a S.b x y ∨ S.diagonal x y) S.facets
  have hvP := hG.1.2.extremePoints_subset_extremePoints hvG
  have hpoints := T.wedgeShape_points hP hG (by omega) (by omega) hvG hlen hq hmodel hcell L
  have hfacets := T.wedgeShape_facets hP hG (by omega) (by omega) hvG hlen hq hmodel hcell L
  have hfinite : Wedge.finiteParameters (some (n : ℝ)) (.unpairedI cs) := by
    simp [Wedge.finiteParameters, Wedge.atInfinity]
  have hreal : Wedge.RealizesWFan p1 (some (n : ℝ)) (.unpairedI cs) F :=
    ⟨hfinite, T.wedge_unpaired_realizes hP hG hn hvG hlen hq hmodel hcell L⟩
  apply Wedge.actual_only_protected_edges p1 hW (by change (17 : ℝ) ≤ n; exact_mod_cast hn)
    hlisted F hreal hP hvP (Wedge.pair T.a T.b) S.diagonal Wedge.pair_symm
    _ _ (fun _ _ h => h) _ he hlong
  · intro z hz
    change z ∈ ({S.a,S.b} : Finset (Space 5)) at hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    have ha : S.a ∈ S.points := by simp [Wedge.TypeIShape.points]
    have hb : S.b ∈ S.points := by simp [Wedge.TypeIShape.points]
    have hab : CaseB.chord 17 ≤ dist S.a S.b := by
      rw [S.ab]
      exact CaseB.chord_mono (by norm_num) (by exact_mod_cast hn)
    rcases hz with rfl | rfl
    · exact ⟨S.b, hpoints hb, Or.inl ⟨rfl,rfl⟩, hab⟩
    · exact ⟨S.a, hpoints ha, Or.inr ⟨rfl,rfl⟩, by simpa only [dist_comm] using hab⟩
  · exact Wedge.actualGeometry_coverage hP hvP _ _ _ _ hpoints hfacets
  · intro a b hd
    exact T.wedgeShape_diagonal_not_edge hP hG (by omega) (by omega) hvG hlen hq hmodel hcell L hd

/-- In a paired fan the only long actual edges are the original polygon
edge and the actual first lateral edge, whose parameter is m. -/
theorem wedge_paired_only_edges (p1 : CaseB.P1) (hW : Wedge.W p1)
    (hP : UnitUniform 5 P) (hG : PolygonFace P G n)
    (hn : 17 ≤ n) (hvG : v ∈ G.extremePoints ℝ)
    (hlen : D.length ≤ 5) (hq : ∀ i, 3 ≤ q i)
    (hmodel : ∀ i, Congruent (D.facet i) (duoprismModel n (q i)))
    (hcell : ∀ i : Fin D.length, Congruent (D.cell i) (polygonPrismModel n))
    {m : ℕ} (hm : 17 ≤ m) {cs : List ℕ}
    (L : CyclicLabels (D := D) (some (m : ℝ) :: cs.map fun q => some (q : ℝ)) q)
    (hlisted : CaseB.WListed p1 (some (n : ℝ)) (.pairedI (some (m : ℝ)) cs))
    {x y : Space 5} (he : Edge (vertexFigure P v
      (vertexCentroid (vertices P (uniform_finitePolytope hP.1)))) x y)
    (hlong : CaseB.chord 17 ≤ dist x y) :
    let S := T.wedgeShape hP hG (by omega) (by omega) hvG hlen hq hmodel hcell L
    Wedge.pair T.a T.b x y ∨ S.partner x y := by
  dsimp only
  let S := T.wedgeShape hP hG (by omega) (by omega) hvG hlen hq hmodel hcell L
  let protectedPair := fun x y => Wedge.pair S.a S.b x y ∨ S.partner x y
  let F := Wedge.actualGeometry hP v S.points
    {S.a,S.b,S.x S.first,S.x (finRotate _ S.first)}
    (fun x y => Wedge.pair S.a S.b x y ∨ S.partner x y ∨ S.diagonal x y) S.facets
  have hvP := hG.1.2.extremePoints_subset_extremePoints hvG
  have hpoints := T.wedgeShape_points hP hG (by omega) (by omega) hvG hlen hq hmodel hcell L
  have hfacets := T.wedgeShape_facets hP hG (by omega) (by omega) hvG hlen hq hmodel hcell L
  have hfinite : Wedge.finiteParameters (some (n : ℝ)) (.pairedI (some (m : ℝ)) cs) := by
    simp [Wedge.finiteParameters, Wedge.atInfinity]
  have hreal : Wedge.RealizesWFan p1 (some (n : ℝ)) (.pairedI (some (m : ℝ)) cs) F :=
    ⟨hfinite, T.wedge_paired_realizes hP hG hn hvG hlen hq hmodel hcell L⟩
  apply Wedge.actual_only_protected_edges p1 hW (by change (17 : ℝ) ≤ n; exact_mod_cast hn)
    hlisted F hreal hP hvP protectedPair S.diagonal _ _ _ _ _ he hlong
  · intro a b h
    rcases h with h | h
    · exact Or.inl (Wedge.pair_symm h)
    · exact Or.inr (Wedge.pair_symm h)
  · intro z hz
    change z ∈ ({S.a,S.b,S.x S.first,S.x (finRotate _ S.first)} : Finset (Space 5)) at hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    have ha : S.a ∈ S.points := by simp [Wedge.TypeIShape.points]
    have hb : S.b ∈ S.points := by simp [Wedge.TypeIShape.points]
    have hc (i) : S.x i ∈ S.points := by simp [Wedge.TypeIShape.points]
    have hab : CaseB.chord 17 ≤ dist S.a S.b := by
      rw [S.ab]
      exact CaseB.chord_mono (by norm_num) (by exact_mod_cast hn)
    have hpartner : CaseB.chord 17 ≤ dist (S.x S.first) (S.x (finRotate _ S.first)) := by
      rw [S.consecutive]
      change CaseB.chord 17 ≤ CaseB.chord m
      exact CaseB.chord_mono (by norm_num) (by exact_mod_cast hm)
    rcases hz with rfl | rfl | rfl | rfl
    · exact ⟨S.b, hpoints hb, Or.inl (Or.inl ⟨rfl,rfl⟩), hab⟩
    · exact ⟨S.a, hpoints ha, Or.inl (Or.inr ⟨rfl,rfl⟩), by simpa only [dist_comm] using hab⟩
    · exact ⟨_, hpoints (hc _), Or.inr (Or.inl ⟨rfl,rfl⟩), hpartner⟩
    · exact ⟨_, hpoints (hc _), Or.inr (Or.inr ⟨rfl,rfl⟩), by simpa only [dist_comm] using hpartner⟩
  · exact Wedge.actualGeometry_coverage hP hvP _ _ _ _ hpoints hfacets
  · intro a b hh
    change Wedge.pair S.a S.b a b ∨ S.partner a b ∨ S.diagonal a b at hh
    change (Wedge.pair S.a S.b a b ∨ S.partner a b) ∨ S.diagonal a b
    tauto
  · intro a b hd
    exact T.wedgeShape_diagonal_not_edge hP hG (by omega) (by omega) hvG hlen hq hmodel hcell L hd

end Uniform5.Composition.TypeIFanChart
