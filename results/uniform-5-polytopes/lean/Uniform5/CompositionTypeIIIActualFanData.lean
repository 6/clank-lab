import Uniform5.CompositionTypeIIICellNeighbors
import Uniform5.CompositionPyramidLateralIdentification

/-! A coherent actual fan is constructed from F5(iii). Both pyramids use
the same actual antiprism base and their apices are the uniquely identified
third neighbors of the corresponding actual prism cells. -/
noncomputable section
namespace Uniform5.Composition
open Set

structure TypeIIIActualFanData {P G : Set (Space 5)}
    (D : ActualPolygonCycle P G) (v : Space 5) (n : ℕ) where
  anti : Fin D.length
  length_four : D.length = 4
  base : AntiprismNeighborChart (D.cell anti) G v n
  lateral : Fin D.length → Space 5
  lateral_mem : ∀ t, t ≠ anti → lateral t ∈ D.cell t
  lateral_outside : ∀ t, t ≠ anti → lateral t ∉ G
  lateral_edges : ∀ t, t ≠ anti → ∀ w,
    Edge (D.cell t) v w ↔ w = base.a ∨ w = base.b ∨ w = lateral t
  first : AntiprismPrismNeighborChart (D.facet anti) (D.cell anti) G v n
  last : AntiprismPrismNeighborChart (D.facet ((finRotate D.length).symm anti))
    (D.cell anti) G v n
  first_base : first.base = base
  last_base : last.base = base
  first_apex : first.apex = lateral (finRotate D.length anti)
  last_apex : last.apex = lateral ((finRotate D.length).symm anti)
  duoprism : ∀ t ∈ D.slotsAwayFrom anti,
    ∃ q, 3 ≤ q ∧ Congruent (D.facet t) (duoprismModel n q)
  duoprism_pair : ∃ q r, 3 ≤ q ∧ 3 ≤ r ∧ CaseB.TypeIIIPair q r ∧
    Congruent (D.facet (finRotate D.length anti)) (duoprismModel n q) ∧
    Congruent (D.facet (finRotate D.length (finRotate D.length anti))) (duoprismModel n r)

namespace ActualPolygonCycle
variable {P G : Set (Space 5)} (D : ActualPolygonCycle P G)

theorem typeIII_actual_fan {n : ℕ} (hP : UnitUniform 5 P)
    (hG : PolygonFace P G n) (hn : 17 ≤ n) {v : Space 5}
    (hv : v ∈ G.extremePoints ℝ) (hIII : D.CaseBTypeIII n) :
    Nonempty (TypeIIIActualFanData D v n) := by
  classical
  obtain ⟨hlen, a, i, j, q, r, _, hq, hr, hpair, hCA, haway, _, hanti, hqi, hrj⟩ := hIII
  have haaway : a ∉ D.slotsAwayFrom a := by simp [slotsAwayFrom]
  let k := (finRotate D.length).symm a
  have hkaway : k ∉ D.slotsAwayFrom a := by
    rw [D.slotsAwayFrom_mem]
    intro hh
    exact hh.2 ((finRotate D.length).apply_symm_apply a)
  have hGfacet (t : Fin D.length) : PolygonFace (D.facet t) G n :=
    ⟨face_restrict hG.1 (D.facet_incidence t).1.1.2.1 (D.facet_incidence t).2.1, hG.2⟩
  obtain ⟨T₁⟩ := unitUniform4_antiprismPrism_specified_chart (D.facet_unitUniform hP a)
    (by omega : 5 ≤ n) (hanti a haaway) (hGfacet a) hv
    (D.cell_facet hP hG a) (D.cell_contains a) hCA
  let B := T₁.base
  obtain ⟨T₂, hT₂⟩ := unitUniform4_antiprismPrism_shared_base (D.facet_unitUniform hP k)
    (by omega : 5 ≤ n) (hanti k hkaway) (hGfacet k) hv
    (D.cell_facet_of_not_away hP hG a k hkaway) (D.cell_contains a) hCA B
  have hc := D.typeIII_cell_third_neighbors hP hG hn hv hlen a i j q r hq hr haway hqi hrj B
  have hc' : ∀ t : Fin D.length, ∃ z : Space 5, t ≠ a →
      z ∈ D.cell t ∧ z ∉ G ∧ z ≠ B.a ∧ z ≠ B.b ∧
        ∀ w, Edge (D.cell t) v w ↔ w = B.a ∨ w = B.b ∨ w = z := by
    intro t
    by_cases ht : t = a
    · exact ⟨v, fun h => (h ht).elim⟩
    · obtain ⟨z, hz⟩ := hc t ht
      exact ⟨z, fun _ => hz⟩
  choose z hz using hc'
  have hcellne (t : Fin D.length) (ht : t ≠ a) : D.cell t ≠ D.cell a := by
    intro he
    exact ht (Fin.ext (D.cell_injective t.isLt a.isLt he))
  have hra : finRotate D.length a ≠ a := (finRotate_ne_and_twice_ne D.length_ge a).1
  have hka : k ≠ a := D.predecessor_ne a
  have hfirst : T₁.apex = z (finRotate D.length a) := by
    symm
    apply T₁.cell_lateral_eq_apex (P := P)
      (uniform_finitePolytope (D.facet_unitUniform hP a).1)
      (D.next_cell_facet hP hG a).1 hG.1 (D.cell_face a)
      (D.cell_face _) (D.cell_contains a) (D.cell_contains _)
      hG.2.1 (D.cell_dimension a) (D.cell_dimension _) (hcellne _ hra)
    · exact ((hz _ hra).2.2.2.2 _).mpr (Or.inr (Or.inr rfl))
    · exact (hz _ hra).2.1
  have hlast : T₂.apex = z k := by
    symm
    apply T₂.cell_lateral_eq_apex (P := P)
      (uniform_finitePolytope (D.facet_unitUniform hP k).1)
      (D.cell_facet hP hG k).1 hG.1 (D.cell_face a)
      (D.cell_face k) (D.cell_contains a) (D.cell_contains k)
      hG.2.1 (D.cell_dimension a) (D.cell_dimension k) (hcellne k hka)
    · exact ((hz k hka).2.2.2.2 _).mpr (Or.inr (Or.inr rfl))
    · exact (hz k hka).2.1
  refine ⟨{
    anti := a, length_four := hlen, base := B, lateral := z,
    lateral_mem := fun t ht => (hz t ht).1,
    lateral_outside := fun t ht => (hz t ht).2.1,
    lateral_edges := fun t ht => (hz t ht).2.2.2.2,
    first := T₁, last := T₂, first_base := rfl, last_base := hT₂,
    first_apex := hfirst, last_apex := hlast, duoprism := ?_, duoprism_pair := ?_ }⟩
  · intro t ht
    have ht' : t = i ∨ t = j := by simpa [haway] using ht
    rcases ht' with rfl | rfl
    · exact ⟨q, hq, hqi⟩
    · exact ⟨r, hr, hrj⟩
  · have hcirc : ∀ (m : ℕ), m = 4 → ∀ a : Fin m,
        finRotate m (finRotate m a) ≠ a ∧
        finRotate m (finRotate m (finRotate m a)) = (finRotate m).symm a := by
      intro m hm
      subst m
      decide
    obtain ⟨hrr, hrrr⟩ := hcirc D.length hlen a
    have hfirst : finRotate D.length a ∈ D.slotsAwayFrom a :=
      (D.slotsAwayFrom_mem a _).mpr ⟨hra, hrr⟩
    have hsecond : finRotate D.length (finRotate D.length a) ∈ D.slotsAwayFrom a := by
      apply (D.slotsAwayFrom_mem a _).mpr
      exact ⟨hrr, by rw [hrrr]; exact hka⟩
    have hnxt : finRotate D.length a ≠ finRotate D.length (finRotate D.length a) :=
      (finRotate_ne_and_twice_ne D.length_ge (finRotate D.length a)).1.symm
    rw [haway] at hfirst hsecond
    simp only [Finset.mem_insert, Finset.mem_singleton] at hfirst hsecond
    rcases hfirst with hfi | hfj <;> rcases hsecond with hsi | hsj
    · exact (hnxt (hfi.trans hsi.symm)).elim
    · exact ⟨q,r,hq,hr,hpair,hfi.symm ▸ hqi,hsj.symm ▸ hrj⟩
    · refine ⟨r,q,hr,hq,?_,hfj.symm ▸ hrj,hsi.symm ▸ hqi⟩
      unfold CaseB.TypeIIIPair at hpair ⊢
      tauto
    · exact (hnxt (hfj.trans hsj.symm)).elim

end ActualPolygonCycle
end Uniform5.Composition
