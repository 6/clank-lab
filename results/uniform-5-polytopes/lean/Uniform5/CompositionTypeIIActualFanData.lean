import Uniform5.CompositionTypeIIICellNeighbors
import Uniform5.CompositionPyramidLateralIdentification

/-! A coherent actual fan is constructed from F5(ii). Both pyramids use
the same actual antiprism base and their apices are the uniquely identified
third neighbors of the corresponding actual prism cells. -/
noncomputable section
namespace Uniform5.Composition
open Set

theorem finRotate_three_cell_incident_tail {m : ℕ} (hm : m = 3)
    (a t : Fin m) (ht : t ≠ a) :
    ∃ j : Fin m, j ≠ a ∧ finRotate m j ≠ a ∧ (j = t ∨ finRotate m j = t) := by
  subst m
  exact (by decide : ∀ a t : Fin 3, t ≠ a →
    ∃ j : Fin 3, j ≠ a ∧ finRotate 3 j ≠ a ∧ (j = t ∨ finRotate 3 j = t)) a t ht

structure TypeIIActualFanData {P G : Set (Space 5)}
    (D : ActualPolygonCycle P G) (v : Space 5) (n : ℕ) where
  anti : Fin D.length
  opposite : Fin D.length
  away : D.slotsAwayFrom anti = {opposite}
  length_three : D.length = 3
  antiprism : Congruent (D.cell anti) (antiprismModel n)
  first_model : Congruent (D.facet anti) (antiprismPrismModel n)
  last_model : Congruent (D.facet ((finRotate D.length).symm anti)) (antiprismPrismModel n)
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
  duoprism : ∃ q, 3 ≤ q ∧ Congruent (D.facet opposite) (duoprismModel n q)

namespace ActualPolygonCycle
variable {P G : Set (Space 5)} (D : ActualPolygonCycle P G)

theorem typeII_actual_fan {n : ℕ} (hP : UnitUniform 5 P)
    (hG : PolygonFace P G n) (hn : 17 ≤ n) {v : Space 5}
    (hv : v ∈ G.extremePoints ℝ) (hII : D.CaseBTypeII n) :
    Nonempty (TypeIIActualFanData D v n) := by
  classical
  obtain ⟨hlen, a, i, q, hq, hCA, haway, _, hanti, hqi⟩ := hII
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
  have hab : B.a ≠ B.b := by
    intro he
    have hh := B.chord_ab
    rw [he, dist_self] at hh
    have hc := CaseB.case_chord_pos (q := n) (by exact_mod_cast (show 3 ≤ n by omega))
    linarith
  have hc (t : Fin D.length) (ht : t ≠ a) :
      ∃ z, z ∈ D.cell t ∧ z ∉ G ∧ z ≠ B.a ∧ z ≠ B.b ∧
        ∀ w, Edge (D.cell t) v w ↔ w = B.a ∨ w = B.b ∨ w = z := by
    obtain ⟨u, hua, hrua, hut⟩ := finRotate_three_cell_incident_tail hlen a t ht
    have huaway : u ∈ D.slotsAwayFrom a := (D.slotsAwayFrom_mem a u).mpr ⟨hua, hrua⟩
    have hui : u = i := by simpa [haway] using huaway
    have hC : Facet (D.facet u) (D.cell t) := by
      rcases hut with he | he
      · rw [← he]; exact D.cell_facet hP hG u
      · rw [← he]; exact D.next_cell_facet hP hG u
    exact unitUniform4_duoprism_cell_third_neighbor (D.facet_unitUniform hP u)
      (by omega) hq (by omega) (hui.symm ▸ hqi) (hGfacet u) hv hC
      (D.cell_contains t) B.polygon_neighbors hab
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
    anti := a, opposite := i, away := haway, length_three := hlen,
    antiprism := hCA, first_model := hanti a haaway, last_model := hanti k hkaway,
    base := B, lateral := z,
    lateral_mem := fun t ht => (hz t ht).1,
    lateral_outside := fun t ht => (hz t ht).2.1,
    lateral_edges := fun t ht => (hz t ht).2.2.2.2,
    first := T₁, last := T₂, first_base := rfl, last_base := hT₂,
    first_apex := hfirst, last_apex := hlast, duoprism := ⟨q, hq, hqi⟩ }⟩

end ActualPolygonCycle
end Uniform5.Composition
