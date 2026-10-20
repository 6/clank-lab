import Uniform5.CompositionCaseBIndexedRadius

/-! An actual specified duoprism determines its parameter in the polygon
cycle. In particular a large second factor rules out cycle type (iii). -/
noncomputable section
namespace Uniform5.Composition
open Set

/-- The regular polygon angle determines its integer parameter. -/
theorem polygon_angle_parameter_injective {m n : ℕ} (hm : 3 ≤ m) (hn : 3 ≤ n)
    (he : Real.pi * (1 - 2 / (m : ℝ)) = Real.pi * (1 - 2 / (n : ℝ))) : m = n := by
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hh : (2 : ℝ) / m = 2 / n := by nlinarith [Real.pi_pos]
  have heq := (div_eq_div_iff hm0 hn0).mp hh
  exact_mod_cast (show (m : ℝ) = n by linarith)

namespace ActualPolygonCycle
variable {P G : Set (Space 5)} (D : ActualPolygonCycle P G)

/-- A duoprism's second parameter cannot change when the same actual slot
is recognized by another concrete model. -/
theorem duoprism_slot_parameter {k m n : ℕ} (hP : UnitUniform 5 P)
    (hG : PolygonFace P G k) (hk : k ≠ 4) (hm : 3 ≤ m) (hn : 3 ≤ n)
    (i : Fin D.length)
    (hM : Congruent (D.facet i) (duoprismModel k m))
    (hN : Congruent (D.facet i) (duoprismModel k n)) : m = n :=
  polygon_angle_parameter_injective hm hn
    ((D.duoprism_slot hP hG hk hm i hM).2.2.symm.trans
      (D.duoprism_slot hP hG hk hn i hN).2.2)

/-- A large-parameter duoprism slot is not an antiprism-prism slot. -/
theorem large_duoprism_slot_not_antiprism {k n : ℕ} (hP : UnitUniform 5 P)
    (hG : PolygonFace P G k) (hk : k ≠ 4) (hn : 17 ≤ n)
    (i : Fin D.length) (hN : Congruent (D.facet i) (duoprismModel k n)) :
    ¬ Congruent (D.facet i) (antiprismPrismModel k) := by
  intro hA
  have h₁ := (D.duoprism_slot hP hG hk (by omega) i hN).2.2
  have h₂ := (D.antiprismPrism_slot hP hG hk i hA).2
  have hn' : (17 : ℝ) ≤ n := by exact_mod_cast hn
  have hdiv : (2 : ℝ) / n < 1 / 2 :=
    (div_lt_iff₀ (by positivity : (0 : ℝ) < n)).mpr (by linarith)
  nlinarith [Real.pi_pos]

/-- Type (iii) permits only second parameters 3, 4, and 5, so cannot
contain an actual duoprism with a large second factor. -/
theorem large_duoprism_not_typeIII {k n : ℕ} (hP : UnitUniform 5 P)
    (hG : PolygonFace P G k) (hk : k ≠ 4) (hn : 17 ≤ n)
    (s : Fin D.length) (hN : Congruent (D.facet s) (duoprismModel k n)) :
    ¬ D.CaseBTypeIII k := by
  rintro ⟨_, a, i, j, q, r, _, hq, hr, hpair, _, hslots, _, hanti, hqi, hrj⟩
  have hs : s ∈ D.slotsAwayFrom a := by
    by_contra hs
    exact D.large_duoprism_slot_not_antiprism hP hG hk hn s hN (hanti s hs)
  rw [hslots, Finset.mem_insert, Finset.mem_singleton] at hs
  have hbq : q ≤ 5 := by
    rcases hpair with ⟨rfl, _⟩ | ⟨_, hq⟩
    · omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      omega
  have hbr : r ≤ 5 := by
    rcases hpair with ⟨_, hr⟩ | ⟨rfl, _⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      omega
    · omega
  rcases hs with rfl | rfl
  · have he := D.duoprism_slot_parameter hP hG hk (show 3 ≤ n by omega) hq s hN hqi
    omega
  · have he := D.duoprism_slot_parameter hP hG hk (show 3 ≤ n by omega) hr s hN hrj
    omega

/-- A family polygon or a large polygon containing a specified large
second factor has just the type-(i)/(ii) alternatives used by P1 and the
partner filter. This is derived from the actual F5 classification. -/
theorem large_duoprism_cycle_types (classification4D : CitedClassification4D)
    {k n : ℕ} (hP : UnitUniform 5 P) (hG : PolygonFace P G k)
    (hk : ¬ CaseB.ExceptionalPolygon k) (hn : 17 ≤ n)
    (s : Fin D.length) (hN : Congruent (D.facet s) (duoprismModel k n)) :
    D.CaseBTypeI k ∨ D.CaseBTypeII k := by
  have hk4 : k ≠ 4 := by
    intro he
    exact hk (by simp [CaseB.ExceptionalPolygon, he])
  rcases D.nonexceptional_cycle_types classification4D hP hG hk with hI | hII | hIII
  · exact Or.inl hI
  · exact Or.inr hII
  · exact (D.large_duoprism_not_typeIII hP hG hk4 hn s hN hIII).elim

/-- The parameter of a specified actual duoprism occurs in the actual
configuration, so its canonical partner tail and radius equation follow. -/
theorem typeI_specified_duoprism_radius {k n : ℕ} (hP : UnitUniform 5 P)
    (hG : PolygonFace P G k) (hk : k ≠ 4) (hn : 17 ≤ n)
    (geometry : D.Stage1Geometry k) (hI : D.CaseBTypeI k)
    (s : Fin D.length) (hN : Congruent (D.facet s) (duoprismModel k n)) :
    ∃ tail : List ℕ, CaseB.PartnerTail n tail ∧
      CaseB.AngleCondition ((n : ℝ) :: CaseB.realConfig tail) ∧
      CaseB.Closable ((n : ℝ) :: CaseB.realConfig tail) ∧
      intrinsicRadius P ^ 2 = CaseB.polygonRadius k ^ 2 +
        CaseB.polygonRadius n ^ 2 + CaseB.delta tail n := by
  obtain ⟨_, q, hq, _⟩ := hI
  have he : q s = n := D.duoprism_slot_parameter hP hG hk (hq s).1
    (by omega) s (hq s).2.1 hN
  have hmem : n ∈ List.ofFn q := List.mem_ofFn.mpr ⟨s, he⟩
  obtain ⟨tail, _, ht, ha, hc, hr⟩ := D.typeI_paired_radius_data hP hG hk geometry
    q (fun j => (hq j).1) (fun j => (hq j).2.1) (fun j => (hq j).2.2) hn hmem
  exact ⟨tail, ht, ha, hc, hr⟩

end ActualPolygonCycle
end Uniform5.Composition
