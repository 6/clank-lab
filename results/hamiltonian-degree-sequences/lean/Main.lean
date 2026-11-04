import Cycles

namespace NWDigraph

/-! ## Main results -/

theorem G6_counterexample : StronglyConnected G6 ∧ NWHyp G6 ∧ ¬ HasHamCycle G6 :=
  ⟨G6_sc, G6_nw, G6_noham⟩

theorem G7_counterexample : StronglyConnected G7 ∧ NWHyp G7 ∧ ¬ HasHamCycle G7 :=
  ⟨G7_sc, G7_nw, G7_noham⟩

/-- For every `u ≥ 4`, `F u` on `u + 4` vertices is strongly connected, satisfies the
Nash-Williams hypothesis and has no Hamilton cycle. -/
theorem F_counterexample (u : ℕ) (hu : 4 ≤ u) :
    StronglyConnected (F u) ∧ NWHyp (F u) ∧ ¬ HasHamCycle (F u) :=
  ⟨F_sc u (by omega), F_nw u hu, F_noham u⟩

/-- In `G6` no cycle passes through both vertex 2 and vertex 3. -/
theorem G6_no_cycle_through_2_3 : ¬ CycleThrough G6 2 3 := G6_nocycle

/-- In `F u` no cycle passes through both `s = u` and `r1 = u + 2`. -/
theorem F_no_cycle_through_s_r1 (u : ℕ) :
    ¬ CycleThrough (F u) ⟨u, by omega⟩ ⟨u + 2, by omega⟩ :=
  F_nocycle u _ _ rfl (Or.inl rfl)

/-- In `F u` no cycle passes through both `s = u` and `r2 = u + 3`. -/
theorem F_no_cycle_through_s_r2 (u : ℕ) :
    ¬ CycleThrough (F u) ⟨u, by omega⟩ ⟨u + 3, by omega⟩ :=
  F_nocycle u _ _ rfl (Or.inr rfl)

theorem counterexample_all (n : ℕ) (hn : 6 ≤ n) :
    ∃ G : Digraph n, StronglyConnected G ∧ NWHyp G ∧ ¬ HasHamCycle G := by
  rcases (by omega : n = 6 ∨ n = 7 ∨ 8 ≤ n) with rfl | rfl | h
  · exact ⟨G6, G6_counterexample⟩
  · exact ⟨G7, G7_counterexample⟩
  · obtain ⟨u, rfl⟩ : ∃ u, n = u + 4 := ⟨n - 4, by omega⟩
    exact ⟨F u, F_counterexample u (by omega)⟩

theorem not_nashWilliamsConjecture : ¬ NashWilliamsConjecture := by
  intro H
  obtain ⟨G, hsc, hnw, hno⟩ := counterexample_all 6 le_rfl
  exact hno (H 6 (by norm_num) G hsc hnw)

theorem kot_counterexample_all (n : ℕ) (hn : 7 ≤ n) :
    ∃ G : Digraph n, KOTHyp G ∧ ¬ HasHamCycle G := by
  rcases (by omega : n = 7 ∨ 8 ≤ n) with rfl | h
  · exact ⟨G7, ⟨G7_nw, by decide⟩, G7_noham⟩
  · obtain ⟨u, rfl⟩ : ∃ u, n = u + 4 := ⟨n - 4, by omega⟩
    exact ⟨F u, ⟨F_nw u (by omega), F_kot3 u (by omega)⟩, F_noham u⟩

theorem not_kotConjecture6 : ¬ KOTConjecture6 := by
  intro H
  obtain ⟨G, hk, hno⟩ := kot_counterexample_all 7 le_rfl
  exact hno (H 7 (by norm_num) G hk)

end NWDigraph
