import Antony24

/-! Statement, axiom and example checks for the public build. -/
namespace Antony24.PublicChecks

/-- The main theorem, restated with its full type. -/
example {V : Type*} [Finite V] (G : SimpleGraph V) (hG : Cubic G) :
    Graceful4 (S2 G) ↔ PMC G :=
  graceful4_s2_iff_pmc G hG

/-- The expanded form: labels 1 to 4, and a perfect matching equal to a whole cut. -/
example {V : Type*} [Finite V] (G : SimpleGraph V) (hG : Cubic G) :
    (∃ c : SubVertex G → ℕ,
      (∀ v, 1 ≤ c v ∧ c v ≤ 4) ∧
      (∀ ⦃u v⦄, (S2 G).Adj u v → c u ≠ c v) ∧
      (∀ ⦃v u w⦄, (S2 G).Adj v u → (S2 G).Adj v w → u ≠ w →
        Nat.dist (c v) (c u) ≠ Nat.dist (c v) (c w))) ↔
      ∃ (A : Set V) (M : G.Subgraph), M.IsPerfectMatching ∧
        ∀ u v, M.Adj u v ↔ G.Adj u v ∧
          ((u ∈ A ∧ v ∉ A) ∨ (u ∉ A ∧ v ∈ A)) :=
  four_labels_s2_iff_perfectMatching_equal_cut G hG

/-- info: 'Antony24.graceful4_s2_iff_pmc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms graceful4_s2_iff_pmc

/-- info: 'Antony24.four_labels_s2_iff_perfectMatching_equal_cut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms four_labels_s2_iff_perfectMatching_equal_cut

/-- info: 'Antony24.pmc_union_iff' depends on axioms: [propext, Classical.choice] -/
#guard_msgs in
#print axioms pmc_union_iff

/-- info: 'Antony24.graceful4_union_iff' depends on axioms: [propext, Classical.choice] -/
#guard_msgs in
#print axioms graceful4_union_iff

/-- info: 'Antony24.cubic_union' depends on axioms: [propext] -/
#guard_msgs in
#print axioms cubic_union

/-! Two examples. The complete graph `K₄` has no perfect matching cut, so its double
subdivision has no graceful 4-coloring. The triangular prism has one (the three
rungs), so its double subdivision has a graceful 4-coloring. -/

/-- The complete graph on four vertices. -/
abbrev K4 : SimpleGraph (Fin 4) := ⊤

theorem k4_cubic : Cubic K4 := by
  unfold Cubic; decide

theorem k4_not_pmc : ¬ PMC K4 := by
  unfold PMC; simp only [ExistsUnique]; decide

theorem k4_s2_not_graceful4 : ¬ Graceful4 (S2 K4) :=
  fun h => k4_not_pmc ((graceful4_s2_iff_pmc K4 k4_cubic).mp h)

/-- Adjacency of the triangular prism on `Fin 6`: triangles `0 1 2` and `3 4 5`,
and rungs `i -- i + 3`. -/
def prismAdj (u v : Fin 6) : Bool :=
  u ≠ v && ((u.val < 3 && v.val < 3) || (3 ≤ u.val && 3 ≤ v.val) ||
    u.val + 3 = v.val || v.val + 3 = u.val)

/-- The triangular prism. -/
def prism : SimpleGraph (Fin 6) where
  Adj u v := prismAdj u v = true
  symm := by unfold Symmetric; decide
  loopless := by unfold Irreflexive; decide

instance : DecidableRel prism.Adj := fun u v =>
  inferInstanceAs (Decidable (prismAdj u v = true))

theorem prism_cubic : Cubic prism := by
  unfold Cubic; decide

theorem prism_pmc : PMC prism := by
  refine ⟨fun v => decide (v.val < 3), ?_⟩
  simp only [ExistsUnique]; decide

theorem prism_s2_graceful4 : Graceful4 (S2 prism) :=
  (graceful4_s2_iff_pmc prism prism_cubic).mpr prism_pmc

end Antony24.PublicChecks
