import Antony24.Basic

/-! Bridges to the usual definitions. -/
namespace Antony24

variable {V : Type*} (G : SimpleGraph V)

/-- The spanning subgraph containing every edge across the indicated two sides,
and no other edges. -/
def exactCut (side : V → Bool) : G.Subgraph where
  verts := Set.univ
  Adj u v := G.Adj u v ∧ side u ≠ side v
  adj_sub h := h.1
  edge_vert _ := Set.mem_univ _
  symm _ _ h := ⟨h.1.symm, Ne.symm h.2⟩

@[simp] theorem exactCut_adj (side : V → Bool) (u v : V) :
    (exactCut G side).Adj u v ↔ G.Adj u v ∧ side u ≠ side v := Iff.rfl

/-- Our unique-crossing-neighbour definition is literally the assertion that
an entire cut is a perfect matching in Mathlib's standard sense. -/
theorem pmc_iff_exactCut_perfectMatching :
    PMC G ↔ ∃ side, (exactCut G side).IsPerfectMatching := by
  simp only [PMC, SimpleGraph.Subgraph.isPerfectMatching_iff, exactCut_adj]

/-- An explicit subset-based cut, for comparison with the usual graph definition. -/
def InCut (A : Set V) (u v : V) : Prop :=
  (u ∈ A ∧ v ∉ A) ∨ (u ∉ A ∧ v ∈ A)

/-- PMC is equivalent to an actual perfect matching whose adjacency is exactly
all graph edges crossing a subset. The iff excludes additional crossing edges. -/
theorem pmc_iff_perfectMatching_equal_cut :
    PMC G ↔ ∃ (A : Set V) (M : G.Subgraph), M.IsPerfectMatching ∧
      ∀ u v, M.Adj u v ↔ G.Adj u v ∧ InCut A u v := by
  classical
  constructor
  · intro h
    obtain ⟨side, hs⟩ := (pmc_iff_exactCut_perfectMatching G).mp h
    refine ⟨{v | side v = true}, exactCut G side, hs, ?_⟩
    intro u v
    simp only [exactCut_adj, InCut, Set.mem_setOf_eq]
    cases hu : side u <;> cases hv : side v <;> simp [hu, hv]
  · rintro ⟨A, M, hM, he⟩
    refine ⟨fun v => decide (v ∈ A), ?_⟩
    intro v
    obtain ⟨w, hw, hu⟩ := SimpleGraph.Subgraph.isPerfectMatching_iff.mp hM v
    have bridge (u z : V) :
        M.Adj u z ↔ G.Adj u z ∧ decide (u ∈ A) ≠ decide (z ∈ A) := by
      rw [he]
      by_cases hu : u ∈ A <;> by_cases hz : z ∈ A <;> simp [InCut, hu, hz]
    exact ⟨w, (bridge v w).mp hw, fun z hz => hu z ((bridge v z).mpr hz)⟩

/-- Natural-number labels with exactly the permitted range; no surjectivity or
global injectivity is required. The second condition is proper vertex colouring,
the third is proper colouring by absolute differences on incident edges. -/
def IsGracefulFourLabels (c : V → ℕ) : Prop :=
  (∀ v, 1 ≤ c v ∧ c v ≤ 4) ∧
  (∀ ⦃u v⦄, G.Adj u v → c u ≠ c v) ∧
  (∀ ⦃v u w⦄, G.Adj v u → G.Adj v w → u ≠ w →
    Nat.dist (c v) (c u) ≠ Nat.dist (c v) (c w))

/-- Adding one to the Fin 4 indices gives labels precisely in {1,2,3,4}. -/
theorem isGraceful_iff_labels (c : V → Colour) :
    IsGraceful G c ↔ IsGracefulFourLabels G (fun v => (c v).val + 1) := by
  have range (v : V) : 1 ≤ (c v).val + 1 ∧ (c v).val + 1 ≤ 4 := by
    have h := (c v).isLt
    omega
  constructor
  · rintro ⟨hp, hd⟩
    refine ⟨range, ?_, ?_⟩
    · intro u v huv he
      apply hp huv
      apply Fin.ext
      change (c u).val + 1 = (c v).val + 1 at he
      exact Nat.add_right_cancel he
    · intro v u w hvu hvw huw
      simpa only [Nat.dist_add_add_right] using hd hvu hvw huw
  · rintro ⟨_, hp, hd⟩
    constructor
    · intro u v huv he
      exact hp huv (congrArg (fun x : Colour => x.val + 1) he)
    · intro v u w hvu hvw huw
      simpa only [diff, Nat.dist_add_add_right] using hd hvu hvw huw

/-- The definition used in the all-instance theorem is equivalent to literal
natural-number labels {1,2,3,4} with the ordinary absolute-difference condition. -/
theorem graceful4_iff_four_labels :
    Graceful4 G ↔ ∃ c : V → ℕ, IsGracefulFourLabels G c := by
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨fun v => (c v).val + 1, (isGraceful_iff_labels G c).mp hc⟩
  · rintro ⟨c, hc⟩
    let c' : V → Colour := fun v => ⟨c v - 1, by have := hc.1 v; omega⟩
    have he (v : V) : (c' v).val + 1 = c v := by
      have := hc.1 v
      dsimp [c']
      omega
    refine ⟨c', (isGraceful_iff_labels G c').mpr ?_⟩
    simpa only [he] using hc

end Antony24
