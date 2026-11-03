import Antony24.Basic

/-! Degree and size facts for the double subdivision. -/
namespace Antony24

variable {V : Type*} (G : SimpleGraph V)

def dartEquiv : Dart G ≃ G.Dart where
  toFun d := ⟨d.val, d.property⟩
  invFun d := ⟨d.toProd, d.adj⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance S2.decidableAdj [DecidableEq V] [DecidableRel G.Adj] :
    DecidableRel (S2 G).Adj := by
  intro x y
  cases x <;> cases y <;> dsimp [S2] <;> infer_instance

/-- Neighbours of an original vertex are its outgoing incidences. -/
def originalNeighborEquiv (v : V) :
    (S2 G).neighborSet (Sum.inl v) ≃ G.neighborSet v where
  toFun z := by
    rcases z with ⟨z, hz⟩
    cases z with
    | inl w => exact False.elim hz
    | inr d =>
      exact ⟨d.val.2, by change v = d.val.1 at hz; simpa [hz] using d.property⟩
  invFun w := ⟨.inr ⟨(v, w.val), w.property⟩, rfl⟩
  left_inv z := by
    rcases z with ⟨z, hz⟩
    cases z with
    | inl w => exact False.elim hz
    | inr d =>
      apply Subtype.ext
      apply congrArg Sum.inr
      apply Subtype.ext
      change v = d.val.1 at hz
      exact Prod.ext hz rfl
  right_inv w := rfl

/-- Extend any ordinary proper colouring over the odd replacement paths. -/
def S2.coloring {α : Type*} (c : G.Coloring α) : (S2 G).Coloring α :=
  SimpleGraph.Coloring.mk (fun x => match x with
    | .inl v => c v
    | .inr d => c d.val.2) (by
      intro x y h
      cases x with
      | inl v =>
        cases y with
        | inl w => exact False.elim h
        | inr d =>
          change v = d.val.1 at h
          simpa [h] using c.valid d.property
      | inr d =>
        cases y with
        | inl v =>
          change v = d.val.1 at h
          simpa [h] using (c.valid d.property).symm
        | inr e =>
          change e = d.rev at h
          simpa [h, Dart.rev] using (c.valid d.property).symm)

theorem s2_colorable {n : ℕ} (h : G.Colorable n) : (S2 G).Colorable n := by
  obtain ⟨c⟩ := h
  exact ⟨S2.coloring G c⟩

/-- In particular double subdivision preserves bipartiteness. -/
theorem s2_two_colorable (h : G.Colorable 2) : (S2 G).Colorable 2 :=
  s2_colorable G h

/-- No double subdivision has a triangle, independently of the source graph. -/
theorem s2_no_triangle (x y z : SubVertex G) :
    ¬ ((S2 G).Adj x y ∧ (S2 G).Adj y z ∧ (S2 G).Adj z x) := by
  rintro ⟨hxy, hyz, hzx⟩
  rcases x with x | ⟨⟨x₁, x₂⟩, hx⟩ <;>
    rcases y with y | ⟨⟨y₁, y₂⟩, hy⟩ <;>
    rcases z with z | ⟨⟨z₁, z₂⟩, hz⟩ <;>
    simp_all [S2, Dart.rev, Subtype.mk.injEq, Prod.mk.injEq] <;>
    dsimp at * <;> simp_all

theorem s2_triangle_free : (S2 G).CliqueFree 3 := by
  classical
  intro s hs
  obtain ⟨a, b, c, hab, hac, hbc, _⟩ := SimpleGraph.is3Clique_iff.mp hs
  exact s2_no_triangle G a b c ⟨hab, hbc, hac.symm⟩

section Finite
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

omit [DecidableEq V] in
theorem dart_card : Fintype.card (Dart G) = 2 * G.edgeFinset.card := by
  rw [Fintype.card_congr (dartEquiv G)]
  exact G.dart_card_eq_twice_card_edges

omit [DecidableEq V] in
theorem s2_vertex_card : Fintype.card (SubVertex G) =
    Fintype.card V + 2 * G.edgeFinset.card := by
  rw [Fintype.card_sum, dart_card]

theorem s2_degree_original (v : V) : (S2 G).degree (.inl v) = G.degree v := by
  rw [← SimpleGraph.card_neighborSet_eq_degree,
    ← SimpleGraph.card_neighborSet_eq_degree]
  exact Fintype.card_congr (originalNeighborEquiv G v)

theorem s2_internal_neighborFinset (d : Dart G) :
    (S2 G).neighborFinset (.inr d) = {.inl d.val.1, .inr d.rev} := by
  ext x
  cases x <;> simp [S2]

theorem s2_degree_internal (d : Dart G) : (S2 G).degree (.inr d) = 2 := by
  rw [SimpleGraph.degree, s2_internal_neighborFinset]
  simp

theorem cubic_degree (h : Cubic G) (v : V) : G.degree v = 3 := by
  obtain ⟨a, b, c, hab, hac, hbc, hn⟩ := h v
  have heq : G.neighborFinset v = {a, b, c} := by
    ext w
    simp only [SimpleGraph.mem_neighborFinset, hn, Finset.mem_insert,
      Finset.mem_singleton]
  rw [SimpleGraph.degree, heq]
  simp [hab, hac, hbc]

theorem cubic_iff_degree_three : Cubic G ↔ ∀ v, G.degree v = 3 := by
  constructor
  · intro h v
    exact cubic_degree G h v
  · intro h v
    have hv : (G.neighborFinset v).card = 3 := h v
    obtain ⟨a, b, c, hab, hac, hbc, hn⟩ := Finset.card_eq_three.mp hv
    refine ⟨a, b, c, hab, hac, hbc, ?_⟩
    intro w
    have hw : w ∈ G.neighborFinset v ↔ w = a ∨ w = b ∨ w = c := by
      rw [hn]
      simp
    simpa only [SimpleGraph.mem_neighborFinset] using hw

theorem cubic_iff_regular_three : Cubic G ↔ G.IsRegularOfDegree 3 :=
  cubic_iff_degree_three G

theorem s2_degree_le_three (h : Cubic G) (x : SubVertex G) :
    (S2 G).degree x ≤ 3 := by
  cases x with
  | inl v => rw [s2_degree_original, cubic_degree G h]
  | inr d => rw [s2_degree_internal]; decide

theorem s2_edge_card : (S2 G).edgeFinset.card = 3 * G.edgeFinset.card := by
  have hs := (S2 G).sum_degrees_eq_twice_card_edges
  rw [Fintype.sum_sum_type] at hs
  simp only [s2_degree_original, s2_degree_internal] at hs
  rw [G.sum_degrees_eq_twice_card_edges] at hs
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, dart_card] at hs
  omega

end Finite
end Antony24
