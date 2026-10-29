import LabelledUnion

namespace ADKZPricing.LabelledCell
variable {V W : Type*}

/-- Walks include vertex membership even at length zero. -/
inductive CellWalk (G : LabelledCell V) : V → V → ℕ → Prop
  | nil (x : V) (hx : G.vertex x) : CellWalk G x x 0
  | cons {x y z : V} {L : ℕ} (hxy : G.edge x y) (tail : CellWalk G y z L) :
      CellWalk G x z (L + 1)

theorem CellWalk.vertices {G : LabelledCell V} {x y : V} {L : ℕ}
    (p : CellWalk G x y L) : G.vertex x ∧ G.vertex y := by
  induction p with
  | nil x hx => exact ⟨hx, hx⟩
  | cons hxy _ ih => exact ⟨(G.edge_vertices _ _ hxy).1, ih.2⟩

theorem CellWalk.transfer {G H : LabelledCell V}
    (hv : ∀ x, G.vertex x → H.vertex x)
    (he : ∀ x y, G.edge x y → H.edge x y)
    {x y : V} {L : ℕ} (p : CellWalk G x y L) : CellWalk H x y L := by
  induction p with
  | nil x hx => exact .nil x (hv x hx)
  | cons hxy _ ih => exact .cons (he _ _ hxy) ih

/-- Every guarded Cartesian walk projects to two actual factor walks;
    the numbers of steps add exactly, including stationary projections. -/
theorem cartesian_walk_split (G : LabelledCell V) (H : LabelledCell W)
    {x y : V × W} {L : ℕ} (p : CellWalk (cartesian G H) x y L) :
    ∃ a b : ℕ, a + b = L ∧ CellWalk G x.1 y.1 a ∧ CellWalk H x.2 y.2 b := by
  induction p with
  | nil x hx => exact ⟨0, 0, rfl, .nil x.1 hx.1, .nil x.2 hx.2⟩
  | @cons x y z L hxy tail ih =>
    obtain ⟨a, b, hab, pa, pb⟩ := ih
    rcases hxy with ⟨he, hfix, _⟩ | ⟨he, hfix, _⟩
    · refine ⟨a + 1, b, by omega, .cons he pa, ?_⟩
      rw [hfix]
      exact pb
    · refine ⟨a, b + 1, by omega, ?_, .cons he pb⟩
      rw [hfix]
      exact pa

theorem cartesian_walk_lower_bound (G : LabelledCell V) (H : LabelledCell W)
    (x y : V × W) (a b : ℕ)
    (ha : ∀ k, CellWalk G x.1 y.1 k → a ≤ k)
    (hb : ∀ k, CellWalk H x.2 y.2 k → b ≤ k)
    {L : ℕ} (p : CellWalk (cartesian G H) x y L) : a + b ≤ L := by
  obtain ⟨u, v, huv, pu, pv⟩ := cartesian_walk_split G H p
  have h1 := ha u pu
  have h2 := hb v pv
  omega

/-- The union is literally the two original cell graphs. Shared-facet
    vertices/edges remain present with the same labels throughout. -/
theorem left_union_walk_lower_bound (G G' : LabelledCell V) (H : LabelledCell W)
    (x y : V × W) (a b : ℕ)
    (ha : ∀ k, CellWalk (union G G') x.1 y.1 k → a ≤ k)
    (hb : ∀ k, CellWalk H x.2 y.2 k → b ≤ k)
    {L : ℕ} (p : CellWalk (union (cartesian G H) (cartesian G' H)) x y L) : a + b ≤ L := by
  apply cartesian_walk_lower_bound (union G G') H x y a b ha hb
  exact p.transfer (fun z hz => (union_cartesian_vertex G G' H z).mp hz)
    (fun z w hz => (union_cartesian_edge G G' H z w).mp hz)

theorem right_union_walk_lower_bound (G : LabelledCell V) (H H' : LabelledCell W)
    (x y : V × W) (a b : ℕ)
    (ha : ∀ k, CellWalk G x.1 y.1 k → a ≤ k)
    (hb : ∀ k, CellWalk (union H H') x.2 y.2 k → b ≤ k)
    {L : ℕ} (p : CellWalk (union (cartesian G H) (cartesian G H')) x y L) : a + b ≤ L := by
  apply cartesian_walk_lower_bound G (union H H') x y a b ha hb
  exact p.transfer (fun z hz => (cartesian_union_vertex G H H' z).mp hz)
    (fun z w hz => (cartesian_union_edge G H H' z w).mp hz)

#print axioms cartesian_walk_split
#print axioms left_union_walk_lower_bound
#print axioms right_union_walk_lower_bound
end ADKZPricing.LabelledCell
