import GuardedDistances

namespace ADKZPricing.LabelledCell
variable {V : Type*}

/-- A finite guarded cell walk as a total sequence, with guards only on
    its actual prefix. No ambient nonvertices enter the representation. -/
theorem CellWalk.sequence {G : LabelledCell V} {x y : V} {L : ℕ}
    (h : CellWalk G x y L) :
    ∃ p : ℕ → V, p 0 = x ∧ p L = y ∧
      (∀ j, j ≤ L → G.vertex (p j)) ∧ (∀ j, j < L → G.edge (p j) (p (j + 1))) := by
  induction h with
  | nil x hx =>
    exact ⟨fun _ => x, rfl, rfl, fun _ _ => hx, fun j hj => (Nat.not_lt_zero j hj).elim⟩
  | @cons x y z L hxy _ ih =>
    obtain ⟨p, hp0, hpL, hv, he⟩ := ih
    let q : ℕ → V := fun j => if j = 0 then x else p (j - 1)
    refine ⟨q, by simp [q], by simpa [q] using hpL, ?_, ?_⟩
    · intro j hj
      by_cases hz : j = 0
      · simpa [q, hz] using (G.edge_vertices x y hxy).1
      · simpa [q, hz] using hv (j - 1) (by omega)
    · intro j hj
      by_cases hz : j = 0
      · simpa [q, hz, hp0] using hxy
      · simpa [q, hz, show j + 1 ≠ 0 by omega, show j - 1 + 1 = j by omega] using
          he (j - 1) (by omega)

/-- Reconstruct a guarded walk from its actual prefix, preserving its
    length. Used after sign confinement changes cell membership. -/
theorem CellWalk.of_sequence (G : LabelledCell V) (L : ℕ) (p : ℕ → V)
    (hv : ∀ j, j ≤ L → G.vertex (p j))
    (he : ∀ j, j < L → G.edge (p j) (p (j + 1))) : CellWalk G (p 0) (p L) L := by
  induction L generalizing p with
  | zero => exact .nil _ (hv 0 (by omega))
  | succ L ih =>
    have ht := ih (fun j => p (j + 1)) (fun j hj => hv (j + 1) (by omega))
      (fun j hj => he (j + 1) (by omega))
    exact .cons (he 0 (by omega)) ht

/-- Finite full-path arrays turn into guarded walks without adding a
    vertex outside their actual index range. -/
theorem CellWalk.of_finite_sequence (G : LabelledCell V) (L : ℕ) (p : Fin (L + 1) → V)
    (hv : ∀ j, G.vertex (p j))
    (he : ∀ j : Fin L, G.edge (p j.castSucc) (p j.succ)) :
    CellWalk G (p 0) (p (Fin.last L)) L := by
  induction L with
  | zero => exact .nil _ (hv 0)
  | succ L ih =>
    have ht := ih (fun i => p i.succ) (fun i => hv i.succ) (fun i => he i.succ)
    exact .cons (he 0) ht

theorem CellWalk.map {W : Type*} {G : LabelledCell V} {H : LabelledCell W}
    (f : V → W) (hv : ∀ v, G.vertex v → H.vertex (f v))
    (he : ∀ v w, G.edge v w → H.edge (f v) (f w))
    {x y : V} {L : ℕ} (h : CellWalk G x y L) : CellWalk H (f x) (f y) L := by
  induction h with
  | nil x hx => exact .nil _ (hv x hx)
  | cons hxy _ ih => exact .cons (he _ _ hxy) ih

#print axioms CellWalk.of_finite_sequence
#print axioms CellWalk.map
#print axioms CellWalk.sequence
#print axioms CellWalk.of_sequence
end ADKZPricing.LabelledCell
