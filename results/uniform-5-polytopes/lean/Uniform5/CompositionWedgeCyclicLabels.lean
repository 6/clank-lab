import Uniform5.CompositionWedgeTypeIShape
import Mathlib.Data.List.Rotate

/-! Cyclic relabeling for literal W fans preserves every facet incidence. -/
noncomputable section
namespace Uniform5.Composition.TypeIFanChart
open Set

private theorem rotate_cast {a b : ℕ} (h : a = b) (i : Fin a) :
    Fin.cast h (finRotate a i) = finRotate b (Fin.cast h i) := by
  subst b
  rfl

private theorem rotate_add {n : ℕ} [NeZero n] (a i : Fin n) :
    finRotate n i + a = finRotate n (i + a) := by
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n => simp only [finRotate_succ_apply]; abel

private theorem rotate_rev {n : ℕ} (i : Fin n) :
    finRotate n (finRotate n i).rev = i.rev := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    cases n with
    | zero => apply Fin.ext; omega
    | succ n =>
      apply Fin.ext
      simp only [finRotate_succ_apply, Fin.val_add, Fin.val_rev]
      have h1 : ((1 : Fin (n + 1 + 1)) : ℕ) = 1 := by simp
      rw [h1]
      have hi := i.isLt
      by_cases h : i.val + 1 < n + 1 + 1
      · rw [Nat.mod_eq_of_lt h]
        rw [Nat.mod_eq_of_lt (show n + 1 + 1 - (i.val + 1 + 1) + 1 < n + 1 + 1 by omega)]
        omega
      · have hh : i.val + 1 = n + 1 + 1 := by omega
        rw [hh, Nat.mod_self]
        simp

variable {P G : Set (Space 5)} {D : ActualPolygonCycle P G}
    {c : List Wedge.Parameter} {q : Fin D.length → ℕ}

/-- Rotation transports both the vertex labels and the facet labels. -/
noncomputable def CyclicLabels.rotate (L : CyclicLabels (D := D) c q) (k : ℕ) :
    CyclicLabels (D := D) (c.rotate k) q := by
  letI : NeZero c.length := ⟨by have := labels_length L; have := D.length_ge; omega⟩
  let e : Fin (c.rotate k).length ≃ Fin c.length :=
    (finCongr (List.length_rotate c k)).trans (Equiv.addRight (k : Fin c.length))
  have he (i : Fin (c.rotate k).length) :
      e (finRotate _ i) = finRotate _ (e i) := by
    change Fin.cast (List.length_rotate c k) (finRotate _ i) + (k : Fin c.length) = _
    rw [rotate_cast, rotate_add]
    rfl
  refine {
    vertex := e.trans L.vertex
    facet := fun i => L.facet (e i)
    incidence := ?_
    parameter := ?_ }
  · intro i
    simpa only [Equiv.trans_apply, he] using L.incidence (e i)
  · intro i
    rw [List.get_rotate]
    convert L.parameter (e i) using 2
    apply Fin.ext
    simp [e, Fin.val_add, Nat.add_mod]

/-- Reversal reverses edge orientation; its vertex shift is essential. -/
noncomputable def CyclicLabels.reverse (L : CyclicLabels (D := D) c q) :
    CyclicLabels (D := D) c.reverse q := by
  let e : Fin c.reverse.length ≃ Fin c.length :=
    (finCongr (List.length_reverse (as := c))).trans Fin.revPerm
  have he (i : Fin c.reverse.length) :
      finRotate _ (e (finRotate _ i)) = e i := by
    change finRotate _ (Fin.cast (List.length_reverse (as := c)) (finRotate _ i)).rev = _
    rw [rotate_cast, rotate_rev]
    rfl
  refine {
    vertex := (e.trans (finRotate _)).trans L.vertex
    facet := fun i => L.facet (e i)
    incidence := ?_
    parameter := ?_ }
  · intro i
    rcases L.incidence (e i) with h | h
    · right
      simpa only [Equiv.trans_apply, he] using h
    · left
      simpa only [Equiv.trans_apply, he] using h
  · intro i
    convert L.parameter (e i) using 1
    simp only [e, List.get_eq_getElem, List.getElem_reverse, Equiv.trans_apply,
      Fin.revPerm_apply, finCongr_apply, Fin.val_rev, Fin.coe_cast]
    congr 1 <;> omega

/-- The literal parameter cycle has its identity incidence labels. -/
noncomputable def cyclicLabels_ofFn (q : Fin D.length → ℕ) :
    CyclicLabels (D := D) ((List.ofFn q).map (fun k : ℕ => some (k : ℝ))) q where
  vertex := finCongr (by simp)
  facet := fun i => Fin.cast (by simp) i
  incidence i := Or.inl ⟨rfl, rotate_cast (by simp) i⟩
  parameter i := by
    simp only [List.get_eq_getElem, List.getElem_map, List.getElem_ofFn]
    rfl

/-- Dihedral canonicalization produces a genuine geometric relabeling. -/
theorem cyclicLabels_of_dihedral (q : Fin D.length → ℕ) {c : List ℕ}
    (h : (List.ofFn q).IsRotated c ∨ (List.ofFn q).reverse.IsRotated c) :
    Nonempty (CyclicLabels (D := D) (c.map (fun k : ℕ => some (k : ℝ))) q) := by
  rcases h with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · simpa only [List.map_rotate] using Nonempty.intro ((cyclicLabels_ofFn q).rotate k)
  · simpa only [List.map_rotate, List.map_reverse] using
      Nonempty.intro ((cyclicLabels_ofFn q).reverse.rotate k)

end Uniform5.Composition.TypeIFanChart
