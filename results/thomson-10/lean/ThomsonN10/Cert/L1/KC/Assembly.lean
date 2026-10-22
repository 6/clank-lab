/- Adapted from proof/lean/ClaudeL1/KC/Assembly.lean, aravindkarthigeyan/thomson-n9-lean, commit 168ff0c98cab4dfda0460ba55f8d169070ac385e (MIT). -/
/-
ThomsonN10.Cert.L1.KC.Assembly : the final residual check.

  residual = hscale * (H(u) + H(v) + H(t)) + c0  -  kscale * K(u,v,t)
             -  sscale * (T(u,v,t) + T(v,u,t) + T(t,u,v))

`checkL1 L` decodes the Kronecker value of the residual into balanced digits and proves that
the l1 norm of its collected coefficients over the box `[0,21)^3` is at most `L`; it also
exports `DegLt 21` (so that the residual equals the box sum of its coefficient monomials).
The permuted copies `T(v,u,t)`, `T(t,u,v)` are evaluated by packing the leaf-permuted tree
(`PTree.mapLeaves`), which is correct for any leaf order.

Core Lean only (upstream L1 implementation).
-/
import ThomsonN10.Cert.L1.KC.Ops

namespace ThomsonN10.Cert.L1.KC

namespace PTree

/-- apply a term map to every leaf -/
noncomputable def mapLeaves (f : Term → Term) (t : PTree) : PTree :=
  PTree.rec (motive := fun _ => PTree) (fun s => .leaf (f s)) (fun _ _ l r => .node l r) t

theorem toPoly_mapLeaves (f : Term → Term) (t : PTree) :
    (t.mapLeaves f).toPoly = t.toPoly.map f := by
  induction t with
  | leaf s => rfl
  | node l r ihl ihr =>
    show (l.mapLeaves f).toPoly ++ (r.mapLeaves f).toPoly = _
    rw [ihl, ihr, toPoly, List.map_append]

end PTree

/-- a priori facts about the leaf-permuted trees -/
theorem degLt_map_perm {D : Nat} {p : Poly} (f : Term → Term)
    (hf : ∀ s : Term, s.a < D → s.b < D → s.d < D → (f s).a < D ∧ (f s).b < D ∧ (f s).d < D)
    (hp : Poly.DegLt D p) : Poly.DegLt D (p.map f) := by
  intro s hs
  simp only [List.mem_map] at hs
  obtain ⟨t, ht, rfl⟩ := hs
  have := hp t ht
  exact hf t this.1 this.2.1 this.2.2

structure Assembly where
  w : Nat
  hs : List Int
  hscale : Int
  c0 : Int
  kscale : Int
  K : PTree
  sscale : Int
  T : PTree
deriving Inhabited

namespace Assembly
noncomputable section

def lhsPoly (A : Assembly) : Poly :=
  (uPoly A.hs ++ (uPoly A.hs).map Term.perm1 ++ (uPoly A.hs).map Term.perm3).map
    (Term.scale A.hscale) ++ [⟨A.c0, 0, 0, 0⟩]

def sosPoly (A : Assembly) : Poly :=
  (A.T.toPoly ++ A.T.toPoly.map Term.perm1 ++ A.T.toPoly.map Term.perm3).map (Term.scale A.sscale)

def residual (A : Assembly) : Poly :=
  A.lhsPoly ++ Poly.neg (A.K.toPoly.map (Term.scale A.kscale)) ++ Poly.neg A.sosPoly

def packVal (w : Nat) (t : PTree) : Int := ishl (t.pack w 21).1 (w * (t.pack w 21).2)

def kval (A : Assembly) : Int :=
  A.hscale * (horner (((2 ^ A.w : Nat) : Int)) A.hs + horner (((2 ^ (A.w * 21) : Nat) : Int)) A.hs +
      horner (((2 ^ (A.w * (21 * 21)) : Nat) : Int)) A.hs) + A.c0 -
    A.kscale * packVal A.w A.K -
    A.sscale * (packVal A.w A.T + packVal A.w (A.T.mapLeaves Term.perm1) +
      packVal A.w (A.T.mapLeaves Term.perm3))

def l1bound (A : Assembly) : Nat :=
  A.hscale.natAbs * (l1L A.hs + l1L A.hs + l1L A.hs) + (A.c0.natAbs + 0) +
    A.kscale.natAbs * A.K.l1 + A.sscale.natAbs * (A.T.l1 + A.T.l1 + A.T.l1)

def degOK (A : Assembly) : Bool :=
  decide (A.hs.length ≤ 21) && decide (A.K.maxDeg < 21) && decide (A.T.maxDeg < 21)

/-- **residual l1 check** (balanced-digit decoding of the Kronecker value) -/
def checkL1 (A : Assembly) (L : Nat) : Bool :=
  A.degOK && decide (1 ≤ A.w) && decide (A.l1bound < 2 ^ (A.w - 1)) &&
    Nat.ble (dl1 A.w (2 ^ (A.w - 1)) (Nat.log2 (21 * 21 * 21) + 1) (21 * 21 * 21)
      (A.kval + (offsetNat A.w (21 * 21 * 21) : Int)).toNat) L

theorem l1_residual (A : Assembly) : A.residual.l1 = A.l1bound := by
  simp only [residual, lhsPoly, sosPoly, l1bound, Poly.l1_append, Poly.l1_neg, Poly.l1_map_scale,
    Poly.l1_map_of_c Term.perm1 (fun _ => rfl), Poly.l1_map_of_c Term.perm3 (fun _ => rfl),
    l1_uPoly, PTree.l1_eq]
  rfl

theorem residual_deg (A : Assembly) (h : A.degOK = true) : A.residual.DegLt 21 := by
  simp only [degOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hh, hK⟩, hT⟩ := h
  have hu : (uPoly A.hs).DegLt 21 := by
    intro s hs
    have := deg_uPolyAux A.hs 0 s hs
    omega
  have hperm1 : ∀ s : Term, s.a < 21 → s.b < 21 → s.d < 21 →
      (Term.perm1 s).a < 21 ∧ (Term.perm1 s).b < 21 ∧ (Term.perm1 s).d < 21 := by
    intro s h1 h2 h3; simp only [Term.perm1]; omega
  have hperm3 : ∀ s : Term, s.a < 21 → s.b < 21 → s.d < 21 →
      (Term.perm3 s).a < 21 ∧ (Term.perm3 s).b < 21 ∧ (Term.perm3 s).d < 21 := by
    intro s h1 h2 h3; simp only [Term.perm3]; omega
  have hsc : ∀ (k : Int), ∀ s : Term, s.a < 21 → s.b < 21 → s.d < 21 →
      (Term.scale k s).a < 21 ∧ (Term.scale k s).b < 21 ∧ (Term.scale k s).d < 21 := by
    intro k s h1 h2 h3; simp only [Term.scale]; omega
  have hKd : A.K.toPoly.DegLt 21 := degLt_of_maxDeg' A.K hK
  have hTd : A.T.toPoly.DegLt 21 := degLt_of_maxDeg' A.T hT
  have hc : Poly.DegLt 21 ([⟨A.c0, 0, 0, 0⟩] : Poly) := by
    intro s hs; simp only [List.mem_singleton] at hs; subst hs; simp
  refine Poly.DegLt.append (Poly.DegLt.append (Poly.DegLt.append ?_ hc) ?_) ?_
  · exact degLt_map_perm _ (hsc A.hscale)
      (((hu.append (degLt_map_perm _ hperm1 hu)).append (degLt_map_perm _ hperm3 hu)))
  · exact Poly.DegLt.neg (degLt_map_perm _ (hsc A.kscale) hKd)
  · exact Poly.DegLt.neg (degLt_map_perm _ (hsc A.sscale)
      ((hTd.append (degLt_map_perm _ hperm1 hTd)).append (degLt_map_perm _ hperm3 hTd)))
where
  degLt_of_maxDeg' (t : PTree) (h : t.maxDeg < 21) : t.toPoly.DegLt 21 := by
    intro s hs
    have := PTree.le_maxDeg t s hs
    omega

/-- the `Lean.Grind` integer cast on `Int` is the identity -/
theorem grind_intCast_int (n : Int) :
    @IntCast.intCast Int (@Lean.Grind.Ring.intCast Int inferInstance) n = n := rfl

theorem kval_eq (A : Assembly) :
    uval (((2 ^ A.w : Nat) : Int)) (Poly.toU 21 A.residual) = A.kval := by
  rw [← Poly.eval_kron]
  simp only [residual, lhsPoly, sosPoly]
  rw [← PTree.toPoly_mapLeaves Term.perm1 A.T, ← PTree.toPoly_mapLeaves Term.perm3 A.T]
  simp only [Poly.eval_append, Poly.eval_neg, Poly.eval_scale, Poly.eval_perm1, Poly.eval_perm3,
    eval_uPoly]
  -- the permuted copies are now evaluated as leaf-mapped trees at the standard point
  have e1 := PTree.eval_kron_pack A.w 21 A.K
  have e2 := PTree.eval_kron_pack A.w 21 A.T
  have e3 := PTree.eval_kron_pack A.w 21 (A.T.mapLeaves Term.perm1)
  have e4 := PTree.eval_kron_pack A.w 21 (A.T.mapLeaves Term.perm3)
  simp only [kval, packVal, two_pow_mul_cast]
  rw [e1, e2, e3, e4]
  simp only [Poly.eval, Term.eval, Lean.Grind.Semiring.pow_zero, grind_intCast_int]
  grind



/-- **Soundness of the residual check**: the collected l1 norm of the residual over the box
`[0,21)^3` is at most `L`, and every exponent of the residual is `< 21`. -/
theorem checkL1_sound (A : Assembly) (L : Nat) (h : A.checkL1 L = true) :
    boxL1 21 A.residual ≤ L ∧ A.residual.DegLt 21 := by
  simp only [checkL1, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hdeg, hw⟩, hl1⟩, hL⟩ := h
  refine ⟨?_, residual_deg A hdeg⟩
  rw [kron_decode_l1 A.w 21 hw A.residual (residual_deg A hdeg) (by rw [l1_residual]; exact hl1),
    kval_eq, balDigits_l1]
  exact Nat.le_of_ble_eq_true hL

section Eval
open Lean.Grind
attribute [local instance] Semiring.natCast Ring.intCast
variable {α : Type u} [CommRing α]

/-- the residual as a function -/
theorem eval_residual (A : Assembly) (x y z : α) :
    A.residual.eval x y z =
      (A.hscale : α) * (horner x A.hs + horner y A.hs + horner z A.hs) + (A.c0 : α) -
        (A.kscale : α) * A.K.toPoly.eval x y z -
        (A.sscale : α) * (A.T.toPoly.eval x y z + A.T.toPoly.eval y x z + A.T.toPoly.eval z x y) := by
  simp only [residual, lhsPoly, sosPoly, Poly.eval_append, Poly.eval_neg, Poly.eval_scale,
    Poly.eval_perm1, Poly.eval_perm3, eval_uPoly]
  simp only [Poly.eval, Term.eval, Semiring.pow_zero]
  grind

end Eval

end
end Assembly

end ThomsonN10.Cert.L1.KC
