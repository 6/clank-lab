/- Adapted from proof/lean/ClaudeL1/KC/Check.lean, aravindkarthigeyan/thomson-n9-lean, commit 168ff0c98cab4dfda0460ba55f8d169070ac385e (MIT). -/
/-
ThomsonN10.Cert.L1.KC.Check (copied from the upstream exact checker, namespace renamed) : kernel-evaluable Boolean checkers and their soundness theorems.

Data layout (chosen for the Lean kernel's GMP-accelerated `Nat` operations):
* a polynomial is a binary tree of terms (`PTree`); the leaves, read left to right, are the
  uncollected term list `PTree.toPoly`.  The Kronecker value is assembled bottom-up with
  *relative* exponents (`PTree.pack`), so every intermediate integer is only as wide as the
  exponent span of its subtree (correct for any tree shape; efficient when leaves are sorted).
* multiplication by `2^s` uses `Nat.shiftLeft` (`ishl`), never an explicit `2^s` multiplication.

`SOSBlock.check`   : the identity `g * Σ_j c_j^2 = target` (exact, zero test).
`SOSBlock.checkL1` : the residual `g * Σ_j c_j^2 - target` has collected l1 norm `≤ L`
                     (balanced-digit decoding).
-/
import ThomsonN10.Cert.L1.KC.Kronecker

namespace ThomsonN10.Cert.L1.KC

/-! ### Shifts -/

/-- `ishl v s = v * 2^s`, through the GMP-accelerated `Nat.shiftLeft`. -/
def ishl : Int → Nat → Int
  | .ofNat n, s => .ofNat (n <<< s)
  | .negSucc n, s => .negSucc ((n + 1) <<< s - 1)

theorem ishl_eq (v : Int) (s : Nat) : ishl v s = v * ((2 ^ s : Nat) : Int) := by
  cases v with
  | ofNat n => simp only [ishl, Nat.shiftLeft_eq, Int.ofNat_eq_natCast, Int.natCast_mul]
  | negSucc n =>
    simp only [ishl, Nat.shiftLeft_eq]
    have hq : 1 ≤ (n + 1) * 2 ^ s := Nat.mul_pos (by omega) (Nat.two_pow_pos s)
    have hc : (((n + 1) * 2 ^ s : Nat) : Int) = ((n : Int) + 1) * ((2 ^ s : Nat) : Int) := by
      rw [Int.natCast_mul]; simp
    rw [Int.negSucc_eq, Int.negSucc_eq, Int.neg_mul, ← hc]
    omega

theorem two_pow_mul_cast (w k : Nat) : ((2 ^ (w * k) : Nat) : Int) = ((2 ^ w : Nat) : Int) ^ k := by
  rw [Nat.pow_mul, Int.natCast_pow]

theorem uval_append (X : Int) (l₁ l₂ : UPoly) : uval X (l₁ ++ l₂) = uval X l₁ + uval X l₂ := by
  induction l₁ with
  | nil => simp [uval]
  | cons e l ih => simp only [List.cons_append, uval, ih]; omega

/-- kernel-friendly `max` (one `Nat.ble`, one `cond`) -/
def natMax (a b : Nat) : Nat := cond (Nat.ble a b) b a

theorem natMax_eq (a b : Nat) : natMax a b = max a b := by
  unfold natMax
  cases h : Nat.ble a b
  · have : ¬ a ≤ b := by intro hab; rw [Nat.ble_eq_true_of_le hab] at h; cases h
    simp only [cond_false]; omega
  · have : a ≤ b := Nat.le_of_ble_eq_true h
    simp only [cond_true]; omega

theorem nat_mul_eq (a b : Nat) : Nat.mul a b = a * b := rfl
theorem nat_sub_eq (a b : Nat) : Nat.sub a b = a - b := rfl
theorem nat_add_eq (a b : Nat) : Nat.add a b = a + b := rfl
theorem int_add_eq (a b : Int) : Int.add a b = a + b := rfl
theorem int_mul_eq (a b : Int) : Int.mul a b = a * b := rfl

/-! ### Term trees -/

inductive PTree where
  | leaf (s : Term)
  | node (l r : PTree)
deriving Inhabited

namespace PTree

def toPoly : PTree → Poly
  | leaf s => [s]
  | node l r => toPoly l ++ toPoly r

/-- one combination step of `pack` -/
def packStep (w : Nat) (pl pr : Int × Nat) : Int × Nat :=
  cond (Nat.ble pl.2 pr.2) (Int.add pl.1 (ishl pr.1 (Nat.mul w (Nat.sub pr.2 pl.2))), pl.2)
    (Int.add pr.1 (ishl pl.1 (Nat.mul w (Nat.sub pl.2 pr.2))), pr.2)

/-- `(v, m)` with `v * X^m` = Kronecker value, `m` = least Kronecker exponent.
Defined with the recursor directly (cheaper kernel reduction than structural recursion). -/
noncomputable def pack (w D : Nat) (t : PTree) : Int × Nat :=
  PTree.rec (motive := fun _ => Int × Nat) (fun s => (s.c, kexp D s.a s.b s.d))
    (fun _ _ pl pr => packStep w pl pr) t

noncomputable def l1 (t : PTree) : Nat :=
  PTree.rec (motive := fun _ => Nat) (fun s => s.c.natAbs) (fun _ _ x y => Nat.add x y) t

noncomputable def maxDeg (t : PTree) : Nat :=
  PTree.rec (motive := fun _ => Nat) (fun s => natMax s.a (natMax s.b s.d))
    (fun _ _ x y => natMax x y) t

theorem pack_leaf (w D : Nat) (s : Term) : pack w D (leaf s) = (s.c, kexp D s.a s.b s.d) := rfl
theorem pack_node (w D : Nat) (l r : PTree) :
    pack w D (node l r) = packStep w (pack w D l) (pack w D r) := rfl
theorem l1_leaf (s : Term) : l1 (leaf s) = s.c.natAbs := rfl
theorem l1_node (l r : PTree) : l1 (node l r) = l1 l + l1 r := rfl
theorem maxDeg_leaf (s : Term) : maxDeg (leaf s) = max s.a (max s.b s.d) := by
  simp only [maxDeg, natMax_eq]
theorem maxDeg_node (l r : PTree) : maxDeg (node l r) = max (maxDeg l) (maxDeg r) :=
  natMax_eq (maxDeg l) (maxDeg r)

theorem l1_eq (t : PTree) : t.l1 = t.toPoly.l1 := by
  induction t with
  | leaf s => simp [l1_leaf, toPoly, Poly.l1]
  | node l r ihl ihr => simp [l1_node, toPoly, Poly.l1_append, ihl, ihr]

theorem le_maxDeg (t : PTree) : ∀ s ∈ t.toPoly, s.a ≤ t.maxDeg ∧ s.b ≤ t.maxDeg ∧ s.d ≤ t.maxDeg := by
  induction t with
  | leaf s =>
    intro x hx; simp only [toPoly, List.mem_singleton] at hx; subst hx
    rw [maxDeg_leaf]; omega
  | node l r ihl ihr =>
    intro x hx
    simp only [toPoly, List.mem_append] at hx
    rw [maxDeg_node]
    rcases hx with hx | hx
    · have := ihl x hx; omega
    · have := ihr x hx; omega

theorem pack_spec (w D : Nat) (t : PTree) :
    (t.pack w D).1 * ((2 ^ w : Nat) : Int) ^ (t.pack w D).2 =
      uval ((2 ^ w : Nat) : Int) (Poly.toU D t.toPoly) ∧
    ∀ e ∈ Poly.toU D t.toPoly, (t.pack w D).2 ≤ e.2 := by
  induction t with
  | leaf s =>
    refine ⟨by simp [pack_leaf, toPoly, Poly.toU, uval], ?_⟩
    intro e he
    simp only [toPoly, Poly.toU, List.map_cons, List.map_nil, List.mem_singleton] at he
    subst he; simp [pack_leaf]
  | node l r ihl ihr =>
    obtain ⟨vl, kl⟩ := ihl
    obtain ⟨vr, kr⟩ := ihr
    simp only [toPoly, Poly.toU, List.map_append] at *
    rw [uval_append, pack_node]
    unfold packStep
    cases hb : Nat.ble (pack w D l).2 (pack w D r).2
    · have hle' : (r.pack w D).2 ≤ (l.pack w D).2 := by
        have : ¬ (pack w D l).2 ≤ (pack w D r).2 := by
          intro h; rw [Nat.ble_eq_true_of_le h] at hb; cases hb
        omega
      simp only [cond_false]
      refine ⟨?_, ?_⟩
      · rw [int_add_eq, ishl_eq, nat_mul_eq, nat_sub_eq, two_pow_mul_cast, Int.add_mul, vr,
          Int.mul_assoc, ← Int.pow_add, Nat.sub_add_cancel hle', vl, Int.add_comm]
      · intro e he
        rcases List.mem_append.mp he with he | he
        · exact Nat.le_trans hle' (kl e he)
        · exact kr e he
    · have hle : (l.pack w D).2 ≤ (r.pack w D).2 := Nat.le_of_ble_eq_true hb
      simp only [cond_true]
      refine ⟨?_, ?_⟩
      · rw [int_add_eq, ishl_eq, nat_mul_eq, nat_sub_eq, two_pow_mul_cast, Int.add_mul, vl,
          Int.mul_assoc, ← Int.pow_add, Nat.sub_add_cancel hle, vr]
      · intro e he
        rcases List.mem_append.mp he with he | he
        · exact kl e he
        · exact Nat.le_trans hle (kr e he)

/-- value of a tree at the Kronecker point, through `pack` -/
theorem eval_kron_pack (w D : Nat) (t : PTree) :
    t.toPoly.eval (((2 ^ w : Nat) : Int)) (((2 ^ w : Nat) : Int) ^ D) (((2 ^ w : Nat) : Int) ^ (D * D)) =
      ishl (t.pack w D).1 (w * (t.pack w D).2) := by
  rw [Poly.eval_kron, ← (pack_spec w D t).1, ishl_eq, two_pow_mul_cast]

end PTree

/-! ### Fused digit decoding + l1 (no intermediate lists) -/

/-- `Σ_{k<S} |e_k - H|` for the sequential digits `e_k` of `K` (fallback). -/
noncomputable def seqL1 (w H : Nat) (S : Nat) (K : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun _ rec K => Nat.add (Nat.add (Nat.sub (Nat.mod K (2 ^ w)) H) (Nat.sub H (Nat.mod K (2 ^ w))))
      (rec (Nat.shiftRight K w))) S K

/-- divide-and-conquer version of `seqL1` (same digits as `digitsDC`). -/
noncomputable def dl1 (w H : Nat) (fuel : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun S K => seqL1 w H S K)
    (fun _ rec S K => cond (Nat.ble S 1) (seqL1 w H S K)
      (Nat.add (rec (Nat.div S 2) (Nat.mod K (2 ^ (Nat.mul w (Nat.div S 2)))))
        (rec (Nat.sub S (Nat.div S 2)) (Nat.shiftRight K (Nat.mul w (Nat.div S 2)))))) fuel

theorem absdiff_eq (e H : Nat) : (e - H) + (H - e) = ((e : Int) - (H : Int)).natAbs := by omega

theorem seqL1_eq (w H : Nat) : ∀ S K,
    seqL1 w H S K = ((digitsSeq w S K).map (fun e : Nat => ((e : Int) - (H : Int)).natAbs)).sum := by
  intro S
  induction S with
  | zero => intro K; rfl
  | succ S ih =>
    intro K
    show Nat.add (Nat.add (Nat.sub (Nat.mod K (2 ^ w)) H) (Nat.sub H (Nat.mod K (2 ^ w))))
      (seqL1 w H S (Nat.shiftRight K w)) = _
    rw [ih]
    simp only [digitsSeq, List.map_cons, List.sum_cons]
    rw [← absdiff_eq]; rfl

theorem dl1_eq (w H : Nat) : ∀ f S K,
    dl1 w H f S K = ((digitsDC w f S K).map (fun e : Nat => ((e : Int) - (H : Int)).natAbs)).sum := by
  intro f
  induction f with
  | zero => intro S K; exact seqL1_eq w H S K
  | succ f ih =>
    intro S K
    show cond (Nat.ble S 1) (seqL1 w H S K)
      (Nat.add (dl1 w H f (Nat.div S 2) (Nat.mod K (2 ^ (Nat.mul w (Nat.div S 2)))))
        (dl1 w H f (Nat.sub S (Nat.div S 2)) (Nat.shiftRight K (Nat.mul w (Nat.div S 2))))) = _
    by_cases hS : S ≤ 1
    · rw [Nat.ble_eq_true_of_le hS, cond_true, seqL1_eq]
      simp only [digitsDC, hS, if_pos]
    · have hb : Nat.ble S 1 = false := by
        cases h : Nat.ble S 1
        · rfl
        · exact absurd (Nat.le_of_ble_eq_true h) hS
      rw [hb, cond_false, ih, ih]
      simp only [digitsDC, hS, ite_false, List.map_append, List.sum_append]
      rfl

/-- the l1 of the balanced digits, computed by `dl1` -/
theorem balDigits_l1 (w S : Nat) (K : Int) :
    ((balDigits w S K).map Int.natAbs).sum =
      dl1 w (2 ^ (w - 1)) (Nat.log2 S + 1) S (K + (offsetNat w S : Int)).toNat := by
  rw [dl1_eq]
  unfold balDigits
  rw [List.map_map]
  rfl

/-! ### SOS blocks -/

/-- One block of a sum-of-squares certificate: `g * Σ_j c_j^2 = target`.  Exponents `< D`. -/
structure SOSBlock where
  w : Nat
  D : Nat
  g : PTree
  cols : List PTree
  target : PTree
deriving Inhabited

/-- `c(X)^2` from the packed form `(v, m)`: `v^2 * 2^(w*2m)` -/
def sqTerm (w : Nat) (p : Int × Nat) : Int := ishl (Int.mul p.1 p.1) (Nat.mul w (Nat.mul 2 p.2))

noncomputable def sqSum (w D : Nat) (cols : List PTree) : Int :=
  List.rec (motive := fun _ => Int) 0 (fun c _ acc => Int.add (sqTerm w (c.pack w D)) acc) cols

noncomputable def l1sq (cols : List PTree) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun c _ acc => Nat.add (Nat.mul c.l1 c.l1) acc) cols

noncomputable def maxDegL (cols : List PTree) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun c _ acc => natMax c.maxDeg acc) cols

theorem sqSum_nil (w D : Nat) : sqSum w D [] = 0 := rfl
theorem sqSum_cons (w D : Nat) (c : PTree) (cs : List PTree) :
    sqSum w D (c :: cs) = ishl ((c.pack w D).1 * (c.pack w D).1) (w * (2 * (c.pack w D).2)) +
      sqSum w D cs := rfl
theorem l1sq_cons (c : PTree) (cs : List PTree) : l1sq (c :: cs) = c.l1 * c.l1 + l1sq cs := rfl
theorem maxDegL_cons (c : PTree) (cs : List PTree) :
    maxDegL (c :: cs) = max c.maxDeg (maxDegL cs) :=
  natMax_eq c.maxDeg (maxDegL cs)

namespace SOSBlock
noncomputable section

/-- `Σ_j c_j * c_j` as an uncollected polynomial -/
def sqPoly (cols : List PTree) : Poly := Poly.sum (cols.map (fun c => Poly.mul c.toPoly c.toPoly))

/-- the uncollected residual `g * Σ_j c_j^2 - target` -/
def residual (B : SOSBlock) : Poly :=
  Poly.mul B.g.toPoly (sqPoly B.cols) ++ Poly.neg B.target.toPoly

/-- Kronecker value of the residual, assembled from packed trees -/
def kval (B : SOSBlock) : Int :=
  ishl ((B.g.pack B.w B.D).1 * sqSum B.w B.D B.cols) (B.w * (B.g.pack B.w B.D).2) -
    ishl (B.target.pack B.w B.D).1 (B.w * (B.target.pack B.w B.D).2)

/-- a priori l1 bound of the residual -/
def l1bound (B : SOSBlock) : Nat := B.g.l1 * l1sq B.cols + B.target.l1

def degOK (B : SOSBlock) : Bool :=
  decide (B.g.maxDeg + 2 * maxDegL B.cols < B.D) && decide (B.target.maxDeg < B.D)

/-- **exact identity check** -/
def check (B : SOSBlock) : Bool :=
  B.degOK && decide (B.l1bound < 2 ^ B.w) && (B.kval == 0)

/-- **residual l1 check**: collected l1 norm of `g * Σ c_j^2 - target` is at most `L` -/
def checkL1 (B : SOSBlock) (L : Nat) : Bool :=
  B.degOK && decide (1 ≤ B.w) && decide (B.l1bound < 2 ^ (B.w - 1)) &&
    Nat.ble (dl1 B.w (2 ^ (B.w - 1)) (Nat.log2 (B.D * B.D * B.D) + 1) (B.D * B.D * B.D)
      (B.kval + (offsetNat B.w (B.D * B.D * B.D) : Int)).toNat) L

theorem l1_sqPoly (cols : List PTree) : (sqPoly cols).l1 = l1sq cols := by
  induction cols with
  | nil => rfl
  | cons c cs ih =>
    simp only [sqPoly, List.map_cons, Poly.sum, Poly.l1_append, Poly.l1_mul, ← PTree.l1_eq] at *
    rw [ih, l1sq_cons]

theorem l1_residual (B : SOSBlock) : B.residual.l1 = B.l1bound := by
  simp [residual, l1bound, Poly.l1_append, Poly.l1_mul, Poly.l1_neg, l1_sqPoly, PTree.l1_eq]

theorem sqPoly_deg (cols : List PTree) :
    ∀ s ∈ sqPoly cols, s.a ≤ 2 * maxDegL cols ∧ s.b ≤ 2 * maxDegL cols ∧ s.d ≤ 2 * maxDegL cols := by
  induction cols with
  | nil => intro s hs; cases hs
  | cons c cs ih =>
    intro s hs
    simp only [sqPoly, List.map_cons, Poly.sum, List.mem_append] at hs
    rw [maxDegL_cons]
    rcases hs with hs | hs
    · simp only [Poly.mul, List.mem_flatMap, List.mem_map] at hs
      obtain ⟨s1, h1, s2, h2, rfl⟩ := hs
      have := PTree.le_maxDeg c s1 h1
      have := PTree.le_maxDeg c s2 h2
      simp only [Term.mul]; omega
    · have := ih s hs; omega

theorem residual_deg (B : SOSBlock) (h : B.degOK = true) : B.residual.DegLt B.D := by
  simp only [degOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  intro s hs
  simp only [residual, List.mem_append] at hs
  rcases hs with hs | hs
  · simp only [Poly.mul, List.mem_flatMap, List.mem_map] at hs
    obtain ⟨s1, hs1, s2, hs2, rfl⟩ := hs
    have := PTree.le_maxDeg B.g s1 hs1
    have := sqPoly_deg B.cols s2 hs2
    simp only [Term.mul]; omega
  · simp only [Poly.neg, List.mem_map] at hs
    obtain ⟨t, ht, rfl⟩ := hs
    have := PTree.le_maxDeg B.target t ht
    simp only [Term.neg]; omega

theorem eval_sqPoly (w D : Nat) (cols : List PTree) :
    (sqPoly cols).eval (((2 ^ w : Nat) : Int)) (((2 ^ w : Nat) : Int) ^ D)
      (((2 ^ w : Nat) : Int) ^ (D * D)) = sqSum w D cols := by
  induction cols with
  | nil => rfl
  | cons c cs ih =>
    simp only [sqPoly, List.map_cons, Poly.sum, Poly.eval_append, Poly.eval_mul] at *
    rw [ih, PTree.eval_kron_pack, sqSum_cons]; simp only [ishl_eq]
    congr 1
    rw [show w * (2 * (c.pack w D).2) = w * (c.pack w D).2 + w * (c.pack w D).2 by rw [Nat.two_mul, Nat.mul_add],
      Nat.pow_add, Int.natCast_mul]
    grind

theorem kval_eq (B : SOSBlock) :
    uval (((2 ^ B.w : Nat) : Int)) (Poly.toU B.D B.residual) = B.kval := by
  rw [← Poly.eval_kron]
  simp only [residual, Poly.eval_append, Poly.eval_mul, Poly.eval_neg, eval_sqPoly,
    PTree.eval_kron_pack, kval]
  simp only [ishl_eq]
  grind

open Lean.Grind in
/-- **Soundness of the exact block check**: the identity `g * Σ_j c_j^2 = target` holds as an
identity of polynomial functions on every commutative ring. -/
theorem check_sound (B : SOSBlock) (h : B.check = true) {α : Type u} [CommRing α] (x y z : α) :
    B.g.toPoly.eval x y z * (sqPoly B.cols).eval x y z = B.target.toPoly.eval x y z := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨hdeg, hl1⟩, hk⟩ := h
  have hz := kron_eval_zero B.w B.D B.residual (residual_deg B hdeg) (by rw [l1_residual]; exact hl1)
    (by rw [kval_eq]; exact hk) x y z
  simp only [residual, Poly.eval_append, Poly.eval_mul, Poly.eval_neg] at hz
  grind

/-- `sqPoly` evaluates to the sum of squares of the columns -/
theorem eval_sqPoly_any {α : Type u} [Lean.Grind.CommRing α] (x y z : α) (cols : List PTree) :
    (sqPoly cols).eval x y z = (cols.map (fun c => c.toPoly.eval x y z * c.toPoly.eval x y z)).foldr (· + ·) 0 := by
  induction cols with
  | nil => rfl
  | cons c cs ih =>
    simp only [sqPoly, List.map_cons, Poly.sum, Poly.eval_append, Poly.eval_mul, List.foldr_cons] at *
    rw [ih]

/-- **Soundness of the residual l1 check**: the collected l1 norm of
`g * Σ_j c_j^2 - target` over the box `[0,D)^3` is at most `L`. -/
theorem checkL1_sound (B : SOSBlock) (L : Nat) (h : B.checkL1 L = true) :
    boxL1 B.D B.residual ≤ L := by
  simp only [checkL1, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hdeg, hw⟩, hl1⟩, hL⟩ := h
  rw [kron_decode_l1 B.w B.D hw B.residual (residual_deg B hdeg) (by rw [l1_residual]; exact hl1),
    kval_eq, balDigits_l1]
  exact Nat.le_of_ble_eq_true hL

end
end SOSBlock

/-! ### Chained chunks: `prev + g * Σ_j c_j^2 = next` -/

/-- A chunk of columns of one SOS block, chained through running totals: the cumulative
polynomial `next` equals `prev + g * Σ_j c_j^2`.  Chunk theorems telescope, so only the final
running total is needed by the residual assembly, and each chunk is its own declaration
(bounded kernel memory). -/
structure SOSChunk where
  w : Nat
  D : Nat
  g : PTree
  cols : List PTree
  prev : PTree
  next : PTree
deriving Inhabited

namespace SOSChunk
noncomputable section

def residual (B : SOSChunk) : Poly :=
  Poly.mul B.g.toPoly (SOSBlock.sqPoly B.cols) ++ B.prev.toPoly ++ Poly.neg B.next.toPoly

def kval (B : SOSChunk) : Int :=
  ishl ((B.g.pack B.w B.D).1 * sqSum B.w B.D B.cols) (B.w * (B.g.pack B.w B.D).2) +
    ishl (B.prev.pack B.w B.D).1 (B.w * (B.prev.pack B.w B.D).2) -
    ishl (B.next.pack B.w B.D).1 (B.w * (B.next.pack B.w B.D).2)

def l1bound (B : SOSChunk) : Nat := B.g.l1 * l1sq B.cols + B.prev.l1 + B.next.l1

def degOK (B : SOSChunk) : Bool :=
  decide (B.g.maxDeg + 2 * maxDegL B.cols < B.D) && decide (B.prev.maxDeg < B.D) &&
    decide (B.next.maxDeg < B.D)

def check (B : SOSChunk) : Bool :=
  B.degOK && decide (B.l1bound < 2 ^ B.w) && (B.kval == 0)

theorem residual_deg (B : SOSChunk) (h : B.degOK = true) : B.residual.DegLt B.D := by
  simp only [degOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  intro s hs
  simp only [residual, List.mem_append] at hs
  rcases hs with (hs | hs) | hs
  · simp only [Poly.mul, List.mem_flatMap, List.mem_map] at hs
    obtain ⟨s1, hs1, s2, hs2, rfl⟩ := hs
    have := PTree.le_maxDeg B.g s1 hs1
    have := SOSBlock.sqPoly_deg B.cols s2 hs2
    simp only [Term.mul]; omega
  · have := PTree.le_maxDeg B.prev s hs; omega
  · simp only [Poly.neg, List.mem_map] at hs
    obtain ⟨t, ht, rfl⟩ := hs
    have := PTree.le_maxDeg B.next t ht
    simp only [Term.neg]; omega

theorem l1_residual (B : SOSChunk) : B.residual.l1 = B.l1bound := by
  simp [residual, l1bound, Poly.l1_append, Poly.l1_mul, Poly.l1_neg, SOSBlock.l1_sqPoly,
    PTree.l1_eq]
  omega

theorem kval_eq (B : SOSChunk) :
    uval (((2 ^ B.w : Nat) : Int)) (Poly.toU B.D B.residual) = B.kval := by
  rw [← Poly.eval_kron]
  simp only [residual, Poly.eval_append, Poly.eval_mul, Poly.eval_neg, SOSBlock.eval_sqPoly,
    PTree.eval_kron_pack, kval]
  simp only [ishl_eq]
  grind

open Lean.Grind in
/-- **Soundness of a chained chunk**: `next = prev + g * Σ_j c_j^2` on every commutative ring. -/
theorem check_sound (B : SOSChunk) (h : B.check = true) {α : Type u} [CommRing α] (x y z : α) :
    B.next.toPoly.eval x y z =
      B.prev.toPoly.eval x y z + B.g.toPoly.eval x y z * (SOSBlock.sqPoly B.cols).eval x y z := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨hdeg, hl1⟩, hk⟩ := h
  have hz := kron_eval_zero B.w B.D B.residual (residual_deg B hdeg)
    (by rw [l1_residual]; exact hl1) (by rw [kval_eq]; exact hk) x y z
  simp only [residual, Poly.eval_append, Poly.eval_mul, Poly.eval_neg] at hz
  grind

end
end SOSChunk

end ThomsonN10.Cert.L1.KC
