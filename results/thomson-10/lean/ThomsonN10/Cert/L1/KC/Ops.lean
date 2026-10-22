/- Adapted from proof/lean/ClaudeL1/KC/Ops.lean, aravindkarthigeyan/thomson-n9-lean, commit 168ff0c98cab4dfda0460ba55f8d169070ac385e (MIT). -/
/-
ThomsonN10.Cert.L1.KC.Ops : polynomial operations used by the kernel blocks and the assembly.

* argument permutations of a polynomial (the six orders of `edgeSymmetrize`),
* boundary substitutions `F(u,u,1)`, `F(v,v,1)`, `F(t,t,1)`, `F(1,1,1)`,
* integer scaling, univariate column polynomials `Σ c_i u^i`,
* the Chebyshev recurrence `q_k` (same recurrence as the upstream project's `circleKernel`),
* the kernel expression `exprPoly cols k = 54·δ²·correctedFactorKernel` (see `KernelBridge`),

each with an evaluation lemma in every commutative ring, an exact l1 formula and a per-variable
degree bound.  The kernel never expands these polynomials: Kronecker values come from the
evaluation lemmas (integer arithmetic), l1 bounds from Nat recurrences.

Core Lean only.  Written from scratch for the N=9 certificate (upstream L1 implementation).
-/
import ThomsonN10.Cert.L1.KC.Check

namespace ThomsonN10.Cert.L1.KC

/-! ### Term maps -/

namespace Term
/-- `F v u t` -/
def perm1 (s : Term) : Term := ⟨s.c, s.b, s.a, s.d⟩
/-- `F u t v` -/
def perm2 (s : Term) : Term := ⟨s.c, s.a, s.d, s.b⟩
/-- `F t u v` -/
def perm3 (s : Term) : Term := ⟨s.c, s.b, s.d, s.a⟩
/-- `F v t u` -/
def perm4 (s : Term) : Term := ⟨s.c, s.d, s.a, s.b⟩
/-- `F t v u` -/
def perm5 (s : Term) : Term := ⟨s.c, s.d, s.b, s.a⟩
/-- `F u u 1` -/
def bu (s : Term) : Term := ⟨s.c, s.a + s.b, 0, 0⟩
/-- `F v v 1` -/
def bv (s : Term) : Term := ⟨s.c, 0, s.a + s.b, 0⟩
/-- `F t t 1` -/
def bt (s : Term) : Term := ⟨s.c, 0, 0, s.a + s.b⟩
/-- `F 1 1 1` -/
def b1 (s : Term) : Term := ⟨s.c, 0, 0, 0⟩
/-- `k * F` -/
def scale (k : Int) (s : Term) : Term := ⟨k * s.c, s.a, s.b, s.d⟩
end Term

/-! ### l1 -/

namespace Poly

theorem l1_map_of_c (f : Term → Term) (hf : ∀ s, (f s).c = s.c) (p : Poly) :
    l1 (p.map f) = l1 p := by
  induction p with
  | nil => rfl
  | cons s p ih => simp only [List.map_cons, l1, hf, ih]

theorem l1_map_scale (k : Int) (p : Poly) : l1 (p.map (Term.scale k)) = k.natAbs * l1 p := by
  induction p with
  | nil => simp [l1]
  | cons s p ih => simp only [List.map_cons, l1, Term.scale, Int.natAbs_mul, ih, Nat.mul_add]

end Poly

/-- l1 of a coefficient list -/
def l1L : List Int → Nat
  | [] => 0
  | c :: cs => c.natAbs + l1L cs

/-! ### Univariate columns -/

/-- `Σ_j cs[j] u^(i+j)` -/
def uPolyAux : List Int → Nat → Poly
  | [], _ => []
  | c :: cs, i => ⟨c, i, 0, 0⟩ :: uPolyAux cs (i + 1)

/-- `Σ_i cs[i] u^i` -/
def uPoly (cs : List Int) : Poly := uPolyAux cs 0
/-- `Σ_i cs[i] v^i` -/
def vPoly (cs : List Int) : Poly := (uPoly cs).map Term.perm1

theorem l1_uPolyAux (cs : List Int) (i : Nat) : Poly.l1 (uPolyAux cs i) = l1L cs := by
  induction cs generalizing i with
  | nil => rfl
  | cons c cs ih => simp only [uPolyAux, Poly.l1, l1L, ih]

theorem l1_uPoly (cs : List Int) : Poly.l1 (uPoly cs) = l1L cs := l1_uPolyAux cs 0
theorem l1_vPoly (cs : List Int) : Poly.l1 (vPoly cs) = l1L cs := by
  rw [vPoly, Poly.l1_map_of_c Term.perm1 (fun _ => rfl), l1_uPoly]

/-! ### Chebyshev polynomials `q_k` -/

/-- `t - u v` -/
def wPoly : Poly := [⟨1, 0, 0, 1⟩, ⟨-1, 1, 1, 0⟩]
/-- `(1 - u^2)(1 - v^2)` -/
def mPoly : Poly := [⟨1, 0, 0, 0⟩, ⟨-1, 2, 0, 0⟩, ⟨-1, 0, 2, 0⟩, ⟨1, 2, 2, 0⟩]

/-- `q_0 = 1`, `q_1 = t - uv`, `q_{n+2} = w q_{n+1} + w q_{n+1} - m q_n` -/
def qPoly : Nat → Poly
  | 0 => [⟨1, 0, 0, 0⟩]
  | 1 => wPoly
  | n + 2 => Poly.mul wPoly (qPoly (n + 1)) ++ Poly.mul wPoly (qPoly (n + 1)) ++
      Poly.neg (Poly.mul mPoly (qPoly n))

/-- exact l1 of `qPoly`, by the pair recurrence -/
def qL1Pair (n : Nat) : Nat × Nat :=
  Nat.rec (motive := fun _ => Nat × Nat) (1, 2) (fun _ p => (p.2, 4 * p.2 + 4 * p.1)) n
def qL1 (n : Nat) : Nat := (qL1Pair n).1

theorem l1_qPoly (n : Nat) : Poly.l1 (qPoly n) = qL1 n ∧ Poly.l1 (qPoly (n + 1)) = qL1 (n + 1) := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    show Poly.l1 (Poly.mul wPoly (qPoly (n + 1)) ++ Poly.mul wPoly (qPoly (n + 1)) ++
      Poly.neg (Poly.mul mPoly (qPoly n))) = (qL1Pair (n + 1)).2
    rw [Poly.l1_append, Poly.l1_append, Poly.l1_neg, Poly.l1_mul, Poly.l1_mul, ih.1, ih.2]
    show 2 * qL1 (n + 1) + 2 * qL1 (n + 1) + 4 * qL1 n = 4 * (qL1Pair n).2 + 4 * (qL1Pair n).1
    show 2 * (qL1Pair n).2 + 2 * (qL1Pair n).2 + 4 * (qL1Pair n).1 = _
    omega

/-! ### The kernel expression -/

/-- `Σ_{cols} c(u) c(v) * q_k(u,v,t)` -/
def rootPoly (cols : List (List Int)) (k : Nat) : Poly :=
  Poly.mul (Poly.sum (cols.map (fun c => Poly.mul (uPoly c) (vPoly c)))) (qPoly k)

/-- plain sum over the six argument orders of `edgeSymmetrize` (no `1/6`) -/
def sym6 (p : Poly) : Poly :=
  p ++ p.map Term.perm1 ++ p.map Term.perm2 ++ p.map Term.perm3 ++ p.map Term.perm4 ++
    p.map Term.perm5

/-- `72 s + 9 s(u,u,1) + 9 s(v,v,1) + 9 s(t,t,1) + s(1,1,1)` -/
def corrOf (s : Poly) : Poly :=
  s.map (Term.scale 72) ++ (s.map Term.bu).map (Term.scale 9) ++
    (s.map Term.bv).map (Term.scale 9) ++ (s.map Term.bt).map (Term.scale 9) ++ s.map Term.b1

/-- `54 δ² · correctedFactorKernel` for the integer factor columns `cols` (see `KernelBridge`) -/
def exprPoly (cols : List (List Int)) (k : Nat) : Poly := corrOf (sym6 (rootPoly cols k))

/-- `Σ_{cols} (l1 c)^2` -/
def colL1 : List (List Int) → Nat
  | [] => 0
  | c :: cs => l1L c * l1L c + colL1 cs

theorem l1_sum_cols (cols : List (List Int)) :
    Poly.l1 (Poly.sum (cols.map (fun c => Poly.mul (uPoly c) (vPoly c)))) = colL1 cols := by
  induction cols with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.map_cons, Poly.sum, Poly.l1_append, Poly.l1_mul, l1_uPoly, l1_vPoly] at *
    rw [ih]; rfl

theorem l1_sym6 (p : Poly) : Poly.l1 (sym6 p) = 6 * Poly.l1 p := by
  simp only [sym6, Poly.l1_append, Poly.l1_map_of_c Term.perm1 (fun _ => rfl),
    Poly.l1_map_of_c Term.perm2 (fun _ => rfl), Poly.l1_map_of_c Term.perm3 (fun _ => rfl),
    Poly.l1_map_of_c Term.perm4 (fun _ => rfl), Poly.l1_map_of_c Term.perm5 (fun _ => rfl)]
  omega

theorem l1_corrOf (s : Poly) : Poly.l1 (corrOf s) = 100 * Poly.l1 s := by
  simp only [corrOf, Poly.l1_append, Poly.l1_map_scale, Poly.l1_map_of_c Term.bu (fun _ => rfl),
    Poly.l1_map_of_c Term.bv (fun _ => rfl), Poly.l1_map_of_c Term.bt (fun _ => rfl),
    Poly.l1_map_of_c Term.b1 (fun _ => rfl)]
  show 72 * _ + 9 * _ + 9 * _ + 9 * _ + _ = _
  omega

theorem l1_exprPoly (cols : List (List Int)) (k : Nat) :
    Poly.l1 (exprPoly cols k) = 600 * colL1 cols * qL1 k := by
  rw [exprPoly, l1_corrOf, l1_sym6, rootPoly, Poly.l1_mul, l1_sum_cols, (l1_qPoly k).1,
    ← Nat.mul_assoc, Nat.mul_assoc 600]

/-! ### Degrees (per variable) -/

/-- every term has `u`-exponent `≤ A`, `v`-exponent `≤ B`, `t`-exponent `≤ C` -/
def Deg3 (A B C : Nat) (p : Poly) : Prop := ∀ s ∈ p, s.a ≤ A ∧ s.b ≤ B ∧ s.d ≤ C

namespace Deg3

theorem append {A B C : Nat} {p q : Poly} (hp : Deg3 A B C p) (hq : Deg3 A B C q) :
    Deg3 A B C (p ++ q) := by
  intro s hs
  rcases List.mem_append.mp hs with h | h
  · exact hp s h
  · exact hq s h

theorem neg {A B C : Nat} {p : Poly} (hp : Deg3 A B C p) : Deg3 A B C (Poly.neg p) := by
  intro s hs
  simp only [Poly.neg, List.mem_map] at hs
  obtain ⟨t, ht, rfl⟩ := hs
  exact hp t ht

theorem mono {A B C A' B' C' : Nat} {p : Poly} (hp : Deg3 A B C p) (h1 : A ≤ A') (h2 : B ≤ B')
    (h3 : C ≤ C') : Deg3 A' B' C' p := by
  intro s hs
  have := hp s hs
  omega

theorem mul {A B C A' B' C' : Nat} {p q : Poly} (hp : Deg3 A B C p) (hq : Deg3 A' B' C' q) :
    Deg3 (A + A') (B + B') (C + C') (Poly.mul p q) := by
  intro s hs
  simp only [Poly.mul, List.mem_flatMap, List.mem_map] at hs
  obtain ⟨s1, h1, s2, h2, rfl⟩ := hs
  have := hp s1 h1
  have := hq s2 h2
  simp only [Term.mul]
  omega

theorem map {A B C A' B' C' : Nat} {p : Poly} (f : Term → Term)
    (hf : ∀ s : Term, s.a ≤ A → s.b ≤ B → s.d ≤ C → (f s).a ≤ A' ∧ (f s).b ≤ B' ∧ (f s).d ≤ C')
    (hp : Deg3 A B C p) : Deg3 A' B' C' (p.map f) := by
  intro s hs
  simp only [List.mem_map] at hs
  obtain ⟨t, ht, rfl⟩ := hs
  have := hp t ht
  exact hf t this.1 this.2.1 this.2.2

theorem sum {A B C : Nat} : ∀ (ps : List Poly), (∀ p ∈ ps, Deg3 A B C p) → Deg3 A B C (Poly.sum ps)
  | [], _ => by intro s hs; cases hs
  | p :: ps, h => by
    simp only [Poly.sum]
    exact append (h p (List.mem_cons_self ..)) (sum ps (fun q hq => h q (List.mem_cons_of_mem _ hq)))

theorem toDegLt {D : Nat} {p : Poly} (hp : Deg3 (D - 1) (D - 1) (D - 1) p) (hD : 1 ≤ D) :
    p.DegLt D := by
  intro s hs
  have := hp s hs
  omega

end Deg3

theorem deg_uPolyAux (cs : List Int) (i : Nat) :
    ∀ s ∈ uPolyAux cs i, i ≤ s.a ∧ s.a < i + cs.length ∧ s.b = 0 ∧ s.d = 0 := by
  induction cs generalizing i with
  | nil => intro s hs; cases hs
  | cons c cs ih =>
    intro s hs
    simp only [uPolyAux, List.mem_cons] at hs
    rcases hs with rfl | hs
    · show i ≤ i ∧ i < i + (cs.length + 1) ∧ (0 : Nat) = 0 ∧ (0 : Nat) = 0
      omega
    · have := ih (i + 1) s hs
      simp only [List.length_cons]; omega

theorem deg_uPoly {m : Nat} (cs : List Int) (h : cs.length ≤ m + 1) : Deg3 m 0 0 (uPoly cs) := by
  intro s hs
  have := deg_uPolyAux cs 0 s hs
  omega

theorem deg_vPoly {m : Nat} (cs : List Int) (h : cs.length ≤ m + 1) : Deg3 0 m 0 (vPoly cs) :=
  Deg3.map Term.perm1 (fun s h1 h2 h3 => by simp only [Term.perm1]; omega) (deg_uPoly cs h)

theorem deg_qPoly (n : Nat) : Deg3 n n n (qPoly n) ∧ Deg3 (n + 1) (n + 1) (n + 1) (qPoly (n + 1)) := by
  have hw : Deg3 1 1 1 wPoly := by
    intro s hs; simp only [wPoly, List.mem_cons, List.mem_nil_iff, or_false] at hs
    rcases hs with rfl | rfl <;> simp
  have hm : Deg3 2 2 0 mPoly := by
    intro s hs; simp only [mPoly, List.mem_cons, List.mem_nil_iff, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl <;> simp
  induction n with
  | zero =>
    refine ⟨?_, hw⟩
    intro s hs; simp only [qPoly, List.mem_cons, List.mem_nil_iff, or_false] at hs
    subst hs; simp
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    show Deg3 (n + 2) (n + 2) (n + 2) (Poly.mul wPoly (qPoly (n + 1)) ++
      Poly.mul wPoly (qPoly (n + 1)) ++ Poly.neg (Poly.mul mPoly (qPoly n)))
    have h1 : Deg3 (n + 2) (n + 2) (n + 2) (Poly.mul wPoly (qPoly (n + 1))) :=
      (Deg3.mul hw ih.2).mono (by omega) (by omega) (by omega)
    have h2 : Deg3 (n + 2) (n + 2) (n + 2) (Poly.mul mPoly (qPoly n)) :=
      (Deg3.mul hm ih.1).mono (by omega) (by omega) (by omega)
    exact (h1.append h1).append h2.neg

/-- the shape condition on the kernel factor columns of block `k` -/
def colsOK (cols : List (List Int)) (k : Nat) : Bool :=
  decide (k ≤ 10) && cols.all (fun c => decide (c.length + k ≤ 11))

theorem deg_rootPoly (cols : List (List Int)) (k : Nat) (h : colsOK cols k = true) :
    Deg3 10 10 10 (rootPoly cols k) := by
  simp only [colsOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨hk, hc⟩ := h
  have hs : Deg3 (10 - k) (10 - k) 0
      (Poly.sum (cols.map (fun c => Poly.mul (uPoly c) (vPoly c)))) := by
    apply Deg3.sum
    intro p hp
    simp only [List.mem_map] at hp
    obtain ⟨c, hcm, rfl⟩ := hp
    have hl : c.length ≤ (10 - k) + 1 := by
      have h1 := hc c hcm
      try simp only [decide_eq_true_eq] at h1
      omega
    exact (Deg3.mul (deg_uPoly c hl) (deg_vPoly c hl)).mono (by omega) (by omega) (by omega)
  exact (Deg3.mul hs (deg_qPoly k).1).mono (by omega) (by omega) (by omega)

theorem deg_sym6 {n : Nat} {p : Poly} (hp : Deg3 n n n p) : Deg3 n n n (sym6 p) := by
  have hm : ∀ f : Term → Term, (∀ s : Term, s.a ≤ n → s.b ≤ n → s.d ≤ n →
      (f s).a ≤ n ∧ (f s).b ≤ n ∧ (f s).d ≤ n) → Deg3 n n n (p.map f) :=
    fun f hf => Deg3.map f hf hp
  refine Deg3.append (Deg3.append (Deg3.append (Deg3.append (Deg3.append hp ?_) ?_) ?_) ?_) ?_ <;>
    apply hm <;>
    intro s h1 h2 h3 <;> simp only [Term.perm1, Term.perm2, Term.perm3, Term.perm4, Term.perm5] <;>
    omega

theorem deg_corrOf {n : Nat} {s : Poly} (hs : Deg3 n n n s) :
    Deg3 (n + n) (n + n) (n + n) (corrOf s) := by
  have hm : ∀ f : Term → Term, (∀ s : Term, s.a ≤ n → s.b ≤ n → s.d ≤ n →
      (f s).a ≤ n + n ∧ (f s).b ≤ n + n ∧ (f s).d ≤ n + n) → Deg3 (n + n) (n + n) (n + n) (s.map f) :=
    fun f hf => Deg3.map f hf hs
  have hsc : ∀ (k : Int) (q : Poly), Deg3 (n + n) (n + n) (n + n) q →
      Deg3 (n + n) (n + n) (n + n) (q.map (Term.scale k)) :=
    fun k q hq => Deg3.map _ (fun s h1 h2 h3 => by simp only [Term.scale]; omega) hq
  refine Deg3.append (Deg3.append (Deg3.append (Deg3.append ?_ ?_) ?_) ?_) ?_
  · apply hm; intro s h1 h2 h3; simp only [Term.scale]; omega
  · apply hsc; apply hm; intro s h1 h2 h3; simp only [Term.bu]; omega
  · apply hsc; apply hm; intro s h1 h2 h3; simp only [Term.bv]; omega
  · apply hsc; apply hm; intro s h1 h2 h3; simp only [Term.bt]; omega
  · apply hm; intro s h1 h2 h3; simp only [Term.b1]; omega

theorem deg_exprPoly (cols : List (List Int)) (k : Nat) (h : colsOK cols k = true) :
    Deg3 20 20 20 (exprPoly cols k) :=
  deg_corrOf (deg_sym6 (deg_rootPoly cols k h))

/-! ### Evaluation in an arbitrary commutative ring -/

section Eval
open Lean.Grind
attribute [local instance] Semiring.natCast Ring.intCast

variable {α : Type u} [CommRing α]

theorem one_pow' (n : Nat) : (1 : α) ^ n = 1 := Semiring.one_pow n

namespace Poly

theorem eval_map (f : Term → Term) (x y z x' y' z' : α)
    (hf : ∀ s : Term, Term.eval x y z (f s) = Term.eval x' y' z' s) (p : Poly) :
    Poly.eval x y z (p.map f) = Poly.eval x' y' z' p := by
  induction p with
  | nil => rfl
  | cons s p ih => simp only [List.map_cons, Poly.eval, hf, ih]

theorem eval_perm1 (x y z : α) (p : Poly) : Poly.eval x y z (p.map Term.perm1) = Poly.eval y x z p :=
  eval_map _ _ _ _ _ _ _ (fun s => by simp only [Term.eval, Term.perm1]; grind) p
theorem eval_perm2 (x y z : α) (p : Poly) : Poly.eval x y z (p.map Term.perm2) = Poly.eval x z y p :=
  eval_map _ _ _ _ _ _ _ (fun s => by simp only [Term.eval, Term.perm2]; grind) p
theorem eval_perm3 (x y z : α) (p : Poly) : Poly.eval x y z (p.map Term.perm3) = Poly.eval z x y p :=
  eval_map _ _ _ _ _ _ _ (fun s => by simp only [Term.eval, Term.perm3]; grind) p
theorem eval_perm4 (x y z : α) (p : Poly) : Poly.eval x y z (p.map Term.perm4) = Poly.eval y z x p :=
  eval_map _ _ _ _ _ _ _ (fun s => by simp only [Term.eval, Term.perm4]; grind) p
theorem eval_perm5 (x y z : α) (p : Poly) : Poly.eval x y z (p.map Term.perm5) = Poly.eval z y x p :=
  eval_map _ _ _ _ _ _ _ (fun s => by simp only [Term.eval, Term.perm5]; grind) p

theorem eval_bu (x y z : α) (p : Poly) : Poly.eval x y z (p.map Term.bu) = Poly.eval x x 1 p :=
  eval_map _ _ _ _ _ _ _ (fun s => by
    simp only [Term.eval, Term.bu, Semiring.pow_add, Semiring.pow_zero, one_pow']; grind) p
theorem eval_bv (x y z : α) (p : Poly) : Poly.eval x y z (p.map Term.bv) = Poly.eval y y 1 p :=
  eval_map _ _ _ _ _ _ _ (fun s => by
    simp only [Term.eval, Term.bv, Semiring.pow_add, Semiring.pow_zero, one_pow']; grind) p
theorem eval_bt (x y z : α) (p : Poly) : Poly.eval x y z (p.map Term.bt) = Poly.eval z z 1 p :=
  eval_map _ _ _ _ _ _ _ (fun s => by
    simp only [Term.eval, Term.bt, Semiring.pow_add, Semiring.pow_zero, one_pow']; grind) p
theorem eval_b1 (x y z : α) (p : Poly) : Poly.eval x y z (p.map Term.b1) = Poly.eval 1 1 1 p :=
  eval_map _ _ _ _ _ _ _ (fun s => by
    simp only [Term.eval, Term.b1, Semiring.pow_zero, one_pow']) p

theorem eval_scale (k : Int) (x y z : α) (p : Poly) :
    Poly.eval x y z (p.map (Term.scale k)) = (k : α) * Poly.eval x y z p := by
  induction p with
  | nil => simp only [List.map_nil, Poly.eval]; grind
  | cons s p ih =>
    simp only [List.map_cons, Poly.eval, ih, Term.eval, Term.scale, Ring.intCast_mul]; grind

end Poly

/-- `Σ_i cs[i] x^i` (Horner) -/
def horner (x : α) : List Int → α
  | [] => 0
  | c :: cs => (c : α) + x * horner x cs

theorem eval_uPolyAux (x y z : α) (cs : List Int) (i : Nat) :
    Poly.eval x y z (uPolyAux cs i) = x ^ i * horner x cs := by
  induction cs generalizing i with
  | nil => simp only [uPolyAux, Poly.eval, horner]; grind
  | cons c cs ih =>
    simp only [uPolyAux, Poly.eval, ih, horner, Term.eval, Semiring.pow_zero, Semiring.pow_succ]
    grind

theorem eval_uPoly (x y z : α) (cs : List Int) : Poly.eval x y z (uPoly cs) = horner x cs := by
  rw [uPoly, eval_uPolyAux, Semiring.pow_zero]; grind

theorem eval_vPoly (x y z : α) (cs : List Int) : Poly.eval x y z (vPoly cs) = horner y cs := by
  rw [vPoly, Poly.eval_perm1, eval_uPoly]

/-- the Chebyshev pair recurrence `(Q_n, Q_{n+1})` for `Q_{n+2} = 2a Q_{n+1} - b Q_n` -/
def qStep (a b : α) (p : α × α) : α × α := (p.2, a * p.2 + a * p.2 - b * p.1)
def qPair (a b : α) (n : Nat) : α × α :=
  Nat.rec (motive := fun _ => α × α) (1, a) (fun _ p => qStep a b p) n
/-- `circ a b n` = the upstream project's `circleKernel a b n` (same recurrence) -/
def circ (a b : α) (n : Nat) : α := (qPair a b n).1

theorem circ_zero (a b : α) : circ a b 0 = 1 := rfl
theorem circ_one (a b : α) : circ a b 1 = a := rfl
theorem circ_succ_succ (a b : α) (n : Nat) :
    circ a b (n + 2) = a * circ a b (n + 1) + a * circ a b (n + 1) - b * circ a b n := rfl

/-- `q_k(x,y,z) = circ (z - x y) ((1 - x x)(1 - y y)) k` -/
def qVal (x y z : α) (k : Nat) : α := circ (z - x * y) ((1 - x * x) * (1 - y * y)) k

theorem eval_wPoly (x y z : α) : Poly.eval x y z wPoly = z - x * y := by
  simp only [wPoly, Poly.eval, Term.eval, Ring.intCast_one, Ring.intCast_neg_one,
    Semiring.pow_zero, Semiring.pow_one]
  grind

theorem eval_mPoly (x y z : α) : Poly.eval x y z mPoly = (1 - x * x) * (1 - y * y) := by
  simp only [mPoly, Poly.eval, Term.eval, Ring.intCast_one, Ring.intCast_neg_one,
    Semiring.pow_zero, Semiring.pow_two]
  grind

theorem eval_qPoly (x y z : α) (n : Nat) :
    Poly.eval x y z (qPoly n) = qVal x y z n ∧ Poly.eval x y z (qPoly (n + 1)) = qVal x y z (n + 1) := by
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · simp only [qPoly, Poly.eval, Term.eval, Ring.intCast_one, Semiring.pow_zero, qVal, circ_zero]
      grind
    · simp only [qPoly, eval_wPoly]; rfl
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    show Poly.eval x y z (Poly.mul wPoly (qPoly (n + 1)) ++ Poly.mul wPoly (qPoly (n + 1)) ++
      Poly.neg (Poly.mul mPoly (qPoly n))) = _
    rw [Poly.eval_append, Poly.eval_append, Poly.eval_neg, Poly.eval_mul, Poly.eval_mul,
      eval_wPoly, eval_mPoly, ih.1, ih.2, qVal, qVal, qVal, circ_succ_succ]
    grind

/-- `Σ_{cols} horner(c, x) * horner(c, y)` -/
def colSum (x y : α) : List (List Int) → α
  | [] => 0
  | c :: cs => horner x c * horner y c + colSum x y cs

theorem eval_sum_cols (x y z : α) (cols : List (List Int)) :
    Poly.eval x y z (Poly.sum (cols.map (fun c => Poly.mul (uPoly c) (vPoly c)))) = colSum x y cols := by
  induction cols with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.map_cons, Poly.sum, Poly.eval_append, Poly.eval_mul, eval_uPoly, eval_vPoly,
      colSum] at *
    rw [ih]

def rootVal (cols : List (List Int)) (k : Nat) (x y z : α) : α := colSum x y cols * qVal x y z k

def symVal (cols : List (List Int)) (k : Nat) (x y z : α) : α :=
  rootVal cols k x y z + rootVal cols k y x z + rootVal cols k x z y + rootVal cols k z x y +
    rootVal cols k y z x + rootVal cols k z y x

/-- the value of `exprPoly cols k` -/
def exprVal (cols : List (List Int)) (k : Nat) (x y z : α) : α :=
  ((72 : Int) : α) * symVal cols k x y z + ((9 : Int) : α) * symVal cols k x x 1 +
    ((9 : Int) : α) * symVal cols k y y 1 + ((9 : Int) : α) * symVal cols k z z 1 +
    symVal cols k 1 1 1

theorem eval_rootPoly (x y z : α) (cols : List (List Int)) (k : Nat) :
    Poly.eval x y z (rootPoly cols k) = rootVal cols k x y z := by
  rw [rootPoly, Poly.eval_mul, eval_sum_cols, (eval_qPoly x y z k).1, rootVal]

theorem eval_sym6 (x y z : α) (p : Poly) :
    Poly.eval x y z (sym6 p) = Poly.eval x y z p + Poly.eval y x z p + Poly.eval x z y p +
      Poly.eval z x y p + Poly.eval y z x p + Poly.eval z y x p := by
  simp only [sym6, Poly.eval_append, Poly.eval_perm1, Poly.eval_perm2, Poly.eval_perm3,
    Poly.eval_perm4, Poly.eval_perm5]

theorem eval_corrOf (x y z : α) (s : Poly) :
    Poly.eval x y z (corrOf s) = ((72 : Int) : α) * Poly.eval x y z s +
      ((9 : Int) : α) * Poly.eval x x 1 s + ((9 : Int) : α) * Poly.eval y y 1 s +
      ((9 : Int) : α) * Poly.eval z z 1 s + Poly.eval 1 1 1 s := by
  simp only [corrOf, Poly.eval_append, Poly.eval_scale, Poly.eval_bu, Poly.eval_bv, Poly.eval_bt,
    Poly.eval_b1]

theorem eval_exprPoly (x y z : α) (cols : List (List Int)) (k : Nat) :
    Poly.eval x y z (exprPoly cols k) = exprVal cols k x y z := by
  simp only [exprPoly, eval_corrOf, eval_sym6, eval_rootPoly, exprVal, symVal]

end Eval

end ThomsonN10.Cert.L1.KC
