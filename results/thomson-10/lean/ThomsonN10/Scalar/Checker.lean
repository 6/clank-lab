/- Adapted from proof/lean/ThomsonN9/Bernstein/Checker.lean in
   aravindkarthigeyan/thomson-n9-lean, MIT, commit
   168ff0c98cab4dfda0460ba55f8d169070ac385e. -/
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-!
# A verified homogeneous Bernstein positivity checker

A list `e = [e₀, …, eₘ]` of integers represents the binary form
`homEval e s t = ∑ⱼ eⱼ sʲ tᵐ⁻ʲ`.  If every `eⱼ ≥ 0` then this form is nonnegative on the
closed quadrant `s, t ≥ 0`.  (These are the Bernstein coefficients up to the positive
binomial factors, so no binomials are needed anywhere.)

A subdivision step replaces `e` by the two forms
* `leftChild e`  with `homEval (leftChild e) s t = homEval e (2s+t) t`, and
* `rightChild e` with `homEval (rightChild e) s t = homEval e s (2t+s)`.
The two linear maps `(s,t) ↦ (2s+t,t)` and `(s,t) ↦ (s,2t+s)` map the quadrant onto
`{t ≤ s}` and `{s ≤ t}`, so nonnegativity of both children implies nonnegativity of `e`
(`nonneg_of_children`).  Children may be replaced by `x ↦ x / d` (floor division by a
positive integer `d`): the rounded form is a lower bound up to the factor `d`
(`homEval_mapDiv`), so this keeps numbers small without affecting soundness.

`runSteps` processes a preorder bit string (`1` = accept leaf, `0` = split) with an explicit
stack, all in `ℤ`/`ℕ` arithmetic so that the kernel can evaluate it with GMP acceleration.
`runSteps_sound` is the soundness theorem.  `rootForm` turns an integer polynomial in `y`
and an interval `A/M ≤ y ≤ B/M` into the root binary form, and `checkInterval_sound` is the
end-to-end statement `checkInterval … = true → ∀ y, A ≤ M*y ≤ B → 0 ≤ p(y)`.
-/

namespace ThomsonN10.Scalar.Bernstein

/-! ### Univariate integer polynomials, ascending coefficient lists -/

/-- Horner evaluation in `ℝ` of an integer coefficient list (ascending powers). -/
noncomputable def polyEval : List ℤ → ℝ → ℝ
  | [], _ => 0
  | a :: l, y => (a : ℝ) + y * polyEval l y

@[simp] theorem polyEval_nil (y : ℝ) : polyEval [] y = 0 := rfl
@[simp] theorem polyEval_cons (a : ℤ) (l : List ℤ) (y : ℝ) :
    polyEval (a :: l) y = a + y * polyEval l y := rfl

/-- `polyEval` is the usual coefficient sum. -/
theorem polyEval_eq_sum : ∀ (l : List ℤ) (y : ℝ),
    polyEval l y = ∑ i ∈ Finset.range l.length, ((l.getD i 0 : ℤ) : ℝ) * y ^ i
  | [], y => by simp
  | a :: l, y => by
    rw [polyEval_cons, polyEval_eq_sum l y, List.length_cons, Finset.sum_range_succ',
      Finset.mul_sum]
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one, pow_succ]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun i _ => by ring

/-- Coefficientwise sum (the shorter list is padded with zeros). -/
def addL : List ℤ → List ℤ → List ℤ
  | [], m => m
  | a :: l, [] => a :: l
  | a :: l, b :: m => (a + b) :: addL l m

theorem length_addL : ∀ l m : List ℤ, (addL l m).length = max l.length m.length
  | [], m => by simp [addL]
  | a :: l, [] => by simp [addL]
  | a :: l, b :: m => by simp [addL, length_addL l m, Nat.succ_max_succ]

theorem polyEval_addL : ∀ (l m : List ℤ) (y : ℝ),
    polyEval (addL l m) y = polyEval l y + polyEval m y
  | [], m, y => by simp [addL]
  | a :: l, [], y => by simp [addL]
  | a :: l, b :: m, y => by
    simp only [addL, polyEval_cons, polyEval_addL l m y]
    push_cast; ring

/-- Multiply every coefficient by `c`. -/
def scaleL (c : ℤ) (l : List ℤ) : List ℤ := l.map (fun x => c * x)

@[simp] theorem length_scaleL (c : ℤ) (l : List ℤ) : (scaleL c l).length = l.length := by
  simp [scaleL]

theorem polyEval_scaleL (c : ℤ) : ∀ (l : List ℤ) (y : ℝ),
    polyEval (scaleL c l) y = c * polyEval l y
  | [], y => by simp [scaleL]
  | a :: l, y => by
    have ih := polyEval_scaleL c l y
    simp only [scaleL, List.map_cons, polyEval_cons] at ih ⊢
    rw [ih]; push_cast; ring

/-- Multiply by `1 - 2y²`. -/
def mulQuad : List ℤ → List ℤ
  | [] => []
  | a :: l => addL (a :: l) (0 :: 0 :: scaleL (-2) (a :: l))

theorem polyEval_mulQuad (q : List ℤ) (y : ℝ) :
    polyEval (mulQuad q) y = (1 - 2 * y ^ 2) * polyEval q y := by
  cases q with
  | nil => simp [mulQuad]
  | cons a l =>
    simp only [mulQuad, polyEval_addL, polyEval_cons, polyEval_scaleL]
    push_cast; ring

/-- Coefficients of `q(1 - 2y²)`. -/
def compQuad : List ℤ → List ℤ
  | [] => []
  | a :: l => addL [a] (mulQuad (compQuad l))

theorem polyEval_compQuad : ∀ (q : List ℤ) (y : ℝ),
    polyEval (compQuad q) y = polyEval q (1 - 2 * y ^ 2)
  | [], y => by simp [compQuad]
  | a :: l, y => by
    rw [compQuad, polyEval_addL, polyEval_mulQuad, polyEval_compQuad l y]
    simp

/-- Coefficients (in `y`) of `D - 2 y Q(1 - 2y²)`, where `Q` has coefficient list `q`. -/
def potential (q : List ℤ) (D : ℤ) : List ℤ := addL [D] (0 :: scaleL (-2) (compQuad q))

theorem polyEval_potential (q : List ℤ) (D : ℤ) (y : ℝ) :
    polyEval (potential q D) y = D - 2 * y * polyEval q (1 - 2 * y ^ 2) := by
  simp only [potential, polyEval_addL, polyEval_cons, polyEval_scaleL, polyEval_compQuad,
    polyEval_nil]
  push_cast; ring

/-! ### Binary forms -/

/-- `homEval [e₀,…,eₘ] s t = ∑ⱼ eⱼ sʲ tᵐ⁻ʲ`. -/
noncomputable def homEval : List ℤ → ℝ → ℝ → ℝ
  | [], _, _ => 0
  | a :: l, s, t => (a : ℝ) * t ^ l.length + s * homEval l s t

@[simp] theorem homEval_nil (s t : ℝ) : homEval [] s t = 0 := rfl
@[simp] theorem homEval_cons (a : ℤ) (l : List ℤ) (s t : ℝ) :
    homEval (a :: l) s t = a * t ^ l.length + s * homEval l s t := rfl

theorem homEval_one (l : List ℤ) (y : ℝ) : homEval l y 1 = polyEval l y := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem homEval_smul (l : List ℤ) (c Y W : ℝ) :
    homEval l (c * Y) (c * W) * c = c ^ l.length * homEval l Y W := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [homEval_cons, List.length_cons]
    calc ((a : ℝ) * (c * W) ^ l.length + c * Y * homEval l (c * Y) (c * W)) * c
        = (a : ℝ) * (c * W) ^ l.length * c + c * Y * (homEval l (c * Y) (c * W) * c) := by
          ring
      _ = c ^ (l.length + 1) * ((a : ℝ) * W ^ l.length + Y * homEval l Y W) := by
          rw [ih, mul_pow]; ring

theorem homEval_nonneg {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    ∀ l : List ℤ, (∀ x ∈ l, 0 ≤ x) → 0 ≤ homEval l s t
  | [], _ => le_refl 0
  | a :: l, h => by
    rw [homEval_cons]
    have ha : (0 : ℝ) ≤ a := by exact_mod_cast h a (List.mem_cons.2 (Or.inl rfl))
    have hl := homEval_nonneg hs ht l (fun x hx => h x (List.mem_cons.2 (Or.inr hx)))
    exact add_nonneg (mul_nonneg ha (pow_nonneg ht _)) (mul_nonneg hs hl)

/-- Floor division of every coefficient by `d`. -/
def divAll (d : ℤ) (l : List ℤ) : List ℤ := l.map (fun x => x / d)

theorem homEval_divAll {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) {d : ℤ} (hd : 0 < d) :
    ∀ l : List ℤ, (d : ℝ) * homEval (divAll d l) s t ≤ homEval l s t
  | [] => by simp [divAll]
  | a :: l => by
    have ih := homEval_divAll hs ht hd l
    simp only [divAll, List.map_cons, homEval_cons, List.length_map] at ih ⊢
    have h1 : ((a / d : ℤ) : ℝ) * (d : ℝ) ≤ (a : ℝ) := by
      exact_mod_cast Int.ediv_mul_le a (ne_of_gt hd)
    calc (d : ℝ) * (((a / d : ℤ) : ℝ) * t ^ l.length
            + s * homEval (List.map (fun x => x / d) l) s t)
        = (((a / d : ℤ) : ℝ) * d) * t ^ l.length
            + s * ((d : ℝ) * homEval (List.map (fun x => x / d) l) s t) := by ring
      _ ≤ (a : ℝ) * t ^ l.length + s * homEval l s t :=
          add_le_add (mul_le_mul_of_nonneg_right h1 (pow_nonneg ht _))
            (mul_le_mul_of_nonneg_left ih hs)

theorem length_addL_eq {l m : List ℤ} (h : l.length = m.length) :
    (addL l m).length = l.length := by
  rw [length_addL, h, max_self]

theorem homEval_addL_of_length (s t : ℝ) : ∀ (l m : List ℤ), l.length = m.length →
    homEval (addL l m) s t = homEval l s t + homEval m s t
  | [], [], _ => by simp [addL]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: l, b :: m, h => by
    have h' : l.length = m.length := by simpa using h
    simp only [addL, homEval_cons, length_addL_eq h', homEval_addL_of_length s t l m h']
    rw [h']; push_cast; ring

theorem homEval_scaleL (c : ℤ) (s t : ℝ) : ∀ l : List ℤ,
    homEval (scaleL c l) s t = c * homEval l s t
  | [] => by simp [scaleL]
  | a :: l => by
    have ih := homEval_scaleL c s t l
    simp only [scaleL, List.map_cons, homEval_cons, List.length_map] at ih ⊢
    rw [ih]; push_cast; ring

/-! ### Subdivision -/

/-- `addShift p [f₀,…,f_{k-1}] = [p+f₀, f₀+f₁, …, f_{k-2}+f_{k-1}, f_{k-1}]`. -/
def addShift : ℤ → List ℤ → List ℤ
  | p, [] => [p]
  | p, x :: xs => (p + x) :: addShift x xs

theorem length_addShift : ∀ (p : ℤ) (l : List ℤ), (addShift p l).length = l.length + 1
  | _, [] => rfl
  | _, x :: xs => by simp [addShift, length_addShift x xs]

theorem homEval_addShift (s t : ℝ) : ∀ (p : ℤ) (l : List ℤ),
    homEval (addShift p l) s t = p * t ^ l.length + (s + t) * homEval l s t
  | p, [] => by simp [addShift]
  | p, x :: xs => by
    simp only [addShift, homEval_cons, length_addShift, List.length_cons,
      homEval_addShift s t x xs]
    push_cast; ring

/-- Taylor shift `s ↦ s + t` of a binary form (additions only). -/
def shiftS : List ℤ → List ℤ
  | [] => []
  | a :: l => addShift a (shiftS l)

theorem length_shiftS : ∀ l : List ℤ, (shiftS l).length = l.length
  | [] => rfl
  | a :: l => by simp [shiftS, length_addShift, length_shiftS l]

theorem homEval_shiftS (s t : ℝ) : ∀ l : List ℤ, homEval (shiftS l) s t = homEval l (s + t) t
  | [] => rfl
  | a :: l => by
    simp only [shiftS, homEval_addShift, length_shiftS, homEval_shiftS s t l, homEval_cons]

/-- `scaleFrom c [x₀,x₁,…] = [c x₀, 2c x₁, 4c x₂, …]`. -/
def scaleFrom : ℤ → List ℤ → List ℤ
  | _, [] => []
  | c, x :: xs => (c * x) :: scaleFrom (2 * c) xs

theorem length_scaleFrom : ∀ (c : ℤ) (l : List ℤ), (scaleFrom c l).length = l.length
  | _, [] => rfl
  | c, x :: xs => by simp [scaleFrom, length_scaleFrom (2 * c) xs]

theorem homEval_scaleFrom (s t : ℝ) : ∀ (c : ℤ) (l : List ℤ),
    homEval (scaleFrom c l) s t = c * homEval l (2 * s) t
  | c, [] => by simp [scaleFrom]
  | c, x :: xs => by
    simp only [scaleFrom, homEval_cons, length_scaleFrom, homEval_scaleFrom s t (2 * c) xs]
    push_cast; ring

/-- Left child: `homEval (leftChild e) s t = homEval e (2s+t) t`. -/
def leftChild (e : List ℤ) : List ℤ := scaleFrom 1 (shiftS e)

theorem homEval_leftChild (e : List ℤ) (s t : ℝ) :
    homEval (leftChild e) s t = homEval e (2 * s + t) t := by
  rw [leftChild, homEval_scaleFrom, homEval_shiftS]; simp

theorem homEval_append_singleton (s t : ℝ) (b : ℤ) : ∀ l : List ℤ,
    homEval (l ++ [b]) s t = t * homEval l s t + b * s ^ l.length
  | [] => by simp
  | a :: l => by
    simp only [List.cons_append, homEval_cons, List.length_append, List.length_cons,
      List.length_nil, homEval_append_singleton s t b l]
    ring

theorem homEval_reverse : ∀ (l : List ℤ) (s t : ℝ), homEval l.reverse s t = homEval l t s
  | [], _, _ => rfl
  | a :: l, s, t => by
    rw [List.reverse_cons, homEval_append_singleton, homEval_reverse l, List.length_reverse,
      homEval_cons]
    ring

/-- Right child: `homEval (rightChild e) s t = homEval e s (2t+s)`. -/
def rightChild (e : List ℤ) : List ℤ := (leftChild e.reverse).reverse

theorem homEval_rightChild (e : List ℤ) (s t : ℝ) :
    homEval (rightChild e) s t = homEval e s (2 * t + s) := by
  rw [rightChild, homEval_reverse, homEval_leftChild, homEval_reverse]

/-! ### Nonnegativity on the quadrant and the checker -/

/-- The binary form is nonnegative on the closed quadrant. -/
def Nonneg (e : List ℤ) : Prop := ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → 0 ≤ homEval e s t

theorem nonneg_of_children {e : List ℤ} (hl : Nonneg (leftChild e))
    (hr : Nonneg (rightChild e)) : Nonneg e := by
  intro s t hs ht
  rcases le_total t s with h | h
  · have key := hl ((s - t) / 2) t (by linarith) ht
    rw [homEval_leftChild] at key
    have e1 : 2 * ((s - t) / 2) + t = s := by ring
    rwa [e1] at key
  · have key := hr s ((t - s) / 2) hs (by linarith)
    rw [homEval_rightChild] at key
    have e1 : 2 * ((t - s) / 2) + s = t := by ring
    rwa [e1] at key

theorem nonneg_of_divAll {e : List ℤ} {d : ℤ} (hd : 0 < d) (h : Nonneg (divAll d e)) :
    Nonneg e := by
  intro s t hs ht
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  exact le_trans (mul_nonneg hd'.le (h s t hs ht)) (homEval_divAll hs ht hd e)

/-- Sign test by constructor (kernel friendly). -/
def isNonneg : ℤ → Bool
  | Int.ofNat _ => true
  | Int.negSucc _ => false

theorem isNonneg_sound : ∀ x : ℤ, isNonneg x = true → 0 ≤ x
  | Int.ofNat n, _ => by simp
  | Int.negSucc _, h => by simp [isNonneg] at h

def allNonneg : List ℤ → Bool
  | [] => true
  | x :: xs => isNonneg x && allNonneg xs

theorem allNonneg_sound : ∀ l : List ℤ, allNonneg l = true → ∀ x ∈ l, 0 ≤ x
  | [], _ => by simp
  | x :: xs, h => by
    simp only [allNonneg, Bool.and_eq_true] at h
    intro y hy
    rcases List.mem_cons.1 hy with rfl | hy
    · exact isNonneg_sound _ h.1
    · exact allNonneg_sound xs h.2 y hy

theorem nonneg_of_allNonneg {e : List ℤ} (h : allNonneg e = true) : Nonneg e :=
  fun _ _ hs ht => homEval_nonneg hs ht e (allNonneg_sound e h)

/-- Inspects every entry; its value is irrelevant for soundness.  It makes kernel
reduction evaluate the children eagerly (no deep chains of delayed computations). -/
def forceList : List ℤ → Bool
  | [] => true
  | x :: xs => (isNonneg x || true) && forceList xs

/-- Process `fuel` tokens of the preorder bit string `bits` (least significant bit first;
`1` = accepted leaf, `0` = split) starting from `stack`.  Returns the remaining stack. -/
def runSteps (d : ℤ) : ℕ → ℕ → List (List ℤ) → Option (List (List ℤ))
  | 0, _, stack => some stack
  | _ + 1, _, [] => none
  | fuel + 1, bits, e :: stack =>
    if bits % 2 = 1 then
      (if allNonneg e then runSteps d fuel (bits / 2) stack else none)
    else
      let l := divAll d (leftChild e)
      let r := divAll d (rightChild e)
      if forceList l && forceList r then runSteps d fuel (bits / 2) (l :: r :: stack)
      else none

theorem runSteps_sound {d : ℤ} (hd : 0 < d) :
    ∀ (fuel bits : ℕ) (stack S : List (List ℤ)), runSteps d fuel bits stack = some S →
      (∀ e ∈ S, Nonneg e) → ∀ e ∈ stack, Nonneg e
  | 0, _, stack, S, h, hS => by
    simp only [runSteps, Option.some.injEq] at h
    subst h; exact hS
  | _ + 1, _, [], _, h, _ => by simp [runSteps] at h
  | fuel + 1, bits, e :: stack, S, h, hS => by
    simp only [runSteps] at h
    by_cases hb : bits % 2 = 1
    · simp only [hb, ↓reduceIte] at h
      by_cases ha : allNonneg e = true
      · simp only [ha, ↓reduceIte] at h
        have ih := runSteps_sound hd fuel (bits / 2) stack S h hS
        intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact nonneg_of_allNonneg ha
        · exact ih x hx
      · simp [ha] at h
    · simp only [hb, ↓reduceIte] at h
      by_cases hf : (forceList (divAll d (leftChild e)) && forceList (divAll d (rightChild e))) = true
      · simp only [hf, ↓reduceIte] at h
        have ih := runSteps_sound hd fuel (bits / 2) _ S h hS
        intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact nonneg_of_children (nonneg_of_divAll hd (ih _ (by simp)))
            (nonneg_of_divAll hd (ih _ (by simp)))
        · exact ih x (by simp [hx])
      · simp [hf] at h

/-! ### Root form for an interval and the end-to-end checker -/

/-- `mulLinAux α β p e` is the form `(α s + β t)·e + α p tᵏ⁺¹`-style product; see
`homEval_mulLinAux`. -/
def mulLinAux (α β : ℤ) : ℤ → List ℤ → List ℤ
  | p, [] => [α * p]
  | p, x :: xs => (α * p + β * x) :: mulLinAux α β x xs

theorem length_mulLinAux (α β : ℤ) : ∀ (p : ℤ) (l : List ℤ),
    (mulLinAux α β p l).length = l.length + 1
  | _, [] => rfl
  | _, x :: xs => by simp [mulLinAux, length_mulLinAux α β x xs]

theorem homEval_mulLinAux (α β : ℤ) (s t : ℝ) : ∀ (p : ℤ) (l : List ℤ),
    homEval (mulLinAux α β p l) s t = α * p * t ^ l.length + (α * s + β * t) * homEval l s t
  | p, [] => by simp [mulLinAux]
  | p, x :: xs => by
    simp only [mulLinAux, homEval_cons, length_mulLinAux, List.length_cons,
      homEval_mulLinAux α β s t x xs]
    push_cast; ring

/-- Multiplication of a binary form by the linear form `α s + β t`. -/
def mulLin (α β : ℤ) (e : List ℤ) : List ℤ := mulLinAux α β 0 e

theorem length_mulLin (α β : ℤ) (e : List ℤ) : (mulLin α β e).length = e.length + 1 :=
  length_mulLinAux α β 0 e

theorem homEval_mulLin (α β : ℤ) (e : List ℤ) (s t : ℝ) :
    homEval (mulLin α β e) s t = (α * s + β * t) * homEval e s t := by
  rw [mulLin, homEval_mulLinAux]; simp

/-- `(linSubstAux α β γ δ a).1` is the binary form `homEval a (α s + β t) (γ s + δ t)`;
the second component is `(γ s + δ t) ^ a.length`. -/
def linSubstAux (α β γ δ : ℤ) : List ℤ → List ℤ × List ℤ
  | [] => ([], [1])
  | x :: rest =>
    let r := linSubstAux α β γ δ rest
    (addL (scaleL x r.2) (mulLin α β r.1), mulLin γ δ r.2)

theorem linSubstAux_spec (α β γ δ : ℤ) (s t : ℝ) : ∀ l : List ℤ,
    (linSubstAux α β γ δ l).1.length = l.length ∧
    (linSubstAux α β γ δ l).2.length = l.length + 1 ∧
    homEval (linSubstAux α β γ δ l).1 s t = homEval l (α * s + β * t) (γ * s + δ * t) ∧
    homEval (linSubstAux α β γ δ l).2 s t = (γ * s + δ * t) ^ l.length
  | [] => by simp [linSubstAux]
  | x :: rest => by
    obtain ⟨h1, h2, h3, h4⟩ := linSubstAux_spec α β γ δ s t rest
    have hlen : (scaleL x (linSubstAux α β γ δ rest).2).length =
        (mulLin α β (linSubstAux α β γ δ rest).1).length := by
      rw [length_scaleL, length_mulLin, h1, h2]
    simp only [linSubstAux]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [length_addL_eq hlen, length_scaleL, h2, List.length_cons]
    · rw [length_mulLin, h2, List.length_cons]
    · rw [homEval_addL_of_length s t _ _ hlen, homEval_scaleL, homEval_mulLin, h3, h4,
        homEval_cons]
    · rw [homEval_mulLin, h4, List.length_cons, pow_succ]; ring

/-- Root binary form of the polynomial `a` on the interval `A/M ≤ y ≤ B/M`. -/
def rootForm (a : List ℤ) (A B M : ℤ) : List ℤ := (linSubstAux A B M M a).1

theorem homEval_rootForm (a : List ℤ) (A B M : ℤ) (s t : ℝ) :
    homEval (rootForm a A B M) s t = homEval a (A * s + B * t) (M * s + M * t) :=
  (linSubstAux_spec A B M M s t a).2.2.1

theorem polyEval_nonneg_of_rootForm {a : List ℤ} {A B M : ℤ} (hM : 0 < M) (hAB : A < B)
    (h : Nonneg (rootForm a A B M)) :
    ∀ y : ℝ, (A : ℝ) ≤ M * y → M * y ≤ B → 0 ≤ polyEval a y := by
  intro y h1 h2
  have hBA : (0 : ℝ) < (B : ℝ) - A := by
    have : (A : ℝ) < B := by exact_mod_cast hAB
    linarith
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hs : 0 ≤ ((B : ℝ) - M * y) / (B - A) := div_nonneg (by linarith) hBA.le
  have ht : 0 ≤ ((M : ℝ) * y - A) / (B - A) := div_nonneg (by linarith) hBA.le
  have key := h _ _ hs ht
  rw [homEval_rootForm] at key
  have e1 : (A : ℝ) * (((B : ℝ) - M * y) / (B - A)) + B * (((M : ℝ) * y - A) / (B - A))
      = M * y := by
    field_simp; ring
  have e2 : (M : ℝ) * (((B : ℝ) - M * y) / (B - A)) + M * (((M : ℝ) * y - A) / (B - A))
      = M * 1 := by
    field_simp; ring
  rw [e1, e2] at key
  have hsm := homEval_smul a (M : ℝ) y 1
  rw [homEval_one] at hsm
  have hprod : 0 ≤ (M : ℝ) ^ a.length * polyEval a y := by
    rw [← hsm]; exact mul_nonneg key hMr.le
  by_contra hneg
  have := mul_neg_of_pos_of_neg (pow_pos hMr a.length) (not_le.mp hneg)
  linarith

def isSomeNil : Option (List (List ℤ)) → Bool
  | some [] => true
  | _ => false

theorem isSomeNil_sound {o : Option (List (List ℤ))} (h : isSomeNil o = true) : o = some [] := by
  match o, h with
  | some [], _ => rfl

/-- End-to-end checker: polynomial `a` (ascending integer coefficients), interval
`A/M ≤ y ≤ B/M`, rounding divisor `d`, number of tokens `fuel`, preorder tree `bits`. -/
def checkInterval (a : List ℤ) (A B M d : ℤ) (fuel bits : ℕ) : Bool :=
  decide (0 < M) && decide (A < B) && decide (0 < d) &&
    isSomeNil (runSteps d fuel bits [rootForm a A B M])

theorem checkInterval_sound {a : List ℤ} {A B M d : ℤ} {fuel bits : ℕ}
    (h : checkInterval a A B M d fuel bits = true) :
    ∀ y : ℝ, (A : ℝ) ≤ M * y → M * y ≤ B → 0 ≤ polyEval a y := by
  simp only [checkInterval, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hM, hAB⟩, hd⟩, hrun⟩ := h
  have hroot := runSteps_sound hd fuel bits _ [] (isSomeNil_sound hrun) (by simp)
    (rootForm a A B M) (by simp)
  exact polyEval_nonneg_of_rootForm hM hAB hroot

/-- Chained version, for certificates split into several kernel checks: if a run from
`stack` ends in `S` and every form of `S` is nonnegative, so is every form of `stack`. -/
theorem nonneg_of_runSteps {d : ℤ} {fuel bits : ℕ} {stack S : List (List ℤ)}
    (hd : 0 < d) (h : runSteps d fuel bits stack = some S) (hS : ∀ e ∈ S, Nonneg e) :
    ∀ e ∈ stack, Nonneg e :=
  runSteps_sound hd fuel bits stack S h hS

/-- Cover check: consecutive intervals `[x, p₀], [p₀, p₁], …` (endpoints over the common
denominator `M`), each verified as a single leaf. -/
def checkCover (a : List ℤ) (M : ℤ) : ℤ → List ℤ → Bool
  | _, [] => false
  | x, [y] => checkInterval a x y M 1 1 1
  | x, y :: z :: rest => checkInterval a x y M 1 1 1 && checkCover a M y (z :: rest)

theorem checkCover_sound {a : List ℤ} {M : ℤ} : ∀ (x : ℤ) (l : List ℤ),
    checkCover a M x l = true →
      ∀ y : ℝ, (x : ℝ) ≤ M * y → M * y ≤ ((l.getLastD x : ℤ) : ℝ) → 0 ≤ polyEval a y
  | _, [], h => by simp [checkCover] at h
  | _, [_], h => fun y' h1 h2 => checkInterval_sound h y' h1 h2
  | x, y :: z :: rest, h => by
    simp only [checkCover, Bool.and_eq_true] at h
    intro y' h1 h2
    by_cases hy : (M : ℝ) * y' ≤ y
    · exact checkInterval_sound h.1 y' h1 hy
    · exact checkCover_sound y (z :: rest) h.2 y' (le_of_lt (not_le.mp hy)) h2

end ThomsonN10.Scalar.Bernstein
