/- Adapted from proof/lean/ThomsonN9/Certificates/IntervalCircuit.lean,
   aravindkarthigeyan/thomson-n9-lean @ 168ff0c98cab4dfda0460ba55f8d169070ac385e (MIT). -/
import ThomsonN10.Local.Certificates.ScaledInterval

/-! Sound shared arithmetic circuits, checked by finite integer endpoint tests. -/

namespace ThomsonN10.Local.Certificates.IntervalCircuit

inductive Op where
  | input (index : ℕ)
  | constant (numerator denominator : ℤ)
  | add (left right : ℕ)
  | neg (arg : ℕ)
  | mul (left right : ℕ)
  | inv (arg : ℕ)
  | sqrt (arg : ℕ)
  deriving DecidableEq, Repr

namespace Op

def refs : Op → List ℕ
  | .input _ | .constant _ _ => []
  | .add i j | .mul i j => [i,j]
  | .neg i | .inv i | .sqrt i => [i]

def RefsBelow (n : ℕ) : Op → Prop
  | .input _ | .constant _ _ => True
  | .add i j | .mul i j => i < n ∧ j < n
  | .neg i | .inv i | .sqrt i => i < n

instance (n : ℕ) (op : Op) : Decidable (RefsBelow n op) := by
  cases op <;> unfold RefsBelow <;> infer_instance

theorem refs_lt {n : ℕ} {op : Op} (h : RefsBelow n op) {i : ℕ}
    (hi : i ∈ op.refs) : i < n := by
  cases op <;> simp_all [RefsBelow, refs] <;> omega

noncomputable def eval (inputs values : ℕ → ℝ) : Op → ℝ
  | .input i => inputs i
  | .constant num den => (num : ℝ)/den
  | .add i j => values i+values j
  | .neg i => -values i
  | .mul i j => values i*values j
  | .inv i => (values i)⁻¹
  | .sqrt i => Real.sqrt (values i)

theorem eval_congr (op : Op) (inputs f g : ℕ → ℝ)
    (h : ∀ i ∈ op.refs, f i = g i) : op.eval inputs f = op.eval inputs g := by
  cases op <;> simp_all [eval, refs]

def Check (scale : ℤ) (inputs bounds : ℕ → ScaledInterval) (out : ScaledInterval) : Op → Prop
  | .input i => out = inputs i
  | .constant num den => ScaledInterval.ConstCheck scale num den out
  | .add i j => ScaledInterval.AddCheck (bounds i) (bounds j) out
  | .neg i => ScaledInterval.NegCheck (bounds i) out
  | .mul i j => ScaledInterval.MulCheck scale (bounds i) (bounds j) out
  | .inv i => ScaledInterval.InvCheck scale (bounds i) out
  | .sqrt i => ScaledInterval.SqrtCheck scale (bounds i) out

instance (scale : ℤ) (inputs bounds : ℕ → ScaledInterval) (out : ScaledInterval) (op : Op) :
    Decidable (Check scale inputs bounds out op) := by
  cases op <;> unfold Check <;> infer_instance

theorem check_sound {scale : ℤ} (hs : 0 < scale) {op : Op}
    {inputBounds bounds : ℕ → ScaledInterval} {inputs values : ℕ → ℝ} {out : ScaledInterval}
    (hinputs : ∀ i, ScaledInterval.Contains scale (inputBounds i) (inputs i))
    (hvalues : ∀ i ∈ op.refs, ScaledInterval.Contains scale (bounds i) (values i))
    (hcheck : op.Check scale inputBounds bounds out) :
    ScaledInterval.Contains scale out (op.eval inputs values) := by
  cases op with
  | input i =>
      change out = inputBounds i at hcheck
      subst out
      exact hinputs i
  | constant num den => exact ScaledInterval.const_sound hcheck
  | add i j =>
      exact ScaledInterval.add_sound (hvalues i (by simp [refs]))
        (hvalues j (by simp [refs])) hcheck
  | neg i => exact ScaledInterval.neg_sound (hvalues i (by simp [refs])) hcheck
  | mul i j =>
      exact ScaledInterval.mul_sound hs (hvalues i (by simp [refs]))
        (hvalues j (by simp [refs])) hcheck
  | inv i => exact ScaledInterval.inv_sound hs (hvalues i (by simp [refs])) hcheck
  | sqrt i => exact ScaledInterval.sqrt_sound hs (hvalues i (by simp [refs])) hcheck

end Op

structure Node where
  op : Op
  bound : ScaledInterval
  deriving DecidableEq, Repr

def Node.Check (scale : ℤ) (inputs : ℕ → ScaledInterval) (nodes : ℕ → Node) (i : ℕ) : Prop :=
  (nodes i).op.RefsBelow i ∧
    (nodes i).op.Check scale inputs (fun j => (nodes j).bound) (nodes i).bound

instance (scale : ℤ) (inputs : ℕ → ScaledInterval) (nodes : ℕ → Node) (i : ℕ) :
    Decidable (Node.Check scale inputs nodes i) := by
  unfold Node.Check
  infer_instance

/-- Total real semantics: invalid forward references evaluate as zero and are rejected by Check. -/
noncomputable def value (inputs : ℕ → ℝ) (nodes : ℕ → Node) (i : ℕ) : ℝ :=
  Nat.strongRecOn i fun j previous =>
    (nodes j).op.eval inputs (fun k => if h : k < j then previous k h else 0)

theorem value_unfold (inputs : ℕ → ℝ) (nodes : ℕ → Node) (i : ℕ) :
    value inputs nodes i = (nodes i).op.eval inputs
      (fun k => if k < i then value inputs nodes k else 0) := by
  unfold value
  exact Nat.strongRecOn_eq _ _

theorem value_eq (inputs : ℕ → ℝ) (nodes : ℕ → Node) (i : ℕ)
    (hbefore : (nodes i).op.RefsBelow i) :
    value inputs nodes i = (nodes i).op.eval inputs (value inputs nodes) := by
  rw [value_unfold]
  apply Op.eval_congr
  intro j hj
  simp only [if_pos (Op.refs_lt hbefore hj)]

/-- No semantic identities are assumed: this theorem applies to the recursively defined circuit. -/
theorem checks_sound {scale : ℤ} (hs : 0 < scale)
    (inputBounds : ℕ → ScaledInterval) (inputs : ℕ → ℝ) (nodes : ℕ → Node) (count : ℕ)
    (hinputs : ∀ i, ScaledInterval.Contains scale (inputBounds i) (inputs i))
    (hchecks : ∀ i, i < count → Node.Check scale inputBounds nodes i) :
    ∀ i, i < count → ScaledInterval.Contains scale (nodes i).bound (value inputs nodes i) := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
      intro hi
      rcases hchecks i hi with ⟨hbefore,hcheck⟩
      rw [value_eq inputs nodes i hbefore]
      apply Op.check_sound hs hinputs _ hcheck
      intro j hj
      have hji := Op.refs_lt hbefore hj
      exact ih j hji (hji.trans hi)

#print axioms Op.check_sound
#print axioms value_eq
#print axioms checks_sound

end ThomsonN10.Local.Certificates.IntervalCircuit
