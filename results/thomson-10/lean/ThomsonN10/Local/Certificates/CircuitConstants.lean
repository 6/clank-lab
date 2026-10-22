/- Adapted from proof/lean/ThomsonN9/Certificates/CircuitConstants.lean,
 aravindkarthigeyan/thomson-n9-lean @ 168ff0c98cab4dfda0460ba55f8d169070ac385e (MIT). -/
import ThomsonN10.Local.Certificates.CircuitAlgebra

/-! Explicitly checked rational constant folding in circuit recipes. -/

namespace ThomsonN10.Local.Certificates.IntervalCircuit

open scoped BigOperators

def constantNum : Op → ℤ | .constant n _ => n | _ => 0
def constantDen : Op → ℤ | .constant _ d => d | _ => 0

def ConstantAddCheck (nodes : ℕ → Node) (a b out : ℕ) : Prop :=
  let an := constantNum (nodes a).op
  let ad := constantDen (nodes a).op
  let bn := constantNum (nodes b).op
  let bd := constantDen (nodes b).op
  let cn := constantNum (nodes out).op
  let cd := constantDen (nodes out).op
  (nodes a).op = .constant an ad ∧ (nodes b).op = .constant bn bd ∧
    (nodes out).op = .constant cn cd ∧ 0 < ad ∧ 0 < bd ∧ 0 < cd ∧
      cn*ad*bd = (an*bd+bn*ad)*cd

def ConstantMulCheck (nodes : ℕ → Node) (a b out : ℕ) : Prop :=
  let an := constantNum (nodes a).op
  let ad := constantDen (nodes a).op
  let bn := constantNum (nodes b).op
  let bd := constantDen (nodes b).op
  let cn := constantNum (nodes out).op
  let cd := constantDen (nodes out).op
  (nodes a).op = .constant an ad ∧ (nodes b).op = .constant bn bd ∧
    (nodes out).op = .constant cn cd ∧ 0 < ad ∧ 0 < bd ∧ 0 < cd ∧
      cn*ad*bd = an*bn*cd

instance (nodes : ℕ → Node) (a b out : ℕ) : Decidable (ConstantAddCheck nodes a b out) := by
  unfold ConstantAddCheck
  infer_instance

instance (nodes : ℕ → Node) (a b out : ℕ) : Decidable (ConstantMulCheck nodes a b out) := by
  unfold ConstantMulCheck
  infer_instance

theorem fraction_add_of_cross (an ad bn bd cn cd : ℤ)
    (ha : 0 < ad) (hb : 0 < bd) (hc : 0 < cd)
    (h : cn*ad*bd = (an*bd+bn*ad)*cd) :
    (cn : ℝ)/cd = (an : ℝ)/ad+(bn : ℝ)/bd := by
  have ha' : (ad : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast ha)
  have hb' : (bd : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hb)
  have hc' : (cd : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hc)
  have h' : (cn : ℝ)*ad*bd = ((an : ℝ)*bd+(bn : ℝ)*ad)*cd := by exact_mod_cast h
  field_simp [ha',hb',hc']
  nlinarith

theorem fraction_mul_of_cross (an ad bn bd cn cd : ℤ)
    (ha : 0 < ad) (hb : 0 < bd) (hc : 0 < cd)
    (h : cn*ad*bd = an*bn*cd) :
    (cn : ℝ)/cd = ((an : ℝ)/ad)*((bn : ℝ)/bd) := by
  have ha' : (ad : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast ha)
  have hb' : (bd : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hb)
  have hc' : (cd : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hc)
  have h' : (cn : ℝ)*ad*bd = (an : ℝ)*bn*cd := by exact_mod_cast h
  field_simp [ha',hb',hc']
  nlinarith

theorem constantAdd_sound (inputs : ℕ → ℝ) (nodes : ℕ → Node) (a b out : ℕ)
    (h : ConstantAddCheck nodes a b out) :
    value inputs nodes out = value inputs nodes a+value inputs nodes b := by
  rcases h with ⟨ha,hb,hc,hda,hdb,hdc,hcross⟩
  rw [value_constant inputs nodes out _ _ hc,
    value_constant inputs nodes a _ _ ha, value_constant inputs nodes b _ _ hb]
  exact fraction_add_of_cross _ _ _ _ _ _ hda hdb hdc hcross

theorem constantMul_sound (inputs : ℕ → ℝ) (nodes : ℕ → Node) (a b out : ℕ)
    (h : ConstantMulCheck nodes a b out) :
    value inputs nodes out = value inputs nodes a*value inputs nodes b := by
  rcases h with ⟨ha,hb,hc,hda,hdb,hdc,hcross⟩
  rw [value_constant inputs nodes out _ _ hc,
    value_constant inputs nodes a _ _ ha, value_constant inputs nodes b _ _ hb]
  exact fraction_mul_of_cross _ _ _ _ _ _ hda hdb hdc hcross

def ExtendedSmartAddCheck (nodes : ℕ → Node) (a b out : ℕ) : Prop :=
  SmartAddCheck nodes a b out ∨ ConstantAddCheck nodes a b out

def ExtendedSmartMulCheck (nodes : ℕ → Node) (a b out : ℕ) : Prop :=
  SmartMulCheck nodes a b out ∨ ConstantMulCheck nodes a b out

instance (nodes : ℕ → Node) (a b out : ℕ) : Decidable (ExtendedSmartAddCheck nodes a b out) := by
  unfold ExtendedSmartAddCheck
  infer_instance

instance (nodes : ℕ → Node) (a b out : ℕ) : Decidable (ExtendedSmartMulCheck nodes a b out) := by
  unfold ExtendedSmartMulCheck
  infer_instance

theorem extendedSmartAdd_sound (inputs : ℕ → ℝ) (nodes : ℕ → Node) (a b out : ℕ)
    (h : ExtendedSmartAddCheck nodes a b out) :
    value inputs nodes out = value inputs nodes a+value inputs nodes b := by
  rcases h with h | h
  · exact smartAdd_sound inputs nodes a b out h
  · exact constantAdd_sound inputs nodes a b out h

theorem extendedSmartMul_sound (inputs : ℕ → ℝ) (nodes : ℕ → Node) (a b out : ℕ)
    (h : ExtendedSmartMulCheck nodes a b out) :
    value inputs nodes out = value inputs nodes a*value inputs nodes b := by
  rcases h with h | h
  · exact smartMul_sound inputs nodes a b out h
  · exact constantMul_sound inputs nodes a b out h

def DotRecipe.ExtendedCheck (nodes : ℕ → Node) (n : ℕ) (recipe : DotRecipe) : Prop :=
  ZeroAt nodes (recipe.accumulator 0) ∧
    ∀ k : Fin n,
      ExtendedSmartMulCheck nodes (recipe.left k) (recipe.right k) (recipe.product k) ∧
      ExtendedSmartAddCheck nodes (recipe.accumulator k) (recipe.product k)
        (recipe.accumulator (k.val+1))

instance (nodes : ℕ → Node) (n : ℕ) (recipe : DotRecipe) :
    Decidable (recipe.ExtendedCheck nodes n) := by
  unfold DotRecipe.ExtendedCheck ZeroAt
  infer_instance

theorem DotRecipe.extended_sound (inputs : ℕ → ℝ) (nodes : ℕ → Node) (n : ℕ)
    (recipe : DotRecipe) (h : recipe.ExtendedCheck nodes n) :
    value inputs nodes (recipe.accumulator n) =
      ∑ k ∈ Finset.range n, value inputs nodes (recipe.left k) *
        value inputs nodes (recipe.right k) := by
  have hprefix : ∀ k, k ≤ n → value inputs nodes (recipe.accumulator k) =
      ∑ j ∈ Finset.range k, value inputs nodes (recipe.left j) *
        value inputs nodes (recipe.right j) := by
    intro k
    induction k with
    | zero =>
        intro _
        simpa using zeroAt_sound inputs nodes (recipe.accumulator 0) h.1
    | succ k ih =>
        intro hkn
        obtain ⟨hm,ha⟩ := h.2 ⟨k,by omega⟩
        rw [extendedSmartAdd_sound inputs nodes _ _ _ ha,
          extendedSmartMul_sound inputs nodes _ _ _ hm, ih (by omega), Finset.sum_range_succ]
  exact hprefix n le_rfl

#print axioms constantAdd_sound
#print axioms constantMul_sound
#print axioms DotRecipe.extended_sound

end ThomsonN10.Local.Certificates.IntervalCircuit
