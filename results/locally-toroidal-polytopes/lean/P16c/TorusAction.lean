import Mathlib
import P16c.Toroid
import P16c.TorusDefs

/-! # `[4,4]_(s,0)` acting on the vertices of `{4,4}_(s,0)`

The three reflections of the base flag (vertex `0`, edge `{0, (1,0)}`, square
`{0, (1,0), (0,1), (1,1)}`) satisfy the defining relations of
`[4,4]_(s,0)` (Coxeter–Moser §8.3), so they define `φ : Toroid.G s → Sym((ℤ/s)²)`.
`φ (x^a y^b)` is the translation by `(a, b)`, for `x = r0 r1 r2 r1`,
`y = r1 x r1`, and every element is `x^a y^b d` with `d` one of the eight
elements of `⟨r1, r2⟩`. -/

namespace P16c.Torus

open Toroid

variable (s : ℕ)

/-- `r0 : (x, y) ↦ (1 - x, y)`, moving only the base vertex. -/
def m0 : Equiv.Perm (TorusVertex s) :=
  Function.Involutive.toPerm (fun p => (1 - p.1, p.2)) fun p => by simp

/-- `r1 : (x, y) ↦ (y, x)`, moving only the base edge. -/
def m1 : Equiv.Perm (TorusVertex s) :=
  Function.Involutive.toPerm (fun p => (p.2, p.1)) fun _ => rfl

/-- `r2 : (x, y) ↦ (x, -y)`, moving only the base square. -/
def reflectY : Equiv.Perm (TorusVertex s) :=
  Function.Involutive.toPerm (fun p => (p.1, -p.2)) fun p => by simp

@[simp] lemma m0_apply (p : TorusVertex s) : m0 s p = (1 - p.1, p.2) := rfl
@[simp] lemma m1_apply (p : TorusVertex s) : m1 s p = (p.2, p.1) := rfl
@[simp] lemma m2_apply (p : TorusVertex s) : reflectY s p = (p.1, -p.2) := rfl

/-- The three generators. -/
def gen : Fin 3 → Equiv.Perm (TorusVertex s) := ![m0 s, m1 s, reflectY s]

lemma gen_trans_pow (n : ℕ) (p : TorusVertex s) :
    ((gen s 0 * gen s 1 * gen s 2 * gen s 1) ^ n) p = (p.1 + n, p.2) := by
  induction n generalizing p with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Equiv.Perm.mul_apply, ih]
    simp [gen]
    ring

/-- The action `φ : [4,4]_(s,0) → Sym((ℤ/s)²)`. -/
def phi : G s →* Equiv.Perm (TorusVertex s) :=
  toGroup s (gen s)
    (by intro i; ext p <;> fin_cases i <;> simp [gen, pow_two])
    (by ext p <;> simp [gen, pow_succ])
    (by ext p <;> simp [gen, pow_succ])
    (by ext p <;> simp [gen, pow_succ])
    (by ext p <;> simp [gen_trans_pow])

@[simp] lemma phi_r0 : phi s (r s 0) = m0 s := toGroup_r _ _ _ _ _ _ _ 0
@[simp] lemma phi_r1 : phi s (r s 1) = m1 s := toGroup_r _ _ _ _ _ _ _ 1
@[simp] lemma phi_r2 : phi s (r s 2) = reflectY s := toGroup_r _ _ _ _ _ _ _ 2

/-- The translation `x = r0 r1 r2 r1` and its conjugate `y = r1 x r1`. -/
def tx : G s := r s 0 * r s 1 * r s 2 * r s 1
def ty : G s := r s 1 * tx s * r s 1

lemma phi_tx_pow (n : ℕ) (p : TorusVertex s) : phi s (tx s ^ n) p = (p.1 + n, p.2) := by
  have : phi s (tx s) = gen s 0 * gen s 1 * gen s 2 * gen s 1 := by
    simp [tx, gen]
  rw [map_pow, this, gen_trans_pow]

lemma phi_ty_pow (n : ℕ) (p : TorusVertex s) : phi s (ty s ^ n) p = (p.1, p.2 + n) := by
  have : ty s ^ n = r s 1 * tx s ^ n * r s 1 := by
    have h : (r s 1)⁻¹ = r s 1 := by
      apply inv_eq_of_mul_eq_one_right; simpa [pow_two] using (relations s).1 1
    have e := conj_pow (a := r s 1) (b := tx s) (i := n)
    rw [h] at e
    rw [← e]; rfl
  rw [this, map_mul, map_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, phi_tx_pow]
  simp

/-- The translation element with vector `(a, b)`. -/
def tr (a b : ZMod s) : G s := tx s ^ a.val * ty s ^ b.val

lemma phi_tr [NeZero s] (a b : ZMod s) (p : TorusVertex s) :
    phi s (tr s a b) p = p + (a, b) := by
  simp only [tr, map_mul, Equiv.Perm.mul_apply, phi_ty_pow, phi_tx_pow, ZMod.natCast_val,
    ZMod.cast_id', id]
  rfl

/-- The dihedral subgroup `⟨r1, r2⟩`, the stabilizer of the base vertex. -/
def D : Subgroup (G s) := Subgroup.closure {r s 1, r s 2}

lemma r_mul_self (i : Fin 3) : r s i * r s i = 1 := by
  simpa [pow_two] using (relations s).1 i

lemma braid12 : r s 1 * r s 2 * r s 1 * r s 2 = r s 2 * r s 1 * r s 2 * r s 1 :=
  braid_four (r_mul_self s 1) (r_mul_self s 2) (relations s).2.2.1

/-- The eight elements of `⟨r1, r2⟩`. -/
lemma D_cases {d : G s} (hd : d ∈ D s) :
    d = 1 ∨ d = r s 1 ∨ d = r s 2 ∨ d = r s 1 * r s 2 ∨ d = r s 2 * r s 1 ∨
      d = r s 1 * r s 2 * r s 1 ∨ d = r s 2 * r s 1 * r s 2 ∨
      d = r s 1 * r s 2 * r s 1 * r s 2 := by
  have h1 := r_mul_self s 1
  have h2 := r_mul_self s 2
  have hb := braid12 s
  have step : ∀ x y : G s, y ∈ ({r s 1, r s 2} : Set (G s)) →
      (x = 1 ∨ x = r s 1 ∨ x = r s 2 ∨ x = r s 1 * r s 2 ∨ x = r s 2 * r s 1 ∨
        x = r s 1 * r s 2 * r s 1 ∨ x = r s 2 * r s 1 * r s 2 ∨
        x = r s 1 * r s 2 * r s 1 * r s 2) →
      (x * y = 1 ∨ x * y = r s 1 ∨ x * y = r s 2 ∨ x * y = r s 1 * r s 2 ∨
        x * y = r s 2 * r s 1 ∨ x * y = r s 1 * r s 2 * r s 1 ∨
        x * y = r s 2 * r s 1 * r s 2 ∨ x * y = r s 1 * r s 2 * r s 1 * r s 2) := by
    intro x y hy hx
    rcases hy with rfl | hy
    · rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · simp
      · simp [h1]
      · simp
      · simp
      · simp [mul_assoc, h1]
      · simp [mul_assoc, h1]
      · right; right; right; right; right; right; right
        rw [hb]
      · right; right; right; right; right; right; left
        rw [hb]; simp [mul_assoc, h1]
    · rw [Set.mem_singleton_iff] at hy; subst hy
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · simp
      · simp
      · simp [h2]
      · simp [mul_assoc, h2]
      · simp
      · simp
      · simp [mul_assoc, h2]
      · simp [mul_assoc, h2]
  induction hd using Subgroup.closure_induction_right with
  | one => simp
  | mul_right x _ y hy ih => exact step x y hy ih
  | mul_inv_cancel x _ y hy ih =>
    have hi : y⁻¹ = y := by
      rcases hy with rfl | hy
      · exact inv_eq_of_mul_eq_one_right h1
      · rw [Set.mem_singleton_iff] at hy; subst hy; exact inv_eq_of_mul_eq_one_right h2
    rw [hi]; exact step x y hy ih

/-- Every element is `x^a y^b d` with `d ∈ ⟨r1, r2⟩` (the proof of the `8s²` bound). -/
lemma normal_form [NeZero s] (g : G s) : ∃ a b : ZMod s, ∃ d ∈ D s, g = tr s a b * d := by
  let a := r s 0
  let b := r s 1
  let c := r s 2
  let x := tx s
  let y := ty s
  let N := Subgroup.closure ({x, y} : Set (G s))
  obtain ⟨hi, hab, hbc, hac, hx⟩ := relations s
  have ha : a * a = 1 := by simpa [a, pow_two] using hi 0
  have hb : b * b = 1 := by simpa [b, pow_two] using hi 1
  have hc : c * c = 1 := by simpa [c, pow_two] using hi 2
  obtain ⟨hxy, hby, hcx, hcy⟩ := translation_identities ha hb hc hab hbc hac
  change Commute x y at hxy
  change b * y * b = x at hby
  change c * x * c = x at hcx
  change c * y * c = y⁻¹ at hcy
  have hn : D s ≤ Subgroup.normalizer N := by
    apply (Subgroup.closure_le _).mpr
    intro z hz
    rcases Set.mem_insert_iff.mp hz with rfl | hz
    · apply involution_normalizes_closure b hb
      intro z hz
      rcases Set.mem_insert_iff.mp hz with rfl | hz
      · exact Subgroup.subset_closure (by simp only [← show y = b * x * b from rfl]; simp)
      · have hz' : z = y := Set.mem_singleton_iff.mp hz
        subst z
        rw [hby]
        exact Subgroup.subset_closure (by simp)
    · have hz' : z = c := Set.mem_singleton_iff.mp hz
      subst z
      apply involution_normalizes_closure c hc
      intro z hz
      rcases Set.mem_insert_iff.mp hz with rfl | hz
      · rw [hcx]; exact Subgroup.subset_closure (by simp)
      · have hz' : z = y := Set.mem_singleton_iff.mp hz
        subst z
        rw [hcy]
        exact N.inv_mem (Subgroup.subset_closure (by simp))
  have ht : N ⊔ D s = ⊤ := by
    apply top_unique
    intro z _
    apply PresentedGroup.generated_by (rels s) (N ⊔ D s) _ z
    intro i
    fin_cases i
    · change a ∈ N ⊔ D s
      have he : a = x * b * c * b := by
        simp [x, tx, a, b, c, mul_assoc, hb, hc]
      rw [he]
      have hxb : x ∈ N ⊔ D s := Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
      have hbb : b ∈ N ⊔ D s := Subgroup.mem_sup_right (Subgroup.subset_closure (by simp [b]))
      have hcc : c ∈ N ⊔ D s := Subgroup.mem_sup_right (Subgroup.subset_closure (by simp [c]))
      exact (N ⊔ D s).mul_mem ((N ⊔ D s).mul_mem ((N ⊔ D s).mul_mem hxb hbb) hcc) hbb
    · exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp [r]))
    · exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp [r]))
  have hg : g ∈ ((N ⊔ D s : Subgroup (G s)) : Set (G s)) := by rw [ht]; trivial
  rw [Subgroup.coe_mul_of_right_le_normalizer_left N (D s) hn] at hg
  obtain ⟨t, htN, d, hd, rfl⟩ := hg
  -- `t ∈ ⟨x, y⟩` with `x, y` commuting: `t = x^i y^j`.
  have hnorm : Subgroup.zpowers y ≤ Subgroup.normalizer (Subgroup.zpowers x) := by
    rw [Subgroup.le_normalizer_iff]
    intro q hq z hz
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hq
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hcomm := hxy.symm.zpow_zpow i j
    simp [hcomm.eq, mul_assoc]
  have he : Subgroup.zpowers x ⊔ Subgroup.zpowers y = N := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure, ← Subgroup.closure_union]
    congr 1
  have htN' : t ∈ ((Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup (G s)) : Set (G s)) := by
    rw [he]; exact htN
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hnorm] at htN'
  obtain ⟨p, hp, q, hq, rfl⟩ := htN'
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hq
  have hx' : tx s ^ s = 1 := hx
  have hy : ty s ^ s = 1 := by
    have e : ty s = b * x * b⁻¹ := by simp [ty, x, b, inv_eq_of_mul_eq_one_right hb]
    rw [e, conj_pow, show x ^ s = 1 from hx']
    simp
  refine ⟨(i : ZMod s), (j : ZMod s), d, hd, ?_⟩
  have cast : ∀ k : ℤ, (((k : ZMod s).val : ℕ) : ℤ) = k % (s : ℤ) := fun k => ZMod.val_intCast k
  show tx s ^ i * ty s ^ j * d = tx s ^ (i : ZMod s).val * ty s ^ (j : ZMod s).val * d
  rw [zpow_eq_zpow_emod' i hx', zpow_eq_zpow_emod' j hy, ← cast i, ← cast j, zpow_natCast,
    zpow_natCast]

end P16c.Torus
