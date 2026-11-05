import CK18HJ.Statement
import CK18HJ.Parabola
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Lemma 1 of the paper and Theorem 1

Along a line, `S(w(t)) = C + A t² - 2 s t` with `1 ≤ A ≤ 2 runs w` and
`0 ≤ s ≤ A(m-1)`; then `parabola` gives two letters of different colours.
-/

namespace CK18HJ

variable {m n : ℕ}

/-- The root's entry at `i` as an integer (`none` = wildcard). -/
def ew (w : Fin n → Option (Fin m)) (i : Fin n) : Option ℤ :=
  (w i).map fun c => (c.val : ℤ)

/-- The root's entry before `i`, the letter `0` before the first position. -/
def ep (w : Fin n → Option (Fin m)) (i : Fin n) : Option ℤ :=
  if h : i.val = 0 then some 0 else ew w ⟨i.val - 1, by have := i.isLt; omega⟩

/-- Coefficients of `(o(T) - p(T))²` as `c + a T² - 2 b T`. -/
def coefA : Option ℤ → Option ℤ → ℤ
  | none, some _ => 1
  | some _, none => 1
  | _, _ => 0

def coefB : Option ℤ → Option ℤ → ℤ
  | none, some p => p
  | some c, none => c
  | _, _ => 0

def coefC : Option ℤ → Option ℤ → ℤ
  | some c, some p => (c - p) ^ 2
  | none, some p => p ^ 2
  | some c, none => c ^ 2
  | none, none => 0

/-- `1` at a wildcard. -/
def isW (o : Option ℤ) : ℤ := if o = none then 1 else 0

theorem term_eq (o p : Option ℤ) (T : ℤ) :
    (o.getD T - p.getD T) ^ 2 = coefC o p + coefA o p * T ^ 2 - 2 * coefB o p * T := by
  cases o <;> cases p <;> simp [coefA, coefB, coefC] <;> ring

theorem coefB_bounds (o p : Option ℤ) (M : ℤ) (ho : ∀ c, o = some c → 0 ≤ c ∧ c ≤ M)
    (hp : ∀ c, p = some c → 0 ≤ c ∧ c ≤ M) :
    0 ≤ coefB o p ∧ coefB o p ≤ coefA o p * M := by
  cases o <;> cases p <;> simp_all [coefA, coefB]

theorem coefA_eq (o p : Option ℤ) :
    coefA o p = 2 * (if o = none ∧ p ≠ none then 1 else 0) - (isW o - isW p) := by
  cases o <;> cases p <;> simp [coefA, isW]

theorem coefA_nonneg (o p : Option ℤ) : 0 ≤ coefA o p := by
  cases o <;> cases p <;> simp [coefA]

theorem isW_nonneg (o : Option ℤ) : 0 ≤ isW o := by
  unfold isW; split_ifs <;> norm_num

theorem point_val (w : Fin n → Option (Fin m)) (t : Fin m) (i : Fin n) :
    ((point w t i).val : ℤ) = (ew w i).getD (t.val : ℤ) := by
  unfold point ew; cases w i <;> rfl

theorem prev_point (w : Fin n → Option (Fin m)) (t : Fin m) (i : Fin n) :
    prev (point w t) i = (ep w i).getD (t.val : ℤ) := by
  unfold prev ep
  split_ifs
  · rfl
  · exact point_val w t _

theorem S_point (w : Fin n → Option (Fin m)) (t : Fin m) :
    S (point w t) = ∑ i, coefC (ew w i) (ep w i) + (∑ i, coefA (ew w i) (ep w i)) * (t.val : ℤ) ^ 2
      - 2 * (∑ i, coefB (ew w i) (ep w i)) * (t.val : ℤ) := by
  unfold S
  simp only [point_val, prev_point, term_eq, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_mul, Finset.mul_sum]

theorem ew_bound (w : Fin n → Option (Fin m)) (i : Fin n) :
    ∀ c, ew w i = some c → 0 ≤ c ∧ c ≤ (m : ℤ) - 1 := by
  intro c h
  unfold ew at h
  cases hw : w i with
  | none => simp [hw] at h
  | some x =>
    simp [hw] at h
    have := x.isLt
    omega

theorem ep_bound (w : Fin n → Option (Fin m)) (hm : 1 ≤ m) (i : Fin n) :
    ∀ c, ep w i = some c → 0 ≤ c ∧ c ≤ (m : ℤ) - 1 := by
  intro c h
  unfold ep at h
  split_ifs at h
  · simp at h; omega
  · exact ew_bound w _ c h

theorem runStart_iff (w : Fin n → Option (Fin m)) (i : Fin n) :
    RunStart w i ↔ ew w i = none ∧ ep w i ≠ none := by
  unfold RunStart ep
  have e : ∀ j, ew w j = none ↔ w j = none := fun j => by simp [ew]
  rw [e]
  split_ifs with h
  · simp [h]
  · simp only [h, false_or, ne_eq, e]
    constructor
    · rintro ⟨hi, j, hj, hwj⟩
      refine ⟨hi, ?_⟩
      have : j = ⟨i.val - 1, by have := i.isLt; omega⟩ := Fin.ext (by simp; omega)
      rw [← this]; exact hwj
    · rintro ⟨hi, hwj⟩
      exact ⟨hi, ⟨i.val - 1, by have := i.isLt; omega⟩, by simp; omega, hwj⟩

/-- `Σ (isW (w i) - isW (w (i-1)))` telescopes to `isW (w (n-1)) ≥ 0`. -/
theorem telescope_nonneg (w : Fin n → Option (Fin m)) :
    0 ≤ ∑ i, (isW (ew w i) - isW (ep w i)) := by
  let g : ℕ → ℤ := fun k => if h : k < n then isW (ew w ⟨k, h⟩) else 0
  let H : ℕ → ℤ := fun k => match k with
    | 0 => 0
    | k + 1 => g k
  have hH : ∀ i : Fin n, isW (ew w i) - isW (ep w i) = H (i.val + 1) - H i.val := by
    rintro ⟨k, hk⟩
    cases k with
    | zero => simp [H, g, ep, isW, hk]
    | succ k => simp [H, g, ep, hk, show k < n by omega]
  rw [Finset.sum_congr rfl (fun i _ => hH i),
    Fin.sum_univ_eq_sum_range (fun k => H (k + 1) - H k) n, Finset.sum_range_sub]
  cases n with
  | zero => simp [H]
  | succ k => simp only [H, g]; split_ifs <;> simp [isW_nonneg]

/-- `A ≤ 2 runs`. -/
theorem sumA_le (w : Fin n → Option (Fin m)) :
    ∑ i, coefA (ew w i) (ep w i) ≤ 2 * (runs w : ℤ) := by
  have hr : (runs w : ℤ) = ∑ i, (if ew w i = none ∧ ep w i ≠ none then (1 : ℤ) else 0) := by
    unfold runs
    rw [Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [runStart_iff]
  rw [Finset.sum_congr rfl (fun i _ => coefA_eq _ _), Finset.sum_sub_distrib, ← Finset.mul_sum, hr]
  linarith [telescope_nonneg w]

/-- `A ≥ 1`: the first wildcard starts a run. -/
theorem one_le_sumA (w : Fin n → Option (Fin m)) (hw : ∃ i, w i = none) :
    1 ≤ ∑ i, coefA (ew w i) (ep w i) := by
  classical
  have hne : (Finset.univ.filter fun i => w i = none).Nonempty := by
    obtain ⟨i, hi⟩ := hw; exact ⟨i, by simp [hi]⟩
  set i₀ := (Finset.univ.filter fun i => w i = none).min' hne with hi₀
  have h0 : w i₀ = none := by
    have := Finset.min'_mem _ hne
    rw [← hi₀] at this; simpa using this
  have hmin : ∀ j, w j = none → i₀ ≤ j := fun j hj =>
    Finset.min'_le _ _ (by simp [hj])
  have hA : coefA (ew w i₀) (ep w i₀) = 1 := by
    have e0 : ew w i₀ = none := by simp [ew, h0]
    rw [e0]
    unfold ep
    split_ifs with h
    · rfl
    · cases hp : w ⟨i₀.val - 1, by have := i₀.isLt; omega⟩ with
      | none =>
        have := hmin _ hp
        rw [Fin.le_def] at this; simp at this; omega
      | some c => simp [ew, hp, coefA]
  rw [← hA]
  exact Finset.single_le_sum (f := fun i => coefA (ew w i) (ep w i))
    (fun i _ => coefA_nonneg _ _) (Finset.mem_univ i₀)

theorem main : MainStatement := by
  intro Q K m n hQ hK hm w hw hruns
  have hm1 : 1 ≤ m := by omega
  set A := ∑ i, coefA (ew w i) (ep w i)
  set s := ∑ i, coefB (ew w i) (ep w i)
  set C := ∑ i, coefC (ew w i) (ep w i)
  have hA1 : 1 ≤ A := one_le_sumA w hw
  have hA2 : A ≤ 2 * (Q : ℤ) := by
    have := sumA_le w
    have : (runs w : ℤ) ≤ Q := by exact_mod_cast hruns
    linarith
  have hs0 : 0 ≤ s := Finset.sum_nonneg fun i _ =>
    (coefB_bounds _ _ _ (ew_bound w i) (ep_bound w hm1 i)).1
  have hs : s ≤ A * ((m : ℤ) - 1) := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun i _ => (coefB_bounds _ _ _ (ew_bound w i) (ep_bound w hm1 i)).2
  obtain ⟨t, u, ht0, ht1, hu0, hu1, hc⟩ :=
    parabola (Q : ℤ) (m : ℤ) A s C K (by exact_mod_cast hQ) (by exact_mod_cast hK)
      (by exact_mod_cast hm) hA1 hA2 hs0 hs
  refine ⟨⟨t.toNat, by omega⟩, ⟨u.toNat, by omega⟩, ?_⟩
  have eS : ∀ x : Fin m, S (point w x) = C + A * (x.val : ℤ) ^ 2 - 2 * s * x.val :=
    fun x => S_point w x
  unfold colour
  rw [eS, eS]
  simp only [Int.toNat_of_nonneg ht0, Int.toNat_of_nonneg hu0]
  push_cast
  simp only [ne_eq, decide_eq_decide]
  tauto

theorem unbounded : UnboundedStatement := by
  intro Q
  refine ⟨2 * (32 * (Q + 1)) + 2, fun n => ⟨colour (32 * (Q + 1)), fun w hw hr => ?_⟩⟩
  exact main (Q + 1) (32 * (Q + 1)) _ n (by omega) (by nlinarith) le_rfl w hw (by omega)

end CK18HJ
