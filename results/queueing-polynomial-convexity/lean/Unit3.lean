import BLSRestricted
import H

noncomputable section
open scoped BigOperators
open Set
namespace BLSUnit3
open BLSUnit1 BLSUnit2

/-- The only outstanding hypothesis for the conditional full endpoint. -/
def HConvexity : Prop := ∀ (m d : ℕ),
  ConvexOn ℝ {w : Fin m → ℝ | ∀ i, 0 ≤ w i}
    (fun w => BLSH.complete (List.ofFn w) d)

/-- All original global coordinates are retained, including edges outside S. -/
def normalizedRate {n L : ℕ} (S : Finset (Fin n)) (x : Edge n L → ℝ) : ℝ :=
  rate n L S x / (S.card : ℝ)

/-- Finite averaging over vertex-deletion paths. Fuel at least card S reaches []. -/
def average {n : ℕ} : ℕ → Finset (Fin n) → (List (Finset (Fin n)) → ℝ) → ℝ
  | 0, _, F => F []
  | m+1, S, F => if S = ∅ then F [] else
      (S.card : ℝ)⁻¹ * ∑ v ∈ S, average m (S.erase v) (fun p => F (S::p))

theorem geometric_unroll (a : ℝ) (f b : ℕ → ℝ) (h0 : f 0 = b 0)
    (hs : ∀ d, f (d+1) = a * f d + b (d+1)) (d : ℕ) :
    f d = ∑ k ∈ Finset.range (d+1), a^k * b (d-k) := by
  induction d with
  | zero => simpa using h0
  | succ d ih =>
    rw [hs, ih]
    conv_rhs => rw [Finset.sum_range_succ']
    simp only [pow_zero, one_mul, Nat.sub_zero, Nat.add_sub_add_right, pow_succ']
    rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    ring

theorem normalized_recurrence {n L : ℕ} (hL : 1 ≤ L)
    (S : Finset (Fin n)) (hS : S.Nonempty) (x : Edge n L → ℝ) (d : ℕ) :
    restricted n L (d+1) S x = normalizedRate S x * restricted n L d S x +
      (S.card : ℝ)⁻¹ * ∑ v ∈ S, restricted n L (d+1) (S.erase v) x := by
  have hc : (S.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr hS)
  apply (mul_left_cancel₀ hc)
  rw [deletion_recurrence_succ hL]
  dsimp [normalizedRate]
  field_simp

theorem restricted_unroll {n L : ℕ} (hL : 1 ≤ L)
    (S : Finset (Fin n)) (hS : S.Nonempty) (x : Edge n L → ℝ) (d : ℕ) :
    restricted n L d S x = (S.card : ℝ)⁻¹ *
      ∑ v ∈ S, ∑ k ∈ Finset.range (d+1),
        normalizedRate S x ^ k * restricted n L (d-k) (S.erase v) x := by
  have hc : (S.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr hS)
  have h0 : restricted n L 0 S x =
      (S.card : ℝ)⁻¹ * ∑ v ∈ S, restricted n L 0 (S.erase v) x := by
    simp [restricted_zero, hc]
  rw [geometric_unroll (normalizedRate S x) (fun d => restricted n L d S x)
    (fun d => (S.card : ℝ)⁻¹ * ∑ v ∈ S, restricted n L d (S.erase v) x)
    h0 (normalized_recurrence hL S hS x) d]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem average_mul {n : ℕ} (m : ℕ) (S : Finset (Fin n)) (c : ℝ)
    (F : List (Finset (Fin n)) → ℝ) :
    average m S (fun p => c * F p) = c * average m S F := by
  induction m generalizing S F with
  | zero => rfl
  | succ m ih =>
    simp only [average]
    split_ifs with h
    · rfl
    · simp_rw [ih, ← Finset.mul_sum]
      ring

theorem average_sum {n : ℕ} {ι : Type*} (m : ℕ) (S : Finset (Fin n))
    (K : Finset ι) (F : ι → List (Finset (Fin n)) → ℝ) :
    average m S (fun p => ∑ k ∈ K, F k p) = ∑ k ∈ K, average m S (F k) := by
  induction m generalizing S F with
  | zero => rfl
  | succ m ih =>
    simp only [average]
    split_ifs with h
    · rfl
    · simp_rw [ih]
      rw [Finset.sum_comm, Finset.mul_sum]

theorem average_one {n : ℕ} (m : ℕ) (S : Finset (Fin n)) :
    average m S (fun _ => 1) = 1 := by
  induction m generalizing S with
  | zero => rfl
  | succ m ih =>
    simp only [average]
    split_ifs with h
    · rfl
    · have hc : (S.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr
        (Finset.nonempty_iff_ne_empty.mpr h))
      simp [ih, hc]

theorem representation {n L : ℕ} (hL : 1 ≤ L) (m : ℕ)
    (S : Finset (Fin n)) (hSm : S.card ≤ m) (x : Edge n L → ℝ) (d : ℕ) :
    restricted n L d S x = average m S
      (fun p => BLSH.complete (p.map (fun T => normalizedRate T x)) d) := by
  induction m generalizing S d with
  | zero =>
    have hS : S = ∅ := Finset.card_eq_zero.mp (by omega)
    subst S
    cases d with
    | zero => simp [restricted_zero, average, BLSH.complete]
    | succ d => simp [empty_positive hL (by omega : 1 ≤ d+1), average, BLSH.complete]
  | succ m ih =>
    by_cases hS : S = ∅
    · subst S
      cases d with
      | zero => simp [restricted_zero, average, BLSH.complete]
      | succ d => simp [empty_positive hL (by omega : 1 ≤ d+1), average, BLSH.complete]
    · rw [restricted_unroll hL S (Finset.nonempty_iff_ne_empty.mpr hS) x d]
      simp only [average, hS, ↓reduceIte, List.map_cons, BLSH.complete]
      congr 1
      apply Finset.sum_congr rfl
      intro v hv
      rw [average_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [average_mul, ← ih]
      rw [Finset.card_erase_of_mem hv]
      omega

theorem average_mono {n : ℕ} (m : ℕ) (S : Finset (Fin n))
    (F G : List (Finset (Fin n)) → ℝ) (h : ∀ p, F p ≤ G p) :
    average m S F ≤ average m S G := by
  induction m generalizing S F G with
  | zero => exact h []
  | succ m ih =>
    simp only [average]
    split_ifs with hS
    · exact h []
    · apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
      apply Finset.sum_le_sum
      intro v hv
      exact ih _ _ _ (fun p => h (S::p))

theorem average_add {n : ℕ} (m : ℕ) (S : Finset (Fin n))
    (F G : List (Finset (Fin n)) → ℝ) :
    average m S (fun p => F p + G p) = average m S F + average m S G := by
  induction m generalizing S F G with
  | zero => rfl
  | succ m ih =>
    simp only [average]
    split_ifs with h
    · rfl
    · simp_rw [ih, Finset.sum_add_distrib, mul_add]

theorem normalizedRate_combo {n L : ℕ} (S : Finset (Fin n))
    (x y : Edge n L → ℝ) (a b : ℝ) :
    normalizedRate S (a • x + b • y) = a * normalizedRate S x + b * normalizedRate S y := by
  unfold normalizedRate rate
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have h : (∑ e : Edge n L, if e.val ⊆ S then a * x e + b * y e else 0) =
      a * (∑ e : Edge n L, if e.val ⊆ S then x e else 0) +
      b * (∑ e : Edge n L, if e.val ⊆ S then y e else 0) := by
    simp_rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e he
    split_ifs <;> ring
  rw [h]
  ring

theorem normalizedRate_nonneg {n L : ℕ} (S : Finset (Fin n))
    (x : Edge n L → ℝ) (hx : ∀ e, 0 ≤ x e) : 0 ≤ normalizedRate S x := by
  apply div_nonneg _ (Nat.cast_nonneg _)
  apply Finset.sum_nonneg
  intro e he
  split_ifs
  · exact hx e
  · exact le_rfl

theorem orthant_convex (ι : Type*) : Convex ℝ {x : ι → ℝ | ∀ i, 0 ≤ x i} := by
  intro x hx y hy a b ha hb hab i
  exact add_nonneg (mul_nonneg ha (hx i)) (mul_nonneg hb (hy i))

theorem path_convex (hH : HConvexity) {n L : ℕ}
    (p : List (Finset (Fin n))) (d : ℕ) :
    ConvexOn ℝ {x : Edge n L → ℝ | ∀ e, 0 ≤ x e}
      (fun x => BLSH.complete (p.map (fun T => normalizedRate T x)) d) := by
  refine ⟨orthant_convex _, ?_⟩
  intro x hx y hy a b ha hb hab
  let wx : Fin p.length → ℝ := fun i => normalizedRate p[i.val] x
  let wy : Fin p.length → ℝ := fun i => normalizedRate p[i.val] y
  have hwx : ∀ i, 0 ≤ wx i := fun i => normalizedRate_nonneg _ x hx
  have hwy : ∀ i, 0 ≤ wy i := fun i => normalizedRate_nonneg _ y hy
  have hh := (hH p.length d).2 hwx hwy ha hb hab
  have hc : a • wx + b • wy =
      (fun i : Fin p.length => normalizedRate p[i.val] (a • x + b • y)) := by
    funext i
    exact (normalizedRate_combo _ x y a b).symm
  rw [hc] at hh
  dsimp [wx, wy] at hh
  rw [List.ofFn_getElem_eq_map p (fun T => normalizedRate (L := L) T (a • x + b • y)),
    List.ofFn_getElem_eq_map p (fun T => normalizedRate (L := L) T x),
    List.ofFn_getElem_eq_map p (fun T => normalizedRate (L := L) T y)] at hh
  exact hh

theorem average_convex {n L : ℕ} (m : ℕ) (S : Finset (Fin n))
    (F : List (Finset (Fin n)) → (Edge n L → ℝ) → ℝ)
    (hF : ∀ p, ConvexOn ℝ {x : Edge n L → ℝ | ∀ e, 0 ≤ x e} (F p)) :
    ConvexOn ℝ {x : Edge n L → ℝ | ∀ e, 0 ≤ x e}
      (fun x => average m S (fun p => F p x)) := by
  refine ⟨orthant_convex _, ?_⟩
  intro x hx y hy a b ha hb hab
  calc
    average m S (fun p => F p (a • x + b • y)) ≤
        average m S (fun p => a * F p x + b * F p y) :=
      average_mono m S _ _ (fun p => (hF p).2 hx hy ha hb hab)
    _ = a • average m S (fun p => F p x) + b • average m S (fun p => F p y) := by
      rw [average_add, average_mul, average_mul]
      rfl

theorem conditional_restricted_convex (hH : HConvexity) {n L : ℕ} (hL : 1 ≤ L)
    (S : Finset (Fin n)) (d : ℕ) :
    ConvexOn ℝ {x : Edge n L → ℝ | ∀ e, 0 ≤ x e} (restricted n L d S) := by
  have h := average_convex (L := L) S.card S
    (fun p (x : Edge n L → ℝ) => BLSH.complete (p.map (fun T => normalizedRate T x)) d)
    (fun p => path_convex hH p d)
  have heq : restricted n L d S =
      (fun x => average S.card S (fun p => BLSH.complete (p.map (fun T => normalizedRate T x)) d)) := by
    funext x
    exact representation hL S.card S le_rfl x d
  rw [heq]
  exact h

/-- Every nonterminal averaging weight is strictly positive. -/
theorem averaging_weight_pos {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty) :
    0 < (S.card : ℝ)⁻¹ := inv_pos.mpr (Nat.cast_pos.mpr (Finset.card_pos.mpr hS))

theorem average_nonneg {n : ℕ} (m : ℕ) (S : Finset (Fin n))
    (F : List (Finset (Fin n)) → ℝ) (hF : ∀ p, 0 ≤ F p) :
    0 ≤ average m S F := by
  have h := average_mono m S (fun _ => 0) F hF
  have hz : average m S (fun _ => 0) = 0 := by
    simpa using average_mul m S 0 (fun _ => (1 : ℝ))
  rwa [hz] at h

/-- Exact original full endpoint; only the H convexity obligation is conditional. -/
def FullEndpoint : Prop := ∀ (n L d : ℕ), 2 ≤ n → 2 ≤ L → 2 ≤ d →
  ConvexOn ℝ (stdSimplex ℝ (Edge n L)) (sourcePolynomial n L d)

theorem conditional_source_orthant (hH : HConvexity) {n L : ℕ} (hL : 1 ≤ L) (d : ℕ) :
    ConvexOn ℝ {x : Edge n L → ℝ | ∀ e, 0 ≤ x e} (sourcePolynomial n L d) := by
  have h := conditional_restricted_convex (n := n) hH hL Finset.univ d
  have heq : restricted n L d Finset.univ = sourcePolynomial n L d :=
    funext (restricted_univ n L d)
  rwa [heq] at h

/-- Explicit empty-simplex argument, including all L>n endpoint cases. -/
theorem empty_simplex {n L : ℕ} (h : n < L) : stdSimplex ℝ (Edge n L) = ∅ := by
  have he : IsEmpty (Edge n L) := by
    refine ⟨fun e => ?_⟩
    have hc := edge_card e
    have hle := Finset.card_le_card (Finset.subset_univ e.val)
    simp only [Finset.card_univ, Fintype.card_fin] at hle
    omega
  letI := he
  exact stdSimplex_of_isEmpty_index ℝ (Edge n L)

theorem conditional_fullEndpoint (hH : HConvexity) : FullEndpoint := by
  intro n L d hn hL hd
  by_cases h : L ≤ n
  · exact (conditional_source_orthant hH (by omega : 1 ≤ L) d).subset
      (fun x hx => hx.1) (convex_stdSimplex ℝ _)
  · rw [empty_simplex (Nat.lt_of_not_ge h)]
    exact ⟨convex_empty, by simp⟩

/-- The source itself, with no coordinate relabelling or L≤n premise. -/
theorem source_representation {n L : ℕ} (hL : 1 ≤ L) (d : ℕ) (x : Edge n L → ℝ) :
    sourcePolynomial n L d x = average n Finset.univ
      (fun p => BLSH.complete (p.map (fun T => normalizedRate T x)) d) := by
  rw [← restricted_univ]
  exact representation hL n Finset.univ (by simp) x d

end BLSUnit3
