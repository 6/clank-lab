import RS16.Value

/-!
# The right side (the paper, Step 3)

With `m = E m₁ + 1` and `Z = q^{E m₁}`, every row is a finite sum `Σ φᵢ(q) Z^{αᵢ}` whose
coefficients `φᵢ` have a pole of order at most `poleBound ω row` at `ω` (`row_zexp`). When
`ω^E = 1`, the `N`-th difference in `m₁` of such a sum is regular at `ω` with value `0` as soon as
`N` exceeds the pole bound (`zexp_diff_zero`), because it is `Σ φᵢ Z^{αᵢ} (q^{E αᵢ} - 1)^N`.
-/

open Polynomial

namespace RS16

variable {K : Type*} [Field K]

open scoped Classical

/-- `f` has a pole of order at most `D` at `ω`. -/
def PoleLE (f : RatFunc K) (ω : K) (D : ℕ) : Prop := Regular (f * lin ω ^ D) ω

lemma Regular.add {f g : RatFunc K} {ω : K} (hf : Regular f ω) (hg : Regular g ω) :
    Regular (f + g) ω := by
  obtain ⟨v, hv⟩ := hf; obtain ⟨w, hw⟩ := hg; exact ⟨_, hv.add hw⟩

lemma Regular.mul {f g : RatFunc K} {ω : K} (hf : Regular f ω) (hg : Regular g ω) :
    Regular (f * g) ω := by
  obtain ⟨v, hv⟩ := hf; obtain ⟨w, hw⟩ := hg; exact ⟨_, hv.mul hw⟩

lemma Regular.pow {f : RatFunc K} {ω : K} (hf : Regular f ω) (n : ℕ) : Regular (f ^ n) ω := by
  obtain ⟨v, hv⟩ := hf; exact ⟨_, hv.pow n⟩

lemma regular_lin (ω : K) : Regular (lin ω) ω := ⟨_, hasValueAt_lin ω⟩

lemma PoleLE.of_regular {f : RatFunc K} {ω : K} (h : Regular f ω) : PoleLE f ω 0 := by
  simpa [PoleLE] using h

lemma PoleLE.mono {f : RatFunc K} {ω : K} {D D' : ℕ} (h : PoleLE f ω D) (hD : D ≤ D') :
    PoleLE f ω D' := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hD
  have : f * lin ω ^ (D + k) = (f * lin ω ^ D) * lin ω ^ k := by ring
  rw [PoleLE, this]
  exact h.mul ((regular_lin ω).pow k)

lemma PoleLE.add {f g : RatFunc K} {ω : K} {D : ℕ} (hf : PoleLE f ω D) (hg : PoleLE g ω D) :
    PoleLE (f + g) ω D := by
  rw [PoleLE, add_mul]; exact Regular.add hf hg

lemma PoleLE.mul {f g : RatFunc K} {ω : K} {D D' : ℕ} (hf : PoleLE f ω D)
    (hg : PoleLE g ω D') : PoleLE (f * g) ω (D + D') := by
  have : f * g * lin ω ^ (D + D') = (f * lin ω ^ D) * (g * lin ω ^ D') := by ring
  rw [PoleLE, this]; exact Regular.mul hf hg

/-! ## Sums `Σ φᵢ Z^{αᵢ}` -/

/-- `Σ_{(α, φ) ∈ l} φ · (q^E)^(α m₁)` -/
noncomputable def zsum (E : ℕ) (l : List (ℤ × RatFunc K)) (m1 : ℕ) : RatFunc K :=
  (l.map fun p => p.2 * ((RatFunc.X : RatFunc K) ^ (E : ℤ)) ^ (p.1 * (m1 : ℤ))).sum

/-- `F` is such a sum with coefficients of pole order at most `D` at `ω`. -/
def ZExp (E : ℕ) (ω : K) (D : ℕ) (F : ℕ → RatFunc K) : Prop :=
  ∃ l : List (ℤ × RatFunc K), (∀ p ∈ l, PoleLE p.2 ω D) ∧ ∀ m1, F m1 = zsum E l m1

lemma ZExp.mono {E : ℕ} {ω : K} {D D' : ℕ} {F : ℕ → RatFunc K} (h : ZExp E ω D F)
    (hD : D ≤ D') : ZExp E ω D' F := by
  obtain ⟨l, hl, hF⟩ := h
  exact ⟨l, fun p hp => (hl p hp).mono hD, hF⟩

lemma ZExp.zero (E : ℕ) (ω : K) (D : ℕ) : ZExp E ω D (fun _ => 0) :=
  ⟨[], by simp, by simp [zsum]⟩

lemma ZExp.single (E : ℕ) {ω : K} {D : ℕ} (a : ℤ) {φ : RatFunc K} (h : PoleLE φ ω D) :
    ZExp E ω D (fun m1 => φ * ((RatFunc.X : RatFunc K) ^ (E : ℤ)) ^ (a * (m1 : ℤ))) :=
  ⟨[(a, φ)], by simpa using h, by simp [zsum]⟩

lemma ZExp.const (E : ℕ) {ω : K} {D : ℕ} {φ : RatFunc K} (h : PoleLE φ ω D) :
    ZExp E ω D (fun _ => φ) := by
  simpa using ZExp.single E 0 h

lemma ZExp.add {E : ℕ} {ω : K} {D : ℕ} {F G : ℕ → RatFunc K} (hF : ZExp E ω D F)
    (hG : ZExp E ω D G) : ZExp E ω D (fun m1 => F m1 + G m1) := by
  obtain ⟨l, hl, hF⟩ := hF
  obtain ⟨l', hl', hG⟩ := hG
  refine ⟨l ++ l', fun p hp => ?_, fun m1 => by simp [zsum, hF, hG]⟩
  rcases List.mem_append.mp hp with hp | hp
  · exact hl p hp
  · exact hl' p hp

lemma zsum_mul (E : ℕ) (l l' : List (ℤ × RatFunc K)) (m1 : ℕ) :
    zsum E l m1 * zsum E l' m1 =
      zsum E (l.flatMap fun p => l'.map fun p' => (p.1 + p'.1, p.2 * p'.2)) m1 := by
  have hX : (RatFunc.X : RatFunc K) ^ (E : ℤ) ≠ 0 := zpow_ne_zero _ RatFunc.X_ne_zero
  induction l with
  | nil => simp [zsum]
  | cons a l ih =>
    simp only [zsum, List.map_cons, List.sum_cons, List.flatMap_cons, List.map_append,
      List.sum_append] at ih ⊢
    rw [add_mul, ih]
    congr 1
    simp only [List.map_map, Function.comp_def]
    rw [← List.sum_map_mul_left]
    congr 1
    apply List.map_congr_left
    intro p _
    rw [add_mul, zpow_add₀ hX]
    ring

lemma ZExp.mul {E : ℕ} {ω : K} {D D' : ℕ} {F G : ℕ → RatFunc K} (hF : ZExp E ω D F)
    (hG : ZExp E ω D' G) : ZExp E ω (D + D') (fun m1 => F m1 * G m1) := by
  obtain ⟨l, hl, hF⟩ := hF
  obtain ⟨l', hl', hG⟩ := hG
  refine ⟨_, fun p hp => ?_, fun m1 => by show F m1 * G m1 = _; rw [hF, hG, zsum_mul]⟩
  simp only [List.mem_flatMap, List.mem_map] at hp
  obtain ⟨a, ha, b, hb, rfl⟩ := hp
  exact (hl a ha).mul (hl' b hb)

lemma ZExp.list_sum {ι : Type*} {E : ℕ} {ω : K} {D : ℕ} (l : List ι) (F : ι → ℕ → RatFunc K)
    (h : ∀ i ∈ l, ZExp E ω D (F i)) : ZExp E ω D (fun m1 => (l.map fun i => F i m1).sum) := by
  induction l with
  | nil => simpa using ZExp.zero E ω D
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (h a (by simp)).add (ih fun i hi => h i (by simp [hi]))

lemma ZExp.list_prod {ι : Type*} {E : ℕ} {ω : K} (l : List ι) (D : ι → ℕ)
    (F : ι → ℕ → RatFunc K) (h : ∀ i ∈ l, ZExp E ω (D i) (F i)) :
    ZExp E ω (l.map D).sum (fun m1 => (l.map fun i => F i m1).prod) := by
  induction l with
  | nil => simpa using ZExp.const E (PoleLE.of_regular (hasValueAt_one ω).regular)
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    exact (h a (by simp)).mul (ih fun i hi => h i (by simp [hi]))

/-! ## The factors -/

lemma regular_X_zpow {ω : K} (hω : ω ≠ 0) (z : ℤ) : Regular ((RatFunc.X : RatFunc K) ^ z) ω :=
  (hasValueAt_X_zpow hω z).regular

lemma one_sub_X_ne_zero : (1 - RatFunc.X : RatFunc K) ≠ 0 := by
  intro h
  have : (rf (1 - X) : RatFunc K) = 0 := by simpa [rf] using h
  have h2 : (1 - X : K[X]) = 0 := (RatFunc.algebraMap_injective K) (by simpa using this)
  have := congrArg (Polynomial.eval 0) h2
  simp at this

lemma hasValueAt_one_sub_X_inv {ω : K} (hω1 : ω ≠ 1) :
    HasValueAt (1 - RatFunc.X : RatFunc K)⁻¹ ω (1 - ω)⁻¹ :=
  ((hasValueAt_one ω).sub (hasValueAt_X ω)).inv (sub_ne_zero.mpr (Ne.symm hω1))

/-- `(1 - q)⁻¹` has a pole of order at most `[ω = 1]`. -/
lemma poleLE_one_sub_X_inv (ω : K) :
    PoleLE (1 - RatFunc.X : RatFunc K)⁻¹ ω (if ω = 1 then 1 else 0) := by
  split_ifs with h
  · subst h
    have : (1 - RatFunc.X : RatFunc K)⁻¹ * lin 1 ^ 1 = -1 := by
      have hl : (lin (1 : K) : RatFunc K) = -(1 - RatFunc.X) := by simp [lin, rf]
      rw [pow_one, hl, mul_neg, inv_mul_cancel₀ one_sub_X_ne_zero]
    rw [PoleLE, this]
    exact ⟨_, (hasValueAt_one 1).neg⟩
  · exact PoleLE.of_regular (hasValueAt_one_sub_X_inv h).regular

lemma hasValueAt_qint {ω : K} (hω0 : ω ≠ 0) (hω1 : ω ≠ 1) (x : ℤ) :
    HasValueAt (qint x : RatFunc K) ω ((1 - ω ^ x) / (1 - ω)) := by
  rw [qint, div_eq_mul_inv, div_eq_mul_inv]
  exact ((hasValueAt_one ω).sub (hasValueAt_X_zpow hω0 x)).mul (hasValueAt_one_sub_X_inv hω1)

/-- The geometric polynomial `1 + X + ⋯ + X^(b-1)`. -/
noncomputable def geomPoly (b : ℕ) : K[X] := ∑ i ∈ Finset.range b, X ^ i

lemma qint_natCast (b : ℕ) : (qint (b : ℤ) : RatFunc K) = rf (geomPoly b) := by
  rw [qint, zpow_natCast, div_eq_iff one_sub_X_ne_zero]
  have h := geom_sum_mul (X : K[X]) b
  have h' : rf (geomPoly b * (X - 1)) = rf (X ^ b - 1 : K[X]) := by rw [geomPoly, h]
  simp only [rf, map_mul, map_sub, map_pow, map_one, RatFunc.algebraMap_X] at h'
  linear_combination h'

lemma geomPoly_ne_zero {b : ℕ} (hb : 0 < b) : (geomPoly b : K[X]) ≠ 0 := by
  intro h
  have := congrArg (Polynomial.eval 0) h
  simp only [geomPoly, eval_finsetSum, eval_pow, eval_X, eval_zero] at this
  rw [Finset.sum_eq_single 0 (fun i _ hi => zero_pow hi) (by simp; omega)] at this
  simp at this

/-- `1 / [b]_q` has a pole of order at most `[ω ≠ 1 ∧ ω^b = 1]` (characteristic `0`). -/
lemma poleLE_qint_inv [CharZero K] {ω : K} (hω0 : ω ≠ 0) (b : ℕ+) :
    PoleLE (qint ((b : ℕ) : ℤ) : RatFunc K)⁻¹ ω (if ω ≠ 1 ∧ ω ^ (b : ℕ) = 1 then 1 else 0) := by
  rw [qint_natCast]
  have hb : 0 < (b : ℕ) := b.pos
  split_ifs with h
  · obtain ⟨h1, hb1⟩ := h
    -- `(X - 1) · geomPoly b = X^b - 1 = (X - ω) · G`, `G(ω) = b ω^(b-1) ≠ 0`
    set G : K[X] := ∑ i ∈ Finset.range b, X ^ i * C ω ^ ((b : ℕ) - 1 - i) with hG
    have hGω : G.eval ω ≠ 0 := by
      simp only [hG, eval_finsetSum, eval_mul, eval_pow, eval_X, eval_C]
      rw [Finset.sum_congr rfl (fun i hi => by
        rw [← pow_add, show i + ((b : ℕ) - 1 - i) = (b : ℕ) - 1 by
          have := Finset.mem_range.mp hi; omega])]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      exact mul_ne_zero (Nat.cast_ne_zero.mpr hb.ne') (pow_ne_zero _ hω0)
    have hpoly : geomPoly (b : ℕ) * (X - 1) = G * (X - C ω) := by
      rw [geomPoly, geom_sum_mul, hG, geom_sum₂_mul, ← C_pow, hb1, C_1]
    have hgne : (rf (geomPoly (b : ℕ)) : RatFunc K) ≠ 0 := by
      intro h0
      exact geomPoly_ne_zero hb ((RatFunc.algebraMap_injective K) (by simpa using h0))
    have key : (rf (geomPoly (b : ℕ)) : RatFunc K)⁻¹ * lin ω ^ 1 = rf (X - 1) / rf G := by
      have hG0 := rf_ne_zero hGω
      have := congrArg (algebraMap K[X] (RatFunc K)) hpoly
      rw [map_mul, map_mul] at this
      simp only [lin, rf] at hgne hG0 ⊢
      field_simp
      linear_combination -this
    rw [PoleLE, key]
    exact ⟨_, (hasValueAt_poly _ ω).div (hasValueAt_poly _ ω) hGω⟩
  · apply PoleLE.of_regular
    have hne : (geomPoly (b : ℕ)).eval ω ≠ 0 := by
      by_cases h1 : ω = 1
      · subst h1
        simp [geomPoly, eval_finsetSum, hb.ne']
      · have hb1 : ω ^ (b : ℕ) ≠ 1 := fun hb1 => h ⟨h1, hb1⟩
        intro h0
        have := congrArg (Polynomial.eval ω) (geom_sum_mul (X : K[X]) b)
        simp only [eval_mul, eval_sub, eval_X, eval_one, eval_pow] at this
        rw [show (∑ i ∈ Finset.range b, X ^ i : K[X]).eval ω = 0 by simpa [geomPoly] using h0,
          zero_mul] at this
        exact hb1 (sub_eq_zero.mp this.symm)
    exact ⟨_, (hasValueAt_poly _ ω).inv hne⟩

/-! ## The pole bound of a row and its Z-expansion -/

open scoped Classical in
/-- The pole bound of a row at `ω`: each numerator bracket or sum counts `[ω = 1]`, each
denominator bracket `[b]` counts `[ω ≠ 1 ∧ ω^b = 1]`. -/
noncomputable def poleBound (ω : K) : Row → ℕ
  | .qpow _ _ => 0
  | .br _ => if ω = 1 then 1 else 0
  | .sum _ => if ω = 1 then 1 else 0
  | .mul a b => poleBound ω a + poleBound ω b
  | .div a bs => poleBound ω a + (bs.map fun b : ℕ+ => if ω ≠ 1 ∧ ω ^ (b : ℕ) = 1 then 1 else 0).sum

lemma zexp_qpow (E : ℕ) {ω : K} (hω : ω ≠ 0) (α β : ℤ) :
    ZExp E ω 0 (fun m1 => (RatFunc.X : RatFunc K) ^ (α * ((E : ℤ) * m1 + 1) + β)) := by
  have h := ZExp.single E α (PoleLE.of_regular (regular_X_zpow (K := K) hω (α + β)))
  convert h using 2 with m1
  rw [← zpow_mul, ← zpow_add₀ RatFunc.X_ne_zero]
  ring_nf

lemma zexp_br (E : ℕ) {ω : K} (hω : ω ≠ 0) (γ : ℤ) :
    ZExp E ω (if ω = 1 then 1 else 0) (fun m1 => (qint ((E : ℤ) * m1 + 1 + γ) : RatFunc K)) := by
  have hp := poleLE_one_sub_X_inv ω
  have h1 := ZExp.single E 0 hp
  have h2 := ZExp.single E 1 ((hp.mul (PoleLE.of_regular (regular_X_zpow hω (1 + γ)))).mul
    (PoleLE.of_regular ⟨_, (hasValueAt_one ω).neg⟩))
  simp only [add_zero] at h2
  convert h1.add h2 using 2 with m1
  have e1 : (RatFunc.X : RatFunc K) ^ ((E : ℤ) * m1 + 1 + γ)
      = RatFunc.X ^ (1 + γ) * ((RatFunc.X : RatFunc K) ^ (E : ℤ)) ^ (m1 : ℤ) := by
    rw [← zpow_mul, ← zpow_add₀ RatFunc.X_ne_zero]; ring_nf
  simp only [zero_mul, one_mul, zpow_zero, mul_one]
  rw [qint, e1]
  have := one_sub_X_ne_zero (K := K)
  field_simp
  ring

lemma list_prod_inv {ι : Type*} (l : List ι) (f : ι → RatFunc K) :
    (l.map f).prod⁻¹ = (l.map fun i => (f i)⁻¹).prod := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, mul_comm]

theorem row_zexp [CharZero K] (E : ℕ) {ω : K} (hω : ω ≠ 0) :
    ∀ row : Row, ZExp E ω (poleBound ω row) (fun m1 => row.eval K ((E : ℤ) * m1 + 1))
  | .qpow α β => by simpa [poleBound, Row.eval] using zexp_qpow E hω α β
  | .br γ => by
      simpa [poleBound, Row.eval, add_assoc] using zexp_br E hω γ
  | .sum ts => by
      simp only [poleBound, Row.eval]
      apply ZExp.list_sum
      intro t _
      have hs : PoleLE ((if t.neg then -1 else 1 : RatFunc K)) ω 0 := by
        split_ifs
        · exact PoleLE.of_regular ⟨_, (hasValueAt_one ω).neg⟩
        · exact PoleLE.of_regular ⟨_, hasValueAt_one ω⟩
      have := ((ZExp.const E hs).mul (zexp_qpow E hω t.α t.β)).mul (zexp_br E hω t.γ)
      simpa [add_assoc] using this
  | .mul a b => by
      simpa [poleBound, Row.eval] using (row_zexp E hω a).mul (row_zexp E hω b)
  | .div a bs => by
      simp only [poleBound, Row.eval, div_eq_mul_inv]
      apply (row_zexp E hω a).mul
      have := ZExp.list_prod bs (fun b => if ω ≠ 1 ∧ ω ^ (b : ℕ) = 1 then 1 else 0)
        (fun b _ => (qint ((b : ℕ) : ℤ) : RatFunc K)⁻¹)
        (fun b _ => ZExp.const E (poleLE_qint_inv hω b))
      convert this using 2 with m1
      exact list_prod_inv bs _

lemma poleBound_le_numCount (row : Row) : poleBound (1 : K) row ≤ row.numCount := by
  induction row with
  | qpow => simp [poleBound]
  | br => simp [poleBound, Row.numCount]
  | sum => simp [poleBound, Row.numCount]
  | mul a b iha ihb => simp only [poleBound, Row.numCount]; omega
  | div a bs iha => simpa [poleBound, Row.numCount] using iha

lemma poleBound_le_dens {ω : K} (hω : ω ≠ 1) (row : Row) :
    poleBound ω row ≤ row.dens.length := by
  induction row with
  | qpow => simp [poleBound]
  | br => simp [poleBound, hω]
  | sum => simp [poleBound, hω]
  | mul a b iha ihb => simp only [poleBound, Row.dens, List.length_append]; omega
  | div a bs iha =>
    simp only [poleBound, Row.dens, List.length_append]
    have : (bs.map fun b : ℕ+ => if ω ≠ 1 ∧ ω ^ (b : ℕ) = 1 then 1 else 0).sum ≤ bs.length := by
      induction bs with
      | nil => simp
      | cons b bs ih => simp only [List.map_cons, List.sum_cons, List.length_cons]; split_ifs <;> omega
    omega

/-! ## Differences vanish at `ω` -/

lemma finset_sum_list_sum {ι κ M : Type*} [AddCommMonoid M] (s : Finset κ) (l : List ι)
    (f : κ → ι → M) : ∑ k ∈ s, (l.map (f k)).sum = (l.map fun i => ∑ k ∈ s, f k i).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [Finset.sum_add_distrib, ih]

lemma zsmul_list_sum {ι M : Type*} [AddCommGroup M] (z : ℤ) (l : List ι) (f : ι → M) :
    z • (l.map f).sum = (l.map fun i => z • f i).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [smul_add, ih]

theorem zexp_diff_zero {E D N : ℕ} {ω : K} (hω : ω ≠ 0) (hE : ω ^ E = 1) (hDN : D < N)
    {F : ℕ → RatFunc K} (hF : ZExp E ω D F) (m1 : ℕ) :
    HasValueAt (∑ k ∈ Finset.range (N + 1),
      ((-1 : ℤ) ^ (N - k) * (N.choose k : ℤ)) • F (m1 + k)) ω 0 := by
  obtain ⟨l, hl, hF⟩ := hF
  set Y : RatFunc K := (RatFunc.X : RatFunc K) ^ (E : ℤ)
  have hY : Y ≠ 0 := zpow_ne_zero _ RatFunc.X_ne_zero
  -- rewrite as `Σ_p φ_p Y^(α m₁) (Y^α - 1)^N`
  have hsum : (∑ k ∈ Finset.range (N + 1), ((-1 : ℤ) ^ (N - k) * (N.choose k : ℤ)) • F (m1 + k))
      = (l.map fun p => p.2 * Y ^ (p.1 * (m1 : ℤ)) * (Y ^ p.1 - 1) ^ N).sum := by
    simp only [hF, zsum, zsmul_list_sum]
    rw [finset_sum_list_sum]
    congr 1
    apply List.map_congr_left
    intro p _
    rw [sub_eq_add_neg, add_pow, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [zsmul_eq_mul]
    push_cast
    rw [show p.1 * ((m1 : ℤ) + k) = p.1 * m1 + p.1 * k by ring,
      zpow_add₀ hY, zpow_mul Y p.1 (k : ℤ), zpow_natCast]
    ring
  rw [hsum]
  have h0 := hasValueAt_list_sum l (fun p => p.2 * Y ^ (p.1 * (m1 : ℤ)) * (Y ^ p.1 - 1) ^ N)
    (fun _ => 0) (ω := ω) ?_
  · simpa using h0
  intro p hp
  -- `Y^α - 1` vanishes at `ω`
  have hz : HasValueAt (Y ^ p.1 - 1) ω 0 := by
    have := (hasValueAt_X_zpow (K := K) hω ((E : ℤ) * p.1)).sub (hasValueAt_one ω)
    rw [zpow_mul ω, zpow_natCast, hE, one_zpow, sub_self] at this
    rwa [show Y ^ p.1 = RatFunc.X ^ ((E : ℤ) * p.1) from (zpow_mul _ _ _).symm]
  obtain ⟨g, hg, hgeq⟩ := hz.eq_lin_mul
  obtain ⟨r, hr⟩ := hl p hp
  obtain ⟨gv, hgv⟩ := hg
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt hDN
  have : p.2 * Y ^ (p.1 * (m1 : ℤ)) * (Y ^ p.1 - 1) ^ (D + j + 1)
      = (p.2 * lin ω ^ D) * Y ^ (p.1 * (m1 : ℤ)) * (lin ω ^ (j + 1) * g ^ (D + j + 1)) := by
    rw [hgeq]; ring
  rw [this]
  obtain ⟨yv, hyv⟩ : Regular (Y ^ (p.1 * (m1 : ℤ))) ω := by
    rw [show Y ^ (p.1 * (m1 : ℤ)) = RatFunc.X ^ ((E : ℤ) * (p.1 * m1)) from (zpow_mul _ _ _).symm]
    exact regular_X_zpow hω _
  have := (hr.mul hyv).mul (((hasValueAt_lin ω).pow (j + 1)).mul (hgv.pow (D + j + 1)))
  simpa using this

/-! ## Rows with a factor `[m - 1]_q` -/

lemma hasValueAt_sign (b : Bool) (ω : K) :
    HasValueAt (if b then -1 else 1 : RatFunc K) ω (if b then -1 else 1) := by
  cases b
  · simpa using hasValueAt_one ω
  · simpa using (hasValueAt_one ω).neg

lemma row_regular [CharZero K] {ω : K} (hω0 : ω ≠ 0) (hω1 : ω ≠ 1) (m : ℤ) :
    ∀ row : Row, (∀ b ∈ row.dens, ω ^ (b : ℕ) ≠ 1) → Regular (row.eval K m) ω
  | .qpow α β, _ => regular_X_zpow hω0 _
  | .br γ, _ => (hasValueAt_qint hω0 hω1 _).regular
  | .sum ts, _ => by
      simp only [Row.eval]
      have := hasValueAt_list_sum ts
        (fun t => (if t.neg then -1 else 1) * RatFunc.X ^ (t.α * m + t.β) * qint (m + t.γ))
        (fun t => (if t.neg then -1 else 1) * ω ^ (t.α * m + t.β)
          * ((1 - ω ^ (m + t.γ)) / (1 - ω))) (ω := ω) (fun t _ =>
          ((hasValueAt_sign t.neg ω).mul (hasValueAt_X_zpow hω0 _)).mul
            (hasValueAt_qint hω0 hω1 _))
      exact this.regular
  | .mul a b, h => by
      simp only [Row.dens, List.mem_append] at h
      exact (row_regular hω0 hω1 m a fun x hx => h x (Or.inl hx)).mul
        (row_regular hω0 hω1 m b fun x hx => h x (Or.inr hx))
  | .div a bs, h => by
      simp only [Row.dens, List.mem_append] at h
      simp only [Row.eval]
      obtain ⟨v, hv⟩ := row_regular hω0 hω1 m a fun x hx => h x (Or.inl hx)
      have hp := hasValueAt_list_prod bs (fun b => (qint ((b : ℕ) : ℤ) : RatFunc K))
        (fun b => (1 - ω ^ ((b : ℕ) : ℤ)) / (1 - ω)) (ω := ω)
        (fun b _ => hasValueAt_qint hω0 hω1 _)
      refine ⟨_, hv.div hp ?_⟩
      apply List.prod_ne_zero
      simp only [List.mem_map, not_exists, not_and]
      intro b hb h0
      have hb1 := h b (Or.inr hb)
      rw [div_eq_zero_iff, sub_eq_zero, sub_eq_zero, zpow_natCast] at h0
      rcases h0 with h0 | h0
      · exact hb1 h0.symm
      · exact hω1 h0.symm

/-- A row with a factor `[m - 1]_q` vanishes at `ω ≠ 1` when `ω^(m-1) = 1` and no denominator
bracket vanishes at `ω`. -/
lemma row_m1 [CharZero K] {ω : K} (hω0 : ω ≠ 0) (hω1 : ω ≠ 1) {m : ℤ} (hm : ω ^ (m - 1) = 1) :
    ∀ row : Row, row.hasM1Factor → (∀ b ∈ row.dens, ω ^ (b : ℕ) ≠ 1) →
      HasValueAt (row.eval K m) ω 0
  | .br γ, h, _ => by
      simp only [Row.hasM1Factor] at h
      subst h
      have := hasValueAt_qint (K := K) hω0 hω1 (m + -1)
      rwa [← sub_eq_add_neg, hm, sub_self, zero_div] at this
  | .mul a b, h, hd => by
      simp only [Row.dens, List.mem_append] at hd
      simp only [Row.hasM1Factor] at h
      simp only [Row.eval]
      rcases h with h | h
      · obtain ⟨v, hv⟩ := row_regular hω0 hω1 m b fun x hx => hd x (Or.inr hx)
        simpa using (row_m1 hω0 hω1 hm a h fun x hx => hd x (Or.inl hx)).mul hv
      · obtain ⟨v, hv⟩ := row_regular hω0 hω1 m a fun x hx => hd x (Or.inl hx)
        simpa using hv.mul (row_m1 hω0 hω1 hm b h fun x hx => hd x (Or.inr hx))
  | .div a bs, h, hd => by
      simp only [Row.hasM1Factor] at h
      have ha := row_m1 hω0 hω1 hm a h fun x hx => hd x (by simp [Row.dens, hx])
      obtain ⟨v, hv⟩ := row_regular hω0 hω1 m (.div (.qpow 0 0) bs)
        (fun x hx => hd x (by simpa [Row.dens] using Or.inr (by simpa [Row.dens] using hx)))
      simp only [Row.eval, zero_mul, zero_add, zpow_zero, one_div] at hv ⊢
      rw [div_eq_mul_inv]
      simpa using ha.mul hv
  | .qpow _ _, h, _ => by simp [Row.hasM1Factor] at h
  | .sum _, h, _ => by simp [Row.hasM1Factor] at h

end RS16
