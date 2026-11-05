import RS16.Defs

/-!
# Values of rational functions at a point

Algebra of `HasValueAt`: polynomials, sums, products, inverses, powers of `q`, and the
factorisation of a regular function vanishing at `ω`.
-/

open Polynomial

namespace RS16

variable {K : Type*} [Field K]

/-- polynomials as rational functions -/
noncomputable abbrev rf (p : K[X]) : RatFunc K := algebraMap K[X] (RatFunc K) p

/-- regular at `ω` -/
def Regular (f : RatFunc K) (ω : K) : Prop := ∃ v, HasValueAt f ω v

lemma rf_ne_zero {Q : K[X]} {ω : K} (h : Q.eval ω ≠ 0) : rf Q ≠ 0 := by
  intro h0
  apply h
  have : Q = 0 := (RatFunc.algebraMap_injective K) (by simpa using h0)
  simp [this]

lemma hasValueAt_poly (p : K[X]) (ω : K) : HasValueAt (rf p) ω (p.eval ω) :=
  ⟨p, 1, by simp, by simp, by simp⟩

lemma HasValueAt.unique {f : RatFunc K} {ω v v' : K} (h : HasValueAt f ω v)
    (h' : HasValueAt f ω v') : v = v' := by
  obtain ⟨N, Q, hQ, rfl, rfl⟩ := h
  obtain ⟨N', Q', hQ', hf, rfl⟩ := h'
  have hQr := rf_ne_zero hQ
  have hQr' := rf_ne_zero hQ'
  rw [div_eq_div_iff hQr hQr'] at hf
  have hp : N * Q' = N' * Q := RatFunc.algebraMap_injective K (by simpa using hf)
  have := congrArg (Polynomial.eval ω) hp
  simp only [eval_mul] at this
  rw [div_eq_div_iff hQ hQ']
  exact this

lemma hasValueAt_polynomial_iff (p : K[X]) (ω v : K) :
    HasValueAt (rf p) ω v ↔ v = p.eval ω :=
  ⟨fun h => h.unique (hasValueAt_poly p ω), fun h => h ▸ hasValueAt_poly p ω⟩

lemma hasValueAt_const (a ω : K) : HasValueAt (algebraMap K (RatFunc K) a) ω a := by
  have := hasValueAt_poly (C a) ω
  simpa [rf, ← RatFunc.algebraMap_C] using this

lemma hasValueAt_one (ω : K) : HasValueAt (1 : RatFunc K) ω 1 := by
  simpa using hasValueAt_const (1 : K) ω

lemma hasValueAt_zero (ω : K) : HasValueAt (0 : RatFunc K) ω 0 := by
  simpa using hasValueAt_const (0 : K) ω

lemma hasValueAt_natCast (n : ℕ) (ω : K) : HasValueAt (n : RatFunc K) ω n := by
  simpa using hasValueAt_const (n : K) ω

lemma hasValueAt_X (ω : K) : HasValueAt (RatFunc.X : RatFunc K) ω ω := by
  simpa [rf] using hasValueAt_poly (X : K[X]) ω

lemma HasValueAt.add {f g : RatFunc K} {ω v w : K} (hf : HasValueAt f ω v)
    (hg : HasValueAt g ω w) : HasValueAt (f + g) ω (v + w) := by
  obtain ⟨N, Q, hQ, rfl, rfl⟩ := hf
  obtain ⟨N', Q', hQ', rfl, rfl⟩ := hg
  refine ⟨N * Q' + N' * Q, Q * Q', by simp [hQ, hQ'], ?_, ?_⟩
  · rw [div_add_div _ _ (rf_ne_zero hQ) (rf_ne_zero hQ')]
    simp only [rf, map_add, map_mul]
    ring
  · simp only [eval_add, eval_mul]
    field_simp

lemma HasValueAt.mul {f g : RatFunc K} {ω v w : K} (hf : HasValueAt f ω v)
    (hg : HasValueAt g ω w) : HasValueAt (f * g) ω (v * w) := by
  obtain ⟨N, Q, hQ, rfl, rfl⟩ := hf
  obtain ⟨N', Q', hQ', rfl, rfl⟩ := hg
  refine ⟨N * N', Q * Q', by simp [hQ, hQ'], ?_, ?_⟩
  · rw [div_mul_div_comm]
    simp
  · simp only [eval_mul]
    field_simp

lemma HasValueAt.neg {f : RatFunc K} {ω v : K} (hf : HasValueAt f ω v) :
    HasValueAt (-f) ω (-v) := by
  have := (hasValueAt_const (-1 : K) ω).mul hf
  simpa using this

lemma HasValueAt.sub {f g : RatFunc K} {ω v w : K} (hf : HasValueAt f ω v)
    (hg : HasValueAt g ω w) : HasValueAt (f - g) ω (v - w) := by
  simpa [sub_eq_add_neg] using hf.add hg.neg

lemma HasValueAt.pow {f : RatFunc K} {ω v : K} (hf : HasValueAt f ω v) (n : ℕ) :
    HasValueAt (f ^ n) ω (v ^ n) := by
  induction n with
  | zero => simpa using hasValueAt_one ω
  | succ n ih => simpa [pow_succ] using ih.mul hf

lemma HasValueAt.inv {f : RatFunc K} {ω v : K} (hf : HasValueAt f ω v) (hv : v ≠ 0) :
    HasValueAt f⁻¹ ω v⁻¹ := by
  obtain ⟨N, Q, hQ, rfl, rfl⟩ := hf
  have hN : N.eval ω ≠ 0 := by
    intro h; apply hv; simp [h]
  exact ⟨Q, N, hN, by rw [inv_div], by rw [inv_div]⟩

lemma HasValueAt.div {f g : RatFunc K} {ω v w : K} (hf : HasValueAt f ω v)
    (hg : HasValueAt g ω w) (hw : w ≠ 0) : HasValueAt (f / g) ω (v / w) := by
  simpa [div_eq_mul_inv] using hf.mul (hg.inv hw)

lemma HasValueAt.zsmul {f : RatFunc K} {ω v : K} (hf : HasValueAt f ω v) (z : ℤ) :
    HasValueAt (z • f) ω (z • v) := by
  have := (hasValueAt_const (z : K) ω).mul hf
  simpa [zsmul_eq_mul] using this

lemma hasValueAt_X_zpow {ω : K} (hω : ω ≠ 0) (z : ℤ) :
    HasValueAt ((RatFunc.X : RatFunc K) ^ z) ω (ω ^ z) := by
  rcases Int.eq_nat_or_neg z with ⟨n, rfl | rfl⟩
  · simpa using (hasValueAt_X ω).pow n
  · simpa using ((hasValueAt_X ω).pow n).inv (pow_ne_zero n hω)

lemma hasValueAt_list_sum {ι : Type*} (l : List ι) (f : ι → RatFunc K) (v : ι → K) {ω : K}
    (h : ∀ i ∈ l, HasValueAt (f i) ω (v i)) :
    HasValueAt (l.map f).sum ω (l.map v).sum := by
  induction l with
  | nil => simpa using hasValueAt_zero ω
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (h a (by simp)).add (ih fun i hi => h i (by simp [hi]))

lemma hasValueAt_list_prod {ι : Type*} (l : List ι) (f : ι → RatFunc K) (v : ι → K) {ω : K}
    (h : ∀ i ∈ l, HasValueAt (f i) ω (v i)) :
    HasValueAt (l.map f).prod ω (l.map v).prod := by
  induction l with
  | nil => simpa using hasValueAt_one ω
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons]
    exact (h a (by simp)).mul (ih fun i hi => h i (by simp [hi]))

lemma hasValueAt_finset_sum {ι : Type*} (s : Finset ι) (f : ι → RatFunc K) (v : ι → K) {ω : K}
    (h : ∀ i ∈ s, HasValueAt (f i) ω (v i)) :
    HasValueAt (∑ i ∈ s, f i) ω (∑ i ∈ s, v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hasValueAt_zero ω
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a (by simp)).add (ih fun i hi => h i (by simp [hi]))

lemma HasValueAt.regular {f : RatFunc K} {ω v : K} (h : HasValueAt f ω v) : Regular f ω :=
  ⟨v, h⟩

/-- `X - ω` as a rational function -/
noncomputable abbrev lin (ω : K) : RatFunc K := rf (X - C ω)

lemma hasValueAt_lin (ω : K) : HasValueAt (lin ω) ω 0 := by
  have := hasValueAt_poly (X - C ω) ω
  rwa [eval_sub, eval_X, eval_C, sub_self] at this

/-- A regular function with value `0` at `ω` is `(X - ω)` times a regular function. -/
lemma HasValueAt.eq_lin_mul {f : RatFunc K} {ω : K} (h : HasValueAt f ω 0) :
    ∃ g, Regular g ω ∧ f = lin ω * g := by
  obtain ⟨N, Q, hQ, rfl, h0⟩ := h
  have hN : N.eval ω = 0 := by
    rcases (div_eq_zero_iff.mp h0.symm) with h | h
    · exact h
    · exact absurd h hQ
  have hdvd : X - C ω ∣ N := Polynomial.dvd_iff_isRoot.mpr hN
  obtain ⟨N', rfl⟩ := hdvd
  refine ⟨rf N' / rf Q, ⟨_, N', Q, hQ, rfl, rfl⟩, ?_⟩
  simp [mul_div_assoc]

end RS16
