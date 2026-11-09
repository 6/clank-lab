import ABC.Hand
import ABC.ODE
import ABC.LemmaW

/-!
# Auxiliary facts for the tube construction: coordinates, lattice, orbits

Coordinates on `E 2` and `E 3`, the lattice `2πℤ³`, the orbit `Γ ξ` through a point, and
mean-value estimates for the height `z` along an orbit.
-/

open Set Metric Real

noncomputable section

namespace ABC

/-! ### Coordinates -/

/-- The projection `(x, y, z) ↦ (x, y)`. -/
def proj (x : E 3) : E 2 := !₂[x 0, x 1]

/-- The lattice vector `2π (m, n, k)`. -/
def latt (m n k : ℤ) : E 3 := !₂[2 * π * m, 2 * π * n, 2 * π * k]

/-- The lattice `2πℤ³`. -/
def Lat : Set (E 3) := {v | ∃ m n k : ℤ, v = latt m n k}

@[simp] lemma lift_apply_zero (a : E 2) (c : ℝ) : lift a c 0 = a 0 := by simp [lift]
@[simp] lemma lift_apply_one (a : E 2) (c : ℝ) : lift a c 1 = a 1 := by simp [lift]
@[simp] lemma lift_apply_two (a : E 2) (c : ℝ) : lift a c 2 = c := by simp [lift]
@[simp] lemma proj_apply_zero (x : E 3) : proj x 0 = x 0 := by simp [proj]
@[simp] lemma proj_apply_one (x : E 3) : proj x 1 = x 1 := by simp [proj]
@[simp] lemma latt_apply_zero (m n k : ℤ) : latt m n k 0 = 2 * π * m := by simp [latt]
@[simp] lemma latt_apply_one (m n k : ℤ) : latt m n k 1 = 2 * π * n := by simp [latt]
@[simp] lemma latt_apply_two (m n k : ℤ) : latt m n k 2 = 2 * π * k := by simp [latt]

lemma ext3 {x y : E 3} (h0 : x 0 = y 0) (h1 : x 1 = y 1) (h2 : x 2 = y 2) : x = y := by
  ext i; fin_cases i <;> simpa

lemma ext2 {x y : E 2} (h0 : x 0 = y 0) (h1 : x 1 = y 1) : x = y := by
  ext i; fin_cases i <;> simpa

lemma lift_proj {x : E 3} {c : ℝ} (h : x 2 = c) : lift (proj x) c = x :=
  ext3 (by simp) (by simp) (by simp [h])

lemma proj_lift (a : E 2) (c : ℝ) : proj (lift a c) = a := ext2 (by simp) (by simp)

lemma lift_add_latt (a : E 2) (c : ℝ) (m n k : ℤ) :
    lift a c + latt m n k = lift (a + proj (latt m n k)) (c + 2 * π * k) :=
  ext3 (by simp) (by simp) (by simp)

lemma lift_inj {a b : E 2} {c d : ℝ} (h : lift a c = lift b d) : a = b ∧ c = d := by
  refine ⟨ext2 ?_ ?_, ?_⟩
  · simpa using congrArg (fun x : E 3 => x 0) h
  · simpa using congrArg (fun x : E 3 => x 1) h
  · simpa using congrArg (fun x : E 3 => x 2) h

lemma dist_eq3 (x y : E 3) :
    dist x y = √((x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 + (x 2 - y 2) ^ 2) := by
  rw [EuclideanSpace.dist_eq]; simp [Fin.sum_univ_three, Real.dist_eq, sq_abs]

lemma dist_eq2 (x y : E 2) : dist x y = √((x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2) := by
  rw [EuclideanSpace.dist_eq]; simp [Fin.sum_univ_two, Real.dist_eq, sq_abs]

lemma norm_eq3 (x : E 3) : ‖x‖ = √(x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2) := by
  rw [← dist_zero_right, dist_eq3]; simp

lemma abs_sub_le_dist3 (x y : E 3) (i : Fin 3) : |x i - y i| ≤ dist x y := by
  rw [dist_eq3, ← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_le_sqrt
  fin_cases i <;> simp <;> nlinarith [sq_nonneg (x 0 - y 0), sq_nonneg (x 1 - y 1),
    sq_nonneg (x 2 - y 2)]

lemma abs_sub_le_dist2 (x y : E 2) (i : Fin 2) : |x i - y i| ≤ dist x y := by
  rw [dist_eq2, ← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_le_sqrt
  fin_cases i <;> simp <;> nlinarith [sq_nonneg (x 0 - y 0), sq_nonneg (x 1 - y 1)]

lemma dist_lift (a b : E 2) (c : ℝ) : dist (lift a c) (lift b c) = dist a b := by
  rw [dist_eq3, dist_eq2]; simp

lemma dist_proj_le (x y : E 3) : dist (proj x) (proj y) ≤ dist x y := by
  rw [dist_eq3, dist_eq2]
  apply Real.sqrt_le_sqrt
  simp only [proj_apply_zero, proj_apply_one]
  nlinarith [sq_nonneg (x 2 - y 2)]

/-! ### The lattice -/

lemma latt_add (m n k m' n' k' : ℤ) :
    latt m n k + latt m' n' k' = latt (m + m') (n + n') (k + k') :=
  ext3 (by simp; ring) (by simp; ring) (by simp; ring)

lemma latt_neg (m n k : ℤ) : -latt m n k = latt (-m) (-n) (-k) :=
  ext3 (by simp) (by simp) (by simp)

lemma zero_mem_Lat : (0 : E 3) ∈ Lat := ⟨0, 0, 0, ext3 (by simp) (by simp) (by simp)⟩

lemma add_mem_Lat {u v : E 3} (hu : u ∈ Lat) (hv : v ∈ Lat) : u + v ∈ Lat := by
  obtain ⟨m, n, k, rfl⟩ := hu
  obtain ⟨m', n', k', rfl⟩ := hv
  exact ⟨_, _, _, latt_add _ _ _ _ _ _⟩

lemma neg_mem_Lat {u : E 3} (hu : u ∈ Lat) : -u ∈ Lat := by
  obtain ⟨m, n, k, rfl⟩ := hu
  exact ⟨_, _, _, latt_neg _ _ _⟩

lemma sub_mem_Lat {u v : E 3} (hu : u ∈ Lat) (hv : v ∈ Lat) : u - v ∈ Lat := by
  rw [sub_eq_add_neg]; exact add_mem_Lat hu (neg_mem_Lat hv)

lemma latt_mem_Lat (m n k : ℤ) : latt m n k ∈ Lat := ⟨m, n, k, rfl⟩

lemma smul_ev_mem_Lat (i : Fin 3) : (2 * π) • ev i ∈ Lat := by
  fin_cases i
  · exact ⟨1, 0, 0, ext3 (by simp) (by simp) (by simp)⟩
  · exact ⟨0, 1, 0, ext3 (by simp) (by simp) (by simp)⟩
  · exact ⟨0, 0, 1, ext3 (by simp) (by simp) (by simp)⟩

/-- Two points of `ball p 1` that differ by a lattice vector in `x, y` coincide. -/
lemma eq_of_near {p a b : E 2} (ha : dist a p < 1) (hb : dist b p < 1) {m n : ℤ}
    (h : b = a + proj (latt m n 0)) : b = a := by
  have hab : dist b a < 2 := by
    calc dist b a ≤ dist b p + dist a p := dist_triangle_right _ _ _
      _ < 2 := by linarith
  have h0 := abs_sub_le_dist2 b a 0
  have h1 := abs_sub_le_dist2 b a 1
  rw [h] at h0 h1 hab
  have e0 : (a + proj (latt m n 0)) 0 - a 0 = 2 * π * m := by simp [proj]
  have e1 : (a + proj (latt m n 0)) 1 - a 1 = 2 * π * n := by simp [proj]
  rw [e0] at h0
  rw [e1] at h1
  have hpi := Real.pi_gt_three
  have hm : m = 0 := by
    by_contra hm
    have : (1 : ℝ) ≤ |(m : ℝ)| := by exact_mod_cast Int.one_le_abs hm
    have : |2 * π * m| < 2 := lt_of_le_of_lt h0 hab
    rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * π)] at this
    nlinarith
  have hn : n = 0 := by
    by_contra hn
    have : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn
    have : |2 * π * n| < 2 := lt_of_le_of_lt h1 hab
    rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * π)] at this
    nlinarith
  rw [h, hm, hn]; apply ext2 <;> simp [latt, proj]

/-! ### The field -/

lemma abcField_apply_two (x : E 3) : abcField x 2 = Real.sin (x 1) + Real.cos (x 0) := by
  simp [abcField]

lemma abs_abcField_le (x : E 3) (i : Fin 3) : |abcField x i| ≤ 2 := by
  fin_cases i <;> simp [abcField] <;> rw [abs_le] <;> constructor <;>
    linarith [Real.sin_le_one (x 0), Real.sin_le_one (x 1), Real.sin_le_one (x 2),
      Real.cos_le_one (x 0), Real.cos_le_one (x 1), Real.cos_le_one (x 2),
      Real.neg_one_le_sin (x 0), Real.neg_one_le_sin (x 1), Real.neg_one_le_sin (x 2),
      Real.neg_one_le_cos (x 0), Real.neg_one_le_cos (x 1), Real.neg_one_le_cos (x 2)]

lemma norm_abcField_le (x : E 3) : ‖abcField x‖ ≤ 4 := by
  rw [norm_eq3]
  have h0 := abs_abcField_le x 0
  have h1 := abs_abcField_le x 1
  have h2 := abs_abcField_le x 2
  rw [Real.sqrt_le_left (by norm_num)]
  have e0 : (abcField x 0) ^ 2 ≤ 4 := by nlinarith [abs_nonneg (abcField x 0), sq_abs (abcField x 0)]
  have e1 : (abcField x 1) ^ 2 ≤ 4 := by nlinarith [abs_nonneg (abcField x 1), sq_abs (abcField x 1)]
  have e2 : (abcField x 2) ^ 2 ≤ 4 := by nlinarith [abs_nonneg (abcField x 2), sq_abs (abcField x 2)]
  linarith

lemma abcField_two_lip (x y : E 3) : |abcField x 2 - abcField y 2| ≤ 3 * dist x y :=
  (abs_sub_le_dist3 _ _ 2).trans (abcField_lipschitz.dist_le_mul x y)

lemma abcField_add_Lat (x : E 3) {v : E 3} (hv : v ∈ Lat) : abcField (x + v) = abcField x := by
  obtain ⟨m, n, k, rfl⟩ := hv
  have hs : ∀ (u : ℝ) (j : ℤ), Real.sin (u + 2 * π * j) = Real.sin u := fun u j => by
    rw [show 2 * π * j = (j : ℝ) * (2 * π) by ring]; exact Real.sin_add_int_mul_two_pi u j
  have hc : ∀ (u : ℝ) (j : ℤ), Real.cos (u + 2 * π * j) = Real.cos u := fun u j => by
    rw [show 2 * π * j = (j : ℝ) * (2 * π) by ring]; exact Real.cos_add_int_mul_two_pi u j
  apply ext3 <;> simp [abcField, hs, hc]

/-! ### Orbits -/

/-- The orbit through `ξ` at time `0`. -/
def Γ (ξ : E 3) : ℝ → E 3 := (exists_orbit ξ).choose

lemma Γ_orbit (ξ : E 3) : IsOrbit (Γ ξ) := (exists_orbit ξ).choose_spec.1

@[simp] lemma Γ_zero (ξ : E 3) : Γ ξ 0 = ξ := (exists_orbit ξ).choose_spec.2

lemma Γ_eq {γ : ℝ → E 3} (hγ : IsOrbit γ) {ξ : E 3} (h : γ 0 = ξ) : Γ ξ = γ :=
  orbit_unique (Γ_orbit ξ) hγ (t₀ := 0) (by rw [Γ_zero, h])

lemma Γ_shift {γ : ℝ → E 3} (hγ : IsOrbit γ) (t : ℝ) : Γ (γ t) = fun s => γ (s + t) :=
  Γ_eq (isOrbit_comp_add hγ t) (by simp)

lemma Γ_Γ (ξ : E 3) (t : ℝ) : Γ (Γ ξ t) = fun s => Γ ξ (s + t) := Γ_shift (Γ_orbit ξ) t

lemma isOrbit_add_Lat {γ : ℝ → E 3} (hγ : IsOrbit γ) {v : E 3} (hv : v ∈ Lat) :
    IsOrbit (fun t => γ t + v) := by
  obtain ⟨m, n, k, rfl⟩ := hv
  have h1 := isOrbit_add_lattice (isOrbit_add_lattice (isOrbit_add_lattice hγ 0 m) 1 n) 2 k
  have : latt m n k = (2 * π * m) • ev (0 : Fin 3) + (2 * π * n) • ev (1 : Fin 3) +
      (2 * π * k) • ev (2 : Fin 3) := ext3 (by simp) (by simp) (by simp)
  rw [this]
  simpa only [add_assoc] using h1

lemma Γ_add_Lat (ξ : E 3) {v : E 3} (hv : v ∈ Lat) : Γ (ξ + v) = fun s => Γ ξ s + v :=
  Γ_eq (isOrbit_add_Lat (Γ_orbit ξ) hv) (by simp)

lemma hasDerivAt_z {γ : ℝ → E 3} (hγ : IsOrbit γ) (t : ℝ) :
    HasDerivAt (fun s => γ s 2) (abcField (γ t) 2) t :=
  (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).hasFDerivAt.comp_hasDerivAt t (hγ t)

lemma orbit_continuous {γ : ℝ → E 3} (hγ : IsOrbit γ) : Continuous γ :=
  continuous_iff_continuousAt.2 fun t => (hγ t).continuousAt

lemma orbit_lip {γ : ℝ → E 3} (hγ : IsOrbit γ) (s t : ℝ) : dist (γ s) (γ t) ≤ 4 * dist s t := by
  have : LipschitzWith 4 γ := by
    apply lipschitzWith_of_nnnorm_deriv_le (fun t => (hγ t).differentiableAt)
    intro x
    rw [(hγ x).deriv, ← NNReal.coe_le_coe, coe_nnnorm]
    exact norm_abcField_le _
  simpa using this.dist_le_mul s t

lemma z_lip {γ : ℝ → E 3} (hγ : IsOrbit γ) (s t : ℝ) : |γ s 2 - γ t 2| ≤ 2 * |s - t| := by
  have : LipschitzWith 2 (fun s => γ s 2) := by
    apply lipschitzWith_of_nnnorm_deriv_le (fun t => (hasDerivAt_z hγ t).differentiableAt)
    intro x
    rw [(hasDerivAt_z hγ x).deriv, ← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs]
    exact abs_abcField_le _ 2
  simpa [Real.dist_eq] using this.dist_le_mul s t

/-- Mean-value lower bound for the height on an interval where `V_z ≥ c`. -/
lemma z_lower {γ : ℝ → E 3} (hγ : IsOrbit γ) {u v c : ℝ}
    (hc : ∀ t ∈ Icc u v, c ≤ abcField (γ t) 2) {x y : ℝ} (hx : x ∈ Icc u v) (hy : y ∈ Icc u v)
    (hxy : x ≤ y) : c * (y - x) ≤ γ y 2 - γ x 2 := by
  apply (convex_Icc u v).mul_sub_le_image_sub_of_le_deriv
    (fun t _ => (hasDerivAt_z hγ t).continuousAt.continuousWithinAt)
    (fun t _ => (hasDerivAt_z hγ t).differentiableAt.differentiableWithinAt)
    _ x hx y hy hxy
  intro t ht
  rw [(hasDerivAt_z hγ t).deriv]
  exact hc t (interior_subset ht)

/-- Gronwall, centred at time `t₀`. -/
lemma orbit_dist_le' {γ₁ γ₂ : ℝ → E 3} (h₁ : IsOrbit γ₁) (h₂ : IsOrbit γ₂) (t₀ t : ℝ) :
    dist (γ₁ t) (γ₂ t) ≤ dist (γ₁ t₀) (γ₂ t₀) * Real.exp (3 * |t - t₀|) := by
  have := orbit_dist_le (isOrbit_comp_add h₁ t₀) (isOrbit_comp_add h₂ t₀) (t - t₀)
  simpa using this

end ABC
