import ABC.S4.R3AuxS3

/-! R3 auxiliaries: the cubic and quartic homological equations in the `z = w₀ + i w₁` basis,
and their shear generators. -/

open Set Metric Filter Topology Asymptotics ComplexConjugate Real

noncomputable section

namespace ABC.S4.R3Aux

open ABC.S4

/-! ### Linear combinations of coefficient functions -/

def lc4 (c0 c1 c2 c3 : ℂ) (g0 g1 g2 g3 : ℂ → ℂ) (t : ℂ) : ℂ :=
  c0 * g0 t + c1 * g1 t + c2 * g2 t + c3 * g3 t

def lc5 (c0 c1 c2 c3 c4 : ℂ) (g0 g1 g2 g3 g4 : ℂ → ℂ) (t : ℂ) : ℂ :=
  c0 * g0 t + c1 * g1 t + c2 * g2 t + c3 * g3 t + c4 * g4 t

theorem HolPer.add {f g : ℂ → ℂ} {s : ℝ} (hf : HolPer f s) (hg : HolPer g s) :
    HolPer (fun t => f t + g t) s := by
  obtain ⟨B, hB⟩ := hf.bdd
  obtain ⟨B', hB'⟩ := hg.bdd
  refine ⟨hf.holo.add hg.holo, fun t => by simp [hf.per, hg.per], B + B', fun t ht => ?_⟩
  exact (norm_add_le _ _).trans (add_le_add (hB t ht) (hB' t ht))

theorem HolPer.const_mul {g : ℂ → ℂ} {s : ℝ} (c : ℂ) (hg : HolPer g s) :
    HolPer (fun t => c * g t) s := by
  obtain ⟨B, hB⟩ := hg.bdd
  refine ⟨hg.holo.const_mul c, fun t => by simp [hg.per], ‖c‖ * B, fun t ht => ?_⟩
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hB t ht) (norm_nonneg _)

theorem HolPer.lc4 {g0 g1 g2 g3 : ℂ → ℂ} {s : ℝ} (c0 c1 c2 c3 : ℂ) (h0 : HolPer g0 s)
    (h1 : HolPer g1 s) (h2 : HolPer g2 s) (h3 : HolPer g3 s) :
    HolPer (lc4 c0 c1 c2 c3 g0 g1 g2 g3) s :=
  (((h0.const_mul c0).add (h1.const_mul c1)).add (h2.const_mul c2)).add (h3.const_mul c3)

theorem HolPer.lc5 {g0 g1 g2 g3 g4 : ℂ → ℂ} {s : ℝ} (c0 c1 c2 c3 c4 : ℂ) (h0 : HolPer g0 s)
    (h1 : HolPer g1 s) (h2 : HolPer g2 s) (h3 : HolPer g3 s) (h4 : HolPer g4 s) :
    HolPer (lc5 c0 c1 c2 c3 c4 g0 g1 g2 g3 g4) s :=
  ((((h0.const_mul c0).add (h1.const_mul c1)).add (h2.const_mul c2)).add
    (h3.const_mul c3)).add (h4.const_mul c4)

theorem hasDerivAt_lc4 {g0 g1 g2 g3 : ℂ → ℂ} {d0 d1 d2 d3 t : ℂ} (c0 c1 c2 c3 : ℂ)
    (h0 : HasDerivAt g0 d0 t) (h1 : HasDerivAt g1 d1 t) (h2 : HasDerivAt g2 d2 t)
    (h3 : HasDerivAt g3 d3 t) :
    HasDerivAt (lc4 c0 c1 c2 c3 g0 g1 g2 g3) (c0 * d0 + c1 * d1 + c2 * d2 + c3 * d3) t :=
  (((h0.const_mul c0).add (h1.const_mul c1)).add (h2.const_mul c2)).add (h3.const_mul c3)

theorem hasDerivAt_lc5 {g0 g1 g2 g3 g4 : ℂ → ℂ} {d0 d1 d2 d3 d4 t : ℂ} (c0 c1 c2 c3 c4 : ℂ)
    (h0 : HasDerivAt g0 d0 t) (h1 : HasDerivAt g1 d1 t) (h2 : HasDerivAt g2 d2 t)
    (h3 : HasDerivAt g3 d3 t) (h4 : HasDerivAt g4 d4 t) :
    HasDerivAt (lc5 c0 c1 c2 c3 c4 g0 g1 g2 g3 g4)
      (c0 * d0 + c1 * d1 + c2 * d2 + c3 * d3 + c4 * d4) t :=
  ((((h0.const_mul c0).add (h1.const_mul c1)).add (h2.const_mul c2)).add
    (h3.const_mul c3)).add (h4.const_mul c4)

/-- holomorphic, periodic, bounded, with bounded derivative -/
structure DHolPer (f : ℂ → ℂ) (s : ℝ) : Prop extends HolPer f s where
  dbdd : ∃ B, ∀ t ∈ strip s, ‖deriv f t‖ ≤ B

theorem isOpen_strip (s : ℝ) : IsOpen (strip s) :=
  isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const

theorem HolPer.hasDerivAt {f : ℂ → ℂ} {s : ℝ} (hf : HolPer f s) {t : ℂ} (ht : t ∈ strip s) :
    HasDerivAt f (deriv f t) t :=
  ((hf.holo t ht).differentiableAt ((isOpen_strip s).mem_nhds ht)).hasDerivAt

theorem DHolPer.lc4 {g0 g1 g2 g3 : ℂ → ℂ} {s : ℝ} (c0 c1 c2 c3 : ℂ) (h0 : DHolPer g0 s)
    (h1 : DHolPer g1 s) (h2 : DHolPer g2 s) (h3 : DHolPer g3 s) :
    DHolPer (lc4 c0 c1 c2 c3 g0 g1 g2 g3) s := by
  refine ⟨HolPer.lc4 c0 c1 c2 c3 h0.1 h1.1 h2.1 h3.1, ?_⟩
  obtain ⟨B0, hB0⟩ := h0.dbdd
  obtain ⟨B1, hB1⟩ := h1.dbdd
  obtain ⟨B2, hB2⟩ := h2.dbdd
  obtain ⟨B3, hB3⟩ := h3.dbdd
  refine ⟨‖c0‖ * B0 + ‖c1‖ * B1 + ‖c2‖ * B2 + ‖c3‖ * B3, fun t ht => ?_⟩
  rw [(hasDerivAt_lc4 c0 c1 c2 c3 (h0.1.hasDerivAt ht) (h1.1.hasDerivAt ht)
    (h2.1.hasDerivAt ht) (h3.1.hasDerivAt ht)).deriv]
  refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_)) ?_) <;>
    rw [norm_mul] <;> gcongr <;> [exact hB0 t ht; exact hB1 t ht; exact hB2 t ht; exact hB3 t ht]

theorem DHolPer.lc5 {g0 g1 g2 g3 g4 : ℂ → ℂ} {s : ℝ} (c0 c1 c2 c3 c4 : ℂ) (h0 : DHolPer g0 s)
    (h1 : DHolPer g1 s) (h2 : DHolPer g2 s) (h3 : DHolPer g3 s) (h4 : DHolPer g4 s) :
    DHolPer (lc5 c0 c1 c2 c3 c4 g0 g1 g2 g3 g4) s := by
  refine ⟨HolPer.lc5 c0 c1 c2 c3 c4 h0.1 h1.1 h2.1 h3.1 h4.1, ?_⟩
  obtain ⟨B0, hB0⟩ := h0.dbdd
  obtain ⟨B1, hB1⟩ := h1.dbdd
  obtain ⟨B2, hB2⟩ := h2.dbdd
  obtain ⟨B3, hB3⟩ := h3.dbdd
  obtain ⟨B4, hB4⟩ := h4.dbdd
  refine ⟨‖c0‖ * B0 + ‖c1‖ * B1 + ‖c2‖ * B2 + ‖c3‖ * B3 + ‖c4‖ * B4, fun t ht => ?_⟩
  rw [(hasDerivAt_lc5 c0 c1 c2 c3 c4 (h0.1.hasDerivAt ht) (h1.1.hasDerivAt ht)
    (h2.1.hasDerivAt ht) (h3.1.hasDerivAt ht) (h4.1.hasDerivAt ht)).deriv]
  refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_)) ?_))
    ?_) <;> rw [norm_mul] <;> gcongr <;>
    [exact hB0 t ht; exact hB1 t ht; exact hB2 t ht; exact hB3 t ht; exact hB4 t ht]

theorem solK_dholPer {κ : ℝ} (hκ : ∀ m : ℤ, κ ≠ m) {g : ℂ → ℂ} {s : ℝ} (hs : 0 < s)
    (hg : HolPer g s) : DHolPer (solK κ g) s := by
  obtain ⟨h1, h2⟩ := solK_spec hκ hs hg
  obtain ⟨B, hB⟩ := hg.bdd
  obtain ⟨B', hB'⟩ := h1.bdd
  refine ⟨h1, B + ‖Complex.I * κ‖ * B', fun t ht => ?_⟩
  rw [(h2 t ht).deriv]
  refine (norm_sub_le _ _).trans (add_le_add (hB t ht) ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hB' t ht) (norm_nonneg _)

theorem sol0_dholPer {g : ℂ → ℂ} {s : ℝ} (hs : 0 < s) (hg : HolPer g s) :
    DHolPer (sol0 g) s := by
  obtain ⟨h1, h2⟩ := sol0_spec hs hg
  obtain ⟨B, hB⟩ := hg.bdd
  refine ⟨h1, B + ‖avg g‖, fun t ht => ?_⟩
  rw [(h2 t ht).deriv]
  exact (norm_sub_le _ _).trans (add_le_add (hB t ht) le_rfl)

/-! ### Reality of conjugate-symmetric combinations -/

theorem lc4_conj_of_real {g0 g1 g2 g3 : ℂ → ℂ} (c0 c1 c2 c3 : ℂ) {x : ℂ} (h0 : (g0 x).im = 0)
    (h1 : (g1 x).im = 0) (h2 : (g2 x).im = 0) (h3 : (g3 x).im = 0) :
    conj (lc4 c0 c1 c2 c3 g0 g1 g2 g3 x) = lc4 (conj c0) (conj c1) (conj c2) (conj c3) g0 g1 g2 g3 x := by
  simp only [lc4, map_add, map_mul, Complex.conj_eq_iff_im.2 h0, Complex.conj_eq_iff_im.2 h1,
    Complex.conj_eq_iff_im.2 h2, Complex.conj_eq_iff_im.2 h3]

theorem lc5_conj_of_real {g0 g1 g2 g3 g4 : ℂ → ℂ} (c0 c1 c2 c3 c4 : ℂ) {x : ℂ}
    (h0 : (g0 x).im = 0) (h1 : (g1 x).im = 0) (h2 : (g2 x).im = 0) (h3 : (g3 x).im = 0)
    (h4 : (g4 x).im = 0) :
    conj (lc5 c0 c1 c2 c3 c4 g0 g1 g2 g3 g4 x) =
      lc5 (conj c0) (conj c1) (conj c2) (conj c3) (conj c4) g0 g1 g2 g3 g4 x := by
  simp only [lc5, map_add, map_mul, Complex.conj_eq_iff_im.2 h0, Complex.conj_eq_iff_im.2 h1,
    Complex.conj_eq_iff_im.2 h2, Complex.conj_eq_iff_im.2 h3, Complex.conj_eq_iff_im.2 h4]

theorem lc4_real_of_sym {g0 g1 g2 g3 : ℂ → ℂ} (c0 c1 : ℂ) {x : ℂ}
    (h03 : conj (g0 x) = g3 x) (h12 : conj (g1 x) = g2 x) :
    (lc4 c0 c1 (conj c1) (conj c0) g0 g1 g2 g3 x).im = 0 := by
  rw [← Complex.conj_eq_iff_im]
  have h30 : conj (g3 x) = g0 x := by rw [← h03, Complex.conj_conj]
  have h21 : conj (g2 x) = g1 x := by rw [← h12, Complex.conj_conj]
  simp only [lc4, map_add, map_mul, Complex.conj_conj, h03, h12, h30, h21]
  ring

theorem lc5_real_of_sym {g0 g1 g2 g3 g4 : ℂ → ℂ} (c0 c1 : ℂ) (c2 : ℝ) {x : ℂ}
    (h04 : conj (g0 x) = g4 x) (h13 : conj (g1 x) = g3 x) (h2 : (g2 x).im = 0) :
    (lc5 c0 c1 c2 (conj c1) (conj c0) g0 g1 g2 g3 g4 x).im = 0 := by
  rw [← Complex.conj_eq_iff_im]
  have h40 : conj (g4 x) = g0 x := by rw [← h04, Complex.conj_conj]
  have h31 : conj (g3 x) = g1 x := by rw [← h13, Complex.conj_conj]
  simp only [lc5, map_add, map_mul, Complex.conj_conj, h04, h13, h40, h31,
    Complex.conj_eq_iff_im.2 h2, Complex.conj_ofReal]
  ring


/-! ### The cubic step -/

open Complex in
/-- `z`-basis coefficients of the cubic part `∑ a m n w₀^m w₁^n`, `m + n = 3` -/
def pc0 (a : ℕ → ℕ → ℂ → ℂ) := lc4 (I / 8) (-1 / 8) (-I / 8) (1 / 8) (a 0 3) (a 1 2) (a 2 1) (a 3 0)
open Complex in
def pc1 (a : ℕ → ℕ → ℂ → ℂ) := lc4 (-3 * I / 8) (1 / 8) (-I / 8) (3 / 8) (a 0 3) (a 1 2) (a 2 1) (a 3 0)
open Complex in
def pc2 (a : ℕ → ℕ → ℂ → ℂ) := lc4 (3 * I / 8) (1 / 8) (I / 8) (3 / 8) (a 0 3) (a 1 2) (a 2 1) (a 3 0)
open Complex in
def pc3 (a : ℕ → ℕ → ℂ → ℂ) := lc4 (-I / 8) (-1 / 8) (I / 8) (1 / 8) (a 0 3) (a 1 2) (a 2 1) (a 3 0)

def fc0 (ν : ℝ) (a : ℕ → ℕ → ℂ → ℂ) := solK (-3 * ν) (pc0 a)
def fc1 (ν : ℝ) (a : ℕ → ℕ → ℂ → ℂ) := solK (-ν) (pc1 a)
def fc2 (ν : ℝ) (a : ℕ → ℕ → ℂ → ℂ) := solK ν (pc2 a)
def fc3 (ν : ℝ) (a : ℕ → ℕ → ℂ → ℂ) := solK (3 * ν) (pc3 a)

/-- shear coefficients: `∑ cᵢ ℓᵢ³ = ∑ fⱼ z^(3-j) z̄^j` -/
def cc0 (ν : ℝ) (a : ℕ → ℕ → ℂ → ℂ) :=
  lc4 2 (2 / 3) (2 / 3) 2 (fc0 ν a) (fc1 ν a) (fc2 ν a) (fc3 ν a)
open Complex in
def cc1 (ν : ℝ) (a : ℕ → ℕ → ℂ → ℂ) :=
  lc4 (-2 * I) (2 * I / 3) (-2 * I / 3) (2 * I) (fc0 ν a) (fc1 ν a) (fc2 ν a) (fc3 ν a)
open Complex in
def cc2 (ν : ℝ) (a : ℕ → ℕ → ℂ → ℂ) :=
  lc4 ((-1 + I) / 2) ((1 + I) / 6) ((1 - I) / 6) ((-1 - I) / 2) (fc0 ν a) (fc1 ν a) (fc2 ν a) (fc3 ν a)
open Complex in
def cc3 (ν : ℝ) (a : ℕ → ℕ → ℂ → ℂ) :=
  lc4 ((-1 - I) / 2) ((1 - I) / 6) ((1 + I) / 6) ((-1 + I) / 2) (fc0 ν a) (fc1 ν a) (fc2 ν a) (fc3 ν a)

def uc0 : Fin 2 → ℝ := ![1, 0]
def uc1 : Fin 2 → ℝ := ![0, 1]
def uc2 : Fin 2 → ℝ := ![1, 1]
def uc3 : Fin 2 → ℝ := ![1, -1]

/-- the cubic part `∑_{m+n=3} a m n w₀^m w₁^n` -/
def P3 (a : ℕ → ℕ → ℂ → ℂ) (w : C2) (t : ℂ) : ℂ :=
  a 3 0 t * w 0 ^ 3 + a 2 1 t * w 0 ^ 2 * w 1 + a 1 2 t * w 0 * w 1 ^ 2 + a 0 3 t * w 1 ^ 3

theorem nonres_ne {ν : ℝ} (hnr : NonRes4 ν) {q : ℝ} (hq : q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨
    q = -1 ∨ q = -2 ∨ q = -3 ∨ q = -4) : ∀ m : ℤ, q * ν ≠ m := by
  intro m h
  rcases hq with h' | h' | h' | h' | h' | h' | h' | h' <;> subst h'
  · exact hnr 1 le_rfl (by norm_num) m (by simpa using h)
  · exact hnr 2 (by norm_num) (by norm_num) m (by simpa using h)
  · exact hnr 3 (by norm_num) (by norm_num) m (by simpa using h)
  · exact hnr 4 (by norm_num) (by norm_num) m (by simpa using h)
  · exact hnr 1 le_rfl (by norm_num) (-m) (by push_cast; linarith)
  · exact hnr 2 (by norm_num) (by norm_num) (-m) (by push_cast; linarith)
  · exact hnr 3 (by norm_num) (by norm_num) (-m) (by push_cast; linarith)
  · exact hnr 4 (by norm_num) (by norm_num) (-m) (by push_cast; linarith)

section cubic

variable {a : ℕ → ℕ → ℂ → ℂ} {ν s : ℝ}

theorem pc_holPer (ha : ∀ m n, HolPer (a m n) s) :
    HolPer (pc0 a) s ∧ HolPer (pc1 a) s ∧ HolPer (pc2 a) s ∧ HolPer (pc3 a) s :=
  ⟨HolPer.lc4 _ _ _ _ (ha 0 3) (ha 1 2) (ha 2 1) (ha 3 0),
    HolPer.lc4 _ _ _ _ (ha 0 3) (ha 1 2) (ha 2 1) (ha 3 0),
    HolPer.lc4 _ _ _ _ (ha 0 3) (ha 1 2) (ha 2 1) (ha 3 0),
    HolPer.lc4 _ _ _ _ (ha 0 3) (ha 1 2) (ha 2 1) (ha 3 0)⟩

theorem fc_dholPer (hs : 0 < s) (hnr : NonRes4 ν) (ha : ∀ m n, HolPer (a m n) s) :
    DHolPer (fc0 ν a) s ∧ DHolPer (fc1 ν a) s ∧ DHolPer (fc2 ν a) s ∧ DHolPer (fc3 ν a) s := by
  obtain ⟨h0, h1, h2, h3⟩ := pc_holPer ha
  refine ⟨solK_dholPer ?_ hs h0, solK_dholPer ?_ hs h1, solK_dholPer ?_ hs h2,
    solK_dholPer ?_ hs h3⟩
  · simpa using nonres_ne hnr (q := -3) (by norm_num)
  · simpa using nonres_ne hnr (q := -1) (by norm_num)
  · simpa using nonres_ne hnr (q := 1) (by norm_num)
  · simpa using nonres_ne hnr (q := 3) (by norm_num)

theorem fc_hasDerivAt (hs : 0 < s) (hnr : NonRes4 ν) (ha : ∀ m n, HolPer (a m n) s) {t : ℂ}
    (ht : t ∈ strip s) :
    HasDerivAt (fc0 ν a) (pc0 a t - Complex.I * (-3 * ν) * fc0 ν a t) t ∧
    HasDerivAt (fc1 ν a) (pc1 a t - Complex.I * (-ν) * fc1 ν a t) t ∧
    HasDerivAt (fc2 ν a) (pc2 a t - Complex.I * ν * fc2 ν a t) t ∧
    HasDerivAt (fc3 ν a) (pc3 a t - Complex.I * (3 * ν) * fc3 ν a t) t := by
  obtain ⟨h0, h1, h2, h3⟩ := pc_holPer ha
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := (solK_spec (by simpa using nonres_ne hnr (q := -3) (by norm_num)) hs h0).2 t ht
    simpa [fc0] using this
  · have := (solK_spec (by simpa using nonres_ne hnr (q := -1) (by norm_num)) hs h1).2 t ht
    simpa [fc1] using this
  · exact (solK_spec (by simpa using nonres_ne hnr (q := 1) (by norm_num)) hs h2).2 t ht
  · have := (solK_spec (by simpa using nonres_ne hnr (q := 3) (by norm_num)) hs h3).2 t ht
    simpa [fc3] using this

theorem cubic_ident (hs : 0 < s) (hnr : NonRes4 ν) (ha : ∀ m n, HolPer (a m n) s) {t : ℂ}
    (ht : t ∈ strip s) (w : C2) :
    P3 a w t + shX 3 uc0 (cc0 ν a) ν w t + shX 3 uc1 (cc1 ν a) ν w t +
      shX 3 uc2 (cc2 ν a) ν w t + shX 3 uc3 (cc3 ν a) ν w t = 0 := by
  obtain ⟨d0, d1, d2, d3⟩ := fc_hasDerivAt hs hnr ha ht
  have e0 := (hasDerivAt_lc4 2 (2 / 3) (2 / 3) 2 d0 d1 d2 d3).deriv
  have e1 := (hasDerivAt_lc4 (-2 * Complex.I) (2 * Complex.I / 3) (-2 * Complex.I / 3)
    (2 * Complex.I) d0 d1 d2 d3).deriv
  have e2 := (hasDerivAt_lc4 ((-1 + Complex.I) / 2) ((1 + Complex.I) / 6) ((1 - Complex.I) / 6)
    ((-1 - Complex.I) / 2) d0 d1 d2 d3).deriv
  have e3 := (hasDerivAt_lc4 ((-1 - Complex.I) / 2) ((1 - Complex.I) / 6) ((1 + Complex.I) / 6)
    ((-1 + Complex.I) / 2) d0 d1 d2 d3).deriv
  simp only [shX, cc0, cc1, cc2, cc3, e0, e1, e2, e3]
  simp only [lc4, pc0, pc1, pc2, pc3, P3, lin, uc0, uc1, uc2, uc3]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Complex.ofReal_one,
    Complex.ofReal_zero, Complex.ofReal_neg,
    Nat.cast_ofNat]
  norm_num
  linear_combination ((a 0 3 t)*(w 1)^3 + (a 2 1 t)*(w 0)^2*(w 1) - 9*(fc0 ν a t)*(ν:ℂ)*(w 0)^2*(w 1) + 3*(fc0 ν a t)*(ν:ℂ)*(w 1)^3 - (fc1 ν a t)*(ν:ℂ)*(w 0)^2*(w 1) - (fc1 ν a t)*(ν:ℂ)*(w 1)^3 - (fc2 ν a t)*(ν:ℂ)*(w 0)^2*(w 1) - (fc2 ν a t)*(ν:ℂ)*(w 1)^3 - 9*(fc3 ν a t)*(ν:ℂ)*(w 0)^2*(w 1) + 3*(fc3 ν a t)*(ν:ℂ)*(w 1)^3) * Complex.I_sq

end cubic

theorem lc4_real_of_sym' {g0 g1 g2 g3 : ℂ → ℂ} {c0 c1 c2 c3 : ℂ} (hc2 : c2 = conj c1)
    (hc3 : c3 = conj c0) {x : ℂ} (h03 : conj (g0 x) = g3 x) (h12 : conj (g1 x) = g2 x) :
    (lc4 c0 c1 c2 c3 g0 g1 g2 g3 x).im = 0 := by
  subst hc2 hc3; exact lc4_real_of_sym c0 c1 h03 h12

theorem lc5_real_of_sym' {g0 g1 g2 g3 g4 : ℂ → ℂ} {c0 c1 c2 c3 c4 : ℂ} (hc2 : c2.im = 0)
    (hc3 : c3 = conj c1) (hc4 : c4 = conj c0) {x : ℂ} (h04 : conj (g0 x) = g4 x)
    (h13 : conj (g1 x) = g3 x) (h2 : (g2 x).im = 0) :
    (lc5 c0 c1 c2 c3 c4 g0 g1 g2 g3 g4 x).im = 0 := by
  have : c2 = (c2.re : ℂ) := (Complex.conj_eq_iff_re.1 (Complex.conj_eq_iff_im.2 hc2)).symm
  subst hc3 hc4; rw [this]; exact lc5_real_of_sym c0 c1 c2.re h04 h13 h2

section cubicReal

variable {a : ℕ → ℕ → ℂ → ℂ} {ν s : ℝ}

theorem pc_conj (ha : ∀ m n, CoefFn (a m n) s) (x : ℝ) :
    pc3 a x = conj (pc0 a x) ∧ pc2 a x = conj (pc1 a x) := by
  have r := fun m n => (ha m n).real x
  constructor
  · rw [pc0, lc4_conj_of_real _ _ _ _ (r 0 3) (r 1 2) (r 2 1) (r 3 0), pc3]
    congr 1 <;> simp [map_div₀, Complex.conj_I, map_neg, map_ofNat, map_one,
      map_sub, map_add, map_mul, map_zero] <;> ring
  · rw [pc1, lc4_conj_of_real _ _ _ _ (r 0 3) (r 1 2) (r 2 1) (r 3 0), pc2]
    congr 1 <;> simp [map_div₀, Complex.conj_I, map_neg, map_ofNat, map_one,
      map_sub, map_add, map_mul, map_zero] <;> ring

theorem fc_conj (ha : ∀ m n, CoefFn (a m n) s) (x : ℝ) :
    conj (fc0 ν a x) = fc3 ν a x ∧ conj (fc1 ν a x) = fc2 ν a x := by
  constructor
  · rw [fc0, solK_conj _ (fun y => (pc_conj ha y).1) x, fc3]; congr 1; ring
  · rw [fc1, solK_conj _ (fun y => (pc_conj ha y).2) x, fc2, neg_neg]

theorem cc_coef (hs : 0 < s) (hnr : NonRes4 ν) (ha : ∀ m n, CoefFn (a m n) s) :
    (CoefFn (cc0 ν a) s ∧ DHolPer (cc0 ν a) s) ∧ (CoefFn (cc1 ν a) s ∧ DHolPer (cc1 ν a) s) ∧
    (CoefFn (cc2 ν a) s ∧ DHolPer (cc2 ν a) s) ∧ (CoefFn (cc3 ν a) s ∧ DHolPer (cc3 ν a) s) := by
  obtain ⟨h0, h1, h2, h3⟩ := fc_dholPer hs hnr (fun m n => (ha m n).toHolPer)
  have D0 := DHolPer.lc4 2 (2 / 3) (2 / 3) 2 h0 h1 h2 h3
  have D1 := DHolPer.lc4 (-2 * Complex.I) (2 * Complex.I / 3) (-2 * Complex.I / 3)
    (2 * Complex.I) h0 h1 h2 h3
  have D2 := DHolPer.lc4 ((-1 + Complex.I) / 2) ((1 + Complex.I) / 6) ((1 - Complex.I) / 6)
    ((-1 - Complex.I) / 2) h0 h1 h2 h3
  have D3 := DHolPer.lc4 ((-1 - Complex.I) / 2) ((1 - Complex.I) / 6) ((1 + Complex.I) / 6)
    ((-1 + Complex.I) / 2) h0 h1 h2 h3
  refine ⟨⟨⟨D0.1, fun x => ?_⟩, D0⟩, ⟨⟨D1.1, fun x => ?_⟩, D1⟩, ⟨⟨D2.1, fun x => ?_⟩, D2⟩,
    ⟨⟨D3.1, fun x => ?_⟩, D3⟩⟩ <;>
  refine lc4_real_of_sym' ?_ ?_ (fc_conj ha x).1 (fc_conj ha x).2 <;>
  simp [map_div₀, Complex.conj_I, map_neg, map_ofNat, map_one,
      map_sub, map_add, map_mul, map_zero] <;> ring

end cubicReal

/-! ### The quartic step -/

open Complex in
def pq0 (a : ℕ → ℕ → ℂ → ℂ) :=
  lc5 (1 / 16) (I / 16) (-1 / 16) (-I / 16) (1 / 16) (a 0 4) (a 1 3) (a 2 2) (a 3 1) (a 4 0)
open Complex in
def pq1 (a : ℕ → ℕ → ℂ → ℂ) :=
  lc5 (-1 / 4) (-I / 8) 0 (-I / 8) (1 / 4) (a 0 4) (a 1 3) (a 2 2) (a 3 1) (a 4 0)
def pq2 (a : ℕ → ℕ → ℂ → ℂ) :=
  lc5 (3 / 8) 0 (1 / 8) 0 (3 / 8) (a 0 4) (a 1 3) (a 2 2) (a 3 1) (a 4 0)
open Complex in
def pq3 (a : ℕ → ℕ → ℂ → ℂ) :=
  lc5 (-1 / 4) (I / 8) 0 (I / 8) (1 / 4) (a 0 4) (a 1 3) (a 2 2) (a 3 1) (a 4 0)
open Complex in
def pq4 (a : ℕ → ℕ → ℂ → ℂ) :=
  lc5 (1 / 16) (-I / 16) (-1 / 16) (I / 16) (1 / 16) (a 0 4) (a 1 3) (a 2 2) (a 3 1) (a 4 0)

def fq0 (ν : ℝ) (a : ℕ → ℕ → ℂ → ℂ) := solK (-4 * ν) (pq0 a)
def fq1 (ν : ℝ) (a : ℕ → ℕ → ℂ → ℂ) := solK (-2 * ν) (pq1 a)
def fq2 (_ν : ℝ) (a : ℕ → ℕ → ℂ → ℂ) := sol0 (pq2 a)
def fq3 (ν : ℝ) (a : ℕ → ℕ → ℂ → ℂ) := solK (2 * ν) (pq3 a)
def fq4 (ν : ℝ) (a : ℕ → ℕ → ℂ → ℂ) := solK (4 * ν) (pq4 a)

open Complex in
def cq0 (ν : ℝ) (a : ℕ → ℕ → ℂ → ℂ) :=
  lc5 (2 - I) 1 (2 / 3) 1 (2 + I) (fq0 ν a) (fq1 ν a) (fq2 ν a) (fq3 ν a) (fq4 ν a)
open Complex in
def cq1 (ν : ℝ) (a : ℕ → ℕ → ℂ → ℂ) :=
  lc5 (2 + 4 * I) (-1) (2 / 3) (-1) (2 - 4 * I) (fq0 ν a) (fq1 ν a) (fq2 ν a) (fq3 ν a) (fq4 ν a)
open Complex in
def cq2 (ν : ℝ) (a : ℕ → ℕ → ℂ → ℂ) :=
  lc5 ((-1 + 3 * I) / 2) (I / 4) (1 / 6) (-I / 4) ((-1 - 3 * I) / 2)
    (fq0 ν a) (fq1 ν a) (fq2 ν a) (fq3 ν a) (fq4 ν a)
open Complex in
def cq3 (ν : ℝ) (a : ℕ → ℕ → ℂ → ℂ) :=
  lc5 (-1 / 2 - I / 6) (-I / 4) (1 / 6) (I / 4) (-1 / 2 + I / 6)
    (fq0 ν a) (fq1 ν a) (fq2 ν a) (fq3 ν a) (fq4 ν a)
open Complex in
def cq4 (ν : ℝ) (a : ℕ → ℕ → ℂ → ℂ) :=
  lc5 (-I / 3) 0 0 0 (I / 3) (fq0 ν a) (fq1 ν a) (fq2 ν a) (fq3 ν a) (fq4 ν a)

def uq4 : Fin 2 → ℝ := ![1, 2]

/-- the quartic part `∑_{m+n=4} a m n w₀^m w₁^n` -/
def Q4 (a : ℕ → ℕ → ℂ → ℂ) (w : C2) (t : ℂ) : ℂ :=
  a 4 0 t * w 0 ^ 4 + a 3 1 t * w 0 ^ 3 * w 1 + a 2 2 t * w 0 ^ 2 * w 1 ^ 2 +
    a 1 3 t * w 0 * w 1 ^ 3 + a 0 4 t * w 1 ^ 4

section quartic

variable {a : ℕ → ℕ → ℂ → ℂ} {ν s : ℝ}

theorem pq_holPer (ha : ∀ m n, HolPer (a m n) s) :
    HolPer (pq0 a) s ∧ HolPer (pq1 a) s ∧ HolPer (pq2 a) s ∧ HolPer (pq3 a) s ∧
      HolPer (pq4 a) s :=
  ⟨HolPer.lc5 _ _ _ _ _ (ha 0 4) (ha 1 3) (ha 2 2) (ha 3 1) (ha 4 0),
    HolPer.lc5 _ _ _ _ _ (ha 0 4) (ha 1 3) (ha 2 2) (ha 3 1) (ha 4 0),
    HolPer.lc5 _ _ _ _ _ (ha 0 4) (ha 1 3) (ha 2 2) (ha 3 1) (ha 4 0),
    HolPer.lc5 _ _ _ _ _ (ha 0 4) (ha 1 3) (ha 2 2) (ha 3 1) (ha 4 0),
    HolPer.lc5 _ _ _ _ _ (ha 0 4) (ha 1 3) (ha 2 2) (ha 3 1) (ha 4 0)⟩

theorem fq_dholPer (hs : 0 < s) (hnr : NonRes4 ν) (ha : ∀ m n, HolPer (a m n) s) :
    DHolPer (fq0 ν a) s ∧ DHolPer (fq1 ν a) s ∧ DHolPer (fq2 ν a) s ∧ DHolPer (fq3 ν a) s ∧
      DHolPer (fq4 ν a) s := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := pq_holPer ha
  refine ⟨solK_dholPer ?_ hs h0, solK_dholPer ?_ hs h1, sol0_dholPer hs h2,
    solK_dholPer ?_ hs h3, solK_dholPer ?_ hs h4⟩
  · simpa using nonres_ne hnr (q := -4) (by norm_num)
  · simpa using nonres_ne hnr (q := -2) (by norm_num)
  · simpa using nonres_ne hnr (q := 2) (by norm_num)
  · simpa using nonres_ne hnr (q := 4) (by norm_num)

theorem fq_hasDerivAt (hs : 0 < s) (hnr : NonRes4 ν) (ha : ∀ m n, HolPer (a m n) s) {t : ℂ}
    (ht : t ∈ strip s) :
    HasDerivAt (fq0 ν a) (pq0 a t - Complex.I * (-4 * ν) * fq0 ν a t) t ∧
    HasDerivAt (fq1 ν a) (pq1 a t - Complex.I * (-2 * ν) * fq1 ν a t) t ∧
    HasDerivAt (fq2 ν a) (pq2 a t - avg (pq2 a)) t ∧
    HasDerivAt (fq3 ν a) (pq3 a t - Complex.I * (2 * ν) * fq3 ν a t) t ∧
    HasDerivAt (fq4 ν a) (pq4 a t - Complex.I * (4 * ν) * fq4 ν a t) t := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := pq_holPer ha
  refine ⟨?_, ?_, (sol0_spec hs h2).2 t ht, ?_, ?_⟩
  · have := (solK_spec (by simpa using nonres_ne hnr (q := -4) (by norm_num)) hs h0).2 t ht
    simpa [fq0] using this
  · have := (solK_spec (by simpa using nonres_ne hnr (q := -2) (by norm_num)) hs h1).2 t ht
    simpa [fq1] using this
  · have := (solK_spec (by simpa using nonres_ne hnr (q := 2) (by norm_num)) hs h3).2 t ht
    simpa [fq3] using this
  · have := (solK_spec (by simpa using nonres_ne hnr (q := 4) (by norm_num)) hs h4).2 t ht
    simpa [fq4] using this

theorem quartic_ident (hs : 0 < s) (hnr : NonRes4 ν) (ha : ∀ m n, HolPer (a m n) s) {t : ℂ}
    (ht : t ∈ strip s) (w : C2) :
    Q4 a w t + shX 4 uc0 (cq0 ν a) ν w t + shX 4 uc1 (cq1 ν a) ν w t +
      shX 4 uc2 (cq2 ν a) ν w t + shX 4 uc3 (cq3 ν a) ν w t + shX 4 uq4 (cq4 ν a) ν w t =
      avg (pq2 a) * q2 w ^ 2 := by
  obtain ⟨d0, d1, d2, d3, d4⟩ := fq_hasDerivAt hs hnr ha ht
  have e0 := (hasDerivAt_lc5 (2 - Complex.I) 1 (2 / 3) 1 (2 + Complex.I) d0 d1 d2 d3 d4).deriv
  have e1 := (hasDerivAt_lc5 (2 + 4 * Complex.I) (-1) (2 / 3) (-1) (2 - 4 * Complex.I)
    d0 d1 d2 d3 d4).deriv
  have e2 := (hasDerivAt_lc5 ((-1 + 3 * Complex.I) / 2) (Complex.I / 4) (1 / 6)
    (-Complex.I / 4) ((-1 - 3 * Complex.I) / 2) d0 d1 d2 d3 d4).deriv
  have e3 := (hasDerivAt_lc5 (-1 / 2 - Complex.I / 6) (-Complex.I / 4) (1 / 6) (Complex.I / 4)
    (-1 / 2 + Complex.I / 6) d0 d1 d2 d3 d4).deriv
  have e4 := (hasDerivAt_lc5 (-Complex.I / 3) 0 0 0 (Complex.I / 3) d0 d1 d2 d3 d4).deriv
  simp only [shX, cq0, cq1, cq2, cq3, cq4, e0, e1, e2, e3, e4]
  simp only [lc5, pq0, pq1, pq2, pq3, pq4, Q4, q2, lin, uc0, uc1, uc2, uc3, uq4]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Complex.ofReal_one,
    Complex.ofReal_zero, Complex.ofReal_neg, Nat.cast_ofNat]
  norm_num
  linear_combination ((a 1 3 t)*(w 0)*(w 1)^3 + (a 3 1 t)*(w 0)^3*(w 1) - 16*(fq0 ν a t)*(ν:ℂ)*(w 0)^3*(w 1) + 16*(fq0 ν a t)*(ν:ℂ)*(w 0)*(w 1)^3 - 4*(fq1 ν a t)*(ν:ℂ)*(w 0)^3*(w 1) - 4*(fq1 ν a t)*(ν:ℂ)*(w 0)*(w 1)^3 - 4*(fq3 ν a t)*(ν:ℂ)*(w 0)^3*(w 1) - 4*(fq3 ν a t)*(ν:ℂ)*(w 0)*(w 1)^3 - 16*(fq4 ν a t)*(ν:ℂ)*(w 0)^3*(w 1) + 16*(fq4 ν a t)*(ν:ℂ)*(w 0)*(w 1)^3) * Complex.I_sq

theorem pq_conj (ha : ∀ m n, CoefFn (a m n) s) (x : ℝ) :
    pq4 a x = conj (pq0 a x) ∧ pq3 a x = conj (pq1 a x) ∧ (pq2 a x).im = 0 := by
  have r := fun m n => (ha m n).real x
  refine ⟨?_, ?_, ?_⟩
  · rw [pq0, lc5_conj_of_real _ _ _ _ _ (r 0 4) (r 1 3) (r 2 2) (r 3 1) (r 4 0), pq4]
    congr 1 <;> simp [map_div₀, Complex.conj_I, map_neg, map_ofNat, map_one,
      map_sub, map_add, map_mul, map_zero]
  · rw [pq1, lc5_conj_of_real _ _ _ _ _ (r 0 4) (r 1 3) (r 2 2) (r 3 1) (r 4 0), pq3]
    congr 1 <;> simp [map_div₀, Complex.conj_I, map_neg, map_ofNat, map_one,
      map_sub, map_add, map_mul, map_zero]
  · simp only [pq2, lc5, Complex.add_im, Complex.mul_im, r]
    norm_num

theorem fq_conj (ha : ∀ m n, CoefFn (a m n) s) (x : ℝ) :
    conj (fq0 ν a x) = fq4 ν a x ∧ conj (fq1 ν a x) = fq3 ν a x ∧ (fq2 ν a x).im = 0 := by
  refine ⟨?_, ?_, (sol0_real (fun y => (pq_conj ha y).2.2)).1 x⟩
  · rw [fq0, solK_conj _ (fun y => (pq_conj ha y).1) x, fq4]; congr 1; ring
  · rw [fq1, solK_conj _ (fun y => (pq_conj ha y).2.1) x, fq3]; congr 1; ring

theorem avg_pq2_real (ha : ∀ m n, CoefFn (a m n) s) : (avg (pq2 a)).im = 0 :=
  (sol0_real (fun y => (pq_conj ha y).2.2)).2

theorem cq_coef (hs : 0 < s) (hnr : NonRes4 ν) (ha : ∀ m n, CoefFn (a m n) s) :
    (CoefFn (cq0 ν a) s ∧ DHolPer (cq0 ν a) s) ∧ (CoefFn (cq1 ν a) s ∧ DHolPer (cq1 ν a) s) ∧
    (CoefFn (cq2 ν a) s ∧ DHolPer (cq2 ν a) s) ∧ (CoefFn (cq3 ν a) s ∧ DHolPer (cq3 ν a) s) ∧
    (CoefFn (cq4 ν a) s ∧ DHolPer (cq4 ν a) s) := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := fq_dholPer hs hnr (fun m n => (ha m n).toHolPer)
  have D0 := DHolPer.lc5 (2 - Complex.I) 1 (2 / 3) 1 (2 + Complex.I) h0 h1 h2 h3 h4
  have D1 := DHolPer.lc5 (2 + 4 * Complex.I) (-1) (2 / 3) (-1) (2 - 4 * Complex.I) h0 h1 h2 h3 h4
  have D2 := DHolPer.lc5 ((-1 + 3 * Complex.I) / 2) (Complex.I / 4) (1 / 6)
    (-Complex.I / 4) ((-1 - 3 * Complex.I) / 2) h0 h1 h2 h3 h4
  have D3 := DHolPer.lc5 (-1 / 2 - Complex.I / 6) (-Complex.I / 4) (1 / 6) (Complex.I / 4)
    (-1 / 2 + Complex.I / 6) h0 h1 h2 h3 h4
  have D4 := DHolPer.lc5 (-Complex.I / 3) 0 0 0 (Complex.I / 3) h0 h1 h2 h3 h4
  refine ⟨⟨⟨D0.1, fun x => ?_⟩, D0⟩, ⟨⟨D1.1, fun x => ?_⟩, D1⟩, ⟨⟨D2.1, fun x => ?_⟩, D2⟩,
    ⟨⟨D3.1, fun x => ?_⟩, D3⟩, ⟨⟨D4.1, fun x => ?_⟩, D4⟩⟩ <;>
  refine lc5_real_of_sym' ?_ ?_ ?_ (fq_conj ha x).1 (fq_conj ha x).2.1 (fq_conj ha x).2.2 <;>
  simp [map_div₀, Complex.conj_I, map_neg, map_ofNat, map_one,
      map_sub, map_add, map_mul, map_zero] <;> ring

end quartic

end ABC.S4.R3Aux
