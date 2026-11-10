import Pentagon.Statement
import Pentagon.Cert

/-! Proof of the existence part, by parabolic families, a covering of residues and a sweep of
the small half-periods, all checked by the kernel (`decide +kernel`), plus the combinatorial
half of the exception list. -/

namespace Pentagon
open ZPhi

abbrev Q4 := Nat × Nat × Nat × Nat

def toVec : Q4 → Vec | (a, b, c, d) => ⟨⟨a, b⟩, ⟨c, d⟩⟩
def ofVec (v : Vec) : Q4 := (v.x.p, v.x.q, v.y.p, v.y.q)
theorem toVec_ofVec (v : Vec) : toVec (ofVec v) = v := by
  obtain ⟨⟨a, b⟩, ⟨c, d⟩⟩ := v; rfl

def gA : Q4 → Q4 | (a, b, c, d) => (a + d, b + c + d, c, d)
def gB : Q4 → Q4 | (a, b, c, d) => (a, b, c + b, d + a + b)
def gC : Q4 → Q4 | (a, b, c, d) => (b + d, a + b + c + d, a + d, b + c + d)
def gD : Q4 → Q4 | (a, b, c, d) => (b + c, a + b + d, b + d, a + b + c + d)
def gen : Nat → Q4 → Q4 | 0 => gA | 1 => gB | 2 => gC | _ => gD

theorem add_def (x y : ZPhi) : x + y = ⟨x.p + y.p, x.q + y.q⟩ := rfl
theorem mul_def (x y : ZPhi) :
    x * y = ⟨x.p * y.p + x.q * y.q, x.p * y.q + x.q * y.p + x.q * y.q⟩ := rfl

theorem act_A (q : Q4) : A.act (toVec q) = toVec (gA q) := by
  obtain ⟨a, b, c, d⟩ := q; simp [A, Mat.act, toVec, gA, one, phi, zero, add_def, mul_def]; omega
theorem act_B (q : Q4) : B.act (toVec q) = toVec (gB q) := by
  obtain ⟨a, b, c, d⟩ := q; simp [B, Mat.act, toVec, gB, one, phi, zero, add_def, mul_def]; omega
theorem act_C (q : Q4) : C.act (toVec q) = toVec (gC q) := by
  obtain ⟨a, b, c, d⟩ := q; simp [C, Mat.act, toVec, gC, one, phi, add_def, mul_def]; omega
theorem act_D (q : Q4) : D.act (toVec q) = toVec (gD q) := by
  obtain ⟨a, b, c, d⟩ := q; simp [D, Mat.act, toVec, gD, one, phi, add_def, mul_def]; omega

theorem act_gen (i : Nat) : ∃ M ∈ [A, B, C, D], ∀ q, M.act (toVec q) = toVec (gen i q) := by
  match i with
  | 0 => exact ⟨A, by simp, act_A⟩
  | 1 => exact ⟨B, by simp, act_B⟩
  | 2 => exact ⟨C, by simp, act_C⟩
  | _ + 3 => exact ⟨D, by simp, act_D⟩

theorem orbit_gen {q : Q4} (i : Nat) (h : Orbit (toVec q)) : Orbit (toVec (gen i q)) := by
  obtain ⟨M, hM, hq⟩ := act_gen i
  rw [← hq]; exact Orbit.step hM h

def applyW : List Nat → Q4 → Q4
  | [], q => q
  | i :: w, q => applyW w (gen i q)

theorem orbit_applyW (w : List Nat) {q : Q4} (h : Orbit (toVec q)) : Orbit (toVec (applyW w q)) := by
  induction w generalizing q with
  | nil => exact h
  | cons i w ih => exact ih (orbit_gen i h)

def qadd : Q4 → Q4 → Q4 | (a, b, c, d), (e, f, g, h) => (a + e, b + f, c + g, d + h)
def qsm (n : Nat) : Q4 → Q4 | (a, b, c, d) => (n * a, n * b, n * c, n * d)

theorem gen_lin (i n : Nat) (q r : Q4) :
    gen i (qadd q (qsm n r)) = qadd (gen i q) (qsm n (gen i r)) := by
  obtain ⟨a, b, c, d⟩ := q; obtain ⟨e, f, g, h⟩ := r
  match i with
  | 0 => simp [gen, gA, qadd, qsm, Nat.mul_add]; omega
  | 1 => simp [gen, gB, qadd, qsm, Nat.mul_add]; omega
  | 2 => simp [gen, gC, qadd, qsm, Nat.mul_add]; omega
  | _ + 3 => simp [gen, gD, qadd, qsm, Nat.mul_add]; omega

theorem applyW_lin (w : List Nat) (n : Nat) (q r : Q4) :
    applyW w (qadd q (qsm n r)) = qadd (applyW w q) (qsm n (applyW w r)) := by
  induction w generalizing q r with
  | nil => rfl
  | cons i w ih => simp only [applyW]; rw [gen_lin, ih]

/-- Pⁿ = I + nN for P = A (P = 0) or B (otherwise); `nilP` is N. -/
def nilP (P : Nat) : Q4 → Q4 | (a, b, c, d) => if P = 0 then (d, c + d, 0, 0) else (0, 0, b, a + b)
def gP (P : Nat) : Nat := if P = 0 then 0 else 1
def powP (P n : Nat) (q : Q4) : Q4 := qadd q (qsm n (nilP P q))

theorem powP_zero (P : Nat) (q : Q4) : powP P 0 q = q := by
  obtain ⟨a, b, c, d⟩ := q; simp [powP, qadd, qsm]

theorem powP_succ (P n : Nat) (q : Q4) : powP P (n + 1) q = gen (gP P) (powP P n q) := by
  obtain ⟨a, b, c, d⟩ := q
  by_cases hP : P = 0
  · simp [powP, nilP, gP, hP, gen, gA, qadd, qsm, Nat.succ_mul]; omega
  · simp [powP, nilP, gP, hP, gen, gB, qadd, qsm, Nat.succ_mul]; omega

theorem orbit_powP (P n : Nat) {q : Q4} (h : Orbit (toVec q)) : Orbit (toVec (powP P n q)) := by
  induction n with
  | zero => rw [powP_zero]; exact h
  | succ n ih => rw [powP_succ]; exact orbit_gen _ ih

def ellQ : Q4 → Nat | (a, b, c, d) => a + b + c + d
def linQ : Q4 → Nat | (a, b, c, d) => d + 2 * c + 4 * b + 3 * a

theorem ellQ_lin (n : Nat) (q r : Q4) : ellQ (qadd q (qsm n r)) = ellQ q + n * ellQ r := by
  obtain ⟨a, b, c, d⟩ := q; obtain ⟨e, f, g, h⟩ := r
  simp [ellQ, qadd, qsm, Nat.mul_add]; omega
theorem linQ_lin (n : Nat) (q r : Q4) : linQ (qadd q (qsm n r)) = linQ q + n * linQ r := by
  obtain ⟨a, b, c, d⟩ := q; obtain ⟨e, f, g, h⟩ := r
  simp [linQ, qadd, qsm, Nat.mul_add, Nat.mul_left_comm]; omega

theorem ell_toVec (q : Q4) : ell (toVec q) = ellQ q := by
  obtain ⟨a, b, c, d⟩ := q; rfl
theorem asym_toVec (q : Q4) : Asym (toVec q) ↔ linQ q % 5 = 0 := by
  obtain ⟨a, b, c, d⟩ := q; simp [Asym, toVec, linQ]; omega

def root : Q4 := (0, 0, 1, 0)
theorem orbit_root : Orbit (toVec root) := Orbit.base

abbrev Fam := Nat × Nat × List Nat × Nat × List Nat × Nat
def Fam.m (f : Fam) : Nat := f.1
def Fam.s (f : Fam) : Nat := f.2.1

/-- The family u · Pⁿ · w · (0, 1)ᵗ gives the asymmetric half-periods s + j m, j ≥ 0. -/
def famOK : Fam → Bool
  | (m, s, w, P, u, n0) =>
    let w0 := applyW w root
    let F0 := applyW u w0
    let Dv := applyW u (nilP P w0)
    decide (0 < m) && s == ellQ F0 + n0 * ellQ Dv && (linQ F0 + n0 * linQ Dv) % 5 == 0 &&
      (m == 5 * ellQ Dv || (m == ellQ Dv && linQ Dv % 5 == 0))

theorem fam_sound (f : Fam) (hf : famOK f = true) (j : Nat) :
    ∃ v, Orbit v ∧ ell v = (Fam.s f) + j * (Fam.m f) ∧ Asym v := by
  obtain ⟨m, s, w, P, u, n0⟩ := f
  simp only [famOK, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hf
  obtain ⟨⟨⟨_, hs⟩, h5⟩, hm⟩ := hf
  have h5' : (linQ (applyW u (applyW w root)) + n0 * linQ (applyW u (nilP P (applyW w root)))) % 5 = 0 :=
    by simpa using h5
  have key : ∀ n, applyW u (powP P n (applyW w root)) =
      qadd (applyW u (applyW w root)) (qsm n (applyW u (nilP P (applyW w root)))) :=
    fun n => applyW_lin _ _ _ _
  have orb : ∀ n, Orbit (toVec (applyW u (powP P n (applyW w root)))) :=
    fun n => orbit_applyW u (orbit_powP P n (orbit_applyW w orbit_root))
  generalize hal : ellQ (applyW u (nilP P (applyW w root))) = al at hs hm
  generalize hbe : linQ (applyW u (nilP P (applyW w root))) = be at h5' hm
  rcases hm with hm | ⟨hm, hb⟩
  · refine ⟨toVec (applyW u (powP P (n0 + j * 5) (applyW w root))), orb _, ?_, ?_⟩
    · rw [ell_toVec, key, ellQ_lin, hal]
      simp only [Fam.s, Fam.m, hm, hs, Nat.add_mul, Nat.mul_assoc]; omega
    · rw [asym_toVec, key, linQ_lin, hbe, Nat.add_mul, Nat.mul_comm j 5, Nat.mul_assoc]
      generalize j * be = t; omega
  · refine ⟨toVec (applyW u (powP P (n0 + j) (applyW w root))), orb _, ?_, ?_⟩
    · rw [ell_toVec, key, ellQ_lin, hal]
      simp only [Fam.s, Fam.m, hm, hs, Nat.add_mul]; omega
    · have ht : j * be % 5 = 0 := by rw [Nat.mul_mod, hb]; simp
      rw [asym_toVec, key, linQ_lin, hbe, Nat.add_mul]
      generalize j * be = t at ht; omega

/-! The covering: a CRT splitting tree over `order`, whose leaves also bound the starts. -/

/-- Half-periods outside the claim (0 and 1, and the exceptions below 52). -/
def excl : List Nat := [0, 1, 4, 5, 6, 7, 9, 15, 21, 29, 51]

def leafOK (L : List Fam) (Q r : Nat) : Bool :=
  L.any fun f => Q % (Fam.m f) == 0 && r % (Fam.m f) == (Fam.s f) % (Fam.m f) &&
    (decide ((Fam.s f) ≤ r) || (decide (r ∈ excl) && decide ((Fam.s f) ≤ r + Q)))

def chk : List Nat → List (List Fam) → Nat → Nat → Bool
  | _, [], _, _ => false
  | [], L :: _, Q, r => leafOK L Q r
  | p :: ps, L :: Ls, Q, r =>
    leafOK L Q r || (decide (0 < p) && (List.range p).all fun t => chk ps Ls (Q * p) (r + Q * t))

theorem leaf_sound {L : List Fam} {Q r x : Nat} (h : leafOK L Q r = true) (hx : x % Q = r)
    (hex : x ∉ excl) : ∃ f ∈ L, x % (Fam.m f) = (Fam.s f) % (Fam.m f) ∧ (Fam.s f) ≤ x := by
  simp only [leafOK, List.any_eq_true, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
    decide_eq_true_eq] at h
  obtain ⟨f, hf, ⟨hQ, hr⟩, hs⟩ := h
  refine ⟨f, hf, by rw [← Nat.mod_mod_of_dvd x (Nat.dvd_of_mod_eq_zero hQ), hx, hr], ?_⟩
  have hle : x % Q ≤ x := Nat.mod_le x Q
  rcases hs with hs | ⟨hr', hs⟩
  · omega
  · have hne : x ≠ r := fun e => hex (e ▸ hr')
    have hdm := Nat.div_add_mod x Q
    have hq : x / Q ≠ 0 := fun e => by rw [e, Nat.mul_zero, Nat.zero_add, hx] at hdm; exact hne hdm.symm
    have : Q ≤ Q * (x / Q) := Nat.le_mul_of_pos_right Q (Nat.pos_of_ne_zero hq)
    omega

theorem chk_sound (ps : List Nat) (Ls : List (List Fam)) {Q r x : Nat}
    (h : chk ps Ls Q r = true) (hx : x % Q = r) (hex : x ∉ excl) :
    ∃ L ∈ Ls, ∃ f ∈ L, x % (Fam.m f) = (Fam.s f) % (Fam.m f) ∧ (Fam.s f) ≤ x := by
  induction ps generalizing Ls Q r with
  | nil =>
    match Ls, h with
    | L :: _, h => exact ⟨L, List.mem_cons_self .., leaf_sound h hx hex⟩
  | cons p ps ih =>
    match Ls, h with
    | L :: Ls, h =>
      simp only [chk, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
        List.mem_range] at h
      rcases h with h | ⟨hp, h⟩
      · exact ⟨L, List.mem_cons_self .., leaf_sound h hx hex⟩
      · obtain ⟨L', hL', rest⟩ := ih Ls (h (x / Q % p) (Nat.mod_lt _ hp)) (by rw [Nat.mod_mul, hx])
        exact ⟨L', List.mem_cons_of_mem _ hL', rest⟩

theorem chk_order : chk order levels 1 0 = true := by decide +kernel

theorem levels_ok : (levels.all fun L => L.all famOK) = true := by decide +kernel

def exceptions : List Nat := [4, 5, 6, 7, 9, 15, 21, 29, 51]

theorem of_prog {f : Fam} {x : Nat} (hok : famOK f = true) (hs : (Fam.s f) ≤ x)
    (hx : x % (Fam.m f) = (Fam.s f) % (Fam.m f)) : ∃ v, Orbit v ∧ ell v = x ∧ Asym v := by
  have hd : (x - (Fam.s f)) % (Fam.m f) = 0 := Nat.sub_mod_eq_zero_of_mod_eq hx
  obtain ⟨v, hv, he, ha⟩ := fam_sound f hok ((x - (Fam.s f)) / (Fam.m f))
  refine ⟨v, hv, ?_, ha⟩
  rw [he, Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hd)]; omega

/-- Every ℓ ≥ 2 outside {4, 5, 6, 7, 9, 15, 21, 29, 51} is a + b + c + d for an asymmetric
vector of Γ⁺ · (0, 1)ᵗ. No axioms beyond Lean's. -/
theorem long_half_periods (l : Nat) (h2 : 2 ≤ l) (hl : l ∉ exceptions) :
    ∃ v, Orbit v ∧ ell v = l ∧ Asym v := by
  have hex : l ∉ excl := by
    simp only [excl, exceptions, List.mem_cons, List.not_mem_nil, or_false] at hl ⊢; omega
  obtain ⟨L, hL, f, hf, hx, hs⟩ := chk_sound order levels chk_order (Nat.mod_one l) hex
  exact of_prog (List.all_eq_true.1 (List.all_eq_true.1 levels_ok L hL) f hf) hs hx

/-! The combinatorial half of the exception list: no asymmetric v has ℓ(v) or ℓ(φv) in
{1, 6, 7, 9}. -/

theorem ellQ_gen (i : Nat) (q : Q4) : ellQ q ≤ ellQ (gen i q) := by
  obtain ⟨a, b, c, d⟩ := q
  match i with
  | 0 => simp [gen, gA, ellQ] <;> omega
  | 1 => simp [gen, gB, ellQ] <;> omega
  | 2 => simp [gen, gC, ellQ] <;> omega
  | _ + 3 => simp [gen, gD, ellQ] <;> omega

theorem small_closed : (smallSet.all fun q => (List.range 4).all fun i =>
    decide (9 < ellQ (gen i q)) || decide (gen i q ∈ smallSet)) = true := by decide +kernel

theorem gen_of_mem {M : Mat} (hM : M ∈ [A, B, C, D]) :
    ∃ i < 4, ∀ q, M.act (toVec q) = toVec (gen i q) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hM
  rcases hM with rfl | rfl | rfl | rfl
  · exact ⟨0, by decide, act_A⟩
  · exact ⟨1, by decide, act_B⟩
  · exact ⟨2, by decide, act_C⟩
  · exact ⟨3, by decide, act_D⟩

theorem ofVec_toVec (q : Q4) : ofVec (toVec q) = q := by
  obtain ⟨a, b, c, d⟩ := q; rfl

theorem ell_ofVec (v : Vec) : ell v = ellQ (ofVec v) := by
  rw [← ell_toVec, toVec_ofVec]

theorem small_set {v : Vec} (hv : Orbit v) : ell v ≤ 9 → ofVec v ∈ smallSet := by
  induction hv with
  | base => intro; decide
  | @step M u hM _ ih =>
    intro h9
    obtain ⟨i, hi4, hi⟩ := gen_of_mem hM
    have e : M.act u = toVec (gen i (ofVec u)) := by rw [← hi, toVec_ofVec]
    rw [e, ell_toVec] at h9
    have hu : ofVec u ∈ smallSet := ih (by rw [ell_ofVec]; exact Nat.le_trans (ellQ_gen i _) h9)
    have := List.all_eq_true.1 (List.all_eq_true.1 small_closed _ hu) i (List.mem_range.2 hi4)
    simp only [Bool.or_eq_true, decide_eq_true_eq] at this
    rw [e, ofVec_toVec]
    rcases this with h | h
    · omega
    · exact h

def ellPhiQ : Q4 → Nat | (a, b, c, d) => a + 2 * b + c + 2 * d

theorem small_excl : (smallSet.all fun q => decide (linQ q % 5 ≠ 0) ||
    (decide (ellQ q ∉ [1, 6, 7, 9]) && decide (ellPhiQ q ∉ [1, 6, 7, 9]))) = true := by decide

/-- No asymmetric v ∈ Γ⁺ · (0, 1)ᵗ has ℓ(v) or ℓ(φv) in {1, 6, 7, 9}. No axioms beyond Lean's. -/
theorem exceptions_combinatorial (v : Vec) (hv : Orbit v) (ha : Asym v) :
    ell v ∉ [1, 6, 7, 9] ∧ ell (phiMul v) ∉ [1, 6, 7, 9] := by
  have hphi : ell (phiMul v) = ellPhiQ (ofVec v) := by
    obtain ⟨⟨a, b⟩, ⟨c, d⟩⟩ := v
    simp [phiMul, ell, ellPhiQ, ofVec, phi, mul_def]; omega
  have hle : ellQ (ofVec v) ≤ ellPhiQ (ofVec v) := by
    obtain ⟨⟨a, b⟩, ⟨c, d⟩⟩ := v; simp [ellQ, ellPhiQ, ofVec]; omega
  rw [hphi, ell_ofVec]
  by_cases h9 : ellQ (ofVec v) ≤ 9
  · have hm := small_set hv (by rw [ell_ofVec]; exact h9)
    have := List.all_eq_true.1 small_excl _ hm
    rw [← toVec_ofVec v, asym_toVec] at ha
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at this
    rcases this with h | h
    · exact absurd ha h
    · exact h
  · simp only [List.mem_cons, List.not_mem_nil, or_false]; omega

/-- Davis–Lelièvre Conjecture 4.3, existence part: every even number other than 2, 12, 14 and 18
is the combinatorial period of an asymmetric periodic billiard trajectory on the regular
pentagon. Rests on `kz_thm_2_1` and on six explicit trajectories (`small`), which the exact
path checkers verify. -/
theorem dl_conjecture_4_3_existence
    (small : AsymPeriod 8 ∧ AsymPeriod 10 ∧ AsymPeriod 30 ∧ AsymPeriod 42 ∧ AsymPeriod 58 ∧
      AsymPeriod 102) :
    ∀ n : Nat, 0 < n → n % 2 = 0 → n ≠ 2 → n ≠ 12 → n ≠ 14 → n ≠ 18 → AsymPeriod n := by
  intro n hn he h2 h12 h14 h18
  obtain ⟨s8, s10, s30, s42, s58, s102⟩ := small
  by_cases hx : n / 2 ∈ exceptions
  · simp only [exceptions, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with h | h | h | h | h | h | h | h | h
    all_goals first
      | omega
      | (have : n = 8 := by omega); exact this ▸ s8
      | (have : n = 10 := by omega); exact this ▸ s10
      | (have : n = 30 := by omega); exact this ▸ s30
      | (have : n = 42 := by omega); exact this ▸ s42
      | (have : n = 58 := by omega); exact this ▸ s58
      | (have : n = 102 := by omega); exact this ▸ s102
  · obtain ⟨v, hv, hl, ha⟩ := long_half_periods (n / 2) (by omega) hx
    have := kz_thm_2_1 v hv ha
    rwa [hl, Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero he)] at this

end Pentagon
