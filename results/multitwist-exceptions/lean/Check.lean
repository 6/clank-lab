import Multitwist

/-!
Independent restatements of what `Multitwist.lean` proves, with their exact
types, then a negative control and the axiom guards. All names are in the
namespace `Multitwist`; see `README.md` for the meaning of each statement.
-/

open Multitwist

-- The model: the Artin automorphisms satisfy the braid relations.
example : s1 * s2 * s1 = s2 * s1 * s2 := braid12
example : s2 * s3 * s2 = s3 * s2 * s3 := braid23
example : s1 * s3 = s3 * s1 := comm13

-- F0: each twist fixes its own curve.
example : Ta wa = wa := F0_a
example : Td wd = wd := F0_d
example : Tc wc = wc := F0_c
example : TCp wCp = wCp := F0_Cp
example : TC wC = wC := F0_C

-- F1: the pentagon pattern in the cyclic order a, d, c, C', C. For curves
-- that meet, the twisted word is conjugate neither to the word nor to its
-- inverse; for disjoint curves it is conjugate to the word.
example : ¬ IsConj (Ta wd) wd ∧ ¬ IsConj (Ta wd) wd⁻¹ := F1_meet_a_d
example : IsConj (Ta wc) wc := F1_disjoint_a_c
example : IsConj (Ta wCp) wCp := F1_disjoint_a_Cp
example : ¬ IsConj (Ta wC) wC ∧ ¬ IsConj (Ta wC) wC⁻¹ := F1_meet_a_C
example : ¬ IsConj (Td wa) wa ∧ ¬ IsConj (Td wa) wa⁻¹ := F1_meet_d_a
example : ¬ IsConj (Td wc) wc ∧ ¬ IsConj (Td wc) wc⁻¹ := F1_meet_d_c
example : IsConj (Td wCp) wCp := F1_disjoint_d_Cp
example : IsConj (Td wC) wC := F1_disjoint_d_C
example : IsConj (Tc wa) wa := F1_disjoint_c_a
example : ¬ IsConj (Tc wd) wd ∧ ¬ IsConj (Tc wd) wd⁻¹ := F1_meet_c_d
example : ¬ IsConj (Tc wCp) wCp ∧ ¬ IsConj (Tc wCp) wCp⁻¹ := F1_meet_c_Cp
example : IsConj (Tc wC) wC := F1_disjoint_c_C
example : IsConj (TCp wa) wa := F1_disjoint_Cp_a
example : IsConj (TCp wd) wd := F1_disjoint_Cp_d
example : ¬ IsConj (TCp wc) wc ∧ ¬ IsConj (TCp wc) wc⁻¹ := F1_meet_Cp_c
example : ¬ IsConj (TCp wC) wC ∧ ¬ IsConj (TCp wC) wC⁻¹ := F1_meet_Cp_C
example : ¬ IsConj (TC wa) wa ∧ ¬ IsConj (TC wa) wa⁻¹ := F1_meet_C_a
example : IsConj (TC wd) wd := F1_disjoint_C_d
example : IsConj (TC wc) wc := F1_disjoint_C_c
example : ¬ IsConj (TC wCp) wCp ∧ ¬ IsConj (TC wCp) wCp⁻¹ := F1_meet_C_Cp

-- F2: the two components of t = Ta Tc^(±1) commute.
example : Ta * Tc = Tc * Ta := F2

-- t = Ta Tc (ε = +1) and t = Ta Tc⁻¹ (ε = -1), with their inverses.
example : (Ta * Tc) * (Tai * Tci) = 1 := t_pos_inv
example : (Ta * Tci) * (Tai * Tc) = 1 := t_neg_inv
example : Ta * Tai = 1 ∧ Tai * Ta = 1 := ⟨Ta_Tai, Tai_Ta⟩
example : Tc * Tci = 1 ∧ Tci * Tc = 1 := ⟨Tc_Tci, Tci_Tc⟩

-- F3, for every k: t^0 f_k = Ta^k Td fixes the word of C', and
-- t^(-k) f_k fixes the word of C, for both signs ε.
example (k : ℕ) : (Ta ^ k * Td) wCp = wCp := F3_j0 k
example (k : ℕ) : ((Tai * Tci) ^ k * (Ta ^ k * Td)) wC = wC := F3_jk_pos k
example (k : ℕ) : ((Tai * Tc) ^ k * (Ta ^ k * Td)) wC = wC := F3_jk_neg k
example (k : ℕ) : (Tai * Tci) ^ k * (Ta ^ k * Td) = Tci ^ k * Td := member_pos k
example (k : ℕ) : (Tai * Tc) ^ k * (Ta ^ k * Td) = Tc ^ k * Td := member_neg k

-- F4, for every k: f_k(a) = Ta^k Td (a) meets a and c.
example (k : ℕ) :
    ¬ IsConj (Ta ((Ta ^ k * Td) wa)) ((Ta ^ k * Td) wa) ∧
    ¬ IsConj (Ta ((Ta ^ k * Td) wa)) ((Ta ^ k * Td) wa)⁻¹ := F4_a k
example (k : ℕ) :
    ¬ IsConj (Tc ((Ta ^ k * Td) wa)) ((Ta ^ k * Td) wa) ∧
    ¬ IsConj (Tc ((Ta ^ k * Td) wa)) ((Ta ^ k * Td) wa)⁻¹ := F4_c k

-- Negative control: with C and C' exchanged, the j = 0 member does not fix
-- the word of C.
example : (Ta * Td) wC ≠ wC := by decide

/-- info: 'Multitwist.braid12' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Multitwist.braid12

/-- info: 'Multitwist.braid23' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Multitwist.braid23

/-- info: 'Multitwist.comm13' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Multitwist.comm13

/-- info: 'Multitwist.F0_a' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Multitwist.F0_a

/-- info: 'Multitwist.F0_d' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Multitwist.F0_d

/-- info: 'Multitwist.F0_c' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Multitwist.F0_c

/-- info: 'Multitwist.F0_Cp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Multitwist.F0_Cp

/-- info: 'Multitwist.F0_C' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Multitwist.F0_C

/-- info: 'Multitwist.F1_meet_a_d' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Multitwist.F1_meet_a_d

/-- info: 'Multitwist.F1_disjoint_a_c' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Multitwist.F1_disjoint_a_c

/-- info: 'Multitwist.F1_disjoint_a_Cp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Multitwist.F1_disjoint_a_Cp

/-- info: 'Multitwist.F1_meet_a_C' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Multitwist.F1_meet_a_C

/-- info: 'Multitwist.F1_meet_d_a' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Multitwist.F1_meet_d_a

/-- info: 'Multitwist.F1_meet_d_c' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Multitwist.F1_meet_d_c

/-- info: 'Multitwist.F1_disjoint_d_Cp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Multitwist.F1_disjoint_d_Cp

/-- info: 'Multitwist.F1_disjoint_d_C' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Multitwist.F1_disjoint_d_C

/-- info: 'Multitwist.F1_disjoint_c_a' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Multitwist.F1_disjoint_c_a

/-- info: 'Multitwist.F1_meet_c_d' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Multitwist.F1_meet_c_d

/-- info: 'Multitwist.F1_meet_c_Cp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Multitwist.F1_meet_c_Cp

/-- info: 'Multitwist.F1_disjoint_c_C' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Multitwist.F1_disjoint_c_C

/-- info: 'Multitwist.F1_disjoint_Cp_a' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Multitwist.F1_disjoint_Cp_a

/-- info: 'Multitwist.F1_disjoint_Cp_d' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Multitwist.F1_disjoint_Cp_d

/-- info: 'Multitwist.F1_meet_Cp_c' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Multitwist.F1_meet_Cp_c

/-- info: 'Multitwist.F1_meet_Cp_C' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Multitwist.F1_meet_Cp_C

/-- info: 'Multitwist.F1_meet_C_a' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Multitwist.F1_meet_C_a

/-- info: 'Multitwist.F1_disjoint_C_d' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Multitwist.F1_disjoint_C_d

/-- info: 'Multitwist.F1_disjoint_C_c' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Multitwist.F1_disjoint_C_c

/-- info: 'Multitwist.F1_meet_C_Cp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Multitwist.F1_meet_C_Cp

/-- info: 'Multitwist.F2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Multitwist.F2

/-- info: 'Multitwist.t_pos_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Multitwist.t_pos_inv

/-- info: 'Multitwist.t_neg_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Multitwist.t_neg_inv

/-- info: 'Multitwist.F3_j0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Multitwist.F3_j0

/-- info: 'Multitwist.F3_jk_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Multitwist.F3_jk_pos

/-- info: 'Multitwist.F3_jk_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Multitwist.F3_jk_neg

/-- info: 'Multitwist.member_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Multitwist.member_pos

/-- info: 'Multitwist.member_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Multitwist.member_neg

/-- info: 'Multitwist.F4_a' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Multitwist.F4_a

/-- info: 'Multitwist.F4_c' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Multitwist.F4_c
