/-
The free-group facts behind the counterexample to the consecutive-integers
version of Ivanov's Problem 5 (see the paper in ../paper/).

Model: π1 of the five-holed sphere (disc with punctures 1..4, boundary the
fifth hole) is the free group on x 0, x 1, x 2, x 3 (x i a loop around
puncture i+1). Half twists act by the Artin automorphisms s1, s2, s3; the
Dehn twists about the five curves are
  a = ⟨x0 x1⟩, d = ⟨x1 x2⟩, c = ⟨x2 x3⟩, C' = ⟨x0 x1 x2⟩, C = ⟨x1 x2 x3⟩:
  Ta = s1², Td = s2², Tc = s3², TCp = (s1 s2)³, TC = (s2 s3)³.
A simple closed curve is its conjugacy class up to inversion.

What is checked here, for every k: the curve facts F0-F4 of the paper as
statements about these automorphisms and conjugacy in the free group.
What is NOT checked here (standard topology, proved in the paper): that these
automorphisms are the twists' induced maps, that curves correspond to
conjugacy classes up to inversion, that T_u(v) = v iff i(u,v) = 0, the
pants argument for filling, and that a class fixing a curve is not
pseudo-Anosov.
-/
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Conj

set_option maxRecDepth 100000

namespace Multitwist

abbrev F := FreeGroup (Fin 4)

def x (i : Fin 4) : F := FreeGroup.of i

/-- Artin generators and their inverses. -/
def s1 : Monoid.End F := FreeGroup.lift ![x 0 * x 1 * (x 0)⁻¹, x 0, x 2, x 3]
def s1i : Monoid.End F := FreeGroup.lift ![x 1, (x 1)⁻¹ * x 0 * x 1, x 2, x 3]
def s2 : Monoid.End F := FreeGroup.lift ![x 0, x 1 * x 2 * (x 1)⁻¹, x 1, x 3]
def s2i : Monoid.End F := FreeGroup.lift ![x 0, x 2, (x 2)⁻¹ * x 1 * x 2, x 3]
def s3 : Monoid.End F := FreeGroup.lift ![x 0, x 1, x 2 * x 3 * (x 2)⁻¹, x 2]
def s3i : Monoid.End F := FreeGroup.lift ![x 0, x 1, x 3, (x 3)⁻¹ * x 2 * x 3]

theorem ext_gen {f g : Monoid.End F} (h : ∀ i : Fin 4, f (x i) = g (x i)) : f = g :=
  FreeGroup.ext_hom _ _ h

theorem s1_s1i : s1 * s1i = 1 := ext_gen (by decide)
theorem s1i_s1 : s1i * s1 = 1 := ext_gen (by decide)
theorem s2_s2i : s2 * s2i = 1 := ext_gen (by decide)
theorem s2i_s2 : s2i * s2 = 1 := ext_gen (by decide)
theorem s3_s3i : s3 * s3i = 1 := ext_gen (by decide)
theorem s3i_s3 : s3i * s3 = 1 := ext_gen (by decide)

/-- The braid relations hold (sanity of the model). -/
theorem braid12 : s1 * s2 * s1 = s2 * s1 * s2 := ext_gen (by decide)
theorem braid23 : s2 * s3 * s2 = s3 * s2 * s3 := ext_gen (by decide)
theorem comm13 : s1 * s3 = s3 * s1 := ext_gen (by decide)

/-- Dehn twists about the five curves, and inverses of Ta, Tc. -/
def Ta : Monoid.End F := s1 * s1
def Tai : Monoid.End F := s1i * s1i
def Td : Monoid.End F := s2 * s2
def Tc : Monoid.End F := s3 * s3
def Tci : Monoid.End F := s3i * s3i
def TCp : Monoid.End F := (s1 * s2) ^ 3
def TC : Monoid.End F := (s2 * s3) ^ 3

/-- The five curves, as words. -/
def wa : F := x 0 * x 1
def wd : F := x 1 * x 2
def wc : F := x 2 * x 3
def wCp : F := x 0 * x 1 * x 2
def wC : F := x 1 * x 2 * x 3

theorem Ta_Tai : Ta * Tai = 1 := ext_gen (by decide)
theorem Tai_Ta : Tai * Ta = 1 := ext_gen (by decide)
theorem Tc_Tci : Tc * Tci = 1 := ext_gen (by decide)
theorem Tci_Tc : Tci * Tc = 1 := ext_gen (by decide)

/-! ### F0: each twist fixes its own curve (exactly). -/
theorem F0_a : Ta wa = wa := by decide
theorem F0_d : Td wd = wd := by decide
theorem F0_c : Tc wc = wc := by decide
theorem F0_Cp : TCp wCp = wCp := by decide
theorem F0_C : TC wC = wC := by decide

/-! ### F1: the pentagon pattern. -/

theorem sep_left {u v : F} (ρ : F →* Equiv.Perm (Fin 3)) (hu : ρ u = 1) (hv : ρ v ≠ 1) :
    ¬ IsConj u v ∧ ¬ IsConj u v⁻¹ := by
  refine ⟨fun h => hv ?_, fun h => hv ?_⟩
  · have := MonoidHom.map_isConj ρ h; rw [hu, isConj_one_right] at this; exact this
  · have := MonoidHom.map_isConj ρ h; rw [hu, isConj_one_right, map_inv, inv_eq_one] at this; exact this

theorem sep_right {u v : F} (ρ : F →* Equiv.Perm (Fin 3)) (hu : ρ u ≠ 1) (hv : ρ v = 1) :
    ¬ IsConj u v ∧ ¬ IsConj u v⁻¹ := by
  refine ⟨fun h => hu ?_, fun h => hu ?_⟩
  · have := MonoidHom.map_isConj ρ h; rw [hv, isConj_one_left] at this; exact this
  · have := MonoidHom.map_isConj ρ h; rw [map_inv, hv, inv_one, isConj_one_left] at this; exact this

/-- F1: i(a,d) ≠ 0. -/
theorem F1_meet_a_d : ¬ IsConj (Ta wd) wd ∧ ¬ IsConj (Ta wd) wd⁻¹ :=
  sep_right (FreeGroup.lift ![Equiv.swap 0 1, Equiv.swap 0 2, Equiv.swap 0 2, Equiv.swap 0 2]) (by decide) (by decide)

/-- F1: i(a,c) = 0. -/
theorem F1_disjoint_a_c : IsConj (Ta wc) wc :=
  isConj_iff.mpr ⟨1, by decide⟩

/-- F1: i(a,Cp) = 0. -/
theorem F1_disjoint_a_Cp : IsConj (Ta wCp) wCp :=
  isConj_iff.mpr ⟨1, by decide⟩

/-- F1: i(a,C) ≠ 0. -/
theorem F1_meet_a_C : ¬ IsConj (Ta wC) wC ∧ ¬ IsConj (Ta wC) wC⁻¹ :=
  sep_left (FreeGroup.lift ![Equiv.swap 0 1, Equiv.swap 0 1 * Equiv.swap 1 2, 1, Equiv.swap 0 1 * Equiv.swap 1 2]) (by decide) (by decide)

/-- F1: i(d,a) ≠ 0. -/
theorem F1_meet_d_a : ¬ IsConj (Td wa) wa ∧ ¬ IsConj (Td wa) wa⁻¹ :=
  sep_left (FreeGroup.lift ![Equiv.swap 0 2, Equiv.swap 0 1, Equiv.swap 0 2, Equiv.swap 1 2]) (by decide) (by decide)

/-- F1: i(d,c) ≠ 0. -/
theorem F1_meet_d_c : ¬ IsConj (Td wc) wc ∧ ¬ IsConj (Td wc) wc⁻¹ :=
  sep_right (FreeGroup.lift ![Equiv.swap 0 2, Equiv.swap 0 2, Equiv.swap 0 1, Equiv.swap 0 1]) (by decide) (by decide)

/-- F1: i(d,Cp) = 0. -/
theorem F1_disjoint_d_Cp : IsConj (Td wCp) wCp :=
  isConj_iff.mpr ⟨1, by decide⟩

/-- F1: i(d,C) = 0. -/
theorem F1_disjoint_d_C : IsConj (Td wC) wC :=
  isConj_iff.mpr ⟨1, by decide⟩

/-- F1: i(c,a) = 0. -/
theorem F1_disjoint_c_a : IsConj (Tc wa) wa :=
  isConj_iff.mpr ⟨1, by decide⟩

/-- F1: i(c,d) ≠ 0. -/
theorem F1_meet_c_d : ¬ IsConj (Tc wd) wd ∧ ¬ IsConj (Tc wd) wd⁻¹ :=
  sep_right (FreeGroup.lift ![Equiv.swap 0 1, Equiv.swap 0 2, Equiv.swap 0 2, Equiv.swap 0 1]) (by decide) (by decide)

/-- F1: i(c,Cp) ≠ 0. -/
theorem F1_meet_c_Cp : ¬ IsConj (Tc wCp) wCp ∧ ¬ IsConj (Tc wCp) wCp⁻¹ :=
  sep_left (FreeGroup.lift ![Equiv.swap 0 2, Equiv.swap 0 1 * Equiv.swap 1 2, Equiv.swap 0 2, Equiv.swap 1 2 * Equiv.swap 0 1]) (by decide) (by decide)

/-- F1: i(c,C) = 0. -/
theorem F1_disjoint_c_C : IsConj (Tc wC) wC :=
  isConj_iff.mpr ⟨1, by decide⟩

/-- F1: i(Cp,a) = 0. -/
theorem F1_disjoint_Cp_a : IsConj (TCp wa) wa :=
  isConj_iff.mpr ⟨(x 2)⁻¹ * (x 1)⁻¹ * (x 0)⁻¹, by decide⟩

/-- F1: i(Cp,d) = 0. -/
theorem F1_disjoint_Cp_d : IsConj (TCp wd) wd :=
  isConj_iff.mpr ⟨(x 0)⁻¹, by decide⟩

/-- F1: i(Cp,c) ≠ 0. -/
theorem F1_meet_Cp_c : ¬ IsConj (TCp wc) wc ∧ ¬ IsConj (TCp wc) wc⁻¹ :=
  sep_left (FreeGroup.lift ![Equiv.swap 0 2, Equiv.swap 0 1 * Equiv.swap 1 2, Equiv.swap 0 1 * Equiv.swap 1 2, Equiv.swap 0 1 * Equiv.swap 1 2]) (by decide) (by decide)

/-- F1: i(Cp,C) ≠ 0. -/
theorem F1_meet_Cp_C : ¬ IsConj (TCp wC) wC ∧ ¬ IsConj (TCp wC) wC⁻¹ :=
  sep_right (FreeGroup.lift ![Equiv.swap 0 2, Equiv.swap 1 2 * Equiv.swap 0 1, Equiv.swap 0 2, Equiv.swap 0 1]) (by decide) (by decide)

/-- F1: i(C,a) ≠ 0. -/
theorem F1_meet_C_a : ¬ IsConj (TC wa) wa ∧ ¬ IsConj (TC wa) wa⁻¹ :=
  sep_left (FreeGroup.lift ![Equiv.swap 0 2, Equiv.swap 1 2, Equiv.swap 0 1, Equiv.swap 1 2 * Equiv.swap 0 1]) (by decide) (by decide)

/-- F1: i(C,d) = 0. -/
theorem F1_disjoint_C_d : IsConj (TC wd) wd :=
  isConj_iff.mpr ⟨(x 3)⁻¹ * (x 2)⁻¹ * (x 1)⁻¹, by decide⟩

/-- F1: i(C,c) = 0. -/
theorem F1_disjoint_C_c : IsConj (TC wc) wc :=
  isConj_iff.mpr ⟨(x 1)⁻¹, by decide⟩

/-- F1: i(C,Cp) ≠ 0. -/
theorem F1_meet_C_Cp : ¬ IsConj (TC wCp) wCp ∧ ¬ IsConj (TC wCp) wCp⁻¹ :=
  sep_left (FreeGroup.lift ![Equiv.swap 0 2, Equiv.swap 1 2 * Equiv.swap 0 1, Equiv.swap 0 2, Equiv.swap 0 1 * Equiv.swap 1 2]) (by decide) (by decide)

/-! ### F2: the components of t commute. -/
theorem F2 : Ta * Tc = Tc * Ta := ext_gen (by decide)
theorem Tai_Tci : Tai * Tci = Tci * Tai := ext_gen (by decide)
theorem Tai_Tc : Tai * Tc = Tc * Tai := ext_gen (by decide)

/-! ### F3: the two exceptional members, for every k. -/

theorem pow_fix {e : Monoid.End F} {w : F} (h : e w = w) : ∀ n : ℕ, (e ^ n) w = w
  | 0 => rfl
  | n + 1 => by rw [pow_succ, Monoid.End.coe_mul, Function.comp_apply, h, pow_fix h n]

theorem Ta_fix_Cp : Ta wCp = wCp := by decide
theorem Td_fix_Cp : Td wCp = wCp := by decide
theorem Td_fix_C : Td wC = wC := by decide
theorem Tc_fix_C : Tc wC = wC := by decide
theorem Tci_fix_C : Tci wC = wC := by decide

/-- j = 0: t^0 f_k = Ta^k Td fixes C' (the word x0x1x2 itself). -/
theorem F3_j0 (k : ℕ) : (Ta ^ k * Td) wCp = wCp := by
  rw [Monoid.End.coe_mul, Function.comp_apply, Td_fix_Cp, pow_fix Ta_fix_Cp]

/-- t = Ta Tc (ε = +1) has inverse Tai Tci; for ε = −1, t = Ta Tci has inverse Tai Tc. -/
theorem t_pos_inv : (Ta * Tc) * (Tai * Tci) = 1 := ext_gen (by decide)
theorem t_neg_inv : (Ta * Tci) * (Tai * Tc) = 1 := ext_gen (by decide)

theorem cancel_pow (k : ℕ) : Tai ^ k * Ta ^ k = 1 := by
  have hc : Commute Tai Ta := Tai_Ta.trans Ta_Tai.symm
  rw [← hc.mul_pow, Tai_Ta, one_pow]

/-- j = −k, ε = +1: t^(−k) f_k = Tc^(−k) Td. -/
theorem member_pos (k : ℕ) : (Tai * Tci) ^ k * (Ta ^ k * Td) = Tci ^ k * Td := by
  have hc : Commute Tai Tci := Tai_Tci
  calc (Tai * Tci) ^ k * (Ta ^ k * Td) = (Tai ^ k * Tci ^ k) * (Ta ^ k * Td) := by
        rw [hc.mul_pow]
    _ = (Tci ^ k * Tai ^ k) * (Ta ^ k * Td) := by rw [(hc.pow_pow k k).eq]
    _ = Tci ^ k * ((Tai ^ k * Ta ^ k) * Td) := by simp only [mul_assoc]
    _ = Tci ^ k * Td := by rw [cancel_pow, one_mul]

/-- j = −k, ε = −1: t^(−k) f_k = Tc^k Td. -/
theorem member_neg (k : ℕ) : (Tai * Tc) ^ k * (Ta ^ k * Td) = Tc ^ k * Td := by
  have hc : Commute Tai Tc := Tai_Tc
  calc (Tai * Tc) ^ k * (Ta ^ k * Td) = (Tai ^ k * Tc ^ k) * (Ta ^ k * Td) := by
        rw [hc.mul_pow]
    _ = (Tc ^ k * Tai ^ k) * (Ta ^ k * Td) := by rw [(hc.pow_pow k k).eq]
    _ = Tc ^ k * ((Tai ^ k * Ta ^ k) * Td) := by simp only [mul_assoc]
    _ = Tc ^ k * Td := by rw [cancel_pow, one_mul]

theorem F3_jk_pos (k : ℕ) : ((Tai * Tci) ^ k * (Ta ^ k * Td)) wC = wC := by
  rw [member_pos, Monoid.End.coe_mul, Function.comp_apply, Td_fix_C, pow_fix Tci_fix_C]

theorem F3_jk_neg (k : ℕ) : ((Tai * Tc) ^ k * (Ta ^ k * Td)) wC = wC := by
  rw [member_neg, Monoid.End.coe_mul, Function.comp_apply, Td_fix_C, pow_fix Tc_fix_C]

/-! ### F4: f_k(a) meets a and c, for every k. -/

theorem F4_base_a : ¬ IsConj (Ta (Td wa)) (Td wa) ∧ ¬ IsConj (Ta (Td wa)) (Td wa)⁻¹ :=
  sep_left (FreeGroup.lift ![Equiv.swap 0 1, Equiv.swap 0 2, Equiv.swap 0 2, Equiv.swap 0 1])
    (by decide) (by decide)

theorem F4_base_c : ¬ IsConj (Tc (Td wa)) (Td wa) ∧ ¬ IsConj (Tc (Td wa)) (Td wa)⁻¹ :=
  sep_left (FreeGroup.lift ![Equiv.swap 0 1, Equiv.swap 0 2, Equiv.swap 0 2, Equiv.swap 0 1])
    (by decide) (by decide)

theorem coe_mul_apply (f g : Monoid.End F) (w : F) : (f * g) w = f (g w) := by
  rw [Monoid.End.coe_mul, Function.comp_apply]

theorem back (k : ℕ) (w : F) : (Tai ^ k) ((Ta ^ k) w) = w := by
  rw [← coe_mul_apply, cancel_pow]; rfl

/-- Applying the automorphism Ta^k transports (non-)conjugacy. -/
theorem conj_back {u v : F} (k : ℕ) (h : IsConj ((Ta ^ k) u) ((Ta ^ k) v)) : IsConj u v := by
  have h2 : IsConj ((Tai ^ k) ((Ta ^ k) u)) ((Tai ^ k) ((Ta ^ k) v)) :=
    MonoidHom.map_isConj (Tai ^ k) h
  rwa [back, back] at h2

theorem F4_a (k : ℕ) :
    ¬ IsConj (Ta ((Ta ^ k * Td) wa)) ((Ta ^ k * Td) wa) ∧
    ¬ IsConj (Ta ((Ta ^ k * Td) wa)) ((Ta ^ k * Td) wa)⁻¹ := by
  have h1 : Ta * (Ta ^ k * Td) = Ta ^ k * (Ta * Td) := by
    rw [← mul_assoc, ← pow_succ', pow_succ, mul_assoc]
  have e : Ta ((Ta ^ k * Td) wa) = (Ta ^ k) (Ta (Td wa)) := by
    rw [← coe_mul_apply, h1, coe_mul_apply, coe_mul_apply]
  have e2 : (Ta ^ k * Td) wa = (Ta ^ k) (Td wa) := coe_mul_apply _ _ _
  refine ⟨fun h => F4_base_a.1 (conj_back k ?_), fun h => F4_base_a.2 (conj_back k ?_)⟩
  · rwa [e, e2] at h
  · rwa [e, e2, ← map_inv] at h

theorem F4_c (k : ℕ) :
    ¬ IsConj (Tc ((Ta ^ k * Td) wa)) ((Ta ^ k * Td) wa) ∧
    ¬ IsConj (Tc ((Ta ^ k * Td) wa)) ((Ta ^ k * Td) wa)⁻¹ := by
  have hc : Commute Tc (Ta ^ k) := Commute.pow_right (F2.symm : Commute Tc Ta) k
  have h1 : Tc * (Ta ^ k * Td) = Ta ^ k * (Tc * Td) := by
    rw [← mul_assoc, hc.eq, mul_assoc]
  have e : Tc ((Ta ^ k * Td) wa) = (Ta ^ k) (Tc (Td wa)) := by
    rw [← coe_mul_apply, h1, coe_mul_apply, coe_mul_apply]
  have e2 : (Ta ^ k * Td) wa = (Ta ^ k) (Td wa) := coe_mul_apply _ _ _
  refine ⟨fun h => F4_base_c.1 (conj_back k ?_), fun h => F4_base_c.2 (conj_back k ?_)⟩
  · rwa [e, e2] at h
  · rwa [e, e2, ← map_inv] at h

end Multitwist
