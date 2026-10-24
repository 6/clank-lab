import V2

/-!
Exact types for all declarations in `V2.lean`, concrete controls, and axiom
guards. These are algebraic statements; no surface or pseudo-Anosov theorem
is asserted here.
-/

set_option maxRecDepth 100000

open Multitwist Multitwist.V2

-- Integer normal form in an arbitrary group, with commutation stated.
example {G : Type*} [Group G] (A C D : G) (h : Commute A C) (k n : ℤ) :
    (A * C) ^ n * (A ^ (-1 : ℤ) * C ^ (-(k+1)) * D) =
      A ^ (n-1) * C ^ (n-k-1) * D := integer_identity A C D h k n

-- Exact parameterization in the original Artin/free-group model.
example (k : ℕ) : g k = Tai * Tci ^ (k+1) * Td := rfl
example : t = Ta * Tc := rfl

example {M : Type*} [Monoid M] {a b : M} (h : a * b = 1) (n : ℕ) :
    a ^ n * b ^ n = 1 := cancel_powers h n

-- The two exceptional members, as endomorphisms and as fixed words.
example (k : ℕ) : t * g k = Tci ^ k * Td := first_member k
example (k : ℕ) : t ^ (k+1) * g k = Ta ^ k * Td := second_member k
example (k : ℕ) : ((t ^ 1) * g k) wC = wC := fixed_C k
example (k : ℕ) : ((t ^ (k+1)) * g k) wCp = wCp := fixed_Cp k

-- The inverse and commutation data used to transport nonconjugacy.
example (k : ℕ) : initial k = Tai * Tci ^ (k+1) := rfl
example (k : ℕ) : undo k = Tc ^ (k+1) * Ta := rfl
example (k : ℕ) : undo k * initial k = 1 := undo_initial k
example : Ta * Tci = Tci * Ta := Ta_Tci
example (k : ℕ) : Commute Ta (initial k) := initial_commute_a k
example (k : ℕ) : Commute Tc (initial k) := initial_commute_c k
example {e b : Monoid.End F} (hbe : b * e = 1) {u v : F}
    (h : IsConj (e u) (e v)) : IsConj u v := reflect_conj hbe h
example {e b z : Monoid.End F} {u : F} (hbe : b * e = 1)
    (hc : Commute z e) (hn : ¬ IsConj (z u) u ∧ ¬ IsConj (z u) u⁻¹) :
    ¬ IsConj (z (e u)) (e u) ∧ ¬ IsConj (z (e u)) (e u)⁻¹ :=
  transport hbe hc hn

-- For every k, g_k(a) is moved out of its conjugacy class up to inversion.
example (k : ℕ) :
    ¬ IsConj (Ta ((g k) wa)) ((g k) wa) ∧
    ¬ IsConj (Ta ((g k) wa)) ((g k) wa)⁻¹ := nonconj_a k
example (k : ℕ) :
    ¬ IsConj (Tc ((g k) wa)) ((g k) wa) ∧
    ¬ IsConj (Tc ((g k) wa)) ((g k) wa)⁻¹ := nonconj_c k

-- Swapping C and C' makes each fixed-word assertion false at k = 1.
example : ((t ^ 1) * g 1) wCp ≠ wCp := by decide
example : ((t ^ (1+1)) * g 1) wC ≠ wC := by decide

-- Shifting the first exceptional exponent to 0 fails at k = 1.
example : ((t ^ 0) * g 1) wC ≠ wC := by decide
-- Shifting the second exceptional exponent from k+1 to k fails at k = 2.
example : ((t ^ 2) * g 2) wCp ≠ wCp := by decide
-- Replacing the exponent k+1 inside g_k by k fails at k = 1, n = 2.
example : ((t ^ 2) * (Tai * Tci ^ (1 : ℕ) * Td)) wCp ≠ wCp := by decide

-- Omitting Td makes both purported nonconjugacy conclusions false:
-- both endomorphisms fix this word, hence preserve its conjugacy class.
example : Ta ((initial 1) wa) = (initial 1) wa := by decide
example : Tc ((initial 1) wa) = (initial 1) wa := by decide
example : IsConj (Ta ((initial 1) wa)) ((initial 1) wa) :=
  isConj_iff.mpr ⟨1, by decide⟩
example : IsConj (Tc ((initial 1) wa)) ((initial 1) wa) :=
  isConj_iff.mpr ⟨1, by decide⟩

-- Without commutation, the claimed integer identity is false in S_3.
example : let A : Equiv.Perm (Fin 3) := Equiv.swap 0 1
          let C : Equiv.Perm (Fin 3) := Equiv.swap 1 2
          (A * C) ^ (1 : ℤ) * (A ^ (-1 : ℤ) * C ^ (-(0+1) : ℤ) * 1) ≠
            A ^ (1-1 : ℤ) * C ^ (1-0-1 : ℤ) * 1 := by decide

/-- info: 'Multitwist.V2.integer_identity' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Multitwist.V2.integer_identity

/-- info: 'Multitwist.V2.g' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Multitwist.V2.g

/-- info: 'Multitwist.V2.t' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Multitwist.V2.t

/-- info: 'Multitwist.V2.cancel_powers' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Multitwist.V2.cancel_powers

/-- info: 'Multitwist.V2.first_member' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Multitwist.V2.first_member

/-- info: 'Multitwist.V2.second_member' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Multitwist.V2.second_member

/-- info: 'Multitwist.V2.fixed_C' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Multitwist.V2.fixed_C

/-- info: 'Multitwist.V2.fixed_Cp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Multitwist.V2.fixed_Cp

/-- info: 'Multitwist.V2.initial' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Multitwist.V2.initial

/-- info: 'Multitwist.V2.undo' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Multitwist.V2.undo

/-- info: 'Multitwist.V2.undo_initial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Multitwist.V2.undo_initial

/-- info: 'Multitwist.V2.Ta_Tci' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Multitwist.V2.Ta_Tci

/-- info: 'Multitwist.V2.initial_commute_a' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Multitwist.V2.initial_commute_a

/-- info: 'Multitwist.V2.initial_commute_c' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Multitwist.V2.initial_commute_c

/-- info: 'Multitwist.V2.reflect_conj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Multitwist.V2.reflect_conj

/-- info: 'Multitwist.V2.transport' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Multitwist.V2.transport

/-- info: 'Multitwist.V2.nonconj_a' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Multitwist.V2.nonconj_a

/-- info: 'Multitwist.V2.nonconj_c' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Multitwist.V2.nonconj_c
