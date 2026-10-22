import Mathlib
import P16c.TorusAction

/-! # Stabilizers of the base faces of `{4,4}_(s,0)` in `[4,4]_(s,0)`

For `s ≥ 3`, an element of `[4,4]_(s,0)` mapping the base vertex, edge or square
into itself lies in `⟨r1, r2⟩`, `⟨r0, r2⟩` or `⟨r0, r1⟩` respectively (stated for
any subgroup containing those generators). Also the transitivity statements used
for order reflection: an element mapping a base face of smaller type into a base
face of larger type agrees with an element of the larger stabilizer on the
smaller face. -/

namespace P16c.Torus

open Toroid

variable {s : ℕ}

/-- The base edge `{0, (1,0)}` and square `{0, (1,0), (0,1), (1,1)}`. -/
def E (s : ℕ) : Set (TorusVertex s) := {(0, 0), (1, 0)}
def Q (s : ℕ) : Set (TorusVertex s) := {(0, 0), (1, 0), (0, 1), (1, 1)}

section Facts
variable (hs3 : 3 ≤ s)
include hs3

lemma one_ne_zero' : (1 : ZMod s) ≠ 0 := by
  have := (ZMod.natCast_eq_zero_iff 1 s).not.mpr (by intro h; have := Nat.le_of_dvd one_pos h; omega)
  simpa using this

lemma two_ne_zero' : (2 : ZMod s) ≠ 0 := by
  have := (ZMod.natCast_eq_zero_iff 2 s).not.mpr (by intro h; have := Nat.le_of_dvd two_pos h; omega)
  simpa using this

lemma neg_one_ne_zero' : (-1 : ZMod s) ≠ 0 := neg_ne_zero.mpr (one_ne_zero' hs3)

lemma neg_one_ne_one' : (-1 : ZMod s) ≠ 1 := by
  intro h
  apply two_ne_zero' hs3
  linear_combination -h

lemma two_ne_one' : (2 : ZMod s) ≠ 1 := by
  intro h
  apply one_ne_zero' hs3
  linear_combination h

end Facts

lemma phi_D_zero {d : G s} (hd : d ∈ D s) : phi s d (0, 0) = (0, 0) := by
  rcases D_cases s hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

/-- An element fixing the base vertex lies in `⟨r1, r2⟩`. -/
lemma mem_D_of_fix [NeZero s] {g : G s} (h : phi s g (0, 0) = (0, 0)) : g ∈ D s := by
  obtain ⟨a, b, d, hd, rfl⟩ := normal_form s g
  rw [map_mul, Equiv.Perm.mul_apply, phi_D_zero hd, phi_tr] at h
  simp only [Prod.mk_add_mk, zero_add, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  simpa [tr] using hd

variable (K : Subgroup (G s))

lemma D_le (h1 : r s 1 ∈ K) (h2 : r s 2 ∈ K) : D s ≤ K := by
  rw [D, Subgroup.closure_le]
  rintro x (rfl | rfl) <;> assumption

section
variable (hs3 : 3 ≤ s)
include hs3

/-- Elements of `⟨r1, r2⟩` sending `(1,0)` into the base edge lie in `⟨r2⟩`. -/
lemma D_edge (h2 : r s 2 ∈ K) {d : G s} (hd : d ∈ D s) (he : phi s d (1, 0) ∈ E s) : d ∈ K := by
  have f1 := one_ne_zero' hs3
  have f2 := neg_one_ne_zero' hs3
  have f3 := neg_one_ne_one' hs3
  rcases D_cases s hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [E, f1, f2, f3, f1.symm] at he ⊢
  all_goals assumption

/-- Elements of `⟨r1, r2⟩` sending `(1,0)` and `(0,1)` into the base square lie in `⟨r1⟩`. -/
lemma D_square (h1 : r s 1 ∈ K) {d : G s} (hd : d ∈ D s) (he : phi s d (1, 0) ∈ Q s)
    (hf : phi s d (0, 1) ∈ Q s) : d ∈ K := by
  have f1 := one_ne_zero' hs3
  have f2 := neg_one_ne_zero' hs3
  have f3 := neg_one_ne_one' hs3
  rcases D_cases s hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Q, f1, f2, f3, f1.symm] at he hf ⊢
  all_goals assumption

/-- Elements of `⟨r1, r2⟩` sending `(1,0)` into the base square send the base edge
to an edge of the square: up to `r1` they lie in `⟨r2⟩`. -/
lemma D_edge_in_square (h1 : r s 1 ∈ K)
    {d : G s} (hd : d ∈ D s) (he : phi s d (1, 0) ∈ Q s) :
    ∃ c ∈ K, c * d ∈ Subgroup.closure {r s 2} := by
  have f1 := one_ne_zero' hs3
  have f2 := neg_one_ne_zero' hs3
  have f3 := neg_one_ne_one' hs3
  have r2_mem : r s 2 ∈ Subgroup.closure {r s 2} := Subgroup.subset_closure rfl
  have i1 := r_mul_self s 1
  rcases D_cases s hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Q, f1, f2, f3, f1.symm] at he
  · exact ⟨1, K.one_mem, by simp⟩
  · exact ⟨r s 1, h1, by simp [i1]⟩
  · exact ⟨1, K.one_mem, by simp⟩
  · exact ⟨r s 1, h1, by simp [← mul_assoc, i1]⟩

end

/-- Elements of `⟨r0⟩` move a point of the base edge to `0`, preserving the edge. -/
lemma toZero2 (h0 : r s 0 ∈ K) {g : G s} (h : phi s g (0, 0) ∈ E s) :
    ∃ c ∈ K, phi s (c * g) (0, 0) = (0, 0) ∧ ∀ p, phi s g p ∈ E s → phi s (c * g) p ∈ E s := by
  simp only [E, Set.mem_insert_iff, Set.mem_singleton_iff] at h
  rcases h with h | h
  · exact ⟨1, K.one_mem, by simpa using h, fun p hp => by simpa using hp⟩
  · refine ⟨r s 0, h0, by simp [h], fun p hp => ?_⟩
    simp only [E, Set.mem_insert_iff, Set.mem_singleton_iff] at hp ⊢
    rw [map_mul, Equiv.Perm.mul_apply, phi_r0]
    rcases hp with hp | hp <;> simp [hp]

lemma m0_Q {p : TorusVertex s} (hp : p ∈ Q s) : m0 s p ∈ Q s := by
  simp only [Q, Set.mem_insert_iff, Set.mem_singleton_iff] at hp ⊢
  rcases hp with rfl | rfl | rfl | rfl <;> simp

lemma m1_Q {p : TorusVertex s} (hp : p ∈ Q s) : m1 s p ∈ Q s := by
  simp only [Q, Set.mem_insert_iff, Set.mem_singleton_iff] at hp ⊢
  rcases hp with rfl | rfl | rfl | rfl <;> simp

/-- Elements of `⟨r0, r1⟩` move a vertex of the base square to `0`, preserving the square. -/
lemma toZero3 (h0 : r s 0 ∈ K) (h1 : r s 1 ∈ K) {g : G s} (h : phi s g (0, 0) ∈ Q s) :
    ∃ c ∈ K, phi s (c * g) (0, 0) = (0, 0) ∧ ∀ p, phi s g p ∈ Q s → phi s (c * g) p ∈ Q s := by
  have hQ : ∀ c : G s, (∀ p, p ∈ Q s → phi s c p ∈ Q s) →
      ∀ p, phi s g p ∈ Q s → phi s (c * g) p ∈ Q s := fun c hc p hp => by
    rw [map_mul, Equiv.Perm.mul_apply]; exact hc _ hp
  simp only [Q, Set.mem_insert_iff, Set.mem_singleton_iff] at h
  rcases h with h | h | h | h
  · exact ⟨1, K.one_mem, by simpa using h, hQ 1 fun p hp => by simpa using hp⟩
  · exact ⟨r s 0, h0, by simp [h], hQ _ fun p hp => by simpa using m0_Q hp⟩
  · refine ⟨r s 1 * r s 0 * r s 1, K.mul_mem (K.mul_mem h1 h0) h1, by simp [h], hQ _ ?_⟩
    intro p hp
    simpa using m1_Q (m0_Q (m1_Q hp))
  · refine ⟨r s 0 * r s 1 * r s 0 * r s 1, K.mul_mem (K.mul_mem (K.mul_mem h0 h1) h0) h1,
      by simp [h], hQ _ ?_⟩
    intro p hp
    simpa using m0_Q (m1_Q (m0_Q (m1_Q hp)))

lemma image_sub {g : G s} {S T : Set (TorusVertex s)} (h : phi s g '' S ⊆ T) {p : TorusVertex s}
    (hp : p ∈ S) : phi s g p ∈ T := h (Set.mem_image_of_mem _ hp)

/-- The stabilizer of the base vertex. -/
lemma stab1 [NeZero s] (h1 : r s 1 ∈ K) (h2 : r s 2 ∈ K) {g : G s}
    (h : phi s g '' {(0, 0)} ⊆ {(0, 0)}) : g ∈ K :=
  D_le K h1 h2 (mem_D_of_fix (image_sub h rfl))

section
variable (hs3 : 3 ≤ s)
include hs3

/-- The stabilizer of the base edge. -/
lemma stab2 (h0 : r s 0 ∈ K) (h2 : r s 2 ∈ K) {g : G s} (h : phi s g '' E s ⊆ E s) : g ∈ K := by
  haveI : NeZero s := ⟨by omega⟩
  obtain ⟨c, hc, hc0, hcE⟩ := toZero2 K h0 (image_sub h (by simp [E]))
  have hd := mem_D_of_fix hc0
  have := D_edge K hs3 h2 hd (hcE _ (image_sub h (by simp [E])))
  simpa using K.mul_mem (K.inv_mem hc) this

/-- The stabilizer of the base square. -/
lemma stab3 (h0 : r s 0 ∈ K) (h1 : r s 1 ∈ K) {g : G s} (h : phi s g '' Q s ⊆ Q s) : g ∈ K := by
  haveI : NeZero s := ⟨by omega⟩
  obtain ⟨c, hc, hc0, hcQ⟩ := toZero3 K h0 h1 (image_sub h (by simp [Q]))
  have hd := mem_D_of_fix hc0
  have := D_square K hs3 h1 hd (hcQ _ (image_sub h (by simp [Q])))
    (hcQ _ (image_sub h (by simp [Q])))
  simpa using K.mul_mem (K.inv_mem hc) this

end

/-- A vertex in the base edge: `g` agrees on the base vertex with an element of `⟨r0, r2⟩`. -/
lemma reach12 [NeZero s] (K' : Subgroup (G s)) (h1 : r s 1 ∈ K') (h2 : r s 2 ∈ K')
    (h0 : r s 0 ∈ K) {g : G s} (h : phi s g (0, 0) ∈ E s) : ∃ h' ∈ K', g * h' ∈ K := by
  obtain ⟨c, hc, hc0, -⟩ := toZero2 K h0 h
  refine ⟨(c * g)⁻¹, K'.inv_mem (D_le K' h1 h2 (mem_D_of_fix hc0)), ?_⟩
  simpa [mul_assoc] using K.inv_mem hc

/-- A vertex in the base square. -/
lemma reach13 [NeZero s] (K' : Subgroup (G s)) (h1 : r s 1 ∈ K') (h2 : r s 2 ∈ K')
    (h0 : r s 0 ∈ K) (h1K : r s 1 ∈ K) {g : G s} (h : phi s g (0, 0) ∈ Q s) :
    ∃ h' ∈ K', g * h' ∈ K := by
  obtain ⟨c, hc, hc0, -⟩ := toZero3 K h0 h1K h
  refine ⟨(c * g)⁻¹, K'.inv_mem (D_le K' h1 h2 (mem_D_of_fix hc0)), ?_⟩
  simpa [mul_assoc] using K.inv_mem hc

/-- An edge in the base square. -/
lemma reach23 (hs3 : 3 ≤ s) (K' : Subgroup (G s)) (h2 : r s 2 ∈ K')
    (h0 : r s 0 ∈ K) (h1K : r s 1 ∈ K) {g : G s} (h : phi s g '' E s ⊆ Q s) :
    ∃ h' ∈ K', g * h' ∈ K := by
  haveI : NeZero s := ⟨by omega⟩
  obtain ⟨c, hc, hc0, hcQ⟩ := toZero3 K h0 h1K (image_sub h (by simp [E]))
  obtain ⟨c', hc', hc'd⟩ := D_edge_in_square K hs3 h1K (mem_D_of_fix hc0)
    (hcQ _ (image_sub h (by simp [E])))
  have hK' : Subgroup.closure {r s 2} ≤ K' := (Subgroup.closure_le _).mpr (by simpa using h2)
  refine ⟨(c' * (c * g))⁻¹, K'.inv_mem (hK' hc'd), ?_⟩
  have : g * (c' * (c * g))⁻¹ = c⁻¹ * c'⁻¹ := by group
  rw [this]
  exact K.mul_mem (K.inv_mem hc) (K.inv_mem hc')

end P16c.Torus
