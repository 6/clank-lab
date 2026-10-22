import Mathlib
import P16c.TorusAction

/-! # `[4,4]_(s,0)` maps faces of `{4,4}_(s,0)` to faces -/

namespace P16c.Torus

open Toroid

variable {s : ℕ}

lemma mem_torusFaces {S : Set (TorusVertex s)} :
    S ∈ torusFaces s ↔ S = ∅ ∨ S = Set.univ ∨ (∃ v, S = {v}) ∨
      (∃ v, S = {v, v + (1, 0)}) ∨ (∃ v, S = {v, v + (0, 1)}) ∨
      ∃ v, S = {v, v + (1, 0), v + (0, 1), v + (1, 1)} := by
  simp only [torusFaces, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range,
    eq_comm (b := S)]
  tauto

lemma image_pair (f : Equiv.Perm (TorusVertex s)) (a b : TorusVertex s) :
    f '' {a, b} = {f a, f b} := by
  rw [Set.image_insert_eq, Set.image_singleton]

lemma image_quad (f : Equiv.Perm (TorusVertex s)) (a b c d : TorusVertex s) :
    f '' {a, b, c, d} = {f a, f b, f c, f d} := by
  rw [Set.image_insert_eq, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton]

/-- A permutation mapping every edge and square to a face maps every face to a face. -/
lemma image_mem_of (f : Equiv.Perm (TorusVertex s))
    (hh : ∀ v, f '' {v, v + (1, 0)} ∈ torusFaces s)
    (hv : ∀ v, f '' {v, v + (0, 1)} ∈ torusFaces s)
    (hq : ∀ v, f '' {v, v + (1, 0), v + (0, 1), v + (1, 1)} ∈ torusFaces s)
    {S : Set (TorusVertex s)} (hS : S ∈ torusFaces s) : f '' S ∈ torusFaces s := by
  rcases mem_torusFaces.mp hS with rfl | rfl | ⟨v, rfl⟩ | ⟨v, rfl⟩ | ⟨v, rfl⟩ | ⟨v, rfl⟩
  · exact mem_torusFaces.mpr (Or.inl (Set.image_empty _))
  · exact mem_torusFaces.mpr (Or.inr (Or.inl (Set.image_univ_of_surjective f.surjective)))
  · exact mem_torusFaces.mpr (Or.inr (Or.inr (Or.inl ⟨f v, Set.image_singleton⟩)))
  · exact hh v
  · exact hv v
  · exact hq v

lemma hface (w : TorusVertex s) {S : Set (TorusVertex s)} (h : S = {w, w + (1, 0)}) :
    S ∈ torusFaces s := mem_torusFaces.mpr (by tauto)
lemma vface (w : TorusVertex s) {S : Set (TorusVertex s)} (h : S = {w, w + (0, 1)}) :
    S ∈ torusFaces s := mem_torusFaces.mpr (by tauto)
lemma qface (w : TorusVertex s) {S : Set (TorusVertex s)}
    (h : S = {w, w + (1, 0), w + (0, 1), w + (1, 1)}) : S ∈ torusFaces s :=
  mem_torusFaces.mpr (by tauto)

lemma m0_image {S : Set (TorusVertex s)} (hS : S ∈ torusFaces s) : m0 s '' S ∈ torusFaces s := by
  refine image_mem_of _ (fun v => hface (-v.1, v.2) ?_) (fun v => vface (1 - v.1, v.2) ?_)
    (fun v => qface (-v.1, v.2) ?_) hS
  · rw [image_pair, Set.pair_comm]
    congr 2 <;> ext <;> simp <;> ring
  · rw [image_pair]
    congr 2 <;> ext <;> simp
  · rw [image_quad]
    have e1 : m0 s v = (-v.1, v.2) + (1, 0) := by ext <;> simp; ring
    have e2 : m0 s (v + (1, 0)) = (-v.1, v.2) := by ext <;> simp
    have e3 : m0 s (v + (0, 1)) = (-v.1, v.2) + (1, 1) := by ext <;> simp; ring
    have e4 : m0 s (v + (1, 1)) = (-v.1, v.2) + (0, 1) := by ext <;> simp
    rw [e1, e2, e3, e4]
    ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto

lemma m1_image {S : Set (TorusVertex s)} (hS : S ∈ torusFaces s) : m1 s '' S ∈ torusFaces s := by
  refine image_mem_of _ (fun v => vface (v.2, v.1) ?_) (fun v => hface (v.2, v.1) ?_)
    (fun v => qface (v.2, v.1) ?_) hS
  · rw [image_pair]
    congr 2
  · rw [image_pair]
    congr 2
  · rw [image_quad]
    have e1 : m1 s v = (v.2, v.1) := by ext <;> simp
    have e2 : m1 s (v + (1, 0)) = (v.2, v.1) + (0, 1) := by ext <;> simp
    have e3 : m1 s (v + (0, 1)) = (v.2, v.1) + (1, 0) := by ext <;> simp
    have e4 : m1 s (v + (1, 1)) = (v.2, v.1) + (1, 1) := by ext <;> simp
    rw [e1, e2, e3, e4]
    ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto

lemma m2_image {S : Set (TorusVertex s)} (hS : S ∈ torusFaces s) : reflectY s '' S ∈ torusFaces s := by
  refine image_mem_of _ (fun v => hface (v.1, -v.2) ?_) (fun v => vface (v.1, -v.2 - 1) ?_)
    (fun v => qface (v.1, -v.2 - 1) ?_) hS
  · rw [image_pair]
    congr 2; ext <;> simp
  · rw [image_pair, Set.pair_comm]
    congr 2 <;> ext <;> simp <;> ring
  · rw [image_quad]
    have e1 : reflectY s v = (v.1, -v.2 - 1) + (0, 1) := by ext <;> simp
    have e2 : reflectY s (v + (1, 0)) = (v.1, -v.2 - 1) + (1, 1) := by ext <;> simp
    have e3 : reflectY s (v + (0, 1)) = (v.1, -v.2 - 1) := by ext <;> simp; ring
    have e4 : reflectY s (v + (1, 1)) = (v.1, -v.2 - 1) + (1, 0) := by ext <;> simp; ring
    rw [e1, e2, e3, e4]
    ext p; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto

/-- Every element of `[4,4]_(s,0)` maps faces of `{4,4}_(s,0)` to faces. -/
lemma phi_image_mem (g : G s) {S : Set (TorusVertex s)} (hS : S ∈ torusFaces s) :
    phi s g '' S ∈ torusFaces s := by
  have hg : g ∈ Subgroup.closure (Set.range (r s)) := by
    rw [show Subgroup.closure (Set.range (r s)) = ⊤ from PresentedGroup.closure_range_of _]
    trivial
  have key : ∀ i : Fin 3, ∀ S ∈ torusFaces s, phi s (r s i) '' S ∈ torusFaces s := by
    intro i S hS
    fin_cases i
    · simpa using m0_image hS
    · simpa using m1_image hS
    · simpa using m2_image hS
  induction hg using Subgroup.closure_induction'' generalizing S with
  | mem x hx => obtain ⟨i, rfl⟩ := hx; exact key i S hS
  | inv_mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    have : (r s i)⁻¹ = r s i := inv_eq_of_mul_eq_one_right (r_mul_self s i)
    rw [this]; exact key i S hS
  | one => simpa using hS
  | mul x y _ _ ihx ihy =>
    rw [map_mul, Equiv.Perm.coe_mul, Set.image_comp]
    exact ihx (ihy hS)

end P16c.Torus

namespace P16c.Torus

variable {s : ℕ}

lemma torusProj_add (v w : ℤ × ℤ) : torusProj s (v + w) = torusProj s v + torusProj s w := by
  ext <;> simp [torusProj]

lemma torusProj_surjective : Function.Surjective (torusProj s) := fun p => by
  obtain ⟨a, ha⟩ := ZMod.intCast_surjective p.1
  obtain ⟨b, hb⟩ := ZMod.intCast_surjective p.2
  exact ⟨(a, b), by ext <;> simp [torusProj, ha, hb]⟩

lemma mem_planeFaces {S : Set (ℤ × ℤ)} :
    S ∈ planeFaces ↔ S = ∅ ∨ S = Set.univ ∨ (∃ v, S = {v}) ∨
      (∃ v, S = {v, v + (1, 0)}) ∨ (∃ v, S = {v, v + (0, 1)}) ∨
      ∃ v, S = {v, v + (1, 0), v + (0, 1), v + (1, 1)} := by
  simp only [planeFaces, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range,
    eq_comm (b := S)]
  tauto

/-- The faces of `{4,4}_(s,0)` are exactly the images in `(ℤ/s)²` of the faces of
the square tessellation of the plane. -/
theorem torusFaces_eq_image : torusFaces s = (fun F => torusProj s '' F) '' planeFaces := by
  have e10 : torusProj s (1, 0) = (1, 0) := by ext <;> simp [torusProj]
  have e01 : torusProj s (0, 1) = (0, 1) := by ext <;> simp [torusProj]
  have e11 : torusProj s (1, 1) = (1, 1) := by ext <;> simp [torusProj]
  have img : ∀ F : Set (ℤ × ℤ), F ∈ planeFaces → torusProj s '' F ∈ torusFaces s := by
    intro F hF
    rcases mem_planeFaces.mp hF with rfl | rfl | ⟨v, rfl⟩ | ⟨v, rfl⟩ | ⟨v, rfl⟩ | ⟨v, rfl⟩
    · exact mem_torusFaces.mpr (Or.inl (Set.image_empty _))
    · exact mem_torusFaces.mpr (Or.inr (Or.inl (Set.image_univ_of_surjective torusProj_surjective)))
    · exact mem_torusFaces.mpr (Or.inr (Or.inr (Or.inl ⟨_, Set.image_singleton⟩)))
    · exact hface (torusProj s v) (by
        rw [Set.image_insert_eq, Set.image_singleton, torusProj_add, e10])
    · exact vface (torusProj s v) (by
        rw [Set.image_insert_eq, Set.image_singleton, torusProj_add, e01])
    · exact qface (torusProj s v) (by
        rw [Set.image_insert_eq, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton,
          torusProj_add, torusProj_add, torusProj_add, e10, e01, e11])
  ext S
  constructor
  · intro hS
    have pre : ∀ p : TorusVertex s, ∃ v, torusProj s v = p := torusProj_surjective
    rcases mem_torusFaces.mp hS with rfl | rfl | ⟨p, rfl⟩ | ⟨p, rfl⟩ | ⟨p, rfl⟩ | ⟨p, rfl⟩
    · exact ⟨∅, by simp [planeFaces], Set.image_empty _⟩
    · exact ⟨Set.univ, by simp [planeFaces], Set.image_univ_of_surjective torusProj_surjective⟩
    · obtain ⟨v, rfl⟩ := pre p
      exact ⟨{v}, by simp [planeFaces], Set.image_singleton⟩
    · obtain ⟨v, rfl⟩ := pre p
      refine ⟨{v, v + (1, 0)}, by simp [planeFaces], ?_⟩
      dsimp only
      rw [Set.image_insert_eq, Set.image_singleton, torusProj_add, e10]
    · obtain ⟨v, rfl⟩ := pre p
      refine ⟨{v, v + (0, 1)}, by simp [planeFaces], ?_⟩
      dsimp only
      rw [Set.image_insert_eq, Set.image_singleton, torusProj_add, e01]
    · obtain ⟨v, rfl⟩ := pre p
      refine ⟨{v, v + (1, 0), v + (0, 1), v + (1, 1)}, by simp [planeFaces], ?_⟩
      dsimp only
      rw [Set.image_insert_eq, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton,
        torusProj_add, torusProj_add, torusProj_add, e10, e01, e11]
  · rintro ⟨F, hF, rfl⟩
    exact img F hF

end P16c.Torus
