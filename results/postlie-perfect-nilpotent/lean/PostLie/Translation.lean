import PostLie.Cocycle
import Mathlib.Algebra.Lie.SemiDirect

namespace PostLie

open LieAlgebra

variable {k g n : Type*} [Field k]
  [LieRing g] [LieAlgebra k g] [LieRing n] [LieAlgebra k n]

/-- The graph of a nonlinear cocycle is a homomorphism to a semidirect sum. -/
def graph (L : g →ₗ⁅k⁆ LieDerivation k n n) (P : g →ₗ[k] n)
    (hP : IsCocycle L P) : g →ₗ⁅k⁆ SemiDirectSum n g L where
  toFun a := ⟨P a, a⟩
  map_add' _ _ := by ext <;> simp
  map_smul' _ _ := by ext <;> simp
  map_lie' {a b} := by ext <;> simp [hP a b]

/-- The inner derivation whose first component is the prescribed translation velocity. -/
def translationDerivation (L : g →ₗ⁅k⁆ LieDerivation k n n) (z : n) :
    LieDerivation k (SemiDirectSum n g L) (SemiDirectSum n g L) :=
  LieDerivation.inner k _ _ ⟨z, 0⟩

@[simp] lemma translationDerivation_apply (L : g →ₗ⁅k⁆ LieDerivation k n n)
    (z : n) (h : SemiDirectSum n g L) :
    translationDerivation L z h = ⟨-⁅z, h.left⁆ + L h.right z, 0⟩ := by
  change (⟨⁅h.left, z⁆ + L h.right z - L 0 h.left, ⁅h.right, 0⁆⟩ :
    SemiDirectSum n g L) = _
  have hz : L 0 h.left = 0 := by simp
  rw [hz, sub_zero, ← lie_skew z h.left, lie_zero]
  simp only [neg_neg]

/-- Nilpotence of the second Lie algebra makes every translation derivation nilpotent. -/
lemma translationDerivation_nilpotent [LieRing.IsNilpotent n]
    (L : g →ₗ⁅k⁆ LieDerivation k n n) (z : n) :
    IsNilpotent (translationDerivation L z).toLinearMap := by
  let D := (translationDerivation L z).toLinearMap
  let B := -LieAlgebra.ad k n z
  have hB : IsNilpotent B := by
    obtain ⟨r, hr⟩ := LieAlgebra.nilpotent_ad_of_nilpotent_algebra k n
    exact (show IsNilpotent (LieAlgebra.ad k n z) from ⟨r, hr z⟩).neg
  have hp (j : ℕ) (v : n) :
      (D ^ j) (SemiDirectSum.inl L v) = SemiDirectSum.inl L ((B ^ j) v) := by
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [pow_succ', Module.End.mul_apply, ih, pow_succ', Module.End.mul_apply]
      ext <;> simp [D, B]
  obtain ⟨r, hr⟩ := hB
  refine ⟨r + 1, ?_⟩
  apply LinearMap.ext
  intro h
  rw [pow_succ, Module.End.mul_apply]
  change (D ^ r) (translationDerivation L z h) = 0
  rw [translationDerivation_apply]
  change (D ^ r) (SemiDirectSum.inl L _) = 0
  rw [hp, hr]
  rfl

section CharacteristicZero

variable [CharZero k] [LieRing.IsNilpotent n]

local instance rationalModule (L : g →ₗ⁅k⁆ LieDerivation k n n) :
    Module ℚ (SemiDirectSum n g L) :=
  Module.compHom _ (Rat.castHom k)

/-- A finite translation, obtained by exponentiating a nilpotent inner derivation. -/
noncomputable def translation (L : g →ₗ⁅k⁆ LieDerivation k n n) (z : n) :
    SemiDirectSum n g L ≃ₗ⁅k⁆ SemiDirectSum n g L :=
  (translationDerivation L z).exp (translationDerivation_nilpotent L z)

/-- Translations keep the second component fixed. -/
lemma translation_right (L : g →ₗ⁅k⁆ LieDerivation k n n) (z : n)
    (h : SemiDirectSum n g L) : (translation L z h).right = h.right := by
  let : Module ℚ g := Module.compHom _ (Rat.castHom k)
  have hc : (0 : Module.End k g).comp (SemiDirectSum.projr L).toLinearMap =
      (SemiDirectSum.projr L).toLinearMap.comp (translationDerivation L z).toLinearMap := by
    apply LinearMap.ext
    intro h
    simp
  have he := Module.End.commute_exp_left_of_commute
    (translationDerivation_nilpotent L z) (show IsNilpotent (0 : Module.End k g) from
      ⟨1, by simp⟩) hc
  have hh := LinearMap.congr_fun he h
  change (IsNilpotent.exp (translationDerivation L z).toLinearMap h).right = h.right
  simpa only [IsNilpotent.exp_zero, LinearMap.comp_apply, Module.End.one_apply,
    SemiDirectSum.projr, LieHom.coe_mk, LinearMap.coe_mk, AddHom.coe_mk] using hh.symm

/-- The first component of a translated cocycle graph. -/
noncomputable def translated (L : g →ₗ⁅k⁆ LieDerivation k n n)
    (P : g →ₗ[k] n) (hP : IsCocycle L P) (z : n) : g →ₗ[k] n :=
  (SemiDirectSum.projl L).comp
    ((translation L z).toLinearMap.comp (graph L P hP).toLinearMap)

/-- Finite translation preserves the nonlinear cocycle identity. -/
lemma translated_isCocycle (L : g →ₗ⁅k⁆ LieDerivation k n n)
    (P : g →ₗ[k] n) (hP : IsCocycle L P) (z : n) :
    IsCocycle L (translated L P hP z) := by
  intro a b
  have h := congrArg SemiDirectSum.left
    (((translation L z).toLieHom.comp (graph L P hP)).map_lie a b)
  change (translation L z (graph L P hP ⁅a, b⁆)).left =
    ⁅(translation L z (graph L P hP a)).left, (translation L z (graph L P hP b)).left⁆ +
      L (translation L z (graph L P hP a)).right
        (translation L z (graph L P hP b)).left -
      L (translation L z (graph L P hP b)).right
        (translation L z (graph L P hP a)).left at h
  simpa only [translation_right, graph, translated, LinearMap.comp_apply,
    SemiDirectSum.projl, LieHom.coe_mk, LinearMap.coe_mk, AddHom.coe_mk,
    LieHom.coe_toLinearMap, LieEquiv.coe_coe] using h

end CharacteristicZero

end PostLie
