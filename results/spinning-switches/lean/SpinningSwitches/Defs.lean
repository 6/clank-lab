import Mathlib

/-!
# Generalized spinning switches (Kagey, J. Combin. Theory Ser. A 200 (2023), arXiv:2210.09408)

Switches behave like a finite group `G`, sit at the points of a finite `H`-set `Ω`, and an
adversary permutes them by `H`.  The base `K = Ω → G` of the wreath product carries the action
`(h • k) ω = k (h⁻¹ • ω)` (Kagey, Def. 7), and the wreath product is Mathlib's semidirect product
`K ⋊[spin] H`, whose multiplication is `(k, h) * (k', h') = (k * (h • k'), h * h')`.
-/

namespace SpinningSwitches

variable {G H Ω : Type*} [Group G] [Group H] [MulAction H Ω]

/-- The adversary's action on switch states: `(spin h k) ω = k (h⁻¹ • ω)`. -/
def spin (G : Type*) [Group G] (H : Type*) [Group H] (Ω : Type*) [MulAction H Ω] :
    H →* MulAut (Ω → G) where
  toFun h :=
    { toFun := fun k ω => k (h⁻¹ • ω)
      invFun := fun k ω => k (h • ω)
      left_inv := fun k => by funext ω; simp
      right_inv := fun k => by funext ω; simp
      map_mul' := fun _ _ => rfl }
  map_one' := by ext; simp
  map_mul' := fun a b => by ext k ω; simp [mul_smul]

@[simp] theorem spin_apply (h : H) (k : Ω → G) (ω : Ω) : spin G H Ω h k ω = k (h⁻¹ • ω) := rfl

/-- One turn: the solver's move `k` followed by the adversary's spin `h`, an element of the
wreath product `G ≀_Ω H`. -/
def turn (k : Ω → G) (h : H) : (Ω → G) ⋊[spin G H Ω] H := ⟨k, h⟩

@[simp] theorem turn_left (k : Ω → G) (h : H) : (turn k h).left = k := rfl
@[simp] theorem turn_right (k : Ω → G) (h : H) : (turn k h).right = h := rfl

/-- Kagey, Def. 9: `ks` is a surjective strategy if for every adversary sequence `hs` the
projections to the base of the partial products `1, m₁, m₁m₂, …, m₁⋯m_N`
(`mᵢ = (kᵢ, hᵢ)`) cover the whole base `Ω → G`. -/
def IsSurjectiveStrategy (H : Type*) [Group H] [MulAction H Ω] (ks : List (Ω → G)) : Prop :=
  ∀ hs : List H, hs.length = ks.length → ∀ x : Ω → G,
    ∃ j ≤ ks.length, ((List.zipWith turn ks hs).take j).prod.left = x

end SpinningSwitches
