import CubelikeSC.Frame
import CubelikeSC.LemmaF

/-!
# Cosets numbered as in Lemma F

`enc : Fin 8 → (ZMod 2)^3` reads bit `i` of `u` as coordinate `i`; it is a
bijection, `enc 0 = 0`, and `bdot 3 u h` is the dot product of `enc u, enc h`.
All three facts are decided by the kernel.
-/

namespace CubelikeSC

def enc (u : Fin 8) : W := fun i => if u.val.testBit i then 1 else 0

def dec (c : W) : Fin 8 := ⟨(c 0).val + 2 * (c 1).val + 4 * (c 2).val, by
  have := (c 0).val_lt; have := (c 1).val_lt; have := (c 2).val_lt; omega⟩

set_option maxRecDepth 10000 in
theorem dec_enc : ∀ u : Fin 8, dec (enc u) = u := by decide

set_option maxRecDepth 10000 in
theorem enc_dec : ∀ c : W, enc (dec c) = c := by decide

set_option maxRecDepth 10000 in
theorem bdot_enc : ∀ u h : Fin 8, bdot 3 u h = (enc u ⬝ᵥ enc h).val := by decide

theorem enc_zero : enc 0 = 0 := by decide

/-- `enc` as an equivalence. -/
def encEquiv : Fin 8 ≃ W where
  toFun := enc
  invFun := dec
  left_inv := dec_enc
  right_inv := enc_dec

lemma enc_injective : Function.Injective enc := encEquiv.injective

lemma dec_injective : Function.Injective dec := encEquiv.symm.injective

lemma bdot_dec (u : Fin 8) (c : W) : bdot 3 u (dec c) = (c ⬝ᵥ enc u).val := by
  rw [bdot_enc, enc_dec, dotProduct_comm]

end CubelikeSC
