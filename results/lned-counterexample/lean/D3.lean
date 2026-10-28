import D2

namespace LNEDPilot
open Polynomial

lemma monomial_image_iff (n : ℕ) :
    (X : ℚ[X]) ^ n ∈ V ↔ (H n).eval (1 / 2 : ℚ) = 0 := by
  constructor
  · rintro ⟨h, hI, he⟩
    obtain ⟨h0, hh⟩ := (mem_I_iff h).mp hI
    have hk0 : delta (h - H n) = 0 := by
      rw [delta_sub, he, delta_H, sub_self]
    have hk := delta_kernel_constant (h - H n) hk0
    have hc : (h - H n).eval 0 = 0 := by rw [eval_sub, h0, H_zero, sub_self]
    rw [hc, C_0] at hk
    have heq := sub_eq_zero.mp hk
    rw [← heq]
    exact hh
  · intro hh
    exact ⟨H n, (mem_I_iff (H n)).mpr ⟨H_zero n, hh⟩, delta_H n⟩

#print axioms monomial_image_iff
end LNEDPilot
