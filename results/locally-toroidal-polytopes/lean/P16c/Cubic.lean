import Mathlib

namespace P16c
open Polynomial
variable {K A : Type*} [Field K] [Ring A] [Algebra K A]

/-- A linear factor is coprime to a polynomial exactly when it is not a root. -/
lemma coprime_linear_of_eval_ne (x : K) (f : K[X]) (h : f.eval x ≠ 0) :
    IsCoprime (X - C x) f := by
  apply (irreducible_X_sub_C x).coprime_iff_not_dvd.mpr
  simpa [dvd_iff_isRoot, IsRoot] using h

/-- A nonidentity element killed by the squarefree polynomial with roots 1,l,l⁻¹
has exactly the order of l. No diagonalization or closure field is required. -/
lemma cubic_order (M : A) (l : K) (hl : l ≠ 0) (hl1 : l ≠ 1) (hl2 : l ^ 2 ≠ 1)
    (hM : aeval M ((X - C 1) * ((X - C l) * (X - C l⁻¹))) = 0)
    (hM1 : M ≠ 1) : orderOf M = orderOf l := by
  have hinv1 : l⁻¹ ≠ 1 := by simpa using hl1
  have hdiff : l ≠ l⁻¹ := by
    intro h
    apply hl2
    have := congrArg (fun x : K => x * l) h
    simpa [hl, pow_two] using this
  have hcop (x y : K) (h : x ≠ y) : IsCoprime (X - C x) (X - C y) :=
    isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr h).isUnit
  rw [orderOf_eq_orderOf_iff]
  intro n
  let f : K[X] := X ^ n - 1
  have heval : aeval M f = M ^ n - 1 := by simp [f]
  constructor
  · intro hn
    by_contra hn'
    have hninv : (l⁻¹) ^ n ≠ 1 := by simpa [inv_pow] using hn'
    have hcopf : IsCoprime ((X - C l) * (X - C l⁻¹)) f :=
      (coprime_linear_of_eval_ne l f (by simpa [f] using sub_ne_zero.mpr hn')).mul_left
        (coprime_linear_of_eval_ne l⁻¹ f (by simpa [f] using sub_ne_zero.mpr hninv))
    have hdivf : minpoly K M ∣ f := minpoly.dvd K M (by rw [heval, hn, sub_self])
    have hdivM : minpoly K M ∣ X - C 1 :=
      (hcopf.symm.of_isCoprime_of_dvd_left hdivf).dvd_of_dvd_mul_right (minpoly.dvd K M hM)
    have hz : aeval M (X - C (1 : K)) = 0 := minpoly.dvd_iff.mp hdivM
    apply hM1
    exact sub_eq_zero.mp (by simpa using hz)
  · intro hn
    have hninv : (l⁻¹) ^ n = 1 := by rw [inv_pow, hn, inv_one]
    have hd1 : X - C (1 : K) ∣ f := by rw [dvd_iff_isRoot]; simp [IsRoot, f]
    have hdl : X - C l ∣ f := by simp [dvd_iff_isRoot, IsRoot, f, hn]
    have hdi : X - C l⁻¹ ∣ f := by simp [dvd_iff_isRoot, IsRoot, f, hninv]
    have hd : (X - C (1 : K)) * ((X - C l) * (X - C l⁻¹)) ∣ f :=
      ((hcop 1 l hl1.symm).mul_right (hcop 1 l⁻¹ hinv1.symm)).mul_dvd hd1
        ((hcop l l⁻¹ hdiff).mul_dvd hdl hdi)
    have hz := Polynomial.aeval_eq_zero_of_dvd_aeval_eq_zero hd hM
    rw [heval] at hz
    exact sub_eq_zero.mp hz
end P16c
