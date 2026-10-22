import StanleySnf.Main
import StanleySnf.Bridge

/-!
# The unconditional theorem

`main` with its classical hypothesis discharged by `bridge`.
-/

namespace StanleySnf

/-- **Stanley's class-sum Smith form (MathOverflow 335226), for every `n ≥ 1`.**
The matrix `M n` of multiplication by the class sum of all `n`-cycles on the centre of
`ℤ[S_n]`, in the class-sum basis, has Smith normal form
`diag(stanleyD n 0, …, stanleyD n (n-1), 0, …, 0)`, where `stanleyD n 0 = 1` and
`stanleyD n k = c·k!/gcd(k,n)` with `c = 2` if `k ≡ n (mod 2)` else `1`; and these
invariant factors form a divisor chain. -/
theorem stanley_class_sum_snf (n : ℕ) (hn : 0 < n) :
    HasStanleySNF n (M n) ∧ (∀ r, r + 1 < n → stanleyD n r ∣ stanleyD n (r + 1)) :=
  main n hn (fun μ ν => bridge n hn μ ν)

end StanleySnf
