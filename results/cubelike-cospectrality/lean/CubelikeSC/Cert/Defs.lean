import CubelikeSC.LemmaF

/-!
# Lemma F certificates: the checker (the paper, LP weak duality)

A coset is `(zero, num, r)`: coset `0` iff `zero`, mean `num/15` for coset `0`
and `num` otherwise, residue `r` mod 4. Costs are scaled by 15000, the unit of
the certificate weights. For weights `w ≥ 0` on values,
`L(w) = Σ_u min_{(α,β)} (c_u(α,β) + w(α) + [β ≠ α] w(β)) - Σ_v w_v`
is a lower bound on the total cost of every admissible assignment, so
`L(w) > 128 n` refutes the case. Everything here is executable and is
evaluated by the kernel.
-/

namespace CubelikeSC.Cert

/-- `(zero, num, r)`. -/
abbrev Coset := Bool × Int × Int

def den (c : Coset) : Int := if c.1 then 15 else 1

/-- The values `v ∈ [-n, n]` with `v ≡ r (mod 4)`. -/
def vals (n : Nat) (r : Int) : List Int :=
  let lo : Int := -(n : Int) + ((r + n) % 4)
  (List.range (((n : Int) - lo) / 4 + 1).toNat).map fun (i : Nat) => lo + 4 * (i : Int)

/-- Conditions 1, 2 and 4 for `α, β` taken from `vals n r` (condition 3). -/
def ok (n : Nat) (c : Coset) (a b : Int) : Bool :=
  decide (den c * a ≤ c.2.1) && decide (c.2.1 ≤ den c * b) && decide (a ≤ b) &&
    (decide (a ≠ b) || decide (den c * a = c.2.1)) &&
    (c.1 || (decide (a ≠ n) && decide (b ≠ n)))

/-- The cost of `(α, β)` times 15000. -/
def costS (n : Nat) (c : Coset) (a b : Int) : Int :=
  let M := c.2.1
  if c.1 then 15000 * (n : Int) ^ 2 + 1000 * (M * M + (M - 15 * a) * (15 * b - M))
  else 240000 * (M * M + (M - a) * (b - M))

/-- `w(v)`: the sum of the weights listed for `v`. -/
def wt (w : List (Int × Int)) (v : Int) : Int :=
  w.foldr (fun e s => if e.1 = v then e.2 + s else s) 0

/-- `c(α,β) + w(α) + [β ≠ α] w(β)` over the allowed pairs of one coset. -/
def terms (n : Nat) (c : Coset) (w : List (Int × Int)) : List Int :=
  let vs := vals n c.2.2
  vs.flatMap fun a =>
    let wa := wt w a
    vs.filterMap fun b =>
      if ok n c a b then some (costS n c a b + wa + (if b = a then 0 else wt w b)) else none

def lmin : List Int → Int
  | [] => 0
  | x :: xs => xs.foldl min x

/-- The check for one key: some coset has no allowed bracket, or `w ≥ 0` and
`L(w) > 128 n` (both sides times 15000). -/
def checkKey (n : Nat) (cs : List Coset) (w : List (Int × Int)) : Bool :=
  cs.any (fun c => (terms n c w).isEmpty) ||
    (w.all (fun e => decide (0 ≤ e.2)) &&
      decide (1920000 * (n : Int) <
        (cs.map fun c => lmin (terms n c w)).sum - (w.map (·.2)).sum))

/-- A certificate line: `n`, `m`, the sorted `(μ_u, r_u)` of the cosets `u ≠ 0`, weights. -/
abbrev Entry := Nat × Nat × List (Int × Int) × List (Int × Int)

def Entry.cosets (e : Entry) : List Coset :=
  (true, 16 * (e.2.1 : Int) - e.1, (e.1 : Int) % 4) :: e.2.2.1.map fun p => (false, p.1, p.2)

def Entry.check (e : Entry) : Bool := checkKey e.1 e.cosets e.2.2.2

end CubelikeSC.Cert
