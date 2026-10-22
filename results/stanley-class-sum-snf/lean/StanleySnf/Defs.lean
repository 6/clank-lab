import Mathlib

/-!
# Stanley's class-sum Smith form problem: definitions and the main statement

`M n` is the matrix of multiplication by the class sum `K_(n)` of all `n`-cycles on the
centre of the integral group ring `ℤ[S_n]`, in the basis of class sums `K_μ` (`μ ⊢ n`):
`K_(n) * K_ν = ∑_μ M n μ ν • K_μ`. It is defined literally, as the coefficient of a
fixed permutation of type `μ` in the group-algebra product `K_(n) * K_ν`.

`bridgeFormula` is the classical value of these structure constants:
Frobenius's formula, in which only hook characters survive at an `n`-cycle
(Murnaghan–Nakayama), with `χ^{(n-k,1^k)}((n)) = (-1)^k`, `f^{(n-k,1^k)} = C(n-1,k)`,
and the hook characters given by their generating function
`∑_k χ^{(n-k,1^k)}(μ) q^k = ∏_i (1 - (-q)^{μ_i}) / (1 + q)`.
-/

open Polynomial

namespace StanleySnf

/-! ## Combinatorial data of a partition (as a multiset of parts) -/

/-- `z_μ = ∏_k k^{m_k} m_k!`, the order of the centraliser of a permutation of type `μ`. -/
def zeeM (s : Multiset ℕ) : ℕ :=
  ∏ k ∈ s.toFinset, k ^ (s.count k) * (s.count k).factorial

/-- `z_μ` for a partition. -/
def zee {n : ℕ} (μ : n.Partition) : ℕ := zeeM μ.parts

/-- `(1+q)^{ℓ-1} ∏_i (1 + (-q) + ⋯ + (-q)^{μ_i - 1})`, which equals
`∏_i (1 - (-q)^{μ_i}) / (1 + q)` (see `hookPoly_mul`), the generating function of the
hook characters `χ^{(n-k,1^k)}(μ)`. -/
noncomputable def hookPoly {n : ℕ} (μ : n.Partition) : ℤ[X] :=
  (1 + X) ^ (μ.parts.card - 1) *
    (μ.parts.map fun m => ∑ a ∈ Finset.range m, (-X) ^ a).prod

/-- The hook character value `χ^{(n-k,1^k)}(μ)`. -/
noncomputable def hookChar {n : ℕ} (k : ℕ) (μ : n.Partition) : ℤ := (hookPoly μ).coeff k

/-- The classical value of the structure constant `[K_μ] K_(n) K_ν`:
`(|K_(n)| |K_ν| / n!) ∑_k χ_k((n)) χ_k(ν) χ_k(μ) / C(n-1,k)` with `|K_(n)| = (n-1)!`,
`|K_ν| = n!/z_ν`, `χ_k((n)) = (-1)^k`. -/
noncomputable def bridgeFormula (n : ℕ) (μ ν : n.Partition) : ℚ :=
  ((n - 1).factorial / zee ν : ℚ) *
    ∑ k ∈ Finset.range n,
      (-1 : ℚ) ^ k * hookChar k ν * hookChar k μ / ((n - 1).choose k : ℚ)

/-! ## The class-sum matrix, defined in the group algebra -/

open Equiv

/-- The class sum `K_μ ∈ ℤ[S_n]`. -/
noncomputable def classSum (n : ℕ) (μ : n.Partition) : MonoidAlgebra ℤ (Perm (Fin n)) :=
  ∑ σ ∈ Finset.univ.filter (fun σ : Perm (Fin n) => σ.partition.parts = μ.parts),
    MonoidAlgebra.of ℤ (Perm (Fin n)) σ

theorem exists_rep {n : ℕ} (μ : n.Partition) :
    ∃ σ : Perm (Fin n), σ.partition.parts = μ.parts := by
  have parts_eq_aux : ∀ {s t : Multiset ℕ}, (∀ a ∈ s, 0 < a) → (∀ a ∈ t, 0 < a) →
      s.sum = t.sum → s.filter (2 ≤ ·) = t.filter (2 ≤ ·) → s = t := by
    intro s t hs ht hsum hf
    have key : ∀ u : Multiset ℕ, (∀ a ∈ u, 0 < a) →
        u.filter (fun a => ¬ 2 ≤ a) = Multiset.replicate (u.filter (fun a => ¬ 2 ≤ a)).card 1 := by
      intro u hu
      rw [Multiset.eq_replicate_card]
      intro b hb
      rw [Multiset.mem_filter] at hb
      have := hu b hb.1
      omega
    have hsplit : ∀ u : Multiset ℕ,
        u.sum = (u.filter (2 ≤ ·)).sum + (u.filter (fun a => ¬ 2 ≤ a)).sum := by
      intro u
      rw [← Multiset.sum_add, Multiset.filter_add_not]
    rw [← Multiset.filter_add_not (2 ≤ ·) s, ← Multiset.filter_add_not (2 ≤ ·) t, hf]
    congr 1
    rw [key s hs, key t ht]
    congr 1
    have h1 := hsplit s
    have h2 := hsplit t
    rw [key s hs, Multiset.sum_replicate, smul_eq_mul, mul_one] at h1
    rw [key t ht, Multiset.sum_replicate, smul_eq_mul, mul_one] at h2
    rw [hf] at h1
    omega
  have hle : (μ.parts.filter (2 ≤ ·)).sum ≤ Fintype.card (Fin n) := by
    rw [Fintype.card_fin]
    calc (μ.parts.filter (2 ≤ ·)).sum
        ≤ (μ.parts.filter (2 ≤ ·)).sum + (μ.parts.filter (fun a => ¬ 2 ≤ a)).sum :=
          Nat.le_add_right _ _
      _ = μ.parts.sum := by rw [← Multiset.sum_add, Multiset.filter_add_not]
      _ = n := μ.parts_sum
  obtain ⟨σ, hσ⟩ := (Equiv.Perm.exists_with_cycleType_iff (α := Fin n)
    (m := μ.parts.filter (2 ≤ ·))).mpr ⟨hle, fun a ha => (Multiset.mem_filter.mp ha).2⟩
  refine ⟨σ, parts_eq_aux (fun a ha => σ.partition.parts_pos ha) (fun a ha => μ.parts_pos ha) ?_ ?_⟩
  · rw [σ.partition.parts_sum, μ.parts_sum, Fintype.card_fin]
  · rw [Equiv.Perm.filter_parts_partition_eq_cycleType, hσ]

/-- A fixed permutation of cycle type `μ`. -/
noncomputable def rep {n : ℕ} (μ : n.Partition) : Perm (Fin n) := Classical.choose (exists_rep μ)

/-- `M n μ ν` = coefficient of `K_μ` in `K_(n) * K_ν`, read off at the permutation `rep μ`. -/
noncomputable def M (n : ℕ) : Matrix n.Partition n.Partition ℤ :=
  fun μ ν => (classSum n (Nat.Partition.indiscrete n) * classSum n ν).coeff (rep μ)

/-! ## The invariant factors -/

/-- Stanley's numbers: `d 0 = 1`, `d k = c k! / gcd(k,n)` with `c = 2` if `k ≡ n (mod 2)`,
else `1`. -/
def stanleyD (n k : ℕ) : ℕ :=
  if k = 0 then 1 else (if k % 2 = n % 2 then 2 else 1) * k.factorial / Nat.gcd k n

/-! ## Main statements (proved in `StanleySnf.Main`) -/

/-- The Smith-form statement for an integer matrix `A` indexed by partitions of `n`:
there is a basis `b` of `ℤ^{p(n)}`, indexed by `Fin n ⊕ κ`, such that the column space
of `A` is spanned by `stanleyD n r • b (inl r)`. Together with `stanleyD_dvd`
(divisibility chain) this says the Smith normal form of `A` is
`diag(stanleyD n 0, …, stanleyD n (n-1), 0, …, 0)`. -/
def HasStanleySNF (n : ℕ) (A : Matrix n.Partition n.Partition ℤ) : Prop :=
  ∃ (κ : Type) (_ : Fintype κ) (b : Module.Basis (Fin n ⊕ κ) ℤ (n.Partition → ℤ)),
    LinearMap.range A.mulVecLin =
      Submodule.span ℤ (Set.range fun r : Fin n => (stanleyD n r : ℤ) • b (Sum.inl r))

end StanleySnf
