import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! Definitions and the probability statement for Arpino–Dmitriev–Grometto,
Conjecture 12. A matrix is represented by its column supports, in bijection
with Boolean matrices. No distribution, Greedy gap, or probability identity is
postulated; the statements here are propositions proved in `FullConstruction`. -/
namespace ADG
open Finset

abbrev Matrix (m n : ℕ) := Fin n → Finset (Fin m)

def feasible {m n : ℕ} (A : Matrix m n) : Prop :=
  ∀ i, ∃ j, i ∈ A j

def gain {m n : ℕ} (A : Matrix m n) (U : Finset (Fin m)) (j : Fin n) : ℕ :=
  (U ∩ A j).card

/-- List order breaks ties: the first column of maximum gain wins. -/
def best {m n : ℕ} (A : Matrix m n) (U : Finset (Fin m)) : List (Fin n) → Option (Fin n)
  | [] => none
  | j :: js => match best A U js with
    | none => some j
    | some t => if gain A U t ≤ gain A U j then some j else some t

/-- Each positive step removes covered rows. Zero gain stops, including infeasible inputs.
The fuel m suffices since a positive step removes at least one row. -/
def trace {m n : ℕ} (A : Matrix m n) : ℕ → Finset (Fin m) → List (Fin n × ℕ)
  | 0, _ => []
  | fuel + 1, U =>
    if U = ∅ then [] else
    match best A U (List.finRange n) with
    | none => []
    | some j => if gain A U j = 0 then [] else
      (j, gain A U j) :: trace A fuel (U \ A j)

def greedyTrace {m n : ℕ} (A : Matrix m n) := trace A m univ

def G {m n : ℕ} (A : Matrix m n) : ℕ := (greedyTrace A).length

def tripleCount {m n : ℕ} (A : Matrix m n) : ℕ :=
  ((greedyTrace A).filter (fun t => t.2 = 3)).length

def lpDomain {m n : ℕ} (A : Matrix m n) : Set (Fin n → ℝ) :=
  {x | (∀ j, 0 ≤ x j ∧ x j ≤ 1) ∧ ∀ i, 1 ≤ ∑ j, if i ∈ A j then x j else 0}

/-- Actual real infimum. On empty domains the real sInf convention totalizes it. -/
noncomputable def L {m n : ℕ} (A : Matrix m n) : ℝ :=
  sInf ((fun x : Fin n → ℝ => ∑ j, x j) '' lpDomain A)

/-- Column mass: independent Bernoulli bits, including empty and full supports. -/
def columnMass (m : ℕ) (p : ℝ) (s : Finset (Fin m)) : ℝ :=
  ∏ i, if i ∈ s then p else 1 - p

/-- Finite product law, no independence assumption detached from its weights. -/
def iidMass {α : Type*} [Fintype α] (μ : α → ℝ) {n : ℕ} (a : Fin n → α) : ℝ :=
  ∏ j, μ (a j)

noncomputable def iidProb {α : Type*} [Fintype α] (μ : α → ℝ) (n : ℕ)
    (E : (Fin n → α) → Prop) : ℝ := by
  classical
  exact ∑ a : Fin n → α, if E a then iidMass μ a else 0

noncomputable def matrixProb (m n : ℕ) (p : ℝ) (E : Matrix m n → Prop) : ℝ :=
  iidProb (columnMass m p) n E

noncomputable def parameterP (k : ℕ) : ℝ := 1 / (10 * (k : ℝ)^4)

def gapEvent (k : ℕ) (ε : ℚ) (A : Matrix k (k^10)) : Prop :=
  feasible A ∧ (1 + (ε : ℝ)) * L A ≤ (G A : ℝ)

/-- The probability statement, proved as `frozen_probability_endpoint`. -/
def FrozenProbabilityEndpoint : Prop :=
  ∃ (ε η : ℚ) (k₀ : ℕ), 0 < ε ∧ 0 < η ∧
    ∀ k ≥ k₀, 0 < k ∧ (η : ℝ) ≤ matrixProb k (k^10) (parameterP k) (gapEvent k ε)

/-- All-n source family: totalized at n = 0 by the library's rpow convention. -/
noncomputable def sourceM (n : ℕ) : ℕ := ⌊(n : ℝ) ^ (1 / 10 : ℝ)⌋₊
noncomputable def sourceP (n : ℕ) : ℝ := (n : ℝ) ^ (-(2 / 5 : ℝ)) / 10

/-- Event-based failure of convergence to one; infeasible values do not enter. -/
def SourceNonconvergence : Prop :=
  ∃ (ε η : ℚ), 0 < ε ∧ 0 < η ∧ ∀ N : ℕ, ∃ n ≥ N,
    (η : ℝ) ≤ matrixProb (sourceM n) n (sourceP n)
      (fun A => feasible A ∧ (1 + (ε : ℝ)) * L A ≤ (G A : ℝ))

/-- Exact iid event: distinct designated positions, middle first, all others outside F. -/
def exactlyOnceMiddleFirst {α : Type*} [DecidableEq α] {n : ℕ}
    (F : Finset α) (s₁ s₂ s₃ : α) (a : Fin n → α) : Prop :=
  ∃ i₁ i₂ i₃ : Fin n, i₂ < i₁ ∧ i₂ < i₃ ∧ i₁ ≠ i₃ ∧
    a i₁ = s₁ ∧ a i₂ = s₂ ∧ a i₃ = s₃ ∧
    ∀ j, j ≠ i₁ → j ≠ i₂ → j ≠ i₃ → a j ∉ F

/-- The exactly-once identity, for normalized nonnegative finite laws. -/
def ExactlyOnceIdentity : Prop :=
  ∀ (α : Type) [Fintype α] [DecidableEq α] (μ : α → ℝ),
    (∀ s, 0 ≤ μ s) → (∑ s, μ s) = 1 →
    ∀ (F : Finset α) (s₁ s₂ s₃ : α),
      s₁ ∈ F → s₂ ∈ F → s₃ ∈ F → s₁ ≠ s₂ → s₁ ≠ s₃ → s₂ ≠ s₃ →
      ∀ n, 3 ≤ n →
        iidProb μ n (exactlyOnceMiddleFirst F s₁ s₂ s₃) =
          ((n * (n-1) * (n-2) : ℕ) : ℝ) / 3 * μ s₁ * μ s₂ * μ s₃ *
            (1 - ∑ s ∈ F, μ s) ^ (n-3)

def noLargeColumns {m n : ℕ} (A : Matrix m n) : Prop := ∀ j, (A j).card ≤ 3

def allExactPairs {m n : ℕ} (A : Matrix m n) : Prop :=
  ∀ i j : Fin m, i ≠ j → ∃ c, A c = {i,j}

/-- The phase count of the actual algorithm; m ≥ 2 is eventual and necessary. -/
def GreedyPhaseCount : Prop :=
  ∀ (m n : ℕ) (A : Matrix m n), 2 ≤ m → noLargeColumns A → allExactPairs A →
    ∃ K T : ℕ, tripleCount A = K ∧
      (greedyTrace A).map Prod.snd = List.replicate K 3 ++ List.replicate T 2 ++
        List.replicate ((m - 3*K) % 2) 1 ∧
      ((greedyTrace A).map Prod.fst).Nodup ∧
      (((greedyTrace A).filter (fun t => t.2 = 3)).map (fun t => A t.1)).Pairwise Disjoint ∧
      G A = (m - K + 1) / 2

end ADG
