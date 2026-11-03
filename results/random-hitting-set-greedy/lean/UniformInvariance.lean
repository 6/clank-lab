import UniformEndpoint
import Probability
import LP
import FullConstruction

/-! Invariance of the iid law, the LP and the good event under column relabelling. -/
namespace ADG.Uniform
open Finset
open scoped Classical

def relabel {m n : ℕ} (A : Matrix m n) (π : Equiv.Perm (Fin n)) : Matrix m n :=
  fun j => A (π j)

def relabelEquiv (m n : ℕ) (π : Equiv.Perm (Fin n)) : Matrix m n ≃ Matrix m n where
  toFun A := relabel A π
  invFun A := relabel A π.symm
  left_inv A := by funext j; simp [relabel]
  right_inv A := by funext j; simp [relabel]

theorem iidMass_relabel {m n : ℕ} (A : Matrix m n) (π : Equiv.Perm (Fin n)) (p : ℝ) :
    iidMass (columnMass m p) (relabel A π) = iidMass (columnMass m p) A :=
  Equiv.prod_comp π (fun j => columnMass m p (A j))

/-- Weighted identity for every payoff, including a payoff depending on π.
This is stronger than a marginal event equality. -/
theorem expectation_relabel {m n : ℕ} (π : Equiv.Perm (Fin n)) (p : ℝ)
    (f : Matrix m n → ℝ) :
    (∑ A : Matrix m n, iidMass (columnMass m p) A * f (relabel A π)) =
      ∑ A : Matrix m n, iidMass (columnMass m p) A * f A := by
  apply Fintype.sum_equiv (relabelEquiv m n π)
  intro A
  change iidMass (columnMass m p) A * f (relabel A π) =
    iidMass (columnMass m p) (relabel A π) * f (relabel A π)
  rw [iidMass_relabel]

theorem matrixProb_relabel {m n : ℕ} (π : Equiv.Perm (Fin n)) (p : ℝ)
    (event : Matrix m n → Prop) :
    matrixProb m n p (fun A => event (relabel A π)) = matrixProb m n p event := by
  simpa only [matrixProb, iidProb, mul_ite, mul_one, mul_zero] using
    expectation_relabel π p (fun A => if event A then 1 else 0)

/-- Independent uniform permutation stays independent after relabelling A.
The identity holds for an arbitrary π-dependent payoff, so it is a joint-law
statement; no independence is inferred merely from matching marginals. -/
theorem joint_relabel {m n : ℕ} (p : ℝ)
    (f : Equiv.Perm (Fin n) → Matrix m n → ℝ) :
    (∑ π, ∑ A : Matrix m n, iidMass (columnMass m p) A * f π (relabel A π)) /
        Fintype.card (Equiv.Perm (Fin n)) =
      (∑ π, ∑ A : Matrix m n, iidMass (columnMass m p) A * f π A) /
        Fintype.card (Equiv.Perm (Fin n)) := by
  congr 1
  exact sum_congr rfl (fun π _ => expectation_relabel π p (f π))

theorem feasible_relabel {m n : ℕ} (A : Matrix m n) (π : Equiv.Perm (Fin n)) :
    feasible (relabel A π) ↔ feasible A := by
  constructor
  · intro h i
    obtain ⟨j, hj⟩ := h i
    exact ⟨π j, hj⟩
  · intro h i
    obtain ⟨j, hj⟩ := h i
    exact ⟨π.symm j, by simpa [relabel] using hj⟩

theorem noLarge_relabel {m n : ℕ} (A : Matrix m n) (π : Equiv.Perm (Fin n)) :
    noLargeColumns (relabel A π) ↔ noLargeColumns A := by
  constructor
  · intro h j
    simpa [relabel] using h (π.symm j)
  · intro h j
    exact h (π j)

theorem allPairs_relabel {m n : ℕ} (A : Matrix m n) (π : Equiv.Perm (Fin n)) :
    allExactPairs (relabel A π) ↔ allExactPairs A := by
  constructor
  · intro h i j hij
    obtain ⟨c, hc⟩ := h i j hij
    exact ⟨π c, hc⟩
  · intro h i j hij
    obtain ⟨c, hc⟩ := h i j hij
    exact ⟨π.symm c, by simpa [relabel] using hc⟩

theorem good_relabel {m n : ℕ} (A : Matrix m n) (π : Equiv.Perm (Fin n)) :
    good (relabel A π) ↔ good A := by
  exact and_congr (noLarge_relabel A π) (allPairs_relabel A π)

theorem lpDomain_relabel {m n : ℕ} (A : Matrix m n) (π : Equiv.Perm (Fin n))
    (x : Fin n → ℝ) :
    (fun j => x (π j)) ∈ lpDomain (relabel A π) ↔ x ∈ lpDomain A := by
  have hrow (i : Fin m) :
      (∑ j, if i ∈ relabel A π j then x (π j) else 0) =
        ∑ j, if i ∈ A j then x j else 0 :=
    Equiv.sum_comp π (fun j => if i ∈ A j then x j else 0)
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro j
      simpa using h.1 (π.symm j)
    · intro i
      simpa only [hrow] using h.2 i
  · intro h
    refine ⟨fun j => h.1 (π j), ?_⟩
    intro i
    simpa only [hrow] using h.2 i

theorem L_relabel {m n : ℕ} (A : Matrix m n) (π : Equiv.Perm (Fin n)) :
    L (relabel A π) = L A := by
  unfold L
  congr 1
  ext cost
  constructor
  · rintro ⟨x, hx, rfl⟩
    let y : Fin n → ℝ := fun j => x (π.symm j)
    refine ⟨y, ?_, ?_⟩
    · apply (lpDomain_relabel A π y).mp
      simpa [y] using hx
    · exact Equiv.sum_comp π.symm x
  · rintro ⟨x, hx, rfl⟩
    exact ⟨fun j => x (π j), (lpDomain_relabel A π x).mpr hx, Equiv.sum_comp π x⟩

theorem exceptional_loss {k : ℕ} (hk : threshold ≤ k) :
    (1 / (10000*(k : ℝ)^2) : ℝ) + 160000/(k : ℝ)^2 ≤ (c : ℝ)/8 := by
  have hkr : (10^20 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkn : (k : ℝ) ≠ 0 := by linarith
  have hks : 0 < (k : ℝ)^2 := sq_pos_of_ne_zero hkn
  have hs : (10^20 : ℝ)^2 ≤ (k : ℝ)^2 := by nlinarith
  calc
    _ = (160000 + 1/10000)/(k : ℝ)^2 := by field_simp; ring
    _ ≤ _ := (div_le_iff₀ hks).mpr (by norm_num [c]; nlinarith)

end ADG.Uniform
