import FullProof
import Bernstein

/-- A direct type check against the original frozen statement. -/
example : Makonzi.Endpoint := Makonzi.endpoint
example (p : Fin 3 → ℕ) (hp : ∀ i, 2 ≤ p i) :
    RingHom.ker (Makonzi.phi p) = Makonzi.minorIdeal p :=
  Makonzi.kernel_equality p hp

/- The statement is checked independently of the Endpoint abbreviation. -/
example : Makonzi.Endpoint =
    (∀ p : Fin 3 → ℕ, (∀ i, 2 ≤ p i) →
      RingHom.ker (Makonzi.phi p) = Makonzi.minorIdeal p) := rfl

/- Guard the rings, the single quotient relation, every generator image,
and the signs and order of the three minors. -/
example (p : Fin 3 → ℕ) : Makonzi.SourceRing p =
    MvPolynomial (Fin 3 ⊕ ((i : Fin 3) × Fin (p i))) ℂ := rfl

example (p : Fin 3 → ℕ) : Makonzi.ArrowRing p =
    MvPolynomial (Bool × ((i : Fin 3) × Fin (p i))) ℂ := rfl

open scoped BigOperators in
example (p : Fin 3 → ℕ) (i : Fin 3) : Makonzi.D p i =
    ∏ j : Fin (p i), MvPolynomial.X (false, ⟨i, j⟩) := rfl

open scoped BigOperators in
example (p : Fin 3 → ℕ) (i : Fin 3) : Makonzi.U p i =
    ∏ j : Fin (p i), MvPolynomial.X (true, ⟨i, j⟩) := rfl

open scoped BigOperators in
example (p : Fin 3 → ℕ) (i : Fin 3) : Makonzi.V p i =
    ∏ j : Fin (p i), MvPolynomial.X (Sum.inr ⟨i, j⟩) := rfl

example (p : Fin 3 → ℕ) (i : Fin 3) : Makonzi.W p i =
    MvPolynomial.X (Sum.inl i) := rfl

example (p : Fin 3 → ℕ) : Makonzi.canonicalIdeal p =
    Ideal.span {Makonzi.D p 0 - Makonzi.D p 1 + Makonzi.D p 2} := rfl

example (p : Fin 3 → ℕ) : Makonzi.arrowImage p =
    (fun x => match x with
      | Sum.inl i => if i = 0 then Makonzi.D p 0 * Makonzi.U p 1
          else if i = 1 then Makonzi.D p 1 * Makonzi.U p 0
          else -(Makonzi.D p 1 * Makonzi.U p 2)
      | Sum.inr e => MvPolynomial.X (false, e) * MvPolynomial.X (true, e)) := rfl

example (p : Fin 3 → ℕ) : Makonzi.phi p =
    (Ideal.Quotient.mk (Makonzi.canonicalIdeal p)).comp
      (MvPolynomial.eval₂Hom MvPolynomial.C (Makonzi.arrowImage p)) := rfl

example (p : Fin 3 → ℕ) : Makonzi.minorIdeal p =
    Ideal.span
      {Makonzi.W p 1 * (Makonzi.W p 2 + Makonzi.V p 2) -
          Makonzi.V p 0 * Makonzi.W p 2,
       Makonzi.W p 1 * Makonzi.W p 0 - Makonzi.V p 0 * Makonzi.V p 1,
       Makonzi.W p 2 * Makonzi.W p 0 -
          (Makonzi.W p 2 + Makonzi.V p 2) * Makonzi.V p 1} := rfl

/- Small indexing, sign, and empty-normal-form checks. -/
example : Fintype.card (Makonzi.Edge (fun _ => 2)) = 6 := by decide
example : Fintype.card (Makonzi.Edge ![2, 3, 4]) = 9 := by decide

example : Makonzi.D (fun _ => 2) 0 =
    MvPolynomial.X (false, ⟨0, 0⟩) * MvPolynomial.X (false, ⟨0, 1⟩) := by
  simp [Makonzi.D, Fin.prod_univ_two]

example : Makonzi.U (fun _ => 2) 0 =
    MvPolynomial.X (true, ⟨0, 0⟩) * MvPolynomial.X (true, ⟨0, 1⟩) := by
  simp [Makonzi.U, Fin.prod_univ_two]

example : Makonzi.V (fun _ => 2) 0 =
    MvPolynomial.X (Sum.inr ⟨0, 0⟩) * MvPolynomial.X (Sum.inr ⟨0, 1⟩) := by
  simp [Makonzi.V, Fin.prod_univ_two]

example (p : Fin 3 → ℕ) : Makonzi.arrowImage p (Sum.inl 2) =
    -(Makonzi.D p 1 * Makonzi.U p 2) := rfl

example (p : Fin 3 → ℕ) (r : Makonzi.CoeffRing p)
    (a b c : Fin 0 → Makonzi.CoeffRing p) :
    Makonzi.normalForm p 0 r a b c = Makonzi.coeffEmbed p r := by
  simp [Makonzi.normalForm]

example : RingHom.ker (Makonzi.phi (fun _ => 2)) =
    Makonzi.minorIdeal (fun _ => 2) :=
  Makonzi.kernel_equality (fun _ => 2) (by decide)

/-- info: 'Makonzi.endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Makonzi.endpoint

/-- info: 'Makonzi.kernel_equality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Makonzi.kernel_equality

#check Makonzi.kernel_equality
