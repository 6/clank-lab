import ThomsonN10.Data

/-! The package interfaces of the N10 run. Each is a proposition (not asserted);
each package proves exactly one of them as a theorem named `<Name>_holds`, in its own
modules, importing only `ThomsonN10.Data` and Mathlib (plus its own modules). The final
assembly (`ThomsonN10.Assembly`) derives `Challenge.CompleteTarget` from all of them.
Route: the near-sharp design of the MIT N=9 proof (aravindkarthigeyan/thomson-n9-lean). -/

namespace ThomsonN10.Interfaces

open ThomsonN10

/-- Ordered-pair sum convention: each unordered pair once, as in `coulombEnergy`. -/
noncomputable def pairSum (f : Fin 10 → Fin 10 → ℝ) : ℝ :=
  ∑ i : Fin 10, ∑ j ∈ Finset.Ioi i, f i j

/-- P0: the stationary height exists and is unique in the box. -/
def ParameterExistsUnique : Prop :=
  ∃! h : ℝ, (heightLower : ℝ) ≤ h ∧ h ≤ (heightUpper : ℝ) ∧ stationarity h = 0

/-- P1a: LP separation. Low energy forces every pair product below the cap. -/
def LPSeparation : Prop :=
  ∀ x : Configuration, IsSphereConfiguration x → coulombEnergy x ≤ (energyCap : ℝ) →
    ∀ i j, i ≠ j → inner ℝ (x i) (x j) < (pairCap : ℝ)

/-- P1b: the three-point certificate, on the capped domain. -/
def PairBound : Prop :=
  ∀ x : Configuration, IsSphereConfiguration x →
    (∀ i j, i ≠ j → inner ℝ (x i) (x j) ≤ (pairCap : ℝ)) →
    (certU : ℝ) - (certLoss : ℝ) ≤ pairSum (fun i j => minorant (inner ℝ (x i) (x j)))

/-- P1c: the candidate's energy is at most the certificate's U, which is below the LP cap. -/
def CandidateUpper : Prop :=
  (∀ h : CandidateParameter, coulombEnergy (candidate h) ≤ (certU : ℝ)) ∧
    (certU : ℝ) ≤ (energyCap : ℝ)

/-- P2a: the rational polynomial is a minorant of the Coulomb potential on the cap. -/
def MinorantBound : Prop :=
  ∀ t : ℝ, -1 ≤ t → t ≤ (pairCap : ℝ) → minorant t ≤ (Real.sqrt (2 - 2 * t))⁻¹

/-- P2b: exterior gap outside the seven contact windows. -/
def ExteriorGap : Prop :=
  ∀ h : CandidateParameter, ∀ t : ℝ, -1 ≤ t → t ≤ (pairCap : ℝ) →
    (∀ c : Fin 7, (windowRadius : ℝ) ≤ |t - contact h c|) →
    (gapBound : ℝ) ≤ (Real.sqrt (2 - 2 * t))⁻¹ - minorant t

/-- P3: window classification. If every pair product lies within the window radius of
some contact value, one relabelling matches the candidate's whole Gram matrix. -/
def WindowClassification : Prop :=
  ∀ h : CandidateParameter, ∀ x : Configuration, IsSphereConfiguration x →
    (∀ i j, i ≠ j → ∃ c : Fin 7, |inner ℝ (x i) (x j) - contact h c| < (windowRadius : ℝ)) →
    ∃ p : Equiv.Perm (Fin 10), ∀ i j,
      |inner ℝ (x (p i)) (x (p j)) - inner ℝ (candidate h i) (candidate h j)| ≤
        (windowRadius : ℝ)

/-- P4: local theorem. A configuration whose Gram matrix (after relabelling) is within the
window radius of the candidate's, and whose energy is at most the candidate's, is congruent
to the candidate. -/
def LocalTarget : Prop :=
  ∀ h : CandidateParameter, ∀ x : Configuration, IsSphereConfiguration x →
    (∃ p : Equiv.Perm (Fin 10), ∀ i j,
      |inner ℝ (x (p i)) (x (p j)) - inner ℝ (candidate h i) (candidate h j)| ≤
        (windowRadius : ℝ)) →
    coulombEnergy x ≤ coulombEnergy (candidate h) → Congruent x (candidate h)

end ThomsonN10.Interfaces
