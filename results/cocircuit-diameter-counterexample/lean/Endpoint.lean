import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Real.Basic

/- Endpoint definitions. The proof is assembled in
   SourceKernelCompleteKernelAsync. -/
namespace ADKZPricing

abbrev SignVector := Fin 80 → ℤ

def FaceLE (X Y : SignVector) : Prop := ∀ i, X i = 0 ∨ X i = Y i

def compose (X Y : SignVector) : SignVector :=
  fun i => if X i = 0 then Y i else X i

noncomputable def realSign (x : ℝ) : ℤ := if x < 0 then -1 else if x = 0 then 0 else 1

def Covector (A : Matrix (Fin 80) (Fin 41) ℚ) (X : SignVector) : Prop :=
  ∃ v : Fin 41 → ℝ, ∀ i, X i = realSign (∑ j, (A i j : ℝ) * v j)

def Cocircuit (A : Matrix (Fin 80) (Fin 41) ℚ) (X : SignVector) : Prop :=
  Covector A X ∧ X ≠ 0 ∧
    ∀ Y, Covector A Y → Y ≠ 0 → FaceLE Y X → Y = X

def Adjacent (A : Matrix (Fin 80) (Fin 41) ℚ) (X Y : SignVector) : Prop :=
  Cocircuit A X ∧ Cocircuit A Y ∧ X ≠ Y ∧
    compose X Y = compose Y X ∧ Covector A (compose X Y) ∧
    ∀ Z, Cocircuit A Z → FaceLE Z (compose X Y) → Z = X ∨ Z = Y

def Uniform (A : Matrix (Fin 80) (Fin 41) ℚ) : Prop :=
  ∀ f : Fin 41 → Fin 80, Function.Injective f →
    Matrix.det (fun i j => A (f i) j) ≠ 0

def Complementary (X Y : SignVector) : Prop :=
  (Finset.univ.filter (fun i => X i = 0)).card = 40 ∧
  (Finset.univ.filter (fun i => Y i = 0)).card = 40 ∧
  ∀ i, (X i = 0 ∧ Y i = 1) ∨ (X i = 1 ∧ Y i = 0)

def ShortWalk (A : Matrix (Fin 80) (Fin 41) ℚ) (X Y : SignVector) : Prop :=
  ∃ L : ℕ, L ≤ 41 ∧ ∃ p : Fin (L + 1) → SignVector,
    p 0 = X ∧ p (Fin.last L) = Y ∧
    (∀ i, Cocircuit A (p i)) ∧
    ∀ i : Fin L, Adjacent A (p i.castSucc) (p i.succ)

def ProposedEndpoint : Prop :=
  ∃ A : Matrix (Fin 80) (Fin 41) ℚ, Uniform A ∧
    ∃ X Y : SignVector, Cocircuit A X ∧ Cocircuit A Y ∧
      Complementary X Y ∧ ¬ ShortWalk A X Y

end ADKZPricing
