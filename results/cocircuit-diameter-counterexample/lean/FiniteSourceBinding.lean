import IntegerSourceCertificate
import SourceDistance

namespace ADKZPricing
open Matrix Finset

/-- Closed finite arithmetic checked for each recovered source vertex.
The universal neighbor tests retain every removed basis row. -/
def integerSourceVertexCheck {n d : ℕ} {V : Type*}
    (A : Matrix (Fin n) (Fin (d + 1)) ℤ) (D : IntegerSourceData (n := n) (d := d) V)
    (v : V) : Prop :=
  0 < D.ray v 0 ∧
  (∀ i, 0 ≤ A i ⬝ᵥ D.ray v) ∧
  Function.Injective (D.basis v) ∧
  (∀ i, A i ⬝ᵥ D.ray v = 0 ↔ ∃ j, D.basis v j = i) ∧
  (∀ j k, k ≠ j → ∃ l, D.basis (D.next v j) l = D.basis v k) ∧
  (∀ j, ¬ ∃ l, D.basis (D.next v j) l = D.basis v j)

theorem integerSourceValid_of_checks {n d : ℕ} {V : Type*}
    (A : Matrix (Fin n) (Fin (d + 1)) ℤ) (D : IntegerSourceData (n := n) (d := d) V)
    (H : ∀ v, integerSourceVertexCheck A D v) : IntegerSourceValid A D where
  chart_positive v := (H v).1
  feasible v := (H v).2.1
  basis_injective v := (H v).2.2.1
  active_exact v := (H v).2.2.2.1
  neighbor_keeps v := (H v).2.2.2.2.1
  neighbor_leaves v := (H v).2.2.2.2.2

/-- A balanced integer lookup defines a potential on ALL original label
sets, not just an imported abstract vertex index. No ordering or lookup
correctness assumption is needed: its actual values are kernel-checked. -/
inductive SourceLayerTree where
  | leaf : ℤ → SourceLayerTree
  | branch : ℕ → SourceLayerTree → SourceLayerTree → SourceLayerTree

def SourceLayerTree.lookup : SourceLayerTree → ℕ → ℤ
  | .leaf z, _ => z
  | .branch pivot left right, key => if key < pivot then left.lookup key else right.lookup key

def sourceLabelCode {n : ℕ} (Z : Finset (Fin n)) : ℕ := ∑ i ∈ Z, 2 ^ i.val

def SourceLayerTree.potential {n : ℕ} (T : SourceLayerTree) (Z : Finset (Fin n)) : ℤ :=
  T.lookup (sourceLabelCode Z)

def sourcePotentialVertexCheck {n d : ℕ} {V : Type*}
    (D : IntegerSourceData (n := n) (d := d) V)
    (T : SourceLayerTree) (level : V → ℤ) (v : V) : Prop :=
  T.potential (univ.image (D.basis v)) = level v ∧
  ∀ j, level (D.next v j) ≤ level v + 1

noncomputable section
/-- Same finite basis and neighbor arrays enter the source-cover proof;
the local potential certificate therefore applies to every source edge. -/
theorem sourcePotential_local {n d : ℕ} {V : Type*}
    (A : Matrix (Fin n) (Fin (d + 1)) ℤ) (D : IntegerSourceData (n := n) (d := d) V)
    (H : IntegerSourceValid A D) (T : SourceLayerTree) (level : V → ℤ)
    (hp : ∀ v, sourcePotentialVertexCheck D T level v) :
    ∀ v j, T.potential (H.toCertificate.labels (H.toCertificate.next v j)) ≤
      T.potential (H.toCertificate.labels v) + 1 := by
  intro v j
  change T.potential (univ.image (D.basis (D.next v j))) ≤
    T.potential (univ.image (D.basis v)) + 1
  rw [(hp _).1, (hp _).1]
  exact (hp v).2 j

#print axioms integerSourceValid_of_checks
#print axioms sourcePotential_local
end
end ADKZPricing
