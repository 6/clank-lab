import BaseREhrhart.Decomposition
import BaseREhrhart.StarsBars
import BaseREhrhart.CertificateCore

/-! Finite cardinality consequences of the
unconditional geometric bijection. The histogram is an explicit premise
here; Certificate.lean discharges precisely that premise in the kernel. -/

noncomputable section
open scoped BigOperators
namespace BaseREhrhart

abbrev Fiber (t : ℕ) (b : Fin D) :=
  {n : Fin 6 → ℕ // height b + ∑ j, n j = t}

instance fiberFinite (t : ℕ) (b : Fin D) : Finite (Fiber t b) := by
  let f : Fiber t b → (Fin 6 → Fin (t + 1)) := fun n j =>
    ⟨n.val j, by
      have hj : n.val j ≤ ∑ k, n.val k :=
        Finset.single_le_sum (fun k _ => Nat.zero_le (n.val k)) (Finset.mem_univ j)
      have hn := n.property
      omega⟩
  apply Finite.of_injective f
  intro n m h
  apply Subtype.ext
  funext j
  exact congrArg Fin.val (congrFun h j)

lemma fiber_card (t : ℕ) (b : Fin D) :
    Nat.card (Fiber t b) = binomTerm t (height b) := by
  unfold binomTerm
  split_ifs with hb
  · let e : Fiber t b ≃ NatComposition 5 (t - height b) :=
      Equiv.subtypeEquivRight (fun n => by
        change height b + ∑ j, n j = t ↔ ∑ j, n j = t - height b
        omega)
    rw [Nat.card_congr e, natComposition_card]
  · haveI : IsEmpty (Fiber t b) := ⟨fun n => by have := n.property; omega⟩
    exact Nat.card_eq_zero.mpr (Or.inl inferInstance)

lemma lattice_card_residue_sum (t : ℕ) :
    Nat.card (LatticePoints t) = ∑ b : Fin D, binomTerm t (height b) := by
  let e : Pieces t ≃ (b : Fin D) × Fiber t b :=
    Equiv.subtypeProdEquivSigmaSubtype (fun (b : Fin D) (n : Fin 6 → ℕ) => height b + ∑ j, n j = t)
  rw [Nat.card_congr (latticeEquivPieces t), Nat.card_congr e, Nat.card_sigma]
  exact Finset.sum_congr rfl (fun b _ => fiber_card t b)

lemma residue_sum_eq_histogram (f : ℕ → ℕ) :
    (∑ b : Fin D, f (height b)) = ∑ h : Fin 6, heightCard h * f h.val := by
  have hf := Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset (Fin D))) (t := Finset.range 6) (g := height)
    (by intro b _; exact Finset.mem_range.mpr (Nat.lt_succ_of_le (height_le_five b)))
    (fun b => f (height b))
  have hi : ∀ h : ℕ,
      (∑ b ∈ Finset.univ.filter (fun b : Fin D => height b = h), f (height b)) =
        (Finset.univ.filter (fun b : Fin D => height b = h)).card * f h := by
    intro h
    rw [Finset.sum_congr rfl (fun b hb => by rw [(Finset.mem_filter.mp hb).2])]
    simp
  simp_rw [hi] at hf
  rw [← Fin.sum_univ_eq_sum_range] at hf
  exact hf.symm

/-- Every dependent finite-certificate premise is shown explicitly:
all 537824 residues have the six exact specified fiber sizes. -/
theorem ehrhart_of_histogram (histogram : ∀ h : Fin 6, heightCard h = weight h)
    (t : ℕ) : (Nat.card (LatticePoints t) : ℚ) = proposedPolynomial t := by
  have hc : Nat.card (LatticePoints t) = histogramCount t := by
    rw [lattice_card_residue_sum, residue_sum_eq_histogram]
    simp_rw [histogram]
    rfl
  rw [hc]
  exact histogramCount_eq_polynomial t

end BaseREhrhart
