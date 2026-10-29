import CanonicalCellLabels
import CellSignTransport
import CellWalkSequence
import PathConfinement

namespace ADKZPricing
open Matrix Finset
noncomputable section

theorem star_realSign_feasible_iff {n : ℕ} (c : Option (Fin n)) (i : Fin n) (x : ℝ) :
    0 ≤ (starSign c i : ℤ) * realSign x ↔ 0 ≤ (starSign c i : ℝ) * x := by
  constructor
  · intro h
    unfold starSign at h ⊢
    by_cases hc : c = some i
    · rw [if_pos hc] at h ⊢
      have hx : x ≤ 0 := by
        by_contra hn
        have hp : 0 < x := lt_of_not_ge hn
        rw [(realSign_positive_iff x).mpr hp] at h
        norm_num at h
      linarith
    · rw [if_neg hc] at h ⊢
      simpa only [one_mul] using (realSign_nonnegative_iff x).mp (by simpa only [one_mul] using h)
  · exact star_realSign_nonnegative c i x

/-- Every actual frozen cocircuit in a closed cell becomes an actual
    normalized chart vertex with its COMPLETE original forty-zero label. -/
theorem full_cocircuit_chart_vertex (A : Matrix (Fin 80) (Fin 41) ℚ) (hu : Uniform A)
    (c : Option (Fin 80)) (hr : RegularChart (A.map (Rat.castHom ℝ)) c)
    (X : SignVector) (hx : Cocircuit A X) (hs : ∀ i, 0 ≤ (starSign c i : ℤ) * X i) :
    ChartVertex (A.map (Rat.castHom ℝ)) c (signZeros X) := by
  have hc := uniform_cocircuit_zero_count A hu X hx
  let label := labelOrder (signZeros X) hc
  have hl : Function.Injective label := labelOrder_injective _ hc
  have ha : ActiveRay (A.map (Rat.castHom ℝ)) c label := by
    obtain ⟨v, hv⟩ := hx.1
    refine ⟨v, ?_, ?_, ?_⟩
    · intro hz
      apply hx.2.1
      ext i
      rw [hv i, hz]
      simp [realSign]
    · intro i
      apply (star_realSign_feasible_iff c i _).mp
      change 0 ≤ (starSign c i : ℤ) * realSign (∑ j, (A i j : ℝ) * v j)
      rw [← hv i]
      exact hs i
    · intro j
      apply (realSign_zero_iff _).mp
      change realSign (∑ k, (A (label j) k : ℝ) * v k) = 0
      rw [← hv (label j)]
      exact (mem_filter.mp (labelOrder_mem (signZeros X) hc j)).2
  have he := (regular_chart_vertex_active_iff _ c hr label hl).mpr ha
  simpa only [label, labelOrder_image] using he

/-- An edge of the faithful FULL cocircuit graph confined to one closed
    cell is an edge of its actual labelled chart-cell graph. -/
theorem full_adjacent_chart_edge (A : Matrix (Fin 80) (Fin 41) ℚ) (hu : Uniform A)
    (c : Option (Fin 80)) (hr : RegularChart (A.map (Rat.castHom ℝ)) c)
    (X Y : SignVector) (he : Adjacent A X Y)
    (hx : ∀ i, 0 ≤ (starSign c i : ℤ) * X i)
    (hy : ∀ i, 0 ≤ (starSign c i : ℤ) * Y i) :
    (chartCell (A.map (Rat.castHom ℝ)) c).edge (signZeros X) (signZeros Y) := by
  refine ⟨full_cocircuit_chart_vertex A hu c hr X he.1 hx,
    full_cocircuit_chart_vertex A hu c hr Y he.2.1 hy, ?_⟩
  have hz : signZeros (compose X Y) = signZeros X ∩ signZeros Y := by
    ext i
    simp [signZeros, compose_zero_iff]
  have hc := adjacent_composition_zero_count A hu X Y he
  rw [hz] at hc
  omega

theorem central_star_signs (X : SignVector) (h : CentralSigns X) :
    ∀ i, 0 ≤ (starSign none i : ℤ) * X i := by
  intro i
  simpa [starSign] using h i

theorem neighbor_star_signs (e : Fin 80) (X : SignVector) (h : NeighborSigns e X) :
    ∀ i, 0 ≤ (starSign (some e) i : ℤ) * X i := by
  intro i
  by_cases hi : i = e
  · subst i
    simpa [starSign] using neg_nonneg.mpr h.1
  · simpa [starSign, hi, Ne.symm hi] using h.2 i hi

/-- Full-path confinement supplies ONE fixed exceptional row for the
    entire walk. Every original vertex and shared-facet edge is retained
    when the faithful full path becomes a literal two-cell chart union. -/
theorem full_short_walk_chart_union (A : Matrix (Fin 80) (Fin 41) ℚ) (hu : Uniform A)
    (hr : ∀ c, RegularChart (A.map (Rat.castHom ℝ)) c)
    (X Y : SignVector) (hcomp : Complementary X Y) (hw : ShortWalk A X Y) :
    ∃ L : ℕ, L ≤ 41 ∧ ∃ e : Fin 80,
      LabelledCell.CellWalk (LabelledCell.union
        (chartCell (A.map (Rat.castHom ℝ)) none) (chartCell (A.map (Rat.castHom ℝ)) (some e)))
        (signZeros X) (signZeros Y) L := by
  obtain ⟨L, hL, p, hp0, hpL, hv, he, e, hverts, hedges⟩ :=
    short_walk_two_cell_confinement A hu X Y hcomp hw
  let G := LabelledCell.union (chartCell (A.map (Rat.castHom ℝ)) none)
    (chartCell (A.map (Rat.castHom ℝ)) (some e))
  have hv' : ∀ i, G.vertex (signZeros (p i)) := by
    intro i
    rcases hverts i with hc | hc
    · exact Or.inl (full_cocircuit_chart_vertex A hu none (hr none) _ (hv i) (central_star_signs _ hc))
    · exact Or.inr (full_cocircuit_chart_vertex A hu (some e) (hr (some e)) _ (hv i) (neighbor_star_signs e _ hc))
  have he' : ∀ i : Fin L, G.edge (signZeros (p i.castSucc)) (signZeros (p i.succ)) := by
    intro i
    rcases hedges i with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · exact Or.inl (full_adjacent_chart_edge A hu none (hr none) _ _ (he i)
        (central_star_signs _ hx) (central_star_signs _ hy))
    · exact Or.inr (full_adjacent_chart_edge A hu (some e) (hr (some e)) _ _ (he i)
        (neighbor_star_signs e _ hx) (neighbor_star_signs e _ hy))
  have hwalk := LabelledCell.CellWalk.of_finite_sequence G L (fun i => signZeros (p i)) hv' he'
  change LabelledCell.CellWalk G (signZeros (p 0)) (signZeros (p (Fin.last L))) L at hwalk
  rw [hp0, hpL] at hwalk
  exact ⟨L, hL, e, hwalk⟩

#print axioms full_cocircuit_chart_vertex
#print axioms full_short_walk_chart_union
end
end ADKZPricing
