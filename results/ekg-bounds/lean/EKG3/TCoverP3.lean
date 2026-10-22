import Statement.TheoremTP3

namespace EKG3.P3.Middle
open EKG3

/-- Monotone envelope, extended beyond E1 only for totality. -/
noncomputable def envelope (rows : List CoverRow) (x : ℕ) : ℕ :=
  max Kfin ((rows.map (fun r => if r.ea ≤ x then r.M else 0)).foldr max 0)

private theorem fold_le (ns : List ℕ) (b : ℕ) :
    ns.foldr max 0 ≤ b ↔ ∀ n ∈ ns, n ≤ b := by
  induction ns with
  | nil => simp
  | cons n ns ih => simp [max_le_iff, ih]

theorem envelope_le (rows : List CoverRow) (x b : ℕ) :
    envelope rows x ≤ b ↔ Kfin ≤ b ∧ ∀ r ∈ rows, r.ea ≤ x → r.M ≤ b := by
  simp only [envelope, max_le_iff, fold_le, List.forall_mem_map]
  constructor
  · rintro ⟨h, hs⟩
    exact ⟨h, fun r hr hx => by simpa [hx] using hs r hr⟩
  · rintro ⟨h, hs⟩
    refine ⟨h, fun r hr => ?_⟩
    split_ifs with hx
    · exact hs r hr hx
    · exact Nat.zero_le _

theorem envelope_mono (rows : List CoverRow) : Monotone (envelope rows) := by
  intro x y hxy
  apply (envelope_le rows x _).mpr
  have hy := (envelope_le rows y _).mp (le_refl _)
  exact ⟨hy.1, fun r hr hx => hy.2 r hr (hx.trans hxy)⟩

theorem chain_lower {a b : ℕ} {rows : List CoverRow}
    (h : CoverChain a b rows) : ∀ r ∈ rows, a ≤ r.ea := by
  induction rows generalizing a b with
  | nil => simp
  | cons r rs ih =>
    obtain ⟨ha, hm, hc, ht⟩ := h
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · omega
    · have hw := hc.1
      exact (by omega : a ≤ r.eb).trans (ih ht z hz)

/-- A lookup also bounds all earlier active rows, so it identifies the
envelope without assuming any global bootstrap beyond E1. -/
theorem chain_lookup {a b x : ℕ} {rows : List CoverRow}
    (h : CoverChain a b rows) (hax : a ≤ x) (hx : x < E1) :
    ∃ r ∈ rows, r.ea ≤ x ∧ x < r.eb ∧ b ≤ r.M ∧ r.Conditions ∧
      (∀ z ∈ rows, z.ea ≤ x → z.M ≤ r.M) := by
  induction rows generalizing a b with
  | nil => simp only [CoverChain] at h; omega
  | cons r rs ih =>
    obtain ⟨ha, hm, hc, ht⟩ := h
    by_cases heb : x < r.eb
    · refine ⟨r, by simp, by omega, heb, hm, hc, ?_⟩
      intro z hz hzle
      rcases List.mem_cons.mp hz with rfl | hz
      · exact le_refl _
      · have := chain_lower ht z hz; omega
    · obtain ⟨z, hz, hzlo, hzhi, hzm, hzc, hzall⟩ := ih ht (by omega)
      refine ⟨z, by simp [hz], hzlo, hzhi, hm.trans hzm, hzc, ?_⟩
      intro w hw hwle
      rcases List.mem_cons.mp hw with rfl | hw
      · exact hzm
      · exact hzall w hw hwle

theorem cover_lookup {rows : List CoverRow} (h : CoverChain e0 Kfin rows)
    {x : ℕ} (hlo : e0 ≤ x) (hhi : x < E1) :
    ∃ r ∈ rows, r.ea ≤ x ∧ x < r.eb ∧ r.Conditions ∧ envelope rows x = r.M := by
  obtain ⟨r, hr, hx, hxb, hm, hc, hall⟩ := chain_lookup h hlo hhi
  refine ⟨r, hr, hx, hxb, hc, le_antisymm ?_ ?_⟩
  · exact (envelope_le rows x r.M).mpr ⟨hm, hall⟩
  · exact ((envelope_le rows x _).mp (le_refl _)).2 r hr hx

theorem envelope_base (rows : List CoverRow) (x : ℕ) : Kfin ≤ envelope rows x :=
  (envelope_le rows x _).mp (le_refl _) |>.1

theorem envelope_below {rows : List CoverRow} (hc : CoverChain e0 Kfin rows)
    {x : ℕ} (hx : x < e0) : envelope rows x = Kfin := by
  apply le_antisymm _ (envelope_base rows x)
  apply (envelope_le rows x Kfin).mpr
  refine ⟨le_rfl, ?_⟩
  intro r hr hrx
  have := chain_lower hc r hr
  omega

end EKG3.P3.Middle
