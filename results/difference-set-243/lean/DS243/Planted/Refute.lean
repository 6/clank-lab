import DS243.Planted.Statements

/-! Both planted rules are false, shown in `ZMod 7`: the Fano difference set `{1, 2, 4}`
((7,3,1)) has every nonzero difference exactly once, so pruning at `λ = 1` would reject it;
and `{0, 1, 2}` has no difference more than twice yet is not a difference set. -/

namespace DS243.Planted

open DS243

theorem not_weakPrune : ¬ WeakPrune := by
  intro h
  have hB : ∀ g : ZMod 7, g ≠ 0 → diffCountA ({1, 2, 4} : Finset (ZMod 7)) g = 1 := by decide
  exact h (ZMod 7) 1 {1, 2, 4} {1, 2, 4} (subset_refl _) 1 (by decide) hB (by decide)

theorem not_weakLeaf : ¬ WeakLeaf := by
  intro h
  have := h (ZMod 7) 3 1 {0, 1, 2} (by decide) (by decide) (by decide) 1 (by decide)
  revert this; decide

end DS243.Planted

namespace DS243.Planted

open DS243

/-- The leaf of case 7 with all digits 2 lies only below ID 4251527, in range 1037. -/
theorem not_dropLastRange : ¬ DropLastRange := by
  intro h
  obtain ⟨r, hr, id, h1, h2, tail, hc, hd⟩ := h 7 (by norm_num) (fun _ => 2)
  have dig : ∀ k : ℕ, (hk : k < 12) → prefixDigit id k = 2 := by
    intro k hk
    have := congrArg Fin.val (congrFun hd ⟨k, by omega⟩)
    simpa [idDigits, hk] using this
  have d0 := dig 0 (by norm_num)
  have d1 := dig 1 (by norm_num)
  have d2 := dig 2 (by norm_num)
  have d3 := dig 3 (by norm_num)
  have d4 := dig 4 (by norm_num)
  simp only [prefixDigit] at d0 d1 d2 d3 d4
  norm_num at d0 d1 d2 d3 d4
  rw [lt_min_iff] at h2
  omega

end DS243.Planted
