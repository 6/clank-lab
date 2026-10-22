import Palette

namespace LockedTromino

/-- A width-specific strip family needs vertical seams only. -/
structure VerticalPalette (H : Nat → Prop) (w : Nat) where
  tiles : Nat → Region → Prop
  partition : ∀ h, H h → Tiling (Rectangle h w) (tiles h)
  internal : ∀ h, H h → PairwiseRigid (tiles h)
  vertical : ∀ h k, H h → H k → ∀ A B,
    tiles h A → tiles k B → Rigid A (Shift (h, 0) B)

def StripPlaced {H : Nat → Prop} {w : Nat} (p : VerticalPalette H w)
    (heights : Nat → Nat) (i _j : Nat) : Region → Prop :=
  ShiftTiles (Prefix heights i, 0) (p.tiles (heights i))

theorem strip_assembly {H : Nat → Prop} {w : Nat} (p : VerticalPalette H w)
    (heights : Nat → Nat) (nr h : Nat)
    (hhpos : ∀ i, 0 < heights i) (hwpos : 0 < w)
    (hh : ∀ i, i < nr → H (heights i)) (hend : Prefix heights nr = h) :
    ∃ T, Tiling (Rectangle h w) T ∧ PairwiseRigid T := by
  refine ⟨GridTiles (StripPlaced p heights) nr 1, ?_⟩
  apply rectangular_assembly hhpos (fun _ => hwpos) hend
    (show Prefix (fun _ => w) 1 = (w : Int) by simp [Prefix])
  · intro i hi j hj
    have hj0 : j = 0 := by omega
    subst j
    rw [← shift_rectangle heights (fun _ => w) i 0]
    exact shift_tiling (Prefix heights i, 0) (p.partition _ (hh i hi))
  · intro i hi j _hj
    exact shift_pairwiseRigid _ (p.internal _ (hh i hi))
  · apply all_side_checks
    · intro i hi j _hj A B ha hb
      obtain ⟨C,hc,heq⟩ := ha
      obtain ⟨D,hd,heq'⟩ := hb
      subst A; subst B
      have ht := shift_rigid (Prefix heights i, 0)
        (p.vertical (heights i) (heights (i+1)) (hh i (by omega)) (hh (i+1) hi) C D hc hd)
      rw [shift_comp] at ht
      have he : Add (Prefix heights i, 0) ((heights i : Int), 0) =
          (Prefix heights (i+1), 0) := by
        apply Prod.ext <;> simp only [Add, Prefix] <;> omega
      rw [he] at ht
      exact ht
    · intro _ _ j hj
      omega

theorem six_nine_strip {w : Nat}
    (p : VerticalPalette (fun h => h = 6 ∨ h = 9) w)
    (m : Nat) (hm : 6 ≤ m) (hd : 3 ∣ m) (hw : 4 ≤ w) :
    ∃ T, Locked (Rectangle m w) T := by
  obtain ⟨a,b,hab⟩ := height_six_nine m hm hd
  obtain ⟨T,ht,hr⟩ := strip_assembly p (TwoSizes a 6 9) (a+b) m
    (twoSizes_positive (by decide) (by decide)) (by omega)
    (by intro i _; unfold TwoSizes; split <;> simp)
    (by rw [prefix_twoSizes]; omega)
  exact ⟨T, locked_of_rigid hm hd hw ht hr⟩

structure RigidBlock (h w : Nat) where
  tiles : Region → Prop
  partition : Tiling (Rectangle h w) tiles
  internal : PairwiseRigid tiles

structure WidthFiveCertificate where
  direct6 : RigidBlock 6 5
  direct15 : RigidBlock 15 5
  strips : VerticalPalette (fun h => h = 9 ∨ h = 12) 5

theorem width_five (p : WidthFiveCertificate) (m : Nat) (hm : 6 ≤ m) (hd : 3 ∣ m) :
    ∃ T, Locked (Rectangle m 5) T := by
  by_cases h6 : m = 6
  · subst m
    exact ⟨p.direct6.tiles, locked_of_rigid (by decide) (by decide) (by decide)
      p.direct6.partition p.direct6.internal⟩
  by_cases h15 : m = 15
  · subst m
    exact ⟨p.direct15.tiles, locked_of_rigid (by decide) (by decide) (by decide)
      p.direct15.partition p.direct15.internal⟩
  obtain ⟨a,b,hab⟩ := height_nine_twelve m hm hd h6 h15
  obtain ⟨T,ht,hr⟩ := strip_assembly p.strips (TwoSizes a 9 12) (a+b) m
    (twoSizes_positive (by decide) (by decide)) (by decide)
    (by intro i _; unfold TwoSizes; split <;> simp)
    (by rw [prefix_twoSizes]; omega)
  exact ⟨T, locked_of_rigid hm hd (by decide) ht hr⟩

/-- Finite interface for the exact conjecture. Generated/Universal.lean constructs
a checked value from the supplied coordinate witnesses. -/
structure ProposedCertificate where
  small : ∀ w, 4 ≤ w → w < 56 → w ≠ 5 →
    VerticalPalette (fun h => h = 6 ∨ h = 9) w
  five : WidthFiveCertificate
  tail : Palette (fun h => h = 6 ∨ h = 9) (fun w => w = 8 ∨ w = 9)

theorem universal_of_proposed_certificate (p : ProposedCertificate)
    (m n : Nat) (hm : 6 ≤ m) (hd : 3 ∣ m) (hn : 4 ≤ n) :
    ∃ T, Locked (Rectangle m n) T := by
  by_cases ht : 56 ≤ n
  · exact six_nine_eight_nine_tail p.tail m n hm hd ht
  by_cases h5 : n = 5
  · subst n
    exact width_five p.five m hm hd
  · exact six_nine_strip (p.small n hn (by omega) h5) m hm hd hn

end LockedTromino
