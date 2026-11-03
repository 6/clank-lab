import Antony24.Orientation
import Antony24.Local

/-! The converse construction. -/
namespace Antony24
variable {V : Type*} {G : SimpleGraph V}

private def sideColour (side : V → Bool) (v : V) : Colour :=
  if side v then 0 else 3

private def orientPort (side : V → Bool) (o : V → V → Bool) (u v : V) : Colour :=
  if side u ≠ side v then 2 else if o u v then 3 else 1

private lemma sideColour_extreme (side : V → Bool) (v : V) :
    Extreme (sideColour side v) := by
  cases hv : side v <;> simp [sideColour, hv, Extreme]

private lemma orientPort_path (side : V → Bool) (o : V → V → Bool) (u v : V)
    (h : side u = side v → o u v ≠ o v u) :
    PathOK (sideColour side u)
      (portColour (sideColour side u) (orientPort side o u v))
      (portColour (sideColour side v) (orientPort side o v u))
      (sideColour side v) := by
  apply path_portColour _ _ _ _ (sideColour_extreme side u) (sideColour_extreme side v)
  cases hu : side u <;> cases hv : side v <;>
    cases h₁ : o u v <;> cases h₂ : o v u <;>
    simp_all [sideColour, orientPort]

private lemma orientation_injective (R : SimpleGraph V)
    (htwo : ∀ v, ∃ a b, a ≠ b ∧ ∀ w, R.Adj v w ↔ w = a ∨ w = b)
    (o : V → V → Bool) (hout : ∀ v, ∃! w, R.Adj v w ∧ o v w = true)
    {v u w : V} (hu : R.Adj v u) (hw : R.Adj v w) (hne : u ≠ w) :
    o v u ≠ o v w := by
  obtain ⟨t,ht,htuniq⟩ := hout v
  have htuw : t = u ∨ t = w := by
    obtain ⟨a,b,hab,hh⟩ := htwo v
    have htu := (hh t).mp ht.1
    have huu := (hh u).mp hu
    have hwu := (hh w).mp hw
    aesop
  intro heq
  rcases htuw with rfl | rfl
  · exact hne (htuniq w ⟨hw, heq ▸ ht.2⟩).symm
  · exact hne (htuniq u ⟨hu, heq.symm ▸ ht.2⟩)

private lemma orientPort_injective (side : V → Bool) (o : V → V → Bool)
    (hcross : ∀ v, ∃! w, G.Adj v w ∧ side v ≠ side w)
    (ho : ∀ {v u w}, G.Adj v u → G.Adj v w → side v = side u →
      side v = side w → u ≠ w → o v u ≠ o v w)
    {v u w : V} (hu : G.Adj v u) (hw : G.Adj v w) (hne : u ≠ w) :
    orientPort side o v u ≠ orientPort side o v w := by
  by_cases hsu : side v ≠ side u
  · by_cases hsw : side v ≠ side w
    · obtain ⟨m,hm,hmuniq⟩ := hcross v
      exact (hne ((hmuniq u ⟨hu,hsu⟩).trans (hmuniq w ⟨hw,hsw⟩).symm)).elim
    · cases h : o v w <;> simp [orientPort,hsu,hsw,h]
  · by_cases hsw : side v ≠ side w
    · cases h : o v u <;> simp [orientPort,hsu,hsw,h]
    · have hone := ho hu hw (not_not.mp hsu) (not_not.mp hsw) hne
      cases h₁ : o v u <;> cases h₂ : o v w <;>
        simp_all [orientPort]

/-- Every perfect matching cut of a finite cubic graph gives a graceful
four-colouring of its twice-subdivision, with no connectedness assumption. -/
theorem pmc_implies_graceful4_s2 [Finite V] (hG : Cubic G) :
    PMC G → Graceful4 (S2 G) := by
  classical
  rintro ⟨side,hside⟩
  have htwo := sameSide_two_regular G hG side hside
  obtain ⟨o,ho,hout⟩ := two_regular_orientation (sameSide G side) htwo
  have hoinj : ∀ {v u w}, G.Adj v u → G.Adj v w → side v = side u →
      side v = side w → u ≠ w → o v u ≠ o v w := by
    intro v u w hu hw hsu hsw hne
    exact orientation_injective _ htwo o hout ⟨hu,hsu⟩ ⟨hw,hsw⟩ hne
  let a := sideColour side
  let p := orientPort side o
  let c : SubVertex G → Colour := fun x => match x with
    | .inl v => a v
    | .inr d => portColour (a d.val.1) (p d.val.1 d.val.2)
  have hap : ∀ d : Dart G,
      PathOK (a d.val.1) (c (.inr d)) (c (.inr d.rev)) (a d.val.2) := by
    intro d
    exact orientPort_path side o _ _ (fun heq => ho ⟨d.property,heq⟩)
  have hdiff : ∀ d : Dart G,
      diff (a d.val.1) (c (.inr d)) = (p d.val.1 d.val.2).val := by
    intro d
    exact diff_portColour _ _ (sideColour_extreme side _)
  refine ⟨c, ?_, ?_⟩
  · intro x y hxy
    cases x with
    | inl v =>
      cases y with
      | inl w => exact hxy.elim
      | inr d =>
        change v = d.val.1 at hxy
        subst v
        exact (hap d).1
    | inr d =>
      cases y with
      | inl v =>
        change v = d.val.1 at hxy
        subst v
        exact (hap d).1.symm
      | inr e =>
        change e = d.rev at hxy
        subst e
        exact (hap d).2.1
  · intro x y z hxy hxz hyz
    cases x with
    | inl v =>
      cases y with
      | inl w => exact hxy.elim
      | inr d =>
        cases z with
        | inl w => exact hxz.elim
        | inr e =>
          change v = d.val.1 at hxy
          change v = e.val.1 at hxz
          have hne : d.val.2 ≠ e.val.2 := by
            intro h
            apply hyz
            congr 1
            apply Subtype.ext
            exact Prod.ext (hxy.symm.trans hxz) h
          have hpne := orientPort_injective side o hside hoinj
            (hxy ▸ d.property) (hxz ▸ e.property) hne
          change diff (a v) (c (.inr d)) ≠ diff (a v) (c (.inr e))
          have hdd := hdiff d
          have hee := hdiff e
          rw [← hxy] at hdd
          rw [← hxz] at hee
          rw [hdd, hee]
          exact fun h => hpne (Fin.ext h)
    | inr d =>
      cases y with
      | inl v =>
        change v = d.val.1 at hxy
        subst v
        cases z with
        | inl w =>
          change w = d.val.1 at hxz
          exact (hyz (congrArg Sum.inl hxz.symm)).elim
        | inr e =>
          change e = d.rev at hxz
          subst e
          change diff (c (.inr d)) (a d.val.1) ≠ _
          simpa only [diff, Nat.dist_comm] using (hap d).2.2.2.1
      | inr e =>
        change e = d.rev at hxy
        subst e
        cases z with
        | inl v =>
          change v = d.val.1 at hxz
          subst v
          simpa only [diff, Nat.dist_comm] using (hap d).2.2.2.1.symm
        | inr f =>
          change f = d.rev at hxz
          exact (hyz (congrArg Sum.inr hxz.symm)).elim

end Antony24
