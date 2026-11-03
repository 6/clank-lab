import CD13.Endpoint
import CD13.HK

/-! Adapters between the two word presentations and repeat predicates. -/
namespace CD13.Presentation
universe u
variable {V : Type u}

theorem conGen_to_rel (E : V → V → Prop) {a b : FreeMonoid V}
    (h : conGen (HKRel E) a b) :
    HK.Rel E (FreeMonoid.toList a) (FreeMonoid.toList b) := by
  change ConGen.Rel (HKRel E) a b at h
  induction h with
  | of a b h =>
    cases h with
    | idem i => exact HK.Rel.idem i
    | commute i j h => exact HK.Rel.commute i j h.1 h.2.1 h.2.2
    | edge_left i j h => exact HK.Rel.triangleOut i j h
    | edge_right i j h => exact HK.Rel.triangleIn i j h
  | refl a => exact HK.Rel.refl _
  | symm h ih => exact HK.Rel.symm ih
  | trans h k ih ik => exact HK.Rel.trans ih ik
  | mul h k ih ik => exact HK.Rel.append ih ik

theorem rel_to_conGen (E : V → V → Prop) {a b : List V}
    (h : HK.Rel E a b) :
    conGen (HKRel E) (FreeMonoid.ofList a) (FreeMonoid.ofList b) := by
  change ConGen.Rel (HKRel E) (FreeMonoid.ofList a) (FreeMonoid.ofList b)
  induction h with
  | refl w => exact ConGen.Rel.refl _
  | symm h ih => exact ConGen.Rel.symm ih
  | trans h k ih ik => exact ConGen.Rel.trans ih ik
  | append h k ih ik => exact ConGen.Rel.mul ih ik
  | idem a => exact ConGen.Rel.of _ _ (HKRel.idem a)
  | commute a b h₁ h₂ h₃ =>
    exact ConGen.Rel.of _ _ (HKRel.commute a b ⟨h₁, h₂, h₃⟩)
  | triangleOut a b h => exact ConGen.Rel.of _ _ (HKRel.edge_left a b h)
  | triangleIn a b h => exact ConGen.Rel.of _ _ (HKRel.edge_right a b h)

/-- The two presentations identify exactly the same words. -/
theorem presented_eq_iff_rel (E : V → V → Prop) (a b : List V) :
    PresentedMonoid.mk (HKRel E) (FreeMonoid.ofList a) =
      PresentedMonoid.mk (HKRel E) (FreeMonoid.ofList b) ↔ HK.Rel E a b := by
  rw [PresentedMonoid.mk_eq_mk_iff]
  exact ⟨conGen_to_rel E, rel_to_conGen E⟩

/-- The predicates differ only by the order of the two witnesses and list
parenthesization. Both quantify all occurrence pairs. -/
theorem repeat_iff_reduction (E : V → V → Prop) (w : List V) :
    CD13.RepeatProperty E w ↔ Reduction.RepeatProperty E w := by
  constructor
  · intro h a p m q hw
    have hh := h a p m q (by simpa only [List.append_assoc, List.singleton_append,
      List.cons_append, List.nil_append] using hw)
    exact ⟨hh.2, hh.1⟩
  · intro h a p m q hw
    have hh := h a p m q (by simpa only [List.append_assoc, List.singleton_append,
      List.cons_append, List.nil_append] using hw)
    exact ⟨hh.2, hh.1⟩

theorem reduced_representative (E : V → V → Prop) (w : List V) :
    ∃ v, PresentedMonoid.mk (HKRel E) (FreeMonoid.ofList w) =
      PresentedMonoid.mk (HKRel E) (FreeMonoid.ofList v) ∧
      CD13.RepeatProperty E v ∧ v.length ≤ w.length := by
  obtain ⟨v, hv, hr, hl⟩ := HK.reduced_representative E w
  exact ⟨v, (presented_eq_iff_rel E w v).2 hv,
    (repeat_iff_reduction E v).2 hr, hl⟩

end CD13.Presentation
