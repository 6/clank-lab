import CD13.ModelAction
import CD13.Presentation

/-! Compatibility of word congruence with the presented monoid. -/
noncomputable section
namespace CD13
universe u v
variable {V : Type u} {E : V → V → Prop}

theorem eval_respects_rel (D : LocalSystem.{u, v} E) (hE : Acyclic E)
    {a b : List V} (h : HK.Rel E a b) :
    eval D (FreeMonoid.ofList a) = eval D (FreeMonoid.ofList b) :=
  eval_eq_of_hk_eq D hE ((Presentation.presented_eq_iff_rel E a b).2 h)

/-- Relation words retain the written order; schedules execute their reverse. -/
theorem constructor_run_respects [Finite V] (hE : Acyclic E)
    {a b : List V} (h : HK.Rel E a b) (s : TermState E) :
    run a.reverse s = run b.reverse s := by
  rw [← constructor_eval_run hE a s, ← constructor_eval_run hE b s]
  exact congrFun (eval_respects_rel (constructorSystem hE) hE h) s

end CD13
