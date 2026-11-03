import CD13.Endpoint
import CD13.LocalRelations
import CD13.Recovery
import CD13.AlgebraBridge

/-!
Final presented-action and universal-kernel glue.
The constructor recovery theorem discharges the separating-model premise
for every finite DAG, including the empty vertex type.
-/
noncomputable section
namespace CD13.Faithful
open scoped Classical
universe u
variable {V : Type u} {E : V → V → Prop}

/-- An evaluation-separating model makes its induced HK action injective. -/
theorem injective_of_separates (D : LocalSystem.{u,u} E)
    (ρ : HK E →* Function.End (State D))
    (factor : ∀ w, ρ (PresentedMonoid.mk (HKRel E) w) = eval D w)
    (separates : ∀ u v, eval D u = eval D v →
      PresentedMonoid.mk (HKRel E) u = PresentedMonoid.mk (HKRel E) v) :
    Function.Injective ρ := by
  intro x y h
  obtain ⟨u, rfl⟩ := PresentedMonoid.surjective_mk x
  obtain ⟨v, rfl⟩ := PresentedMonoid.surjective_mk y
  apply separates u v
  simpa only [factor] using h

/-- All legal models respect HK equality, and one separates it, so the
intersection of their kernels is exactly the defining HK congruence. -/
theorem universal_kernel (D : LocalSystem.{u,u} E)
    (respect : ∀ (A : LocalSystem.{u,u} E) u v,
      PresentedMonoid.mk (HKRel E) u = PresentedMonoid.mk (HKRel E) v →
        eval A u = eval A v)
    (separates : ∀ u v, eval D u = eval D v →
      PresentedMonoid.mk (HKRel E) u = PresentedMonoid.mk (HKRel E) v)
    (u v : FreeMonoid V) :
    (∀ A : LocalSystem.{u,u} E, eval A u = eval A v) ↔
      PresentedMonoid.mk (HKRel E) u = PresentedMonoid.mk (HKRel E) v := by
  constructor
  · intro h
    exact separates u v (h D)
  · intro h A
    exact respect A u v h

/-- Exact existential conclusion required at one finite DAG by FullEndpoint.
No premise here is counted as proved by this integration lemma. -/
theorem endpoint_of_separates (D : LocalSystem.{u,u} E)
    (ρ : HK E →* Function.End (State D))
    (generator : ∀ i, ρ (PresentedMonoid.of (HKRel E) i) = update D i)
    (factor : ∀ w, ρ (PresentedMonoid.mk (HKRel E) w) = eval D w)
    (respect : ∀ (A : LocalSystem.{u,u} E) u v,
      PresentedMonoid.mk (HKRel E) u = PresentedMonoid.mk (HKRel E) v →
        eval A u = eval A v)
    (separates : ∀ u v, eval D u = eval D v →
      PresentedMonoid.mk (HKRel E) u = PresentedMonoid.mk (HKRel E) v) :
    ∃ (D : LocalSystem.{u,u} E) (ρ : HK E →* Function.End (State D)),
      Function.Injective ρ ∧
      (∀ i, ρ (PresentedMonoid.of (HKRel E) i) = update D i) ∧
      (∀ u v : FreeMonoid V,
        (∀ A : LocalSystem.{u,u} E, eval A u = eval A v) ↔
          PresentedMonoid.mk (HKRel E) u = PresentedMonoid.mk (HKRel E) v) := by
  exact ⟨D, ρ, injective_of_separates D ρ factor separates, generator,
    universal_kernel D respect separates⟩

/-- The initial constructor vector already separates all written HK words. -/
theorem constructor_separates_lists [Fintype V] (hE : Acyclic E)
    (u v : List V)
    (heq : run (E := E) u.reverse initialState = run v.reverse initialState) :
    HK.Rel E u v := by
  apply AlgebraBridge.word_separation E
    (fun w => run (E := E) w.reverse initialState)
    (fun _ _ h => constructor_run_respects hE h initialState) ?_ u v heq
  intro a b ha hb hstate
  apply Recovery.projection_endpoint (acyclic_irrefl hE) a b
    ((Presentation.repeat_iff_reduction E a).2 ha)
    ((Presentation.repeat_iff_reduction E b).2 hb)
  simpa only [List.reverse_reverse] using hstate

theorem constructor_separates [Fintype V] (hE : Acyclic E)
    (u v : FreeMonoid V)
    (heq : eval (constructorSystem hE) u = eval (constructorSystem hE) v) :
    PresentedMonoid.mk (HKRel E) u = PresentedMonoid.mk (HKRel E) v := by
  have hs : run (E := E) u.toList.reverse initialState =
      run v.toList.reverse initialState := by
    rw [← constructor_eval_run hE, ← constructor_eval_run hE]
    exact congrFun heq initialState
  exact (Presentation.presented_eq_iff_rel E u.toList v.toList).2
    (constructor_separates_lists hE _ _ hs)

/-- Collina–D'Andrea's full finite-DAG local faithfulness endpoint. -/
theorem full_endpoint : FullEndpoint.{u} := by
  intro V _ E hE
  letI : Fintype V := Fintype.ofFinite V
  exact endpoint_of_separates (constructorSystem hE) (action (constructorSystem hE) hE)
    (action_of _ hE) (action_mk _ hE)
    (fun A _ _ h => eval_eq_of_hk_eq A hE h) (constructor_separates hE)

end CD13.Faithful
