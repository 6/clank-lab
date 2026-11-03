import CD13.Model

/-! Local-update laws and the induced HK action. -/
noncomputable section
namespace CD13
open scoped Classical
universe u v
variable {V : Type u} {E : V → V → Prop}

theorem acyclic_irrefl (hE : Acyclic E) (i : V) : ¬ E i i :=
  fun h => hE i (Relation.TransGen.single h)

theorem acyclic_asymm (hE : Acyclic E) {i j : V} (hij : E i j) : ¬ E j i :=
  fun hji => hE i ((Relation.TransGen.single hij).trans (Relation.TransGen.single hji))

def localValue (D : LocalSystem.{u, v} E) (i : V) (s : State D) : D.S i :=
  D.localFn i (fun j => s j.val)

theorem update_eq (D : LocalSystem E) (i : V) (s : State D) :
    update D i s = Function.update s i (localValue D i s) := rfl

theorem localValue_modify (D : LocalSystem E) (i k : V) (s : State D)
    (x : D.S k) (h : ¬ E i k) :
    localValue D i (Function.update s k x) = localValue D i s := by
  apply congrArg (D.localFn i)
  funext j
  apply Function.update_of_ne
  intro hjk
  exact h (hjk ▸ j.property)

theorem localValue_update (D : LocalSystem E) (i k : V) (s : State D)
    (h : ¬ E i k) : localValue D i (update D k s) = localValue D i s :=
  localValue_modify D i k s _ h

theorem update_absorb_modify (D : LocalSystem E) (i : V) (s : State D)
    (x : D.S i) (h : ¬ E i i) :
    update D i (Function.update s i x) = update D i s := by
  rw [update_eq, localValue_modify D i i s x h, Function.update_idem, ← update_eq]

theorem update_idempotent (D : LocalSystem E) (i : V) (h : ¬ E i i) :
    update D i * update D i = update D i := by
  funext s
  exact update_absorb_modify D i s _ h

theorem update_move_inner (D : LocalSystem E) (i j : V) (s : State D)
    (hij : i ≠ j) (hji : ¬ E j i) :
    update D j (update D i s) = Function.update (update D j s) i (localValue D i s) := by
  rw [update_eq D j, localValue_update D j i s hji, update_eq D i,
    update_eq D j]
  exact Function.update_comm hij _ _ _

theorem update_commute (D : LocalSystem E) (i j : V) (h : Independent E i j) :
    update D i * update D j = update D j * update D i := by
  funext s
  change update D i (update D j s) = update D j (update D i s)
  rw [update_eq D i, localValue_update D i j s h.2.1]
  exact (update_move_inner D i j s h.1 h.2.2).symm

theorem update_edge_left (D : LocalSystem E) (i j : V) (hE : Acyclic E)
    (hij : E i j) :
    update D i * update D j * update D i = update D i * update D j := by
  have hne : i ≠ j := by rintro rfl; exact acyclic_irrefl hE i hij
  funext s
  change update D i (update D j (update D i s)) = update D i (update D j s)
  rw [update_move_inner D i j s hne (acyclic_asymm hE hij)]
  exact update_absorb_modify D i _ _ (acyclic_irrefl hE i)

theorem update_edge_right (D : LocalSystem E) (i j : V) (hE : Acyclic E)
    (hij : E i j) :
    update D j * update D i * update D j = update D i * update D j := by
  have hne : i ≠ j := by rintro rfl; exact acyclic_irrefl hE i hij
  funext s
  change update D j (update D i (update D j s)) = update D i (update D j s)
  rw [update_move_inner D i j (update D j s) hne (acyclic_asymm hE hij)]
  rw [show update D j (update D j s) = update D j s from
    congrFun (update_idempotent D j (acyclic_irrefl hE j)) s]
  rfl

/-- Every admissible local system obeys all defining HK relations. -/
theorem eval_respects (D : LocalSystem E) (hE : Acyclic E)
    (a b : FreeMonoid V) (h : HKRel E a b) : eval D a = eval D b := by
  cases h with
  | idem i => exact update_idempotent D i (acyclic_irrefl hE i)
  | commute i j h => exact update_commute D i j h
  | edge_left i j h => exact update_edge_left D i j hE h
  | edge_right i j h => exact update_edge_right D i j hE h

/-- Ordinary-composition action of the presented HK monoid. -/
def action (D : LocalSystem E) (hE : Acyclic E) : HK E →* Function.End (State D) :=
  PresentedMonoid.lift (update D) (eval_respects D hE)

@[simp] theorem action_of (D : LocalSystem E) (hE : Acyclic E) (i : V) :
    action D hE (PresentedMonoid.of (HKRel E) i) = update D i := rfl

@[simp] theorem action_mk (D : LocalSystem E) (hE : Acyclic E) (w : FreeMonoid V) :
    action D hE (PresentedMonoid.mk (HKRel E) w) = eval D w := rfl

theorem eval_eq_of_hk_eq (D : LocalSystem E) (hE : Acyclic E)
    {a b : FreeMonoid V}
    (h : PresentedMonoid.mk (HKRel E) a = PresentedMonoid.mk (HKRel E) b) :
    eval D a = eval D b := congrArg (action D hE) h

@[simp] theorem constructor_update [Finite V] (hE : Acyclic E) (i : V) :
    update (constructorSystem hE) i = step i := rfl

/-- The written product is executed rightmost first, exactly reversing the
chronological constructor schedule. -/
theorem constructor_eval_run [Finite V] (hE : Acyclic E) (w : List V)
    (s : TermState E) :
    eval (constructorSystem hE) (FreeMonoid.ofList w) s = run w.reverse s := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    rw [FreeMonoid.ofList_cons, map_mul]
    change update (constructorSystem hE) a
      (eval (constructorSystem hE) (FreeMonoid.ofList w) s) = _
    rw [ih, constructor_update]
    simp only [List.reverse_cons, run_append, run_cons, run_nil] <;> rfl

end CD13
