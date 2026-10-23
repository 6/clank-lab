import Statement

namespace LitOnlySigma

/-! General bridges: the minimum is attained, identity steps do not matter,
and natural subtraction agrees with the source's nonnegative difference. -/

theorem minimumLight_attained {n : ℕ}
    (move : Configuration n → Fin n → Configuration n) (x : Configuration n) :
    ∃ y, Reachable move x y ∧ lightNumber y = minimumLight move x :=
  Nat.sInf_mem (s := {k | ∃ y, Reachable move x y ∧ lightNumber y = k})
    ⟨lightNumber x, x, Relation.ReflTransGen.refl, rfl⟩

theorem minimumLight_le {n : ℕ}
    {move : Configuration n → Fin n → Configuration n} {x y : Configuration n}
    (h : Reachable move x y) : minimumLight move x ≤ lightNumber y :=
  Nat.sInf_le ⟨y, h, rfl⟩

theorem minimumLight_eq {n : ℕ}
    {move : Configuration n → Fin n → Configuration n} {x : Configuration n} {k : ℕ}
    (attained : ∃ y, Reachable move x y ∧ lightNumber y = k)
    (lower : ∀ y, Reachable move x y → k ≤ lightNumber y) : minimumLight move x = k := by
  apply Nat.le_antisymm
  · obtain ⟨y, hy, hk⟩ := attained
    rw [← hk]
    exact minimumLight_le hy
  · obtain ⟨y, hy, hk⟩ := minimumLight_attained move x
    rw [← hk]
    exact lower y hy

theorem reachable_iff_changing_steps {n : ℕ}
    (move : Configuration n → Fin n → Configuration n) (x y : Configuration n) :
    Reachable move x y ↔
      Relation.ReflTransGen (fun a b => a ≠ b ∧ ∃ v, b = move a v) x y := by
  constructor
  · intro h
    induction h with
    | refl => exact .refl
    | @tail b c _ h ih =>
      by_cases heq : b = c
      · subst c
        exact ih
      · exact ih.tail ⟨heq, h⟩
  · intro h
    induction h with
    | refl => exact .refl
    | tail _ step ih => exact ih.tail step.2

theorem litOnlyReachable_regular {n : ℕ} (G : Graph n) {x y : Configuration n}
    (h : Reachable (litOnlyMove G) x y) : Reachable (regularMove G) x y := by
  induction h with
  | refl => exact .refl
  | @tail a b _ h ih =>
    obtain ⟨v, rfl⟩ := h
    cases hv : a v with
    | false => simpa [litOnlyMove, hv] using ih
    | true => exact ih.tail ⟨v, by simp [litOnlyMove, hv]⟩

theorem regularMinimum_le_litOnlyMinimum {n : ℕ} (G : Graph n) (x : Configuration n) :
    regularMinimum G x ≤ litOnlyMinimum G x := by
  obtain ⟨y, hy, hk⟩ := minimumLight_attained (litOnlyMove G) x
  rw [litOnlyMinimum, ← hk]
  exact minimumLight_le (litOnlyReachable_regular G hy)

/-! Identity of the fixed graph and configuration, independently of the closure proof. -/

theorem graph_undirected : Undirected graph := by
  unfold Undirected
  decide

theorem graph_loopless : ∀ v, graph v v = false := by decide

/-- Remove the six cycle edges from K7; vertex 6 is outside the cycle. -/
theorem graph_is_cycle_complement : ∀ u v : Fin 7,
    graph u v = true ↔ u ≠ v ∧
      ¬ (u.val < 6 ∧ v.val < 6 ∧
        ((u.val + 1) % 6 = v.val ∨ (v.val + 1) % 6 = u.val)) := by decide

theorem start_lights : ∀ v : Fin 7,
    start v = true ↔ v = 0 ∨ v = 1 ∨ v = 3 ∨ v = 4 := by decide

theorem graph_connected : Connected graph := by
  have toHub : ∀ u : Fin 7, u = 6 ∨ graph u 6 = true := by decide
  have fromHub : ∀ v : Fin 7, v = 6 ∨ graph 6 v = true := by decide
  intro u v
  have hu : Relation.ReflTransGen (fun a b => graph a b = true) u 6 := by
    rcases toHub u with rfl | h
    · exact .refl
    · exact .single h
  rcases fromHub v with rfl | h
  · exact hu
  · exact hu.tail h

theorem graph_not_completeMultipartite (m : ℕ) : ¬ CompleteMultipartite graph m := by
  rintro ⟨part, _, adj⟩
  have h01 : part 0 = part 1 := by
    by_contra h
    exact (by decide : ¬ graph 0 1 = true) ((adj 0 1).mpr h)
  have h12 : part 1 = part 2 := by
    by_contra h
    exact (by decide : ¬ graph 1 2 = true) ((adj 1 2).mpr h)
  exact (adj 0 2).mp (by decide) (h01.trans h12)

/-! All finite certificate checks below reduce in the Lean kernel. -/

def closedCodes : Fin 10 → ℕ := ![27, 45, 54, 63, 71, 78, 92, 99, 113, 120]

def InCertificate (y : Configuration 7) : Prop := ∃ i, y = decode (closedCodes i)

theorem certificate_closed : ∀ i : Fin 10, ∀ v : Fin 7, ∃ j : Fin 10,
    litOnlyMove graph (decode (closedCodes i)) v = decode (closedCodes j) := by decide

theorem certificate_lower : ∀ i : Fin 10, 4 ≤ lightNumber (decode (closedCodes i)) := by
  decide

theorem reachable_in_certificate {y : Configuration 7}
    (h : Reachable (litOnlyMove graph) start y) : InCertificate y := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | tail _ h ih =>
    obtain ⟨i, rfl⟩ := ih
    obtain ⟨v, rfl⟩ := h
    exact certificate_closed i v

theorem litOnly_lower {y : Configuration 7}
    (h : Reachable (litOnlyMove graph) start y) : 4 ≤ lightNumber y := by
  obtain ⟨i, rfl⟩ := reachable_in_certificate h
  exact certificate_lower i

theorem start_weight : lightNumber start = 4 := by decide

theorem regular_path : Reachable (regularMove graph) start (decode 0) := by
  have h : Reachable (regularMove graph) start (decode 71) :=
    Relation.ReflTransGen.single ⟨0, by decide⟩
  exact h.tail ⟨4, by decide⟩

theorem regular_minimum : regularMinimum graph start = 0 :=
  minimumLight_eq ⟨decode 0, regular_path, by decide⟩ (fun _ _ => Nat.zero_le _)

theorem litOnly_minimum : litOnlyMinimum graph start = 4 :=
  minimumLight_eq ⟨start, Relation.ReflTransGen.refl, start_weight⟩ (fun _ => litOnly_lower)

theorem discrepancy_at_least_four : 4 ≤ discrepancy graph := by
  have h : litOnlyMinimum graph start - regularMinimum graph start ≤ discrepancy graph :=
    Finset.le_sup (f := fun x => litOnlyMinimum graph x - regularMinimum graph x)
      (Finset.mem_univ start)
  simpa [litOnly_minimum, regular_minimum] using h

theorem exceeds_half : 7 < 2 * discrepancy graph :=
  Nat.lt_of_lt_of_le (by decide : 7 < 2 * 4)
    (Nat.mul_le_mul_left 2 discrepancy_at_least_four)

theorem not_conjecture5 : ¬ Conjecture5 graph := by
  intro h
  obtain ⟨m, _, _, hm⟩ := h graph_undirected graph_connected exceeds_half
  exact graph_not_completeMultipartite m hm

/-- The fixed endpoint, with no assumptions on a certificate or a search. -/
theorem counterexample : CounterexampleStatement :=
  ⟨graph_undirected, graph_connected, regular_minimum, litOnly_minimum,
    graph_not_completeMultipartite, not_conjecture5⟩

end LitOnlySigma
