import ExtensionStatement
import Mathlib.Data.Fintype.Prod

namespace LitOnlySigma

/-! The definitions and endpoint are frozen in ExtensionStatement.  The first
lemmas check the crucial pointwise move rule and its lit-only guard. -/

theorem uniform_regularMove (m : ℕ) (x : Configuration 7) (v : Fin (7 * m)) :
    regularMove (blowup m) (uniformLift m x) v =
      uniformLift m (regularMove graph x (fiberVertex v)) := by
  rfl

theorem uniform_lit_legality (m : ℕ) (x : Configuration 7) (v : Fin (7 * m)) :
    uniformLift m x v = true ↔ x (fiberVertex v) = true := Iff.rfl

theorem uniform_litOnlyMove (m : ℕ) (x : Configuration 7) (v : Fin (7 * m)) :
    litOnlyMove (blowup m) (uniformLift m x) v =
      uniformLift m (litOnlyMove graph x (fiberVertex v)) := by
  cases h : x (fiberVertex v) <;>
    simp [litOnlyMove, uniformLift, h, uniform_regularMove]

/-- Every base vertex has a copy when m is positive. -/
def firstCopy {m : ℕ} (hm : 0 < m) (v : Fin 7) : Fin (7 * m) :=
  finProdFinEquiv (v, ⟨0, hm⟩)

theorem fiber_firstCopy {m : ℕ} (hm : 0 < m) (v : Fin 7) :
    fiberVertex (firstCopy hm v) = v := by
  simp [fiberVertex, firstCopy]

/-- A semiconjugacy of individual moves projects every finite move sequence. -/
theorem reachable_project {n k : ℕ}
    (move : Configuration n → Fin n → Configuration n)
    (move' : Configuration k → Fin k → Configuration k)
    (lift : Configuration n → Configuration k) (vertex : Fin k → Fin n)
    (commutes : ∀ x v, move' (lift x) v = lift (move x (vertex v)))
    {x : Configuration n} {y : Configuration k}
    (h : Reachable move' (lift x) y) :
    ∃ z, Reachable move x z ∧ y = lift z := by
  induction h with
  | refl => exact ⟨x, .refl, rfl⟩
  | @tail a b _ step ih =>
    obtain ⟨z, hz, rfl⟩ := ih
    obtain ⟨v, rfl⟩ := step
    exact ⟨move z (vertex v), hz.tail ⟨vertex v, rfl⟩, commutes z v⟩

/-- Choosing one copy of each base vertex lifts every finite sequence. -/
theorem reachable_lift {n k : ℕ}
    (move : Configuration n → Fin n → Configuration n)
    (move' : Configuration k → Fin k → Configuration k)
    (lift : Configuration n → Configuration k) (copy : Fin n → Fin k)
    (commutes : ∀ x v, move' (lift x) (copy v) = lift (move x v))
    {x y : Configuration n} (h : Reachable move x y) :
    Reachable move' (lift x) (lift y) := by
  induction h with
  | refl => exact .refl
  | @tail a b _ step ih =>
    obtain ⟨v, rfl⟩ := step
    exact ih.tail ⟨copy v, (commutes a v).symm⟩

/-- Projection also proves that no nonuniform configuration is reachable. -/
theorem regular_reachable_uniform {m : ℕ} (hm : 0 < m)
    (x : Configuration 7) (y : Configuration (7 * m)) :
    Reachable (regularMove (blowup m)) (uniformLift m x) y ↔
      ∃ z, Reachable (regularMove graph) x z ∧ y = uniformLift m z := by
  constructor
  · exact reachable_project _ _ _ _ (uniform_regularMove m)
  · rintro ⟨z, hz, rfl⟩
    apply reachable_lift _ _ _ (firstCopy hm) _ hz
    intro a v
    simpa only [fiber_firstCopy] using uniform_regularMove m a (firstCopy hm v)

theorem litOnly_reachable_uniform {m : ℕ} (hm : 0 < m)
    (x : Configuration 7) (y : Configuration (7 * m)) :
    Reachable (litOnlyMove (blowup m)) (uniformLift m x) y ↔
      ∃ z, Reachable (litOnlyMove graph) x z ∧ y = uniformLift m z := by
  constructor
  · exact reachable_project _ _ _ _ (uniform_litOnlyMove m)
  · rintro ⟨z, hz, rfl⟩
    apply reachable_lift _ _ _ (firstCopy hm) _ hz
    intro a v
    simpa only [fiber_firstCopy] using uniform_litOnlyMove m a (firstCopy hm v)

/-- The lit vertices are precisely a product of the base lit set and the copies. -/
def uniformLitEquiv (m : ℕ) (x : Configuration 7) :
    {v : Fin (7 * m) // uniformLift m x v = true} ≃
      {v : Fin 7 // x v = true} × Fin m where
  toFun v := (⟨fiberVertex v.1, v.2⟩, fiberCopy v.1)
  invFun p := ⟨finProdFinEquiv (p.1.1, p.2), by
    simpa [uniformLift, fiberVertex] using p.1.2⟩
  left_inv v := by
    apply Subtype.ext
    exact finProdFinEquiv.apply_symm_apply v.1
  right_inv p := by
    rcases p with ⟨⟨v, hv⟩, i⟩
    simp [fiberVertex, fiberCopy]

theorem uniform_weight (m : ℕ) (x : Configuration 7) :
    lightNumber (uniformLift m x) = lightNumber x * m := by
  have h := Fintype.card_congr (uniformLitEquiv m x)
  simpa [lightNumber, Fintype.card_prod, Fintype.card_subtype] using h

/-- The endpoint for the uniform start; no conclusion about other starts. -/
theorem blowup_regular_minimum (m : ℕ) (hm : 0 < m) :
    regularMinimum (blowup m) (uniformStart m) = 0 := by
  apply minimumLight_eq
  · refine ⟨uniformLift m (decode 0), ?_, ?_⟩
    · exact (regular_reachable_uniform hm start _).mpr ⟨decode 0, regular_path, rfl⟩
    · rw [uniform_weight]
      have hzero : lightNumber (decode 0) = 0 := by decide
      simp [hzero]
  · exact fun _ _ => Nat.zero_le _

theorem blowup_litOnly_minimum (m : ℕ) (hm : 0 < m) :
    litOnlyMinimum (blowup m) (uniformStart m) = 4 * m := by
  apply minimumLight_eq
  · refine ⟨uniformStart m, .refl, ?_⟩
    rw [uniformStart, uniform_weight, start_weight]
  · intro y hy
    obtain ⟨z, hz, rfl⟩ := (litOnly_reachable_uniform hm start y).mp hy
    rw [uniform_weight]
    exact Nat.mul_le_mul_right m (litOnly_lower hz)

theorem blowup_discrepancy_lower (m : ℕ) (hm : 0 < m) :
    4 * m ≤ discrepancy (blowup m) := by
  have h := Finset.le_sup
    (f := fun x => litOnlyMinimum (blowup m) x - regularMinimum (blowup m) x)
    (Finset.mem_univ (uniformStart m))
  simpa [discrepancy, blowup_litOnly_minimum m hm, blowup_regular_minimum m hm] using h

theorem blowup_exceeds_half (m : ℕ) (hm : 0 < m) :
    7 * m < 2 * discrepancy (blowup m) := by
  have h : 7 * m < 2 * (4 * m) := by omega
  exact h.trans_le (Nat.mul_le_mul_left 2 (blowup_discrepancy_lower m hm))

theorem blowup_undirected (m : ℕ) : Undirected (blowup m) := by
  intro u v
  exact graph_undirected (fiberVertex u) (fiberVertex v)

theorem blowup_loopless (m : ℕ) : ∀ v, blowup m v v = false := by
  intro v
  exact graph_loopless (fiberVertex v)

/-- Each fiber is independent, including different copies of one vertex. -/
theorem blowup_same_fiber (m : ℕ) (u v : Fin (7 * m))
    (h : fiberVertex u = fiberVertex v) : blowup m u v = false := by
  unfold blowup
  rw [h]
  exact graph_loopless _

/-- The obstruction has precisely the same induced adjacency as vertices 0,1,2. -/
theorem blowup_induced_copy {m : ℕ} (hm : 0 < m) (u v : Fin 7) :
    blowup m (firstCopy hm u) (firstCopy hm v) = graph u v := by
  simp [blowup, fiber_firstCopy]

theorem blowup_firstCopy_injective {m : ℕ} (hm : 0 < m) :
    Function.Injective (firstCopy hm) := by
  intro u v h
  have := congrArg fiberVertex h
  simpa only [fiber_firstCopy] using this

theorem blowup_not_completeMultipartite (m : ℕ) (hm : 0 < m) (parts : ℕ) :
    ¬ CompleteMultipartite (blowup m) parts := by
  rintro ⟨part, _, adj⟩
  let a := firstCopy hm (0 : Fin 7)
  let b := firstCopy hm (1 : Fin 7)
  let c := firstCopy hm (2 : Fin 7)
  have hab : blowup m a b = false := by
    change blowup m (firstCopy hm 0) (firstCopy hm 1) = false
    rw [blowup_induced_copy]
    decide
  have hbc : blowup m b c = false := by
    change blowup m (firstCopy hm 1) (firstCopy hm 2) = false
    rw [blowup_induced_copy]
    decide
  have hac : blowup m a c = true := by
    change blowup m (firstCopy hm 0) (firstCopy hm 2) = true
    rw [blowup_induced_copy]
    decide
  have hpab : part a = part b := by
    by_contra h
    exact Bool.false_ne_true (hab.symm.trans ((adj a b).mpr h))
  have hpbc : part b = part c := by
    by_contra h
    exact Bool.false_ne_true (hbc.symm.trans ((adj b c).mpr h))
  exact (adj a c).mp hac (hpab.trans hpbc)

/-- A finite ordered list of moves, with no bound on its length. -/
def playMoves {n : ℕ} (move : Configuration n → Fin n → Configuration n)
    (x : Configuration n) : List (Fin n) → Configuration n
  | [] => x
  | v :: vs => playMoves move (move x v) vs

/-- Strict lit-only legality: every played vertex is lit at that moment. -/
def legalMoves {n : ℕ} (G : Graph n) (x : Configuration n) : List (Fin n) → Prop
  | [] => True
  | v :: vs => x v = true ∧ legalMoves G (regularMove G x v) vs

theorem uniform_playMoves {m : ℕ}
    (move : Configuration 7 → Fin 7 → Configuration 7)
    (move' : Configuration (7 * m) → Fin (7 * m) → Configuration (7 * m))
    (commutes : ∀ x v, move' (uniformLift m x) v =
      uniformLift m (move x (fiberVertex v)))
    (x : Configuration 7) (vs : List (Fin (7 * m))) :
    playMoves move' (uniformLift m x) vs =
      uniformLift m (playMoves move x (vs.map fiberVertex)) := by
  induction vs generalizing x with
  | nil => rfl
  | cons v vs ih =>
    simp only [playMoves, List.map_cons, commutes, ih]

theorem uniform_regular_sequence (m : ℕ) (x : Configuration 7)
    (vs : List (Fin (7 * m))) :
    playMoves (regularMove (blowup m)) (uniformLift m x) vs =
      uniformLift m (playMoves (regularMove graph) x (vs.map fiberVertex)) :=
  uniform_playMoves _ _ (uniform_regularMove m) x vs

theorem uniform_litOnly_sequence (m : ℕ) (x : Configuration 7)
    (vs : List (Fin (7 * m))) :
    playMoves (litOnlyMove (blowup m)) (uniformLift m x) vs =
      uniformLift m (playMoves (litOnlyMove graph) x (vs.map fiberVertex)) :=
  uniform_playMoves _ _ (uniform_litOnlyMove m) x vs

theorem uniform_sequence_legality (m : ℕ) (x : Configuration 7)
    (vs : List (Fin (7 * m))) :
    legalMoves (blowup m) (uniformLift m x) vs ↔
      legalMoves graph x (vs.map fiberVertex) := by
  induction vs generalizing x with
  | nil => exact Iff.rfl
  | cons v vs ih =>
    simp only [legalMoves, List.map_cons, uniform_regularMove, uniformLift]
    exact and_congr Iff.rfl (ih _)

/-- A lifted base move list has exactly its original projection. -/
theorem firstCopy_sequence_projection {m : ℕ} (hm : 0 < m) (vs : List (Fin 7)) :
    (vs.map (firstCopy hm)).map fiberVertex = vs := by
  simp only [List.map_map]
  exact List.map_id'' (fun v => fiber_firstCopy hm v) vs

/-- Any chosen base sequence lifts, with its order and multiplicities retained. -/
theorem regular_sequence_lift {m : ℕ} (hm : 0 < m) (x : Configuration 7)
    (vs : List (Fin 7)) :
    playMoves (regularMove (blowup m)) (uniformLift m x) (vs.map (firstCopy hm)) =
      uniformLift m (playMoves (regularMove graph) x vs) := by
  rw [uniform_regular_sequence, firstCopy_sequence_projection]

theorem litOnly_sequence_lift {m : ℕ} (hm : 0 < m) (x : Configuration 7)
    (vs : List (Fin 7)) :
    playMoves (litOnlyMove (blowup m)) (uniformLift m x) (vs.map (firstCopy hm)) =
      uniformLift m (playMoves (litOnlyMove graph) x vs) := by
  rw [uniform_litOnly_sequence, firstCopy_sequence_projection]

theorem lifted_sequence_legality {m : ℕ} (hm : 0 < m) (x : Configuration 7)
    (vs : List (Fin 7)) :
    legalMoves (blowup m) (uniformLift m x) (vs.map (firstCopy hm)) ↔
      legalMoves graph x vs := by
  rw [uniform_sequence_legality, firstCopy_sequence_projection]

/-- The induced edge-plus-isolated-vertex obstruction to complete multipartiteness:
nonadjacency is not transitive on these three distinct vertices. -/
theorem blowup_preserved_obstruction (m : ℕ) (hm : 0 < m) :
    firstCopy hm (0 : Fin 7) ≠ firstCopy hm 1 ∧
    firstCopy hm (1 : Fin 7) ≠ firstCopy hm 2 ∧
    firstCopy hm (0 : Fin 7) ≠ firstCopy hm 2 ∧
    blowup m (firstCopy hm 0) (firstCopy hm 1) = false ∧
    blowup m (firstCopy hm 1) (firstCopy hm 2) = false ∧
    blowup m (firstCopy hm 0) (firstCopy hm 2) = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    exact (by decide : (0 : Fin 7) ≠ 1) (blowup_firstCopy_injective hm h)
  · intro h
    exact (by decide : (1 : Fin 7) ≠ 2) (blowup_firstCopy_injective hm h)
  · intro h
    exact (by decide : (0 : Fin 7) ≠ 2) (blowup_firstCopy_injective hm h)
  · rw [blowup_induced_copy]
    decide
  · rw [blowup_induced_copy]
    decide
  · rw [blowup_induced_copy]
    decide

theorem blowup_connected (m : ℕ) (hm : 0 < m) : Connected (blowup m) := by
  have cover : ∀ u : Fin 7, graph u 6 = true ∨ graph u 0 = true := by decide
  have hubEdge : blowup m (firstCopy hm 0) (firstCopy hm 6) = true := by
    rw [blowup_induced_copy]
    decide
  have toHub : ∀ u : Fin (7 * m), Relation.ReflTransGen
      (fun a b => blowup m a b = true) u (firstCopy hm 6) := by
    intro u
    rcases cover (fiberVertex u) with h | h
    · apply Relation.ReflTransGen.single
      simpa only [blowup, fiber_firstCopy] using h
    · have h' : blowup m u (firstCopy hm 0) = true := by
        simpa only [blowup, fiber_firstCopy] using h
      have hp : Relation.ReflTransGen (fun a b => blowup m a b = true)
          u (firstCopy hm 0) := .single h'
      exact hp.tail hubEdge
  have reverse : ∀ {u v : Fin (7 * m)}, Relation.ReflTransGen
      (fun a b => blowup m a b = true) u v → Relation.ReflTransGen
      (fun a b => blowup m a b = true) v u := by
    intro u v h
    induction h with
    | refl => exact .refl
    | @tail a b _ hab ih =>
      have hba : blowup m b a = true := by
        rw [blowup_undirected m b a]
        exact hab
      have hp : Relation.ReflTransGen (fun a b => blowup m a b = true) b a := .single hba
      exact hp.trans ih
  intro u v
  exact (toHub u).trans (reverse (toHub v))

/-- The all-positive-m endpoint with every hypothesis discharged. -/
theorem uniform_blowup : UniformBlowupStatement := by
  intro m hm
  exact ⟨blowup_undirected m, blowup_connected m hm, blowup_loopless m,
    blowup_regular_minimum m hm, blowup_litOnly_minimum m hm,
    blowup_discrepancy_lower m hm, blowup_exceeds_half m hm,
    blowup_not_completeMultipartite m hm⟩

end LitOnlySigma
