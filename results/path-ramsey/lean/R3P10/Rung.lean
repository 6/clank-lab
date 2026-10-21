import R3P10.Block

/-! # From a rung's UNSAT certificate to "every colouring has a monochromatic path"

Given that every 3-colouring of `K_n` has a monochromatic `P_k` (the rung
below, or nothing when `k = 0`), and that `encode n k` with every path
clause for `P_m` is unsatisfiable, every 3-colouring of `K_n` has a
monochromatic `P_m`. -/

namespace R3P10

variable {n : ℕ}

/-! ## The assignment of a colouring -/

/-- Auxiliary variables: in the block of `g` (variables `top+1 .. top + ns g N`),
the variable of position `k` means "`X` and `act g X` agree at every position `≤ k`". -/
def auxTrue (X : Col n) : List (Gen n) → ℕ → ℕ → Prop
  | [], _, _ => False
  | g :: gs, top, v =>
    if v ≤ top + ns g (edges n).length then
      ∃ k < (edges n).length, skip g k = false ∧ v = top + ns g k + 1 ∧
        ∀ k' ≤ k, vec X k' = vec (act g X) k'
    else auxTrue X gs (top + ns g (edges n).length) v

/-- The assignment of colouring `X`: `var k c` is true iff edge `k` has colour `c`;
auxiliaries carry their meaning. -/
def assign (gs : List (Gen n)) (X : Col n) (v : ℕ) : Prop :=
  if v ≤ 3 * (edges n).length then 1 ≤ v ∧ ((vec X ((v - 1) / 3) : Fin 3) : ℕ) = (v - 1) % 3
  else auxTrue X gs (3 * (edges n).length) v

theorem assign_var (gs : List (Gen n)) (X : Col n) {k : ℕ} (hk : k < (edges n).length)
    (c : Fin 3) : assign gs X (var k c) ↔ vec X k = c := by
  have hc := c.isLt
  unfold assign var
  rw [if_pos (by omega)]
  have h1 : (3 * k + ↑c + 1 - 1) / 3 = k := by omega
  have h2 : (3 * k + ↑c + 1 - 1) % 3 = c := by omega
  rw [h1, h2, Fin.ext_iff]
  omega

theorem cnfTrue_append (A : ℕ → Prop) (F G : CNF) :
    CNFTrue A (F ++ G) ↔ CNFTrue A F ∧ CNFTrue A G := by
  simp [CNFTrue, or_imp, forall_and]

theorem lexBlocks_ok (A : ℕ → Prop) (X : Col n)
    (hx : ∀ k < (edges n).length, ∀ c : Fin 3, A (var k c) ↔ vec X k = c) :
    ∀ (gs : List (Gen n)) (top : ℕ), (∀ v, top < v → (A v ↔ auxTrue X gs top v)) →
      (∀ g ∈ gs, toLex (vecF X) ≤ toLex (vecF (act g X))) → CNFTrue A (lexBlocks gs top) := by
  intro gs
  induction gs with
  | nil => intro _ _ _ C hC; simp [lexBlocks] at hC
  | cons g gs ih =>
    intro top haux hlex
    rw [lexBlocks, cnfTrue_append]
    constructor
    · refine block_ok g top A X hx (fun k hk hs => ?_) (hlex g (by simp))
      have hlt := ns_lt g hs hk
      rw [haux _ (by omega), auxTrue, if_pos (by omega)]
      constructor
      · rintro ⟨k1, _, hs1, hv, h⟩
        rw [ns_inj g hs1 hs (by omega)] at h
        exact h
      · intro h; exact ⟨k, hk, hs, rfl, h⟩
    · refine ih _ (fun v hv => ?_) (fun g' hg' => hlex g' (by simp [hg']))
      rw [haux v (by omega), auxTrue, if_neg (by omega)]

/-! ## The fixed path and the generators -/

/-- The path `0, 1, ..., k-1` has colour 0. -/
def FixedPath (n k : ℕ) (X : Col n) : Prop := ∀ t, t + 1 < k → colOf X t (t + 1) = 0

theorem exactlyOne_ok (A : ℕ → Prop) (X : Col n)
    (hx : ∀ k < (edges n).length, ∀ c : Fin 3, A (var k c) ↔ vec X k = c) :
    CNFTrue A (exactlyOne n) := by
  intro C hC
  simp only [exactlyOne, List.mem_flatMap, List.mem_range, List.mem_cons, List.mem_nil_iff,
    or_false] at hC
  obtain ⟨k, hk, hC⟩ := hC
  have h0 := hx k hk 0
  have h1 := hx k hk 1
  have h2 := hx k hk 2
  simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two] at h0 h1 h2
  rcases hC with h | h | h | h <;> subst h <;>
    simp only [clauseTrue_cons, clauseTrue_nil, or_false, litTrue_lit, litTrue_neg_lit, h0, h1, h2]
    <;> generalize vec X k = a <;> fin_cases a <;> simp

theorem fixUnits_ok (A : ℕ → Prop) (X : Col n) {k : ℕ} (hkn : k ≤ n)
    (hx : ∀ k < (edges n).length, ∀ c : Fin 3, A (var k c) ↔ vec X k = c)
    (hfix : FixedPath n k X) : CNFTrue A (fixUnits n k) := by
  intro C hC
  simp only [fixUnits, List.mem_map, List.mem_range] at hC
  obtain ⟨t, ht, rfl⟩ := hC
  rw [clauseTrue_cons, litTrue_lit]
  left
  have := hx _ (eidx_lt (u := t) (v := t + 1) (by omega) (by omega) (by omega)) 0
  simp only [Fin.isValue, Fin.val_zero] at this
  rw [this, vec_eidx X (by omega) (by omega) (by omega)]
  exact hfix t (by omega)

theorem encode_sat {k : ℕ} (hkn : k ≤ n) (X : Col n) (hfix : FixedPath n k X)
    (hlex : ∀ g ∈ gens n k, toLex (vecF X) ≤ toLex (vecF (act g X))) :
    CNFTrue (assign (gens n k) X) (encode n k) := by
  have hx := fun j (hj : j < (edges n).length) (c : Fin 3) => assign_var (gens n k) X hj c
  rw [encode, cnfTrue_append, cnfTrue_append]
  refine ⟨⟨exactlyOne_ok _ X hx, fixUnits_ok _ X hkn hx hfix⟩, ?_⟩
  refine lexBlocks_ok _ X hx _ _ (fun v hv => ?_) hlex
  rw [assign, if_neg (by omega)]

theorem paths_ok (gs : List (Gen n)) (X : Col n) {m : ℕ} (hX : ¬ HasMonoPath n m X) :
    ∀ C, IsPathClause n m C → ClauseTrue (assign gs X) C := by
  rintro C ⟨c, p, hinj, hmem⟩
  by_contra hC
  apply hX
  refine ⟨c, p, hinj, fun i h => ?_⟩
  have hne : (p ⟨i, by omega⟩).val ≠ (p ⟨i + 1, h⟩).val := fun e =>
    absurd (hinj (Fin.ext e)) (by simp)
  have hl := (hmem _).2 ⟨i, h, rfl⟩
  have : ¬ LitTrue (assign gs X) _ := fun h' => hC ⟨_, hl, h'⟩
  rw [litTrue_neg_nat _ (by simp [var]), not_not,
    assign_var gs X (eidx_lt hne (p _).isLt (p _).isLt), vec_eidx X hne (p _).isLt (p _).isLt]
    at this
  simpa [colOf] using this

theorem act_noMono (g : Gen n) {m : ℕ} {X : Col n} (hX : ¬ HasMonoPath n m X) :
    ¬ HasMonoPath n m (act g X) := by
  rintro ⟨c, p, hinj, hp⟩
  refine hX ⟨g.col.symm c, g.perm.symm ∘ p, g.perm.symm.injective.comp hinj, fun i h => ?_⟩
  have := hp i h
  simp only [act, Sym2.map_mk] at this
  simp [← this]

theorem gens_fix {k : ℕ} (hkn : k ≤ n) {g : Gen n} (hg : g ∈ gens n k) {X : Col n}
    (hX : FixedPath n k X) : FixedPath n k (act g X) := by
  intro t ht
  rw [colOf_act g X (by omega) (by omega)]
  have hk : k ≠ 0 := by omega
  simp only [gens, hk, if_false, List.mem_append, List.mem_flatMap, List.mem_finRange,
    List.mem_filterMap, true_and, List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with ⟨i, j, hij⟩ | rfl | rfl
  · split_ifs at hij with h
    simp only [Option.some.injEq] at hij
    subst hij
    have e1 : permN (Equiv.swap i j).symm t = t := by
      simp only [permN, dif_pos (show t < n by omega), Equiv.symm_swap]
      rw [Equiv.swap_apply_of_ne_of_ne] <;> (intro e; rw [Fin.ext_iff] at e; simp at e; omega)
    have e2 : permN (Equiv.swap i j).symm (t + 1) = t + 1 := by
      simp only [permN, dif_pos (show t + 1 < n by omega), Equiv.symm_swap]
      rw [Equiv.swap_apply_of_ne_of_ne] <;> (intro e; rw [Fin.ext_iff] at e; simp at e; omega)
    show (1 : Equiv.Perm (Fin 3)) (colOf X (permN (Equiv.swap i j).symm t)
      (permN (Equiv.swap i j).symm (t + 1))) = 0
    rw [e1, e2, hX t ht]; rfl
  · have e1 : ∀ a, a < k → permN (Function.Involutive.toPerm _ (revFun_invol n k)).symm a =
        k - 1 - a := by
      intro a ha
      simp only [permN, dif_pos (show a < n by omega), Function.Involutive.toPerm_symm,
        Function.Involutive.coe_toPerm, revFun, dif_pos (show a < k ∧ k ≤ n by omega)]
    rw [e1 t (by omega), e1 (t + 1) ht, colOf_comm]
    have := hX (k - 1 - (t + 1)) (by omega)
    rw [show k - 1 - (t + 1) + 1 = k - 1 - t by omega] at this
    simp [this]
  · have e : ∀ a, permN (1 : Equiv.Perm (Fin n)).symm a = a := fun a => by
      unfold permN; split_ifs <;> rfl
    show (Equiv.swap (1 : Fin 3) 2) (colOf X (permN (1 : Equiv.Perm (Fin n)).symm t)
      (permN (1 : Equiv.Perm (Fin n)).symm (t + 1))) = 0
    rw [e, e, hX t ht]; decide

/-! ## The orbit minimum -/

/-- Colourings reachable from `X` by generator moves. -/
inductive Reach (gs : List (Gen n)) (X : Col n) : Col n → Prop
  | refl : Reach gs X X
  | step {Y : Col n} (g : Gen n) : g ∈ gs → Reach gs X Y → Reach gs X (act g Y)

theorem reach_induct {gs : List (Gen n)} {X : Col n} (P : Col n → Prop)
    (hstep : ∀ g ∈ gs, ∀ Y, P Y → P (act g Y)) (hX : P X) {Y : Col n} (h : Reach gs X Y) :
    P Y := by
  induction h with
  | refl => exact hX
  | step g hg _ ih => exact hstep g hg _ ih

/-- The lex-least colouring reachable from `X` is `≤lex` its image under every generator. -/
theorem orbit_min (gs : List (Gen n)) (X : Col n) :
    ∃ y, Reach gs X y ∧ ∀ g ∈ gs, toLex (vecF y) ≤ toLex (vecF (act g y)) := by
  classical
  let S := Finset.univ.filter (Reach gs X)
  obtain ⟨y, hyS, hmin⟩ := S.exists_min_image (fun Y => toLex (vecF Y))
    ⟨X, by simp [S, Reach.refl]⟩
  have hy : Reach gs X y := by simpa [S] using hyS
  exact ⟨y, hy, fun g hg => hmin _ (by simpa [S] using Reach.step g hg hy)⟩

/-! ## Moving a monochromatic path to `0, ..., k-1` in colour 0 -/

theorem relabel {k : ℕ} (hkn : k ≤ n) {X : Col n} (hX : HasMonoPath n k X) :
    ∃ g : Gen n, FixedPath n k (act g X) := by
  classical
  obtain ⟨c, p, hinj, hp⟩ := hX
  let e : {x : Fin n // x.val < k} ≃ {x : Fin n // x ∈ Set.range p} :=
    { toFun := fun x => ⟨p ⟨x.1.val, x.2⟩, ⟨_, rfl⟩⟩
      invFun := fun y => ⟨⟨(Classical.choose y.2).val, by omega⟩, (Classical.choose y.2).isLt⟩
      left_inv := fun x => by
        have h := Classical.choose_spec (⟨⟨x.1.val, x.2⟩, rfl⟩ : p ⟨x.1.val, x.2⟩ ∈ Set.range p)
        ext; simp [hinj h]
      right_inv := fun y => by
        ext; simp [Classical.choose_spec y.2] }
  let ρ : Equiv.Perm (Fin n) := Equiv.extendSubtype e
  refine ⟨⟨ρ.symm, Equiv.swap c 0⟩, fun t ht => ?_⟩
  have hρ : ∀ a (ha : a < k), permN ρ a = (p ⟨a, ha⟩).val := by
    intro a ha
    simp only [permN, dif_pos (show a < n by omega)]
    rw [Equiv.extendSubtype_apply_of_mem e _ (show (⟨a, _⟩ : Fin n).val < k from ha)]
    rfl
  rw [colOf_act _ X (by omega) (by omega)]
  simp only [Equiv.symm_symm]
  rw [hρ t (by omega), hρ (t + 1) ht]
  have := hp t ht
  simp [colOf, this]

theorem mono_restrict {n' k : ℕ} (h : n' ≤ n) (hn' : ∀ X : Col n', HasMonoPath n' k X) :
    ∀ X : Col n, HasMonoPath n k X := by
  intro X
  obtain ⟨c, p, hinj, hp⟩ := hn' (fun z => X (Sym2.map (Fin.castLE h) z))
  exact ⟨c, Fin.castLE h ∘ p, (Fin.castLE_injective h).comp hinj, fun i hi => by simpa using hp i hi⟩

/-! ## One rung -/

theorem rung {m k : ℕ} (hkn : k ≤ n) (hprev : k = 0 ∨ ∀ X : Col n, HasMonoPath n k X)
    (hunsat : UnsatWithPaths n m (encode n k)) (X : Col n) : HasMonoPath n m X := by
  by_contra hX
  obtain ⟨Y, hYfix, hYfree⟩ : ∃ Y, FixedPath n k Y ∧ ¬ HasMonoPath n m Y := by
    rcases hprev with h0 | hall
    · exact ⟨X, fun t ht => by omega, hX⟩
    · obtain ⟨g, hg⟩ := relabel hkn (hall X)
      exact ⟨act g X, hg, act_noMono g hX⟩
  obtain ⟨y, hy, hmin⟩ := orbit_min (gens n k) Y
  have hP := reach_induct (fun Z => FixedPath n k Z ∧ ¬ HasMonoPath n m Z)
    (fun g hg Z hZ => ⟨gens_fix hkn hg hZ.1, act_noMono g hZ.2⟩) ⟨hYfix, hYfree⟩ hy
  exact hunsat _ (encode_sat hkn y hP.1 hmin) (paths_ok _ y hP.2)

/-! ## Cube and conquer -/

/-- The clause of a cube's negated literals. -/
def negCube (c : List Int) : Clause := c.map fun l => -l

/-- The unit clauses of a cube. -/
def cubeUnits (c : List Int) : CNF := c.map fun l => [l]

theorem litTrue_neg (A : ℕ → Prop) {l : Int} (hl : l ≠ 0) : LitTrue A (-l) ↔ ¬ LitTrue A l := by
  unfold LitTrue
  rcases lt_or_gt_of_ne hl with h | h
  · rw [if_pos (by omega), if_neg (by omega), Int.natAbs_neg, not_not]
  · rw [if_neg (by omega), if_pos h, Int.natAbs_neg]

/-- A cover refutation and one refutation per cube refute the formula. -/
theorem unsat_of_cubes {m : ℕ} {F : CNF} {cubes : List (List Int)}
    (hz : ∀ c ∈ cubes, ∀ l ∈ c, l ≠ 0)
    (hcover : UnsatWithPaths n m (F ++ cubes.map negCube))
    (hcubes : ∀ c ∈ cubes, UnsatWithPaths n m (F ++ cubeUnits c)) :
    UnsatWithPaths n m F := by
  intro A hF hP
  by_cases h : ∃ c ∈ cubes, ∀ l ∈ c, LitTrue A l
  · obtain ⟨c, hc, hl⟩ := h
    refine hcubes c hc A ?_ hP
    rw [cnfTrue_append]
    refine ⟨hF, fun C hC => ?_⟩
    simp only [cubeUnits, List.mem_map] at hC
    obtain ⟨l, hl', rfl⟩ := hC
    exact ⟨l, by simp, hl l hl'⟩
  · push Not at h
    refine hcover A ?_ hP
    rw [cnfTrue_append]
    refine ⟨hF, fun C hC => ?_⟩
    simp only [List.mem_map] at hC
    obtain ⟨c, hc, rfl⟩ := hC
    obtain ⟨l, hl, hnl⟩ := h c hc
    exact ⟨-l, by simp [negCube, hl], (litTrue_neg A (hz c hc l hl)).2 hnl⟩

end R3P10
