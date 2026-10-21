import R3P10.Rung
import Std.Tactic.BVDecide.LRAT.Checker

/-! # Checking `UnsatWithPaths` with Lean's verified LRAT checker

`checkUnsat n m F paths proof` is a Boolean test that, when it returns
`true`, proves `UnsatWithPaths n m F` (`checkUnsat_sound`). It

* checks every literal of `F` is nonzero;
* checks each path `(c, p)` of `paths` is a colour `c < 3` and `m`
  distinct vertices below `n`, so its clause `pclause n c p` is a path
  clause (`isPathClause_pclause`);
* runs the LRAT checker that ships with Lean (`Std.Tactic.BVDecide.LRAT.check`,
  proved sound by `Std.Tactic.BVDecide.LRAT.check_sound`; it backs
  `bv_decide`) on `F` followed by the path clauses.

Only the Boolean's value matters: how `paths` and `proof` were produced
(the solver, drat-trim, our converter, the decoder in `R3P10/Cert.lean`)
is outside the trusted base. -/

namespace R3P10

open Std.Sat Std.Tactic.BVDecide

/-! ## DIMACS literals as `Std.Sat` literals -/

/-- DIMACS literal `l` (nonzero) is variable `|l| - 1` with polarity `l > 0`. -/
def toLit (l : Int) : Literal Nat := (l.natAbs - 1, decide (0 < l))

def toStd (F : CNF) : Std.Sat.CNF Nat := ⟨(F.map fun C => C.map toLit).toArray⟩

open Classical in
theorem toStd_eval (A : ℕ → Prop) (F : CNF) (hz : ∀ C ∈ F, ∀ l ∈ C, l ≠ 0)
    (h : CNFTrue A F) : (toStd F).eval (fun v => decide (A (v + 1))) = true := by
  simp only [toStd, Std.Sat.CNF.eval, List.all_toArray, List.all_map, List.all_eq_true,
    Function.comp_apply]
  intro C hC
  obtain ⟨l, hl, hlt⟩ := h C hC
  have hl0 := hz C hC l hl
  simp only [Std.Sat.CNF.Clause.eval, List.any_map, List.any_eq_true, Function.comp_apply]
  refine ⟨l, hl, ?_⟩
  unfold LitTrue at hlt
  unfold toLit
  have h1 : l.natAbs - 1 + 1 = l.natAbs := by omega
  split_ifs at hlt with hp
  · simp [h1, hp, hlt]
  · simp [h1, hp, hlt]

/-! ## Path clauses from paths -/

/-- Edge indices of `K_n` as a table: entry `u * n + v` is `eidx n u v`. -/
def eTab (n : ℕ) : Array ℕ := ((List.range (n * n)).map fun k => eidx n (k / n) (k % n)).toArray

theorem eTab_get {n u v : ℕ} (hu : u < n) (hv : v < n) : (eTab n)[u * n + v]! = eidx n u v := by
  have hk : u * n + v < n * n :=
    calc u * n + v < u * n + n := by omega
      _ = (u + 1) * n := by rw [Nat.succ_mul]
      _ ≤ n * n := Nat.mul_le_mul_right _ hu
  have h1 : (u * n + v) / n = u := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hv, Nat.zero_add]
  have h2 : (u * n + v) % n = v := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hv]
  simp [eTab, getElem!_pos, hk, h1, h2]

/-- The clause "not every edge `{p i, p (i+1)}` has colour `c`", with the
edge table `t` (`eTab n`) passed in so that it is built once per check. -/
def pclauseT (t : Array ℕ) (n c : ℕ) (p : List ℕ) : Clause :=
  (List.range (p.length - 1)).map fun i => -((3 * t[p[i]! * n + p[i + 1]!]! + c + 1 : ℕ) : Int)

def pclause (n c : ℕ) (p : List ℕ) : Clause := pclauseT (eTab n) n c p

/-- A colour and `m` distinct vertices of `K_n`. -/
def pvalid (n m c : ℕ) (p : List ℕ) : Bool := c < 3 && p.length == m && p.all (· < n) && p.Nodup

theorem isPathClause_pclause {n m c : ℕ} {p : List ℕ} (h : pvalid n m c p = true) :
    IsPathClause n m (pclause n c p) := by
  simp only [pvalid, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨hc, hlen⟩, hlt⟩, hnd⟩ := h
  subst hlen
  have hv : ∀ i (hi : i < p.length), p[i] < n := fun i hi => hlt _ (List.getElem_mem hi)
  refine ⟨⟨c, hc⟩, fun i => ⟨p[i.val], hv _ i.isLt⟩, ?_, ?_⟩
  · intro i j hij
    simp only [Fin.mk.injEq] at hij
    exact Fin.ext ((List.Nodup.getElem_inj_iff hnd).1 hij)
  · intro l
    simp only [pclause, pclauseT, List.mem_map, List.mem_range]
    constructor
    · rintro ⟨i, hi, rfl⟩
      refine ⟨i, by omega, ?_⟩
      rw [getElem!_pos p i (by omega), getElem!_pos p (i + 1) (by omega),
        eTab_get (hv _ _) (hv _ _)]
      rfl
    · rintro ⟨i, hi, rfl⟩
      refine ⟨i, by omega, ?_⟩
      rw [getElem!_pos p i (by omega), getElem!_pos p (i + 1) (by omega),
        eTab_get (hv _ _) (hv _ _)]
      rfl

/-! ## The check and its soundness -/

/-- `F` followed by the path clauses of `paths` is refuted by `proof`, every
literal of `F` is nonzero and every path is valid. -/
def checkUnsat (n m : ℕ) (F : CNF) (paths : Array (ℕ × List ℕ)) (proof : Array LRAT.IntAction) : Bool :=
  let t := eTab n
  F.all (fun C => C.all (· != 0)) && paths.all (fun x => pvalid n m x.1 x.2) &&
    LRAT.check proof (toStd (F ++ (paths.toList.map fun x => pclauseT t n x.1 x.2)))

theorem checkUnsat_sound {n m : ℕ} {F : CNF} {paths : Array (ℕ × List ℕ)}
    {proof : Array LRAT.IntAction} (h : checkUnsat n m F paths proof = true) :
    UnsatWithPaths n m F := by
  simp only [checkUnsat, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq,
    Array.all_eq_true_iff_forall_mem] at h
  obtain ⟨⟨hz, hp⟩, hc⟩ := h
  intro A hF hP
  have hpaths : CNFTrue A (paths.toList.map fun x => pclause n x.1 x.2) := by
    intro C hC
    simp only [List.mem_map] at hC
    obtain ⟨x, hx, rfl⟩ := hC
    exact hP _ (isPathClause_pclause (hp x (Array.mem_toList_iff.1 hx)))
  have hz' : ∀ C ∈ F ++ (paths.toList.map fun x => pclause n x.1 x.2), ∀ l ∈ C, l ≠ 0 := by
    intro C hC l hl
    rcases List.mem_append.1 hC with hC | hC
    · exact hz C hC l hl
    · simp only [List.mem_map] at hC
      obtain ⟨x, _, rfl⟩ := hC
      simp only [pclause, pclauseT, List.mem_map] at hl
      obtain ⟨i, _, rfl⟩ := hl
      omega
  have hev := toStd_eval A _ hz' ((cnfTrue_append A _ _).2 ⟨hF, hpaths⟩)
  have hun := LRAT.check_sound proof _ hc
  simp only [pclause] at hev
  rw [hun] at hev
  exact Bool.false_ne_true hev

end R3P10
