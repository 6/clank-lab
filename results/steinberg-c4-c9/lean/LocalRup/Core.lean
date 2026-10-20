import Std.Sat.CNF

namespace LocalRup

abbrev Lit := Nat × Bool
abbrev Clause := List Lit
abbrev Formula := List Clause
abbrev Assignment := Nat → Bool
abbrev Known := List (Nat × Clause)

def litSat (a : Assignment) (l : Lit) : Prop := a l.1 = l.2
def neg (l : Lit) : Lit := (l.1, !l.2)
def sat (a : Assignment) (c : Clause) : Prop := c.any (fun l => a l.1 == l.2) = true
def models (a : Assignment) (f : Formula) : Prop := f.all (fun c => c.any (fun l => a l.1 == l.2)) = true
def Entails (f : Formula) (c : Clause) : Prop := ∀ a, models a f → sat a c
def Unsat (f : Formula) : Prop := ∀ a, ¬models a f
def Good (f : Formula) (known : Known) : Prop := ∀ e ∈ known, Entails f e.2

theorem sat_iff (a : Assignment) (c : Clause) :
    sat a c ↔ ∃ l ∈ c, litSat a l := by
  simp [sat, litSat, List.any_eq_true, beq_iff_eq]

theorem litSat_neg (a : Assignment) (l : Lit) : litSat a (neg l) ↔ ¬litSat a l := by
  rcases l with ⟨v, b⟩
  cases b <;> cases h : a v <;> simp [litSat, neg, h]

def residual (ass : List Lit) (c : Clause) : Clause :=
  c.filter (fun l => !(ass.contains (neg l)))

def propagate (ass : List Lit) : List Clause → Bool
  | [] => false
  | c :: rest =>
    match residual ass c with
    | [] => true
    | [u] => propagate (u :: ass) rest
    | _ => false

def rup (c : Clause) (hints : List Clause) : Bool := propagate (c.map neg) hints

theorem residual_sat (a : Assignment) (ass : List Lit) (c : Clause)
    (ha : ∀ l ∈ ass, litSat a l) (hc : sat a c) : sat a (residual ass c) := by
  obtain ⟨l, hl, hs⟩ := (sat_iff a c).mp hc
  apply (sat_iff a _).mpr
  refine ⟨l, ?_, hs⟩
  have hn : neg l ∉ ass := fun hn => (litSat_neg a l).mp (ha _ hn) hs
  simpa [residual, List.mem_filter, List.contains_eq_mem] using And.intro hl hn

theorem propagate_sound (hints : List Clause) (ass : List Lit)
    (h : propagate ass hints = true) (a : Assignment)
    (ha : ∀ l ∈ ass, litSat a l) (hh : ∀ c ∈ hints, sat a c) : False := by
  induction hints generalizing ass with
  | nil => simp [propagate] at h
  | cons c rest ih =>
    have hs := residual_sat a ass c ha (hh c (by simp))
    cases hr : residual ass c with
    | nil => simpa [hr, sat] using hs
    | cons u us =>
      cases us with
      | nil =>
        have hu : litSat a u := by simpa [hr, sat_iff] using hs
        apply ih (u :: ass) (by simpa [propagate, hr] using h)
        · intro l hl
          rcases List.mem_cons.mp hl with rfl | hl
          · exact hu
          · exact ha l hl
        · intro d hd
          exact hh d (by simp [hd])
      | cons v vs => simp [propagate, hr] at h

theorem rup_sound (c : Clause) (hints : List Clause) (h : rup c hints = true)
    (a : Assignment) (hh : ∀ d ∈ hints, sat a d) : sat a c := by
  apply Classical.byContradiction
  intro hn
  apply propagate_sound hints (c.map neg) h a ?_ hh
  intro l hl
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hl
  apply (litSat_neg a u).mpr
  intro hs
  exact hn ((sat_iff a c).mpr ⟨u, hu, hs⟩)

def initialFrom (start : Nat) : Formula → Known
  | [] => []
  | c :: cs => (start, c) :: initialFrom (start + 1) cs

def initial (f : Formula) : Known := initialFrom 1 f

theorem initial_mem (start : Nat) (f : Formula) :
    ∀ e ∈ initialFrom start f, e.2 ∈ f := by
  induction f generalizing start with
  | nil => simp [initialFrom]
  | cons c cs ih =>
    intro e he
    simp only [initialFrom, List.mem_cons] at he
    rcases he with rfl | he
    · simp
    · exact List.mem_cons_of_mem c (ih _ e he)

theorem initial_good (f : Formula) : Good f (initial f) := by
  intro e he a ha
  exact List.all_eq_true.mp ha e.2 (initial_mem 1 f e he)

def lookup (known : Known) (id : Nat) : Option Clause :=
  match known with
  | [] => none
  | (key, c) :: rest => if key == id then some c else lookup rest id

theorem lookup_mem (known : Known) (id : Nat) (c : Clause)
    (h : lookup known id = some c) : (id, c) ∈ known := by
  induction known with
  | nil => simp [lookup] at h
  | cons e rest ih =>
    rcases e with ⟨key, d⟩
    simp only [lookup] at h
    split at h
    next eq =>
      have hk : key = id := by simpa using eq
      have hc : d = c := Option.some.inj h
      subst key
      subst d
      simp
    next ne => exact List.mem_cons_of_mem _ (ih h)

def resolve (known : Known) : List Nat → Option (List Clause)
  | [] => some []
  | id :: rest => do return (← lookup known id) :: (← resolve known rest)

theorem resolve_good (f : Formula) (known : Known) (good : Good f known)
    (ids : List Nat) (cs : List Clause) (h : resolve known ids = some cs) :
    ∀ c ∈ cs, Entails f c := by
  induction ids generalizing cs with
  | nil =>
    have hc : [] = cs := by simpa [resolve] using h
    subst cs
    simp
  | cons id rest ih =>
    cases hl : lookup known id with
    | none => simp [resolve, hl] at h
    | some c =>
      cases hr : resolve known rest with
      | none => simp [resolve, hl, hr] at h
      | some tail =>
        have eq : c :: tail = cs := by simpa [resolve, hl, hr] using h
        subst cs
        intro d hd
        rcases List.mem_cons.mp hd with eq | hd
        · subst d
          exact good (id, c) (lookup_mem known id c hl)
        · exact ih tail hr d hd

inductive Step where
  | add (id : Nat) (clause : Clause) (hints : List Nat)
  | del (anchor : Nat) (ids : List Nat)
deriving DecidableEq

def stepCheck (known : Known) : Step → Bool
  | .add _ c hints => match resolve known hints with
    | none => false
    | some cs => rup c cs
  | .del .. => true

/-- Deletions are logically ignored; retained entries are already proved. -/
def next (known : Known) : Step → Known
  | .add id c _ => (id, c) :: known
  | .del .. => known

theorem checked_good (f : Formula) (known : Known) (step : Step)
    (good : Good f known) (h : stepCheck known step = true) : Good f (next known step) := by
  cases step with
  | del anchor ids => exact good
  | add id c hints =>
    cases hr : resolve known hints with
    | none => simp [stepCheck, hr] at h
    | some cs =>
      have hc : Entails f c := by
        intro a ha
        apply rup_sound c cs (by simpa [stepCheck, hr] using h) a
        intro d hd
        exact resolve_good f known good hints cs hr d hd a ha
      intro e he
      rcases List.mem_cons.mp he with rfl | he
      · exact hc
      · exact good e he

def AllChecked (known : Known) : List Step → Prop
  | [] => True
  | s :: rest => stepCheck known s = true ∧ AllChecked (next known s) rest

def runChecks (known : Known) : List Step → Bool
  | [] => true
  | s :: rest => stepCheck known s && runChecks (next known s) rest

def after (known : Known) (steps : List Step) : Known := steps.foldl next known

theorem checked_preserves (f : Formula) (known : Known) (steps : List Step)
    (good : Good f known) (checks : AllChecked known steps) : Good f (after known steps) := by
  induction steps generalizing known with
  | nil => exact good
  | cons s rest ih => exact ih (next known s) (checked_good f known s good checks.1) checks.2

theorem checked_append (known : Known) (xs ys : List Step)
    (hx : AllChecked known xs) (hy : AllChecked (after known xs) ys) :
    AllChecked known (xs ++ ys) := by
  induction xs generalizing known with
  | nil => exact hy
  | cons s rest ih => exact ⟨hx.1, ih (next known s) hx.2 hy⟩

theorem runChecks_eq (known : Known) (steps : List Step) :
    runChecks known steps = true ↔ AllChecked known steps := by
  induction steps generalizing known with
  | nil => simp [runChecks, AllChecked]
  | cons s rest ih => simp [runChecks, AllChecked, ih]

def endsEmpty : List Step → Bool
  | [] => false
  | [.add _ c _] => c.isEmpty
  | [.del ..] => false
  | _ :: rest => endsEmpty rest

def checkFrom (known : Known) (steps : List Step) : Bool :=
  endsEmpty steps && runChecks known steps

theorem refutation_sound (f : Formula) (known : Known) (steps : List Step)
    (good : Good f known) (checks : AllChecked known steps)
    (last : endsEmpty steps = true) : Unsat f := by
  induction steps generalizing known with
  | nil => simp [endsEmpty] at last
  | cons s rest ih =>
    have good' := checked_good f known s good checks.1
    cases rest with
    | nil =>
      cases s with
      | del anchor ids => simp [endsEmpty] at last
      | add id c hints =>
        have hc : c = [] := by simpa [endsEmpty] using last
        subst c
        intro a ha
        have impossible := good' (id, []) (by simp [next]) a ha
        simpa [sat] using impossible
    | cons t tail => exact ih (next known s) good' checks.2 (by simpa only [endsEmpty] using last)

theorem checkFrom_sound (f : Formula) (known : Known) (steps : List Step)
    (good : Good f known) (h : checkFrom known steps = true) : Unsat f := by
  simp only [checkFrom, Bool.and_eq_true] at h
  exact refutation_sound f known steps good ((runChecks_eq known steps).mp h.2) h.1

theorem toStd_unsat (f : Formula) (h : Unsat f) : (Std.Sat.CNF.mk f.toArray).Unsat := by
  intro a
  apply Bool.eq_false_of_ne_true
  intro ha
  apply h a
  simpa [models, Std.Sat.CNF.eval, Std.Sat.CNF.Clause.eval] using ha

end LocalRup
