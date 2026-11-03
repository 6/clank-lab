import CD13.Trace

/-!
Two-letter reconstruction from prior-neighbor event counts.
This is a combinatorial supporting lemma; the
constructor model must still prove that its final terms recover these counts.
-/
namespace CD13.PairRecovery

/-- The second letter is true; the sampled first letter is false. -/
def totalB : List Bool → Nat
  | [] => 0
  | false :: w => totalB w
  | true :: w => totalB w + 1

/-- For each false event, record the number of preceding true events. -/
def reads : List Bool → List Nat
  | [] => []
  | false :: w => 0 :: reads w
  | true :: w => (reads w).map Nat.succ

/-- Fixed binary reconstruction statement before proof lemmas. -/
def BinaryEndpoint : Prop :=
  ∀ u v : List Bool, totalB u = totalB v → reads u = reads v → u = v

 theorem binary_reconstruct (u v : List Bool)
    (hc : totalB u = totalB v) (hr : reads u = reads v) : u = v := by
  induction u generalizing v with
  | nil =>
      cases v with
      | nil => rfl
      | cons b v =>
          cases b
          · simp [reads] at hr
          · simp [totalB] at hc
  | cons a u ih =>
      cases v with
      | nil =>
          cases a
          · simp [reads] at hr
          · simp [totalB] at hc
      | cons b v =>
          cases a <;> cases b
          · simp only [totalB, reads, List.cons.injEq] at hc hr
            exact congrArg (List.cons false) (ih v hc hr.2)
          · simp only [reads] at hr
            obtain ⟨n, ns, _, hn, _⟩ := List.map_eq_cons_iff.mp hr.symm
            omega
          · simp only [reads] at hr
            obtain ⟨n, ns, _, hn, _⟩ := List.map_eq_cons_iff.mp hr
            omega
          · simp only [totalB, reads] at hc hr
            have hc' : totalB u = totalB v := Nat.add_right_cancel hc
            have hr' : reads u = reads v := (List.map_inj_right (fun _ _ h => Nat.succ.inj h)).mp hr
            exact congrArg (List.cons true) (ih v hc' hr')

 theorem binaryEndpoint : BinaryEndpoint := binary_reconstruct

variable {V : Type u} [DecidableEq V]

/-- Project to the two letters and label them false and true respectively. -/
def pairWord (a b : V) : List V → List Bool
  | [] => []
  | c :: w => if c = a then false :: pairWord a b w
      else if c = b then true :: pairWord a b w else pairWord a b w

/-- Direct recurrence for the earlier b-count sampled at each a-event. -/
def samples (a b : V) : List V → List Nat
  | [] => []
  | c :: w => if c = a then 0 :: samples a b w
      else if c = b then (samples a b w).map Nat.succ else samples a b w

 theorem pairWord_reads (a b : V) (w : List V) :
    reads (pairWord a b w) = samples a b w := by
  induction w with
  | nil => rfl
  | cons c w ih =>
      by_cases ha : c = a
      · simp only [pairWord, samples, ite_eq_left ha, reads, ih]
      · by_cases hb : c = b
        · simp only [pairWord, samples, ite_eq_right ha, ite_eq_left hb, reads, ih]
        · simp only [pairWord, samples, ite_eq_right ha, ite_eq_right hb, ih]

 theorem pairWord_decode (a b : V) (w : List V) :
    (pairWord a b w).map (fun x => if x then b else a) = Trace.projection a b w := by
  induction w with
  | nil => rfl
  | cons c w ih =>
      by_cases ha : c = a
      · simp only [pairWord, ite_eq_left ha, List.map_cons]
        rw [ih, Trace.projection_cons]
        simp [ha]
      · by_cases hb : c = b
        · simp only [pairWord, ite_eq_right ha, ite_eq_left hb, List.map_cons]
          rw [ih, Trace.projection_cons]
          simp [hb]
        · simp only [pairWord, ite_eq_right ha, ite_eq_right hb]
          rw [ih, Trace.projection_cons]
          simp [ha, hb]

 theorem pairWord_total (a b : V) (hab : a ≠ b) (w : List V) :
    totalB (pairWord a b w) = (Trace.projection b b w).length := by
  induction w with
  | nil => rfl
  | cons c w ih =>
      by_cases ha : c = a
      · subst c
        simp [pairWord, totalB, Trace.projection, hab, ih]
      · by_cases hb : c = b
        · simp only [pairWord, ite_eq_right ha, ite_eq_left hb, totalB, ih]
          rw [Trace.projection_cons]
          simp [hb]
        · simp only [pairWord, ite_eq_right ha, ite_eq_right hb, ih]
          rw [Trace.projection_cons]
          simp [hb]

/-- Appending an a-event records exactly the preceding number of b-events;
other appended letters leave all previous observations unchanged. -/
 theorem samples_snoc (a b : V) (hab : a ≠ b) (w : List V) (c : V) :
    samples a b (w ++ [c]) =
      if c = a then samples a b w ++ [(Trace.projection b b w).length]
      else samples a b w := by
  induction w with
  | nil =>
      by_cases hc : c = a <;> simp [samples, hc, Trace.projection]
  | cons d w ih =>
      by_cases hd : d = a
      · subst d
        by_cases hc : c = a
        · subst c
          simp [samples, hab, ih, Trace.projection]
        · simp [samples, hc, ih]
      · by_cases he : d = b
        · subst d
          by_cases hc : c = a
          · subst c
            simp [samples, hd, ih, Trace.projection, List.map_append]
          · simp [samples, hd, hc, ih]
        · by_cases hc : c = a
          · subst c
            simp [samples, hd, he, ih, Trace.projection]
          · simp [samples, hd, he, hc, ih]

 theorem projection_reconstruct (a b : V) (hab : a ≠ b) (u v : List V)
    (hc : (Trace.projection b b u).length = (Trace.projection b b v).length)
    (hr : samples a b u = samples a b v) :
    Trace.projection a b u = Trace.projection a b v := by
  have hp : pairWord a b u = pairWord a b v := binary_reconstruct _ _
    (by simpa only [pairWord_total a b hab] using hc)
    (by simpa only [pairWord_reads] using hr)
  simpa only [pairWord_decode] using
    congrArg (List.map (fun x => if x then b else a)) hp

end CD13.PairRecovery
