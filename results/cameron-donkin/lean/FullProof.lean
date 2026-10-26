import Assembly

namespace Donkin

/-- For each finite length, an increasing tail with the exact local hypotheses. -/
theorem tail_exists (m : ℕ) :
    ∃ q : Fin m → ℕ, (∀ i, (q i).Prime) ∧ StrictMono q ∧
      (∀ i, m + 2 < q i) ∧
      (∀ ell : ℕ, ell.Prime → ell ≤ m + 2 → ∀ i, (q i : ZMod ell) = 1) := by
  classical
  let Q : ℕ → ℕ := Nat.rec (Classical.choose (auxiliary_prime (m+2) (m+2)))
    (fun _ prev => Classical.choose (auxiliary_prime (m+2) prev))
  have hzero : m+2 < Q 0 ∧ (Q 0).Prime ∧
      ∀ ell : ℕ, ell.Prime → ell ≤ m+2 → (Nat.cast (Q 0) : ZMod ell) = 1 := by
    exact Classical.choose_spec (auxiliary_prime (m+2) (m+2))
  have hsucc (k : ℕ) : Q k < Q (k+1) ∧ (Q (k+1)).Prime ∧
      ∀ ell : ℕ, ell.Prime → ell ≤ m+2 → (Nat.cast (Q (k+1)) : ZMod ell) = 1 := by
    exact Classical.choose_spec (auxiliary_prime (m+2) (Q k))
  have hQ (k : ℕ) : m+2 < Q k ∧ (Q k).Prime ∧
      ∀ ell : ℕ, ell.Prime → ell ≤ m+2 → (Nat.cast (Q k) : ZMod ell) = 1 := by
    induction k with
    | zero => exact hzero
    | succ k ih =>
      exact ⟨lt_trans ih.1 (hsucc k).1, (hsucc k).2⟩
  have hmono : StrictMono Q := strictMono_nat_of_lt_succ (fun k => (hsucc k).1)
  refine ⟨fun i => Q i.val, fun i => (hQ i.val).2.1, ?_,
    fun i => (hQ i.val).1, ?_⟩
  · intro i j hij
    exact hmono hij
  · intro ell hell hle i
    exact (hQ i.val).2.2 ell hell hle

/-- The unchanged, source-faithful arbitrary finite avoidance endpoint. -/
theorem arbitraryDelay : Donkin.ArbitraryDelay := by
  intro n hn
  obtain ⟨q,hq,hmono,hbig,hsmall⟩ := tail_exists n
  obtain ⟨p,hp3,hpp,hfirst,htail⟩ := finite_lift q hq hmono hbig hsmall
  refine ⟨p,hpp,?_⟩
  intro j hj
  cases j with
  | zero =>
    change p ≠ 3
    omega
  | succ j =>
    cases j with
    | zero =>
      rw [hfirst]
      decide
    | succ k =>
      have hk : k < n := by omega
      have heq : term p (k+1+1) = q ⟨k,hk⟩ := by
        simpa only [Nat.add_assoc] using htail ⟨k,hk⟩
      rw [heq]
      have := hbig ⟨k,hk⟩
      omega

#print axioms Donkin.tail_exists
#print axioms Donkin.arbitraryDelay
end Donkin
