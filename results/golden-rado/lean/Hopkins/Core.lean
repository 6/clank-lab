import Hopkins.Definitions

namespace Hopkins

theorem bool_opposite {u v : Bool} (h : u ≠ v) : u = !v := by
  cases u <;> cases v <;> simp_all

theorem output_color {a b N x y z : ℕ} {c : ℕ → Bool} {d : Bool}
    (hn : ¬ Mono a b N c)
    (hx : 1 ≤ x) (hxN : x ≤ N) (hy : 1 ≤ y) (hyN : y ≤ N)
    (hz : 1 ≤ z) (hzN : z ≤ N) (he : a*x+b*y=z)
    (hcx : c x = d) (hcy : c y = d) : c z = !d := by
  apply bool_opposite
  intro hcz
  exact hn ⟨x,y,z,hx,hxN,hy,hyN,hz,hzN,he,hcx.trans hcy.symm,hcy.trans hcz.symm⟩

theorem input_color {a b N x y z : ℕ} {c : ℕ → Bool} {d : Bool}
    (hn : ¬ Mono a b N c)
    (hx : 1 ≤ x) (hxN : x ≤ N) (hy : 1 ≤ y) (hyN : y ≤ N)
    (hz : 1 ≤ z) (hzN : z ≤ N) (he : a*x+b*y=z)
    (hcy : c y = d) (hcz : c z = d) : c x = !d := by
  apply bool_opposite
  intro hcx
  exact hn ⟨x,y,z,hx,hxN,hy,hyN,hz,hzN,he,hcx.trans hcy.symm,hcy.trans hcz.symm⟩

theorem next_zero {N t : ℕ} {c : ℕ → Bool} (hv : Valid N c)
    (ht : 1 ≤ t) (htN : t+1 ≤ N) (hc : c t = true) : c (t+1) = false := by
  cases h : c (t+1) with
  | false => rfl
  | true => exact False.elim (hv.2 t ht htN ⟨hc,h⟩)

theorem previous_zero {N t : ℕ} {c : ℕ → Bool} (hv : Valid N c)
    (ht : 1 ≤ t) (htN : t+1 ≤ N) (hc : c (t+1) = true) : c t = false := by
  cases h : c t with
  | false => rfl
  | true => exact False.elim (hv.2 t ht htN ⟨h,hc⟩)

def positiveRemainder (a ell : ℕ) : ℕ := (a-1)%ell+1

theorem remainder_bounds (a ell : ℕ) (ha : 1 ≤ a) (hell : 1 ≤ ell) :
    1 ≤ positiveRemainder a ell ∧ positiveRemainder a ell ≤ ell ∧
    positiveRemainder a ell ≤ a := by
  have h1 := Nat.mod_lt (a-1) (by omega : 0 < ell)
  have h2 := Nat.mod_le (a-1) ell
  unfold positiveRemainder
  omega

theorem remainder_representation (a ell : ℕ) (ha : 1 ≤ a) :
    a*(ell+1) = positiveRemainder a ell + (a+(a-1)/ell)*ell := by
  have h := Nat.mod_add_div (a-1) ell
  have hsub : a-1+1=a := by omega
  unfold positiveRemainder
  nlinarith

theorem initial_residue (a ell : ℕ) (ha : 1 ≤ a) (hell : 1 ≤ ell)
    (c : ℕ → Bool) (hv : Valid ((a*(ell+1))^2) c)
    (hn : ¬ Mono a (a*ell) ((a*(ell+1))^2) c) :
    c (positiveRemainder a ell) = true := by
  let s := a*(ell+1)
  change Valid (s^2) c at hv
  change ¬ Mono a (a*ell) (s^2) c at hn
  have hs : 2 ≤ s := by dsimp [s]; nlinarith
  have hsN : s ≤ s^2 := by nlinarith
  have hs1N : s+1 ≤ s^2 := by nlinarith
  have start : c s = true := by
    exact output_color hn (by omega) (by nlinarith) (by omega) (by nlinarith)
      (by omega) hsN (by dsimp [s]; ring) hv.1 hv.1
  have step (u : ℕ) (hu : 1 ≤ u) (huS : u+ell ≤ s)
      (hc : c (u+ell) = true) : c u = true := by
    have ht : 1 ≤ u+ell := by omega
    have htN : u+ell ≤ s^2 := le_trans huS hsN
    have hprod : s*(u+ell) ≤ s^2 := by nlinarith
    have hprodpos : 1 ≤ s*(u+ell) := by nlinarith
    have hz : c (s*(u+ell)) = false := by
      exact output_color hn ht htN ht htN hprodpos hprod
        (by dsimp [s]; ring) hc hc
    have hnext : c (u+ell+1) = false :=
      next_zero hv ht (by omega) hc
    exact input_color hn hu (by omega) (by omega) (by omega)
      hprodpos hprod (by dsimp [s]; ring) hnext hz
  have descent : ∀ k t : ℕ, 1 ≤ t → t+k*ell ≤ s →
      c (t+k*ell) = true → c t = true := by
    intro k
    induction k with
    | zero => intro t ht hb hc; simpa using hc
    | succ k ih =>
      intro t ht hb hc
      have hb' : t+k*ell+ell ≤ s := by nlinarith
      have hc' : c (t+k*ell+ell) = true := by
        convert hc using 1 <;> ring
      exact ih t ht (by nlinarith) (step (t+k*ell) (by omega) hb' hc')
  have hr := (remainder_bounds a ell ha hell).1
  have he := remainder_representation a ell ha
  apply descent (a+(a-1)/ell) (positiveRemainder a ell) hr
  · dsimp [s] at *
    omega
  · simpa only [← he] using start

end Hopkins
