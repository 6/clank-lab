import Hopkins.Core

namespace Hopkins

private theorem mul_ge_one {x y : ℕ} (hx : 1 ≤ x) (hy : 1 ≤ y) : 1 ≤ x*y := by
  nlinarith

theorem upper_square (a ell : ℕ) (ha : 1 ≤ a) (hell : 1 ≤ ell) :
    Forces a (a*ell) ((a*(ell+1))^2) := by
  intro c hv
  by_contra hn
  let s := a*(ell+1)
  let K := a*(ell+1)^2
  let r := positiveRemainder a ell
  let T := a*ell*(r+1)
  change Valid (s^2) c at hv
  change ¬ Mono a (a*ell) (s^2) c at hn
  have hs : 2 ≤ s := by dsimp [s]; nlinarith
  have hsN : s ≤ s^2 := by nlinarith
  have hs1N : s+1 ≤ s^2 := by nlinarith
  obtain ⟨hr1, hrell, hra⟩ := remainder_bounds a ell ha hell
  change 1 ≤ r at hr1
  change r ≤ ell at hrell
  change r ≤ a at hra
  have hcr : c r = true := initial_residue a ell ha hell c hv hn
  have hr2 : 2 ≤ r := by
    by_contra h
    have he : r=1 := by omega
    rw [he, hv.1] at hcr
    contradiction
  have hells : ell ≤ s := by dsimp [s]; nlinarith
  have hrN : r ≤ s^2 := le_trans (le_trans hrell hells) hsN
  have hrnext : r+1 ≤ s^2 := by omega
  have hprev : c (r-1) = false := by
    have he : r-1+1=r := by omega
    apply previous_zero hv (by omega) (by omega)
    simpa only [he] using hcr
  have hnext : c (r+1) = false := next_zero hv hr1 hrnext hcr
  have hKN : K ≤ s^2 := by
    dsimp [K,s]
    nlinarith [sq_nonneg (ell+1)]
  have hTNK : T+ell*r ≤ K := by
    have h1 : a*ell*r ≤ a*ell*ell := Nat.mul_le_mul_left (a*ell) hrell
    have h2 : ell*r ≤ a*ell := by nlinarith
    dsimp [T,K]
    nlinarith
  have hTpos : 1 ≤ T := mul_ge_one (mul_ge_one ha hell) (by omega)
  have hellT : ell ≤ T := by
    have h := Nat.mul_le_mul_left ell (mul_ge_one ha (by omega : 1 ≤ r+1))
    dsimp [T]
    nlinarith only [h]
  have hTN : T ≤ s^2 := by omega
  have htwiceT : 2*a*ell ≤ T := by
    have h := Nat.mul_le_mul_left (a*ell) (show 2 ≤ r+1 by omega)
    dsimp [T]
    nlinarith only [h]
  have houtput (t : ℕ) (ht : 1 ≤ t) (htT : t ≤ T) (hc : c t = true) :
      c (a*(t+ell*r)) = false := by
    have hzN : a*(t+ell*r) ≤ s^2 := by
      have h : t+ell*r ≤ K := by omega
      have h' := Nat.mul_le_mul_left a h
      have he : a*K=s^2 := by dsimp [K,s]; ring
      omega
    exact output_color hn ht (by omega) hr1 hrN (mul_ge_one ha (by omega)) hzN
      (by ring) hc hcr
  have up (t : ℕ) (ht : 1 ≤ t) (htT : t+ell ≤ T) (hc : c t = true) :
      c (t+ell) = true := by
    have hz := houtput t ht (by omega) hc
    have hzN : a*(t+ell*r) ≤ s^2 := by
      have h : t+ell*r ≤ K := by omega
      have h' := Nat.mul_le_mul_left a h
      have he : a*K=s^2 := by dsimp [K,s]; ring
      omega
    have he : a*(t+ell)+(a*ell)*(r-1)=a*(t+ell*r) := by
      have h : r-1+1=r := by omega
      calc
        a*(t+ell)+(a*ell)*(r-1) = a*t+(a*ell)*(r-1+1) := by ring
        _ = a*(t+ell*r) := by rw [h]; ring
    exact input_color hn (by omega) (by omega) (by omega) (by omega)
      (mul_ge_one ha (by omega)) hzN he hprev hz
  have down (t : ℕ) (ht : 1 ≤ t) (htT : t+ell ≤ T)
      (hc : c (t+ell) = true) : c t = true := by
    have hz := houtput (t+ell) (by omega) htT hc
    have hzN : a*(t+ell+ell*r) ≤ s^2 := by
      have h : t+ell+ell*r ≤ K := by omega
      have h' := Nat.mul_le_mul_left a h
      have he : a*K=s^2 := by dsimp [K,s]; ring
      omega
    exact input_color hn ht (by omega) (by omega) hrnext
      (mul_ge_one ha (by omega)) hzN (by ring) hnext hz
  have descent : ∀ k : ℕ, 1 ≤ k → k*ell ≤ T → c (k*ell)=true → c ell=true := by
    intro k
    induction k with
    | zero => omega
    | succ k ih =>
      intro hk hb hc
      by_cases hk0 : k=0
      · simpa [hk0] using hc
      · have hcol : c (k*ell+ell)=true := by simpa [Nat.succ_mul] using hc
        exact ih (by omega) (by nlinarith)
          (down (k*ell) (mul_ge_one (by omega) hell) (by nlinarith) hcol)
  have ascent : ∀ k : ℕ, 1 ≤ k → k*ell ≤ T → c ell=true → c (k*ell)=true := by
    intro k
    induction k with
    | zero => omega
    | succ k ih =>
      intro hk hb hc
      by_cases hk0 : k=0
      · simpa [hk0] using hc
      · have hp := ih (by omega) (by nlinarith) hc
        have hcol := up (k*ell) (mul_ge_one (by omega) hell) (by nlinarith) hp
        simpa [Nat.succ_mul] using hcol
  cases hcell : c ell with
  | false =>
    have ht : c (2*a*ell)=true := by
      exact output_color hn hell (by omega) (by omega) (by omega)
        (mul_ge_one (mul_ge_one (by omega) ha) hell) (by omega) (by ring) hcell hv.1
    have he := descent (2*a) (by omega) htwiceT ht
    rw [hcell] at he
    contradiction
  | true =>
    have ht : c T=true := by
      have hh := ascent (a*(r+1)) (mul_ge_one ha (by omega))
        (by dsimp [T]; nlinarith only []) hcell
      convert hh using 1 <;> dsimp [T] <;> ring
    have hf : c T=false := by
      exact output_color hn hell (by omega) hr1 hrN hTpos hTN
        (by dsimp [T]; ring) hcell hcr
    rw [hf] at ht
    contradiction

theorem upper (a ell : ℕ) (ha : 1 ≤ a) (hell : 1 ≤ ell) :
    Forces a (a * ell) (a ^ 2 * (ell + 1) ^ 2) := by
  convert upper_square a ell ha hell using 1 <;> ring

end Hopkins
