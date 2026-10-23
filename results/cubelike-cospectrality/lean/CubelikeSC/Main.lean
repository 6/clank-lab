import CubelikeSC.Encode
import CubelikeSC.Bracket

/-!
# The reduction: Lemma F implies `|K(S)| ≤ 4` (the paper)

Assume `|K(S)| ≥ 5`. `exists_frame` gives `h₀, h₁, h₂ ∈ K(S)`, independent,
with `σ = comb t'`. The case is `n = |S|`, `B = {c ≠ 0 : comb c ∈ S}` and
`t = t'` (numbered by `dec`). For each coset `u` the bracket of Lemma 9 applied
to the eigenvalues on that coset (without `a = 0` for `u = 0`) is admissible,
and the costs add up to at most `Σ_a λ_a² = 128 n` (Parseval), contradicting
Lemma F.
-/

namespace CubelikeSC

theorem main (hF : LemmaF) : ∀ S : Finset V, (0 : V) ∉ S → (K S).card ≤ 4 := by
  intro S hS0
  by_contra hcon
  obtain ⟨h, hK, hind, t', ht'⟩ := exists_frame S (by omega)
  set n := S.card with hn
  set Bw : Finset W := Finset.univ.filter (fun c => comb h c ∈ S) with hBw
  set B : Finset (Fin 8) := Bw.image dec with hB
  set t : Fin 8 := dec t' with ht
  have comb_inj : Function.Injective (comb h) := by
    intro c c' e
    exact sub_eq_zero.1 (hind (c - c') (by rw [comb_sub, e, sub_self]))
  have hn128 : n < 2 ^ 7 := by
    have hsub : S ⊆ Finset.univ.erase 0 := fun s hs =>
      Finset.mem_erase.2 ⟨fun e => hS0 (e ▸ hs), Finset.mem_univ _⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ] at this
    simp only [Fintype.card_fun, ZMod.card, Fintype.card_fin] at this
    omega
  have hB0 : (0 : Fin 8) ∉ B := by
    intro h0
    obtain ⟨c, hc, e⟩ := Finset.mem_image.1 h0
    have : c = 0 := by rw [← enc_dec c, e, enc_zero]
    subst this
    simp [Bw, comb_zero] at hc
    exact hS0 hc
  have hBcard : B.card = Bw.card := Finset.card_image_of_injective _ dec_injective
  have hBn : B.card ≤ n := by
    rw [hBcard]
    exact Finset.card_le_card_of_injOn (comb h) (fun c hc => (Finset.mem_filter.1 hc).2)
      comb_inj.injOn
  -- the cosets, numbered by `Fin 8`
  set fib : Fin 8 → Finset V := fun u => Finset.univ.filter (fun a => proj h a = enc u) with hfib
  have hmu : ∀ u : Fin 8, ∑ c ∈ Bw, ((-1 : ℤ) ^ (c ⬝ᵥ enc u).val) = mu 3 B u := by
    intro u
    unfold mu
    rw [hB, Finset.sum_image]
    · exact Finset.sum_congr rfl fun c _ => by rw [bdot_dec]
    · intro x _ y _ e; exact dec_injective e
  have hfib_lam : ∀ u, ∑ a ∈ fib u, lam S a = 16 * mu 3 B u := by
    intro u; rw [← hmu]; exact fiber_lam h S (enc u)
  have hfib_card : ∀ u, (fib u).card = 16 := by
    intro u; have := fiber_card h hind (enc u); exact_mod_cast this
  have h0fib : (0 : V) ∈ fib 0 := by
    simp only [hfib, Finset.mem_filter, Finset.mem_univ, true_and, enc_zero]
    funext i; simp [proj]
  have hmu0 : mu 3 B 0 = B.card := by simp [mu, bdot]
  -- the index set of each coset's values
  set I : Fin 8 → Finset V := fun u => if u = 0 then (fib 0).erase 0 else fib u with hI
  have hdata : ∀ u, ∃ N : ℕ, 0 < N ∧ (I u).card = N ∧
      (∑ a ∈ I u, (lam S a : ℚ)) = N * mean 7 3 n B u ∧
      ∀ α β : ℤ, cost 7 3 n B u α β = (if u = 0 then (n : ℚ) ^ 2 else 0) +
        N * ((mean 7 3 n B u) ^ 2 + (mean 7 3 n B u - α) * (β - mean 7 3 n B u)) := by
    intro u
    by_cases hu : u = 0
    · subst hu
      refine ⟨15, by norm_num, ?_, ?_, ?_⟩
      · simp only [hI, if_pos rfl, Finset.card_erase_of_mem h0fib, hfib_card]
      · simp only [hI, if_pos rfl]
        have hsum := Finset.sum_erase_add (fib 0) (lam S) h0fib
        rw [hfib_lam, lam_zero, hmu0] at hsum
        have hz : (∑ a ∈ (fib 0).erase 0, lam S a) = 16 * B.card - n := by linarith
        have hz' : (∑ a ∈ (fib 0).erase 0, (lam S a : ℚ)) = 16 * B.card - n := by
          exact_mod_cast hz
        rw [hz']
        simp only [mean]
        norm_num
        field_simp
      · intro α β
        simp only [cost]
        norm_num
    · refine ⟨16, by norm_num, ?_, ?_, ?_⟩
      · simp only [hI, if_neg hu, hfib_card]
      · simp only [hI, if_neg hu, mean]
        have := hfib_lam u
        have : (∑ a ∈ fib u, (lam S a : ℚ)) = 16 * mu 3 B u := by exact_mod_cast this
        rw [this]; norm_num
      · intro α β
        simp only [cost, if_neg hu]
        norm_num
  choose N hNpos hNcard hNsum hNcost using hdata
  have hbr : ∀ u, ∃ α β : ℤ, (∃ a ∈ I u, lam S a = α) ∧ (∃ a ∈ I u, lam S a = β) ∧
      (α : ℚ) ≤ mean 7 3 n B u ∧ mean 7 3 n B u ≤ β ∧
      (N u : ℚ) * ((mean 7 3 n B u) ^ 2 + (mean 7 3 n B u - α) * (β - mean 7 3 n B u)) ≤
        ∑ a ∈ I u, ((lam S a : ℚ) ^ 2) := fun u =>
    bracket (I u) (lam S) (N u) (hNcard u) (hNpos u) _ (hNsum u)
  choose α β hα hβ hαM hMβ hcost using hbr
  -- facts about a value of coset `u`
  have hmemI : ∀ u a, a ∈ I u → proj h a = enc u := by
    intro u a ha
    by_cases hu : u = 0
    · subst hu
      simp only [hI, if_pos rfl] at ha
      exact (Finset.mem_filter.1 (Finset.mem_of_mem_erase ha)).2
    · simp only [hI, if_neg hu] at ha
      exact (Finset.mem_filter.1 ha).2
  have hval_bound : ∀ a, -(n : ℤ) ≤ lam S a ∧ lam S a ≤ n := fun a => abs_le.1 (abs_lam_le S a)
  have hval_mod : ∀ u a, a ∈ I u → lam S a ≡ n - 2 * bdot 3 u t [ZMOD 4] := by
    intro u a ha
    have := lam_mod4 S a
    rw [← ht', dot_comb, hmemI u a ha] at this
    rw [ht, bdot_dec]
    exact this
  have hval_sep : ∀ u v a b, u ≠ v → a ∈ I u → b ∈ I v → lam S a ≠ lam S b := by
    intro u v a b huv ha hb e
    have := proj_eq_of_lam_eq h hK e
    rw [hmemI u a ha, hmemI v b hb] at this
    exact huv (enc_injective this)
  have hval_n : ∀ u a, u ≠ 0 → a ∈ I u → lam S a ≠ n := by
    intro u a hu ha e
    rw [← lam_zero S] at e
    have h0I : (0 : V) ∈ fib 0 := h0fib
    have := proj_eq_of_lam_eq h hK e
    rw [hmemI u a ha] at this
    have h00 : proj h 0 = enc 0 := by rw [enc_zero]; funext i; simp [proj]
    exact hu (enc_injective (this.trans h00))
  -- the assignment is admissible
  have hadm : Admissible 7 3 n B t α β := by
    obtain ⟨a, ha, ea⟩ := hα 0
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro u
      obtain ⟨a, ha, ea⟩ := hα u
      obtain ⟨b, hb, eb⟩ := hβ u
      exact ⟨ea ▸ (hval_bound a).1, hαM u, hMβ u, eb ▸ (hval_bound b).2⟩
    · intro u e
      have h1 := hαM u; have h2 := hMβ u
      rw [← e] at h2
      exact le_antisymm h1 h2
    · intro u
      obtain ⟨a, ha, ea⟩ := hα u
      obtain ⟨b, hb, eb⟩ := hβ u
      exact ⟨ea ▸ hval_mod u a ha, eb ▸ hval_mod u b hb⟩
    · intro u hu
      obtain ⟨a, ha, ea⟩ := hα u
      obtain ⟨b, hb, eb⟩ := hβ u
      exact ⟨ea ▸ hval_n u a hu ha, eb ▸ hval_n u b hu hb⟩
    · intro u v huv
      obtain ⟨a, ha, ea⟩ := hα u
      obtain ⟨b, hb, eb⟩ := hβ u
      obtain ⟨a', ha', ea'⟩ := hα v
      obtain ⟨b', hb', eb'⟩ := hβ v
      exact ⟨ea ▸ ea' ▸ hval_sep u v a a' huv ha ha', ea ▸ eb' ▸ hval_sep u v a b' huv ha hb',
        eb ▸ ea' ▸ hval_sep u v b a' huv hb ha', eb ▸ eb' ▸ hval_sep u v b b' huv hb hb'⟩
  have hlt := hF n hn128 B hB0 hBn t α β hadm
  -- but the total cost is at most `Σ_a λ_a² = 128 n`
  have hcoset : ∀ u, cost 7 3 n B u (α u) (β u) ≤ ∑ a ∈ fib u, ((lam S a : ℚ) ^ 2) := by
    intro u
    rw [hNcost u]
    have := hcost u
    by_cases hu : u = 0
    · subst hu
      simp only [hI, if_pos rfl] at this
      rw [if_pos rfl, ← Finset.sum_erase_add (fib 0) _ h0fib, lam_zero]
      push_cast
      linarith
    · simp only [hI, if_neg hu] at this
      rw [if_neg hu]
      linarith
  have htot : ∑ u, ∑ a ∈ fib u, ((lam S a : ℚ) ^ 2) = 128 * n := by
    have hpart := Finset.sum_fiberwise (Finset.univ : Finset V) (fun a => dec (proj h a))
      (fun a => ((lam S a : ℚ) ^ 2))
    have hfib' : ∀ u : Fin 8, (Finset.univ.filter fun a => dec (proj h a) = u) = fib u := by
      intro u
      ext a
      simp only [hfib, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro e; rw [← e, enc_dec]
      · intro e; rw [e, dec_enc]
    simp only [hfib'] at hpart
    rw [hpart]
    have := parseval S
    exact_mod_cast this
  have hle := Finset.sum_le_sum fun u (_ : u ∈ Finset.univ) => hcoset u
  have htot' : ∑ u : Fin (2 ^ 3), ∑ a ∈ fib u, ((lam S a : ℚ) ^ 2) = 128 * n := htot
  norm_num at hlt
  linarith

end CubelikeSC
