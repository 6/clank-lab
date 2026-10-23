import Mathlib
import CubelikeSC.Cert.Key

/-!
# Soundness of the certificate check (weak duality)

`case_sound`: if the cosets of a case `(n, B, t)` are a permutation of a list
`cs` with `checkKey n cs w = true`, every admissible assignment of the case
costs more than `128 n`.
-/

namespace CubelikeSC.Cert

open CubelikeSC

lemma sum_allU (f : Fin 8 → ℚ) : (allU.map f).sum = ∑ u, f u := by
  simp [allU, Fin.sum_univ_eight, add_assoc]

lemma mem_allU (u : Fin 8) : u ∈ allU := by fin_cases u <;> simp [allU]

lemma mem_vals {n : ℕ} {r a : ℤ} (h1 : -(n : ℤ) ≤ a) (h2 : a ≤ n) (h3 : a % 4 = r % 4) :
    a ∈ vals n r := by
  unfold vals
  simp only [List.mem_map, List.mem_range]
  set lo : ℤ := -(n : ℤ) + ((r + n) % 4) with hlo
  have hk : 0 ≤ (a - lo) / 4 := by omega
  have ha : a = lo + 4 * ((a - lo) / 4) := by omega
  refine ⟨((a - lo) / 4).toNat, ?_, ?_⟩
  · have : (a - lo) / 4 < ((n : ℤ) - lo) / 4 + 1 := by omega
    exact (Int.toNat_lt_toNat (by omega)).2 this
  · rw [Int.toNat_of_nonneg hk]; exact ha.symm

lemma lmin_le {l : List ℤ} {x : ℤ} (hx : x ∈ l) : lmin l ≤ x := by
  have key : ∀ (l : List ℤ) (acc : ℤ), l.foldl min acc ≤ acc ∧ ∀ y ∈ l, l.foldl min acc ≤ y := by
    intro l
    induction l with
    | nil => intro acc; simp
    | cons z zs ih =>
      intro acc
      obtain ⟨h1, h2⟩ := ih (min acc z)
      refine ⟨le_trans h1 (min_le_left _ _), ?_⟩
      intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact le_trans h1 (min_le_right _ _)
      · exact h2 y hy
  cases l with
  | nil => simp at hx
  | cons z zs =>
    simp only [lmin]
    rcases List.mem_cons.1 hx with rfl | hx
    · exact (key zs _).1
    · exact (key zs z).2 x hx

lemma wt_cons (e : ℤ × ℤ) (w : List (ℤ × ℤ)) (v : ℤ) :
    wt (e :: w) v = (if e.1 = v then e.2 else 0) + wt w v := by
  simp only [wt, List.foldr_cons]; split_ifs <;> simp

lemma wt_nil (v : ℤ) : wt [] v = 0 := rfl

/-- Weak duality, the weight part: by condition 5 every value is an endpoint of
at most one chosen bracket, so the chosen endpoints carry at most `Σ_v w_v`. -/
lemma sum_wt_le (w : List (ℤ × ℤ)) (hw : ∀ e ∈ w, 0 ≤ e.2) (α β : Fin 8 → ℤ)
    (h5 : ∀ u v, u ≠ v → α u ≠ α v ∧ α u ≠ β v ∧ β u ≠ α v ∧ β u ≠ β v) :
    ∑ u, (wt w (α u) + if β u = α u then 0 else wt w (β u)) ≤ (w.map (·.2)).sum := by
  induction w with
  | nil => simp [wt_nil]
  | cons e w ih =>
    simp only [wt_cons, List.map_cons, List.sum_cons]
    have ih' := ih (fun e' he' => hw e' (List.mem_cons_of_mem _ he'))
    have he : 0 ≤ e.2 := hw e (List.mem_cons_self ..)
    set f : Fin 8 → ℤ := fun u =>
      (if e.1 = α u then e.2 else 0) + (if β u = α u then 0 else if e.1 = β u then e.2 else 0)
    have hsplit : ∀ u, ((if e.1 = α u then e.2 else 0) + wt w (α u) +
        if β u = α u then 0 else (if e.1 = β u then e.2 else 0) + wt w (β u)) =
        f u + (wt w (α u) + if β u = α u then 0 else wt w (β u)) := by
      intro u; simp only [f]; split_ifs <;> ring
    rw [Finset.sum_congr rfl (fun u _ => hsplit u), Finset.sum_add_distrib]
    have hf : ∑ u, f u ≤ e.2 := by
      by_cases hex : ∃ u0, e.1 = α u0 ∨ (β u0 ≠ α u0 ∧ e.1 = β u0)
      · obtain ⟨u0, hu0⟩ := hex
        rw [Finset.sum_eq_single u0]
        · simp only [f]; split_ifs <;> simp_all
        · intro u _ hu
          have := h5 u u0 hu
          simp only [f]
          rcases hu0 with h | ⟨_, h⟩ <;> split_ifs <;> simp_all
        · simp
      · push Not at hex
        rw [Finset.sum_eq_zero]
        · exact he
        · intro u _
          simp only [f]
          have := hex u
          split_ifs <;> simp_all
    linarith

lemma two_pow : (2 : ℚ) ^ (7 - 3) = 16 := by norm_num

lemma bdot_zero_left (t : Fin 8) : bdot 3 (0 : Fin 8) t = 0 := by
  revert t; decide

lemma mean_zero (n : ℕ) (B : Finset (Fin 8)) :
    mean 7 3 n B 0 = (16 * B.card - n) / 15 := by
  simp [mean]; norm_num

lemma mean_ne (n : ℕ) (B : Finset (Fin 8)) {u : Fin 8} (hu : u ≠ 0) :
    mean 7 3 n B u = mu 3 B u := by
  simp [mean, hu]

lemma costS_eq (n : ℕ) (B : Finset (Fin 8)) (t u : Fin 8) (a b : ℤ) :
    (costS n (caseCoset n B t u) a b : ℚ) = 15000 * cost 7 3 n B u a b := by
  rcases eq_or_ne u 0 with rfl | hu
  · simp [costS, caseCoset, cost, mean_zero]
    field_simp
    ring
  · simp [costS, caseCoset, cost, mean_ne n B hu, hu]
    ring

/-- One coset of an admissible assignment: its bracket is one of the checker's
pairs, with the checker's cost equal to 15000 times the cost of §3. -/
lemma coset_term (n : ℕ) (B : Finset (Fin 8)) (t : Fin 8) (α β : Fin 8 → ℤ)
    (hadm : Admissible 7 3 n B t α β) (w : List (ℤ × ℤ)) (u : Fin 8) :
    ∃ x ∈ terms n (caseCoset n B t u) w,
      (x : ℚ) = 15000 * cost 7 3 n B u (α u) (β u) +
        (wt w (α u) + if β u = α u then 0 else wt w (β u)) := by
  obtain ⟨h1, h2, h3, h4, -⟩ := hadm
  obtain ⟨ha1, ha2, hb2, hb1⟩ := h1 u
  obtain ⟨hra, hrb⟩ := h3 u
  have e2 := h2 u
  unfold Int.ModEq at hra hrb
  have hab : α u ≤ β u := by exact_mod_cast le_trans ha2 hb2
  refine ⟨costS n (caseCoset n B t u) (α u) (β u) + wt w (α u) +
    (if β u = α u then 0 else wt w (β u)), ?_, ?_⟩
  · unfold terms
    simp only [List.mem_flatMap, List.mem_filterMap]
    refine ⟨α u, mem_vals ha1 (by omega) ?_, β u, mem_vals (by omega) hb1 ?_, ?_⟩
    · rcases eq_or_ne u 0 with rfl | hu
      · simp only [bdot_zero_left] at hra; simp [caseCoset]; omega
      · simp [caseCoset, hu]; omega
    · rcases eq_or_ne u 0 with rfl | hu
      · simp only [bdot_zero_left] at hrb; simp [caseCoset]; omega
      · simp [caseCoset, hu]; omega
    · rw [if_pos]
      rcases eq_or_ne u 0 with rfl | hu
      · rw [mean_zero] at ha2 hb2 e2
        have hA : 15 * α 0 ≤ 16 * (B.card : ℤ) - n := by
          have : (15 : ℚ) * α 0 ≤ 16 * B.card - n := by
            rw [le_div_iff₀ (by norm_num)] at ha2; linarith
          exact_mod_cast this
        have hB : 16 * (B.card : ℤ) - n ≤ 15 * β 0 := by
          have : (16 * B.card - n : ℚ) ≤ 15 * β 0 := by
            rw [div_le_iff₀ (by norm_num)] at hb2; linarith
          exact_mod_cast this
        have hE : α 0 = β 0 → 15 * α 0 = 16 * (B.card : ℤ) - n := by
          intro e
          have := e2 e
          have : (15 : ℚ) * α 0 = 16 * B.card - n := by rw [this]; field_simp
          exact_mod_cast this
        have hE' : α 0 ≠ β 0 ∨ 15 * α 0 = 16 * (B.card : ℤ) - n := by
          by_cases e : α 0 = β 0
          · exact Or.inr (hE e)
          · exact Or.inl e
        simp [ok, caseCoset, den]
        omega
      · rw [mean_ne n B hu] at ha2 hb2 e2
        have hA : α u ≤ mu 3 B u := by exact_mod_cast ha2
        have hB : mu 3 B u ≤ β u := by exact_mod_cast hb2
        have hE : α u = β u → α u = mu 3 B u := fun e => by exact_mod_cast e2 e
        have hn := h4 u hu
        have hE' : α u ≠ β u ∨ α u = mu 3 B u := by
          by_cases e : α u = β u
          · exact Or.inr (hE e)
          · exact Or.inl e
        simp [ok, caseCoset, den, hu]
        omega
  · push_cast
    rw [costS_eq]
    ring

theorem case_sound (n : ℕ) (B : Finset (Fin 8)) (t : Fin 8) (α β : Fin 8 → ℤ)
    (hadm : Admissible 7 3 n B t α β) (cs : List Coset) (w : List (ℤ × ℤ))
    (hperm : cs.Perm (allU.map (caseCoset n B t))) (hchk : checkKey n cs w = true) :
    (2 ^ 7 * n : ℚ) < ∑ u, cost 7 3 n B u (α u) (β u) := by
  have h5 := hadm.2.2.2.2
  choose x hx hxv using coset_term n B t α β hadm w
  unfold checkKey at hchk
  simp only [Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq] at hchk
  rcases hchk with ⟨c, hc, hempty⟩ | ⟨hw, hlt⟩
  · obtain ⟨u, -, rfl⟩ := List.mem_map.1 (hperm.subset hc)
    rw [List.isEmpty_iff] at hempty
    have := hx u
    rw [hempty] at this
    simp at this
  · have hsum : (cs.map fun c => lmin (terms n c w)).sum =
        ((allU.map (caseCoset n B t)).map fun c => lmin (terms n c w)).sum :=
      (hperm.map _).sum_eq
    rw [List.map_map] at hsum
    have hle : ∀ u, (lmin (terms n (caseCoset n B t u) w) : ℚ) ≤
        15000 * cost 7 3 n B u (α u) (β u) +
          (wt w (α u) + if β u = α u then 0 else wt w (β u)) := by
      intro u; rw [← hxv u]; exact_mod_cast lmin_le (hx u)
    have hq : ((cs.map fun c => lmin (terms n c w)).sum : ℚ) =
        ∑ u, (lmin (terms n (caseCoset n B t u) w) : ℚ) := by
      rw [hsum, ← sum_allU]; push_cast [List.map_map]; rfl
    have hW := sum_wt_le w hw α β h5
    have hWq : (((∑ u, (wt w (α u) + if β u = α u then 0 else wt w (β u))) : ℤ) : ℚ) ≤
        ((w.map (·.2)).sum : ℤ) := by exact_mod_cast hW
    rw [Int.cast_sum] at hWq
    simp only [Int.cast_add] at hWq
    have hltq : (1920000 * n : ℚ) <
        ((cs.map fun c => lmin (terms n c w)).sum : ℚ) - ((w.map (·.2)).sum : ℤ) := by
      exact_mod_cast hlt
    rw [hq] at hltq
    have := Finset.sum_le_sum fun u (_ : u ∈ Finset.univ) => hle u
    rw [Finset.sum_add_distrib, ← Finset.mul_sum] at this
    have hC : (∑ u : Fin 8, cost 7 3 n B u (α u) (β u)) =
        ∑ u : Fin (2 ^ 3), cost 7 3 n B u (α u) (β u) := rfl
    norm_num
    linarith

end CubelikeSC.Cert
