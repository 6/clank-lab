import Harborth.DSH

/-! Lifting lemma along one direction. -/

open Finset Pointwise

namespace Harborth

/-- A direction: coordinates `(φ, ψ)` on `(ZMod p)²` with `x = φ x • e + ψ x • d`. -/
structure Dir (p : ℕ) where
  φ : ZMod p × ZMod p → ZMod p
  ψ : ZMod p × ZMod p → ZMod p
  e : ZMod p × ZMod p
  d : ZMod p × ZMod p
  hx : ∀ x, φ x • e + ψ x • d = x

variable {p : ℕ} [Fact p.Prime]

/-- The fibre of `S` over class `g`. -/
def Dir.fib (D : Dir p) (S : Finset (ZMod p × ZMod p)) (g : ZMod p) :
    Finset (ZMod p × ZMod p) := S.filter (fun x => D.φ x = g)

/-- The parameter set of a fibre. -/
def Dir.A (D : Dir p) (S : Finset (ZMod p × ZMod p)) (g : ZMod p) : Finset (ZMod p) :=
  (D.fib S g).image D.ψ

/-- Achievable sums of `t g` elements of the parameter set. -/
def Dir.I (D : Dir p) (S : Finset (ZMod p × ZMod p)) (t : ZMod p → ℕ) (g : ZMod p) :
    Finset (ZMod p) :=
  ((D.A S g).powersetCard (t g)).image (fun B => ∑ x ∈ B, x)

lemma Dir.injOn (D : Dir p) (S : Finset (ZMod p × ZMod p)) (g : ZMod p) :
    Set.InjOn D.ψ (D.fib S g : Set (ZMod p × ZMod p)) := by
  intro x hx y hy h
  simp only [Dir.fib, coe_filter, Set.mem_setOf_eq] at hx hy
  calc x = D.φ x • D.e + D.ψ x • D.d := (D.hx x).symm
    _ = D.φ y • D.e + D.ψ y • D.d := by rw [hx.2, hy.2, h]
    _ = y := D.hx y

lemma Dir.sum_eq (D : Dir p) (T : Finset (ZMod p × ZMod p)) :
    ∑ x ∈ T, x = (∑ x ∈ T, D.φ x) • D.e + (∑ x ∈ T, D.ψ x) • D.d := by
  calc ∑ x ∈ T, x = ∑ x ∈ T, (D.φ x • D.e + D.ψ x • D.d) :=
        Finset.sum_congr rfl (fun x _ => (D.hx x).symm)
    _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_smul, Finset.sum_smul]

lemma Dir.card_A (D : Dir p) (S : Finset (ZMod p × ZMod p)) (g : ZMod p) :
    (D.A S g).card = (D.fib S g).card :=
  card_image_of_injOn (D.injOn S g)

lemma iter_cd {ι : Type*} [DecidableEq ι] (I : ι → Finset (ZMod p)) (s : Finset ι)
    (hI : ∀ g ∈ s, (I g).Nonempty) :
    ∃ R : Finset (ZMod p),
      (∀ r ∈ R, ∃ f : ι → ZMod p, (∀ g ∈ s, f g ∈ I g) ∧ ∑ g ∈ s, f g = r) ∧
      min p (∑ g ∈ s, ((I g).card - 1) + 1) ≤ R.card := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨{0}, ?_, ?_⟩
    · intro r hr
      refine ⟨fun _ => 0, by simp, ?_⟩
      simpa using (mem_singleton.1 hr).symm
    · simp
  | insert a s ha ih =>
    obtain ⟨R, hR, hcard⟩ := ih (fun g hg => hI g (mem_insert_of_mem hg))
    have hIa : (I a).Nonempty := hI a (mem_insert_self _ _)
    have hRne : R.Nonempty := by
      rw [← card_pos]; omega
    have cd := ZMod.cauchy_davenport (Fact.out : p.Prime) hRne hIa
    refine ⟨R + I a, ?_, ?_⟩
    · intro r hr
      obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.1 hr
      obtain ⟨f, hf, hfs⟩ := hR x hx
      refine ⟨fun g => if g = a then y else f g, ?_, ?_⟩
      · intro g hg
        by_cases hga : g = a
        · simp [hga, hy]
        · simp only [hga, if_false]
          exact hf g ((mem_insert.1 hg).resolve_left hga)
      · rw [sum_insert ha]
        simp only [if_true]
        rw [add_comm]
        congr 1
        rw [← hfs]
        exact sum_congr rfl (fun g hg => by simp [show g ≠ a from fun h => ha (h ▸ hg)])
    · rw [sum_insert ha]
      have := card_pos.2 hIa
      omega

/-- Lifting along one direction. -/
theorem lift_core (D : Dir p) (S : Finset (ZMod p × ZMod p)) (t : ZMod p → ℕ)
    (ht : ∀ g, t g ≤ (D.fib S g).card) (hsum : ∑ g, t g = p)
    (hz : ∑ g, (t g : ZMod p) * g = 0)
    (hw : p - 1 ≤ ∑ g, t g * ((D.fib S g).card - t g)) :
    ∃ T ⊆ S, T.card = p ∧ ∑ x ∈ T, x = 0 := by
  classical
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hI : ∀ g, min p (t g * ((D.fib S g).card - t g) + 1) ≤ (D.I S t g).card := by
    intro g
    have key := dsh (D.A S g) (t g) (by rw [D.card_A]; exact ht g)
    rw [D.card_A] at key
    exact key
  have hne : ∀ g ∈ (univ : Finset (ZMod p)), (D.I S t g).Nonempty := by
    intro g _
    rw [← card_pos]
    have := hI g
    omega
  have hS : p - 1 ≤ ∑ g, ((D.I S t g).card - 1) := by
    by_cases hex : ∃ g0, p - 1 ≤ t g0 * ((D.fib S g0).card - t g0)
    · obtain ⟨g0, hg0⟩ := hex
      have h1 := hI g0
      have h2 : ((D.I S t g0).card - 1) ≤ ∑ g, ((D.I S t g).card - 1) :=
        Finset.single_le_sum (f := fun g => (D.I S t g).card - 1)
          (fun _ _ => Nat.zero_le _) (mem_univ g0)
      omega
    · push_neg at hex
      refine hw.trans (Finset.sum_le_sum fun g _ => ?_)
      have h1 := hI g
      have h2 := hex g
      omega
  obtain ⟨R, hR, hRc⟩ := iter_cd (D.I S t) univ hne
  have hRp : R.card = Fintype.card (ZMod p) := by
    rw [ZMod.card]
    have : R.card ≤ Fintype.card (ZMod p) := card_le_univ R
    rw [ZMod.card] at this
    omega
  have hRu : R = univ := eq_univ_of_card R hRp
  obtain ⟨f, hf, hfs⟩ := hR 0 (hRu ▸ mem_univ 0)
  have hB : ∀ g, ∃ B ∈ (D.A S g).powersetCard (t g), ∑ x ∈ B, x = f g :=
    fun g => mem_image.1 (hf g (mem_univ g))
  choose B hBmem hBsum using hB
  have hBsub : ∀ g, B g ⊆ D.A S g := fun g => (mem_powersetCard.1 (hBmem g)).1
  have hBcard : ∀ g, (B g).card = t g := fun g => (mem_powersetCard.1 (hBmem g)).2
  let T : Finset (ZMod p × ZMod p) := S.filter (fun x => D.ψ x ∈ B (D.φ x))
  have hfib : ∀ g, T.filter (fun x => D.φ x = g) =
      (D.fib S g).filter (fun x => D.ψ x ∈ B g) := by
    intro g
    ext x
    simp only [T, Dir.fib, mem_filter]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      subst h3
      exact ⟨⟨h1, rfl⟩, h2⟩
    · rintro ⟨⟨h1, h3⟩, h2⟩
      subst h3
      exact ⟨⟨h1, h2⟩, rfl⟩
  have himg : ∀ g, ((D.fib S g).filter (fun x => D.ψ x ∈ B g)).image D.ψ = B g := by
    intro g
    ext s
    simp only [mem_image, mem_filter]
    constructor
    · rintro ⟨x, ⟨_, hx⟩, rfl⟩
      exact hx
    · intro hs
      obtain ⟨x, hx, rfl⟩ := mem_image.1 (hBsub g hs)
      exact ⟨x, ⟨hx, hs⟩, rfl⟩
  have hinj : ∀ g, Set.InjOn D.ψ
      (((D.fib S g).filter (fun x => D.ψ x ∈ B g) : Finset _) : Set (ZMod p × ZMod p)) :=
    fun g => (D.injOn S g).mono (by exact_mod_cast filter_subset _ _)
  have hcardg : ∀ g, (T.filter (fun x => D.φ x = g)).card = t g := by
    intro g
    rw [hfib, ← card_image_of_injOn (hinj g), himg g, hBcard g]
  have hψg : ∀ g, ∑ x ∈ T.filter (fun x => D.φ x = g), D.ψ x = f g := by
    intro g
    rw [hfib, ← sum_image (f := fun s => s) (hinj g), himg g, hBsum g]
  refine ⟨T, filter_subset _ _, ?_, ?_⟩
  · rw [card_eq_sum_card_fiberwise (f := D.φ) (t := univ) (fun _ _ => mem_univ _)]
    simp only [hcardg]
    exact hsum
  · have h1 : ∑ x ∈ T, D.φ x = 0 := by
      rw [← Finset.sum_fiberwise T D.φ (fun x => D.φ x)]
      rw [← hz]
      refine sum_congr rfl fun g _ => ?_
      rw [sum_congr rfl (fun x hx => (mem_filter.1 hx).2), sum_const, hcardg g]
      simp
    have h2 : ∑ x ∈ T, D.ψ x = 0 := by
      rw [← Finset.sum_fiberwise T D.φ (fun x => D.ψ x)]
      simp only [hψg]
      exact hfs
    rw [D.sum_eq, h1, h2]
    simp

lemma sum_univ_zmod (hp : 11 ≤ p) : ∑ s : ZMod p, s = 0 := by
  have h : ∑ s : ZMod p, s = ∑ s : ZMod p, -s :=
    Fintype.sum_equiv (Equiv.neg (ZMod p)) _ _ (fun x => (neg_neg x).symm)
  rw [Finset.sum_neg_distrib] at h
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h0
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h0
    rw [ZMod.natCast_eq_zero_iff] at this
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have : (2 : ZMod p) * ∑ s : ZMod p, s = 0 := by linear_combination h
  exact (mul_eq_zero.1 this).resolve_left h2

/-- A full fibre gives a zero-sum `p`-subset. -/
theorem full_line (hp : 11 ≤ p) (D : Dir p) (S : Finset (ZMod p × ZMod p)) (g : ZMod p)
    (h : p ≤ (D.fib S g).card) : ∃ T ⊆ S, T.card = p ∧ ∑ x ∈ T, x = 0 := by
  classical
  have hle : (D.A S g).card ≤ p := by
    have := card_le_univ (D.A S g)
    rwa [ZMod.card] at this
  have hcard : (D.fib S g).card = p := by
    have := D.card_A S g
    omega
  have hAu : D.A S g = univ := by
    apply eq_univ_of_card
    rw [ZMod.card]; have := D.card_A S g; omega
  refine ⟨D.fib S g, filter_subset _ _, hcard, ?_⟩
  have h1 : ∑ x ∈ D.fib S g, D.φ x = 0 := by
    have : ∑ x ∈ D.fib S g, D.φ x = ∑ x ∈ D.fib S g, g :=
      sum_congr rfl (fun x hx => (mem_filter.1 hx).2)
    rw [this, sum_const, hcard]
    simp
  have h2 : ∑ x ∈ D.fib S g, D.ψ x = 0 := by
    have : ∑ s ∈ D.A S g, s = ∑ x ∈ D.fib S g, D.ψ x := sum_image (D.injOn S g)
    rw [← this, hAu]
    exact sum_univ_zmod hp
  rw [D.sum_eq, h1, h2]
  simp

end Harborth
