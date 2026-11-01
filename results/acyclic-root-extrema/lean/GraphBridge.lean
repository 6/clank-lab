import Endpoint

namespace BBPSplitStar
open SimpleGraph Polynomial

section Soundness
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

def RankOK (G : SimpleGraph V) (r : V → ℕ) : Prop :=
  ∀ u v w, G.Adj u v → G.Adj u w → r u ≤ r v → r u ≤ r w → v = w

theorem rankOK_isAcyclic {r : V → ℕ} (h : RankOK G r) : G.IsAcyclic := by
  intro v c hc
  obtain ⟨u, hu, hmin⟩ := Finset.exists_min_image c.support.toFinset r
    ⟨v, List.mem_toFinset.mpr c.start_mem_support⟩
  have hu' : u ∈ c.support := List.mem_toFinset.mp hu
  let q := c.rotate u hu'
  have hq : q.IsCycle := hc.rotate hu'
  have hn : ¬ q.Nil := by
    intro hn
    have := hq.three_le_length
    have hz : q.length = 0 := SimpleGraph.Walk.length_eq_zero_iff.mpr hn
    omega
  have hmem (i : ℕ) : q.getVert i ∈ c.support.toFinset := by
    apply List.mem_toFinset.mpr
    exact (SimpleGraph.Walk.mem_support_rotate_iff c u hu').mp
      (q.getVert_mem_support i)
  exact hq.snd_ne_penultimate
    (h u q.snd q.penultimate (q.adj_snd hn) (q.adj_penultimate hn).symm
      (hmin _ (hmem 1)) (hmin _ (hmem (q.length - 1))))

theorem triangle_not_isAcyclic {a b c : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hca : G.Adj c a) : ¬ G.IsAcyclic := by
  intro h
  let p : G.Walk a c := .cons hab (.cons hbc .nil)
  let q : G.Walk a c := .cons hca.symm .nil
  have hp : p.IsPath := by
    apply SimpleGraph.Walk.IsPath.mk'
    simp [p, hab.ne, hbc.ne, hca.ne.symm]
  have hq : q.IsPath := by
    apply SimpleGraph.Walk.IsPath.mk'
    simp [q, hca.ne.symm]
  have he := congrArg (fun t : G.Path a c => t.val.length)
    (h.path_unique ⟨p, hp⟩ ⟨q, hq⟩)
  norm_num [p, q] at he

theorem square_not_isAcyclic {a b c d : V}
    (hac : a ≠ c) (hbd : b ≠ d)
    (hab : G.Adj a b) (hbc : G.Adj b c)
    (hcd : G.Adj c d) (hda : G.Adj d a) : ¬ G.IsAcyclic := by
  intro h
  let p : G.Walk a c := .cons hab (.cons hbc .nil)
  let q : G.Walk a c := .cons hda.symm (.cons hcd.symm .nil)
  have hp : p.IsPath := by
    apply SimpleGraph.Walk.IsPath.mk'
    simp [p, hab.ne, hbc.ne, hac]
  have hq : q.IsPath := by
    apply SimpleGraph.Walk.IsPath.mk'
    simp [q, hda.ne.symm, hcd.ne.symm, hac]
  have he := congrArg (fun t : G.Path a c => t.val.snd)
    (h.path_unique ⟨p, hp⟩ ⟨q, hq⟩)
  exact hbd (by simpa [p, q, SimpleGraph.Walk.snd_cons] using he)
end Soundness

section FiniteCertificate
variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

def peelOrder : ℕ → Finset (Fin n) → List (Fin n)
  | 0, _ => []
  | fuel + 1, S =>
    match (List.finRange n).find? (fun u =>
      decide (u ∈ S ∧ (S.filter (fun v => G.Adj u v)).card ≤ 1)) with
    | none => []
    | some u => u :: peelOrder fuel (S.erase u)

def eliminationRank (S : Finset (Fin n)) (u : Fin n) : ℕ :=
  (peelOrder G n S).idxOf u

def RankCertificate (S : Finset (Fin n)) : Prop :=
  ∀ u ∈ S,
    (S.filter (fun v => G.Adj u v ∧ eliminationRank G S u ≤ eliminationRank G S v)).card ≤ 1

instance rankCertificateDecidable (S : Finset (Fin n)) : Decidable (RankCertificate G S) := by
  unfold RankCertificate
  infer_instance

def ShortCycleOn (S : Finset (Fin n)) : Prop :=
  (∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S, G.Adj a b ∧ G.Adj b c ∧ G.Adj c a) ∨
  (∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S, ∃ d ∈ S,
    a ≠ c ∧ b ≠ d ∧ G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)

instance shortCycleOnDecidable (S : Finset (Fin n)) : Decidable (ShortCycleOn G S) := by
  unfold ShortCycleOn
  infer_instance

theorem rankCertificate_sound {S : Finset (Fin n)} (h : RankCertificate G S) :
    (G.induce (↑S : Set (Fin n))).IsAcyclic := by
  apply rankOK_isAcyclic (r := fun u => eliminationRank G S u.val)
  intro u v w huv huw hrv hrw
  apply Subtype.ext
  exact Finset.card_le_one.mp (h u.val u.property) v.val
    (Finset.mem_filter.mpr ⟨v.property, huv, hrv⟩) w.val
    (Finset.mem_filter.mpr ⟨w.property, huw, hrw⟩)

theorem shortCycleOn_sound {S : Finset (Fin n)} (h : ShortCycleOn G S) :
    ¬ (G.induce (↑S : Set (Fin n))).IsAcyclic := by
  rcases h with ⟨a, ha, b, hb, c, hc, hab, hbc, hca⟩ |
    ⟨a, ha, b, hb, c, hc, d, hd, hac, hbd, hab, hbc, hcd, hda⟩
  · exact triangle_not_isAcyclic (G := G.induce (↑S : Set (Fin n)))
      (a := ⟨a, ha⟩) (b := ⟨b, hb⟩) (c := ⟨c, hc⟩) hab hbc hca
  · exact square_not_isAcyclic (G := G.induce (↑S : Set (Fin n)))
      (a := ⟨a, ha⟩) (b := ⟨b, hb⟩) (c := ⟨c, hc⟩) (d := ⟨d, hd⟩)
      (fun e => hac (congrArg Subtype.val e))
      (fun e => hbd (congrArg Subtype.val e)) hab hbc hcd hda

def FullCoverage : Prop :=
  ∀ S ∈ (Finset.univ : Finset (Fin n)).powerset,
    RankCertificate G S ∨ ShortCycleOn G S

instance fullCoverageDecidable : Decidable (FullCoverage G) := by
  unfold FullCoverage
  infer_instance

theorem acyclic_iff_rankCertificate (h : FullCoverage G)
    {S : Finset (Fin n)} (hS : S ∈ (Finset.univ : Finset (Fin n)).powerset) :
    (G.induce (↑S : Set (Fin n))).IsAcyclic ↔ RankCertificate G S := by
  constructor
  · intro hforest
    rcases h S hS with hr | hc
    · exact hr
    · exact (shortCycleOn_sound G hc hforest).elim
  · exact rankCertificate_sound G

noncomputable def finitePolynomial : Polynomial ℤ := by
  classical
  exact ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
    if RankCertificate G S then X ^ S.card else 0

def countCoefficient (k : ℕ) : ℤ :=
  ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
    if S.card = k ∧ RankCertificate G S then 1 else 0

theorem finitePolynomial_coeff (k : ℕ) :
    (finitePolynomial G).coeff k = countCoefficient G k := by
  classical
  unfold finitePolynomial countCoefficient
  rw [Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro S hS
  by_cases h : RankCertificate G S
  · simp [h, Polynomial.coeff_X_pow, eq_comm]
  · simp [h]

theorem countCoefficient_eq_zero_of_lt {k : ℕ} (hk : n < k) :
    countCoefficient G k = 0 := by
  unfold countCoefficient
  apply Finset.sum_eq_zero
  intro S hS
  have hcard : S.card ≤ n := by
    simpa using Finset.card_le_card (Finset.subset_univ S)
  have hne : S.card ≠ k := by omega
  simp [hne]

theorem A_eq_finitePolynomial (h : FullCoverage G) : A G = finitePolynomial G := by
  classical
  unfold A finitePolynomial
  apply Finset.sum_congr rfl
  intro S hS
  rw [acyclic_iff_rankCertificate G h hS]
  split_ifs <;> rfl
end FiniteCertificate
end BBPSplitStar
