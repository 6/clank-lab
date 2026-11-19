import GCG.Game

namespace GCG

open Finset

/-- `ArboricityLE G d`: the edges of `G` can be coloured with `d` colours so that every
colour class is a forest; that is, the arboricity of `G` is at most `d`. -/
def ArboricityLE {V : Type*} (G : SimpleGraph V) (d : ℕ) : Prop :=
  ∃ f : Sym2 V → Fin d, ∀ i, (SimpleGraph.fromEdgeSet {e | e ∈ G.edgeSet ∧ f e = i}).IsAcyclic

/-- A graph in which, for an injective rank, every vertex has at most one neighbour of
smaller rank, is acyclic. -/
theorem isAcyclic_of_rank {V : Type*} (H : SimpleGraph V) (rank : V → ℕ)
    (hrank : Function.Injective rank)
    (hH : ∀ v w₁ w₂, H.Adj v w₁ → H.Adj v w₂ → rank w₁ < rank v → rank w₂ < rank v →
      w₁ = w₂) :
    H.IsAcyclic := by
  classical
  intro u c hc
  obtain ⟨v, hv, hmax⟩ := c.support.toFinset.exists_max_image rank
    ⟨u, by simp [SimpleGraph.Walk.start_mem_support]⟩
  rw [List.mem_toFinset] at hv
  obtain ⟨x, y, hxy, hset⟩ := Set.ncard_eq_two.mp (hc.ncard_neighborSet_toSubgraph_eq_two hv)
  have hx : c.toSubgraph.Adj v x := by
    change x ∈ c.toSubgraph.neighborSet v; rw [hset]; simp
  have hy : c.toSubgraph.Adj v y := by
    change y ∈ c.toSubgraph.neighborSet v; rw [hset]; simp
  have hlt : ∀ z, c.toSubgraph.Adj v z → rank z < rank v := by
    intro z hz
    have hzs : z ∈ c.support := by
      have := hz.snd_mem; rw [SimpleGraph.Walk.verts_toSubgraph] at this; exact this
    have hle := hmax z (List.mem_toFinset.mpr hzs)
    have hne : z ≠ v := (hz.adj_sub).ne.symm
    exact lt_of_le_of_ne hle (fun h => hne (hrank h))
  exact hxy (hH v x y hx.adj_sub hy.adj_sub (hlt x hx) (hlt y hy))

/-- A degeneracy ordering of a finite set. -/
theorem exists_rank {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ)
    (h : ∀ S : Finset V, S.Nonempty → ∃ v ∈ S, (S.filter (fun u => G.Adj v u)).card < d)
    (S : Finset V) :
    ∃ rank : V → ℕ, Set.InjOn rank S ∧
      ∀ v ∈ S, (S.filter (fun u => G.Adj v u ∧ rank u < rank v)).card < d := by
  induction S using Finset.strongInduction with
  | H S ih =>
    rcases S.eq_empty_or_nonempty with hS | hS
    · subst hS; exact ⟨fun _ => 0, by simp, by simp⟩
    obtain ⟨v, hvS, hv⟩ := h S hS
    obtain ⟨r, hinj, hr⟩ := ih (S.erase v) (Finset.erase_ssubset hvS)
    set N := (S.erase v).sup r + 1 with hN
    have hbig : ∀ x ∈ S.erase v, r x < N := fun x hx =>
      Nat.lt_succ_of_le (Finset.le_sup (f := r) hx)
    refine ⟨fun x => if x = v then N else r x, ?_, ?_⟩
    · intro a ha b hb hab
      simp only at hab
      by_cases hav : a = v <;> by_cases hbv : b = v
      · rw [hav, hbv]
      · rw [ite_eq_left hav, ite_eq_right hbv] at hab
        exact absurd hab (ne_of_gt (hbig b (Finset.mem_erase.mpr ⟨hbv, hb⟩)))
      · rw [ite_eq_right hav, ite_eq_left hbv] at hab
        exact absurd hab (ne_of_lt (hbig a (Finset.mem_erase.mpr ⟨hav, ha⟩)))
      · rw [ite_eq_right hav, ite_eq_right hbv] at hab
        exact hinj (Finset.mem_erase.mpr ⟨hav, ha⟩) (Finset.mem_erase.mpr ⟨hbv, hb⟩) hab
    · intro x hx
      by_cases hxv : x = v
      · subst hxv
        refine lt_of_le_of_lt (Finset.card_le_card ?_) hv
        intro u hu
        simp only [Finset.mem_filter] at hu ⊢
        exact ⟨hu.1, hu.2.1⟩
      · have hxe : x ∈ S.erase v := Finset.mem_erase.mpr ⟨hxv, hx⟩
        refine lt_of_le_of_lt (Finset.card_le_card ?_) (hr x hxe)
        intro u hu
        simp only [Finset.mem_filter, ite_eq_right hxv] at hu ⊢
        obtain ⟨huS, hadj, hlt⟩ := hu
        have huv : u ≠ v := by
          rintro rfl
          rw [ite_eq_left rfl] at hlt
          exact absurd hlt (not_lt.mpr (le_of_lt (hbig x hxe)))
        rw [ite_eq_right huv] at hlt
        exact ⟨Finset.mem_erase.mpr ⟨huv, huS⟩, hadj, hlt⟩

/-- **Degenerate graphs have small arboricity.** If every nonempty vertex set `S` of a
finite graph has a vertex with fewer than `d` neighbours in `S`, the edges split into
`d` forests. -/
theorem arboricityLE_of_degenerate {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ)
    (h : ∀ S : Finset V, S.Nonempty → ∃ v ∈ S, (S.filter (fun u => G.Adj v u)).card < d) :
    ArboricityLE G d := by
  classical
  obtain ⟨rank, hinj, hrank⟩ := exists_rank G d h Finset.univ
  have hinj' : Function.Injective rank := fun a b hab =>
    hinj (Finset.mem_coe.mpr (Finset.mem_univ a)) (Finset.mem_coe.mpr (Finset.mem_univ b)) hab
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    have hV : IsEmpty V := by
      by_contra hne
      rw [not_isEmpty_iff] at hne
      obtain ⟨v, _, hv⟩ := h Finset.univ Finset.univ_nonempty
      exact Nat.not_lt_zero _ hv
    exact ⟨fun e => isEmptyElim e.out.1, fun i => Fin.elim0 i⟩
  set L : V → Finset V := fun v => Finset.univ.filter (fun u => G.Adj v u ∧ rank u < rank v)
    with hL
  have hLd : ∀ v, (L v).card ≤ d := fun v => le_of_lt (hrank v (Finset.mem_univ v))
  let col : V → V → Fin d := fun v u =>
    if hu : u ∈ L v then Fin.castLE (hLd v) ((L v).equivFin ⟨u, hu⟩) else ⟨0, hd⟩
  have hcol : ∀ v u₁ u₂, u₁ ∈ L v → u₂ ∈ L v → col v u₁ = col v u₂ → u₁ = u₂ := by
    intro v u₁ u₂ h₁ h₂ heq
    simp only [col, dite_eq_left h₁, dite_eq_left h₂, Fin.castLE_inj] at heq
    have := (L v).equivFin.injective heq
    exact congrArg Subtype.val this
  let g : V → V → Fin d := fun a b => if rank a < rank b then col b a else col a b
  have hg : ∀ a b, g a b = g b a := by
    intro a b
    simp only [g]
    rcases lt_trichotomy (rank a) (rank b) with hab | hab | hab
    · rw [ite_eq_left hab, ite_eq_right (not_lt.mpr (le_of_lt hab))]
    · have := hinj' hab; subst this; rfl
    · rw [ite_eq_right (not_lt.mpr (le_of_lt hab)), ite_eq_left hab]
  let f : Sym2 V → Fin d := Sym2.lift ⟨g, hg⟩
  refine ⟨f, fun i => ?_⟩
  apply isAcyclic_of_rank _ rank hinj'
  intro v w₁ w₂ h₁ h₂ r₁ r₂
  rw [SimpleGraph.fromEdgeSet_adj] at h₁ h₂
  obtain ⟨⟨e₁, f₁⟩, -⟩ := h₁
  obtain ⟨⟨e₂, f₂⟩, -⟩ := h₂
  have mem₁ : w₁ ∈ L v := by simp only [hL, Finset.mem_filter]; exact ⟨Finset.mem_univ _, e₁, r₁⟩
  have mem₂ : w₂ ∈ L v := by simp only [hL, Finset.mem_filter]; exact ⟨Finset.mem_univ _, e₂, r₂⟩
  simp only [f, Sym2.lift_mk, g, ite_eq_right (not_lt.mpr (le_of_lt r₁)),
    ite_eq_right (not_lt.mpr (le_of_lt r₂))] at f₁ f₂
  exact hcol v w₁ w₂ mem₁ mem₂ (f₁.trans f₂.symm)

end GCG
