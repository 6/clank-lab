import Antony24.Basic

/-! Cycle orientation. -/
namespace Antony24
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

private lemma cycle_fst_nodup {a : V} {p : G.Walk a a} (hp : p.IsCycle) :
    (p.darts.map (fun d : G.Dart => d.fst)).Nodup := by
  rw [p.map_fst_darts]
  have h := hp.reverse.support_nodup
  simpa only [Walk.support_reverse, List.tail_reverse, List.nodup_reverse] using h

private lemma cycle_out_exists {a v : V} {p : G.Walk a a} (hp : p.IsCycle)
    (hv : v ∈ p.support) : ∃ d ∈ p.darts, d.fst = v := by
  have ha : a ∈ p.darts.map (fun d : G.Dart => d.fst) := by
    cases p with
    | nil => exact (hp.ne_nil rfl).elim
    | cons h q => simp [Walk.darts_cons]
  rw [← p.map_fst_darts_append] at hv
  simp only [List.mem_append, List.mem_singleton] at hv
  have hm : v ∈ p.darts.map (fun d : G.Dart => d.fst) := hv.elim id (fun h => h ▸ ha)
  exact List.mem_map.mp hm

private lemma cycle_out_unique {a : V} {p : G.Walk a a} (hp : p.IsCycle)
    {d e : G.Dart} (hd : d ∈ p.darts) (he : e ∈ p.darts) (h : d.fst = e.fst) : d = e :=
  List.inj_on_of_nodup_map (cycle_fst_nodup hp) hd he h

private lemma cycle_no_reverse {a : V} {p : G.Walk a a} (hp : p.IsCycle)
    {d : G.Dart} (hd : d ∈ p.darts) : d.symm ∉ p.darts := by
  intro he
  have h := List.inj_on_of_nodup_map hp.isCircuit.isTrail.edges_nodup hd he
    (show d.edge = d.symm.edge by simp)
  have hh := congrArg (fun d : G.Dart => d.fst) h
  exact G.ne_of_adj d.adj hh

private def CycleArc {a : V} (p : G.Walk a a) (u v : V) : Prop :=
  ∃ d ∈ p.darts, d.fst = u ∧ d.snd = v

private lemma cycle_arc_asymm {a u v : V} {p : G.Walk a a} (hp : p.IsCycle)
    (h : CycleArc p u v) : ¬ CycleArc p v u := by
  rintro ⟨d, hd, hdu, hdv⟩
  obtain ⟨e, he, heu, hev⟩ := h
  have hde : d = e.symm := by
    apply SimpleGraph.Dart.ext
    exact Prod.ext (hdu.trans hev.symm) (hdv.trans heu.symm)
  exact cycle_no_reverse hp he (hde ▸ hd)

private lemma cycle_arc_total {a u v : V} {p : G.Walk a a}
    (h : p.toSubgraph.Adj u v) : CycleArc p u v ∨ CycleArc p v u := by
  have hm : s(u,v) ∈ p.edges := (p.mem_edges_toSubgraph).mp h
  obtain ⟨d, hd, he⟩ := List.mem_map.mp hm
  have hv : d.fst = u ∧ d.snd = v ∨ d.fst = v ∧ d.snd = u := by
    exact SimpleGraph.dart_edge_eq_mk'_iff'.mp he
  rcases hv with hv | hv
  · exact Or.inl ⟨d, hd, hv⟩
  · exact Or.inr ⟨d, hd, hv⟩

/-- Every finite simple graph of degree exactly two admits a directed cycle
orientation: each edge receives opposite Boolean values and each vertex has
exactly one outgoing edge. No nonemptiness assumption is made. -/
theorem two_regular_orientation [Finite V] (G : SimpleGraph V)
    (htwo : ∀ v, ∃ a b, a ≠ b ∧ ∀ w, G.Adj v w ↔ w = a ∨ w = b) :
    ∃ o : V → V → Bool,
      (∀ ⦃u v⦄, G.Adj u v → o u v ≠ o v u) ∧
      ∀ v, ∃! w, G.Adj v w ∧ o v w = true := by
  classical
  letI := Fintype.ofFinite V
  have hcyc : G.IsCycles := by
    intro v _
    obtain ⟨a,b,hab,hh⟩ := htwo v
    apply Set.ncard_eq_two.mpr
    refine ⟨a,b,hab,?_⟩
    ext w
    exact hh w
  have hn : ∀ v, (G.neighborSet v).Nonempty := by
    intro v
    obtain ⟨a,b,hab,hh⟩ := htwo v
    exact ⟨a, (hh a).mpr (Or.inl rfl)⟩
  let r : G.ConnectedComponent → V := fun c => Classical.choose c.exists_rep
  have hr : ∀ c, r c ∈ c.supp := fun c => Classical.choose_spec c.exists_rep
  have hc := fun c => hcyc.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp (hr c) (hn (r c))
  choose p hp hs using hc
  let o : V → V → Bool := fun u v => decide (CycleArc (p (G.connectedComponentMk u)) u v)
  refine ⟨o, ?_, ?_⟩
  · intro u v huv
    have heq := ConnectedComponent.connectedComponentMk_eq_of_adj huv
    have hmem : u ∈ (p (G.connectedComponentMk u)).toSubgraph.verts := by
      rw [hs]
      exact rfl
    have hadj := (hp (G.connectedComponentMk u)).adj_toSubgraph_iff_of_isCycles hcyc hmem v |>.mpr huv
    have ht := cycle_arc_total hadj
    dsimp [o]
    rw [← heq]
    rcases ht with ht | ht
    · simp [ht, cycle_arc_asymm (hp (G.connectedComponentMk u)) ht]
    · have hnot := cycle_arc_asymm (hp (G.connectedComponentMk u)) ht
      simp [ht, hnot]
  · intro v
    have hmem : v ∈ (p (G.connectedComponentMk v)).support := by
      apply (p (G.connectedComponentMk v)).mem_verts_toSubgraph.mp
      rw [hs]
      exact rfl
    obtain ⟨d,hd,hv⟩ := cycle_out_exists (hp (G.connectedComponentMk v)) hmem
    refine ⟨d.snd, ⟨hv ▸ d.adj, ?_⟩, ?_⟩
    · change decide (CycleArc _ _ _) = true
      simp only [decide_eq_true_eq]
      exact ⟨d,hd,hv,rfl⟩
    · intro w hw
      have harc : CycleArc (p (G.connectedComponentMk v)) v w := by
        exact of_decide_eq_true hw.2
      obtain ⟨e,he,hev,hew⟩ := harc
      have heq := cycle_out_unique (hp (G.connectedComponentMk v)) he hd (hev.trans hv.symm)
      exact hew.symm.trans (congrArg (fun d : G.Dart => d.snd) heq)

/-- Keep precisely the edges whose endpoints lie on the same side. -/
def sameSide (G : SimpleGraph V) (side : V → Bool) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ side u = side v
  symm := by intro u v h; exact ⟨h.1.symm, h.2.symm⟩
  loopless := by intro v h; exact G.loopless v h.1

/-- Removing the perfect matching cut from a cubic graph leaves degree two. -/
theorem sameSide_two_regular (G : SimpleGraph V) (hG : Cubic G) (side : V → Bool)
    (hside : ∀ v, ∃! w, G.Adj v w ∧ side v ≠ side w) :
    ∀ v, ∃ a b, a ≠ b ∧ ∀ w, (sameSide G side).Adj v w ↔ w = a ∨ w = b := by
  intro v
  obtain ⟨a,b,c,hab,hac,hbc,hh⟩ := hG v
  obtain ⟨m,hm,hu⟩ := hside v
  have heq : ∀ x, G.Adj v x → x ≠ m → side v = side x := by
    intro x hx hxm
    by_contra hs
    exact hxm (hu x ⟨hx,hs⟩)
  rcases (hh m).mp hm.1 with hma | hmb | hmc
  · subst m
    have hb := heq b ((hh b).mpr (Or.inr (Or.inl rfl))) hab.symm
    have hc := heq c ((hh c).mpr (Or.inr (Or.inr rfl))) hac.symm
    refine ⟨b,c,hbc,?_⟩
    intro w
    change (G.Adj v w ∧ side v = side w) ↔ _
    rw [hh w]
    constructor
    · rintro ⟨hw,hs⟩
      rcases hw with hw | hw | hw
      · exact (hm.2 (hw ▸ hs)).elim
      · exact Or.inl hw
      · exact Or.inr hw
    · rintro (rfl | rfl)
      · exact ⟨Or.inr (Or.inl rfl), hb⟩
      · exact ⟨Or.inr (Or.inr rfl), hc⟩
  · subst m
    have ha := heq a ((hh a).mpr (Or.inl rfl)) hab
    have hc := heq c ((hh c).mpr (Or.inr (Or.inr rfl))) hbc.symm
    refine ⟨a,c,hac,?_⟩
    intro w
    change (G.Adj v w ∧ side v = side w) ↔ _
    rw [hh w]
    constructor
    · rintro ⟨hw,hs⟩
      rcases hw with hw | hw | hw
      · exact Or.inl hw
      · exact (hm.2 (hw ▸ hs)).elim
      · exact Or.inr hw
    · rintro (rfl | rfl)
      · exact ⟨Or.inl rfl, ha⟩
      · exact ⟨Or.inr (Or.inr rfl), hc⟩
  · subst m
    have ha := heq a ((hh a).mpr (Or.inl rfl)) hac
    have hb := heq b ((hh b).mpr (Or.inr (Or.inl rfl))) hbc
    refine ⟨a,b,hab,?_⟩
    intro w
    change (G.Adj v w ∧ side v = side w) ↔ _
    rw [hh w]
    constructor
    · rintro ⟨hw,hs⟩
      rcases hw with hw | hw | hw
      · exact Or.inl hw
      · exact Or.inr hw
      · exact (hm.2 (hw ▸ hs)).elim
    · rintro (rfl | rfl)
      · exact ⟨Or.inl rfl, ha⟩
      · exact ⟨Or.inr (Or.inl rfl), hb⟩

end Antony24
