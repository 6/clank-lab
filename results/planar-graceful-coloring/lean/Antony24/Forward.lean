import Antony24.Basic
import Antony24.Local
import Antony24.Counting

/-! The forward implication, for every finite cubic graph. -/
namespace Antony24
variable {V : Type*} {G : SimpleGraph V}

noncomputable def port (c : SubVertex G → Colour) (v w : V) : ℕ := by
  classical
  exact if h : G.Adj v w then diff (c (.inl v)) (c (.inr ⟨(v,w),h⟩)) else 0

@[simp] theorem port_eq (c : SubVertex G → Colour) {v w : V} (h : G.Adj v w) :
    port c v w = diff (c (.inl v)) (c (.inr ⟨(v,w),h⟩)) := by
  classical
  simp [port, h]

theorem dart_eq_of_src_dst {d e : Dart G} (hs : d.val.1 = e.val.1)
    (ht : d.val.2 = e.val.2) : d = e := by
  apply Subtype.ext
  exact Prod.ext hs ht

theorem orig_star (c : SubVertex G → Colour) (hc : IsGraceful (S2 G) c)
    {v a b d : V} (ha : G.Adj v a) (hb : G.Adj v b) (hd : G.Adj v d)
    (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d) :
    StarOK (c (.inl v)) (c (.inr ⟨(v,a),ha⟩))
      (c (.inr ⟨(v,b),hb⟩)) (c (.inr ⟨(v,d),hd⟩)) := by
  have hn {w z : V} (hw : G.Adj v w) (hz : G.Adj v z) (h : w ≠ z) :
      (Sum.inr (⟨(v,w),hw⟩ : Dart G) : SubVertex G) ≠ .inr ⟨(v,z),hz⟩ := by
    intro q
    exact h (congrArg (fun x : Dart G => x.val.2) (Sum.inr.inj q))
  exact ⟨hc.1 rfl, hc.1 rfl, hc.1 rfl,
    hc.2 rfl rfl (hn ha hb hab), hc.2 rfl rfl (hn ha hd had),
    hc.2 rfl rfl (hn hb hd hbd)⟩

theorem orig_extreme (hg : Cubic G) (c : SubVertex G → Colour)
    (hc : IsGraceful (S2 G) c) (v : V) : Extreme (c (.inl v)) := by
  obtain ⟨a,b,d,hab,had,hbd,hn⟩ := hg v
  exact star_extreme _ _ _ _ (orig_star c hc
    ((hn a).2 (Or.inl rfl)) ((hn b).2 (Or.inr (Or.inl rfl)))
    ((hn d).2 (Or.inr (Or.inr rfl))) hab had hbd)

theorem unique_port (hg : Cubic G) (c : SubVertex G → Colour)
    (hc : IsGraceful (S2 G) c) (v : V) (k : ℕ)
    (hk : k = 1 ∨ k = 2 ∨ k = 3) : ∃! w, G.Adj v w ∧ port c v w = k := by
  classical
  obtain ⟨a,b,d,hab,had,hbd,hn⟩ := hg v
  have ha := (hn a).2 (Or.inl rfl)
  have hb := (hn b).2 (Or.inr (Or.inl rfl))
  have hd := (hn d).2 (Or.inr (Or.inr rfl))
  have st := star_ports _ _ _ _ (orig_star c hc ha hb hd hab had hbd)
  have hp : port c v a = k ∨ port c v b = k ∨ port c v d = k := by
    simp only [port_eq c ha, port_eq c hb, port_eq c hd]
    rcases st with h|h|h|h|h|h <;> omega
  have hex : ∃ w, G.Adj v w ∧ port c v w = k := by
    rcases hp with h|h|h
    · exact ⟨a,ha,h⟩
    · exact ⟨b,hb,h⟩
    · exact ⟨d,hd,h⟩
  obtain ⟨w,hw,hpw⟩ := hex
  refine ⟨w,⟨hw,hpw⟩,?_⟩
  rintro z ⟨hz,hpz⟩
  by_contra hzw
  have hne : (Sum.inr (⟨(v,z),hz⟩ : Dart G) : SubVertex G) ≠ .inr ⟨(v,w),hw⟩ := by
    intro q
    exact hzw (congrArg (fun x : Dart G => x.val.2) (Sum.inr.inj q))
  have he := hc.2 (show (S2 G).Adj (.inl v) (.inr ⟨(v,z),hz⟩) from rfl)
    (show (S2 G).Adj (.inl v) (.inr ⟨(v,w),hw⟩) from rfl) hne
  apply he
  simpa only [← port_eq c hz, ← port_eq c hw] using hpz.trans hpw.symm

theorem subdivided_path (c : SubVertex G → Colour)
    (hc : IsGraceful (S2 G) c) {v w : V} (h : G.Adj v w) :
    PathOK (c (.inl v)) (c (.inr ⟨(v,w),h⟩))
      (c (.inr ⟨(w,v),h.symm⟩)) (c (.inl w)) := by
  have hmid : (S2 G).Adj (.inr ⟨(v,w),h⟩) (.inr ⟨(w,v),h.symm⟩) := rfl
  have hrev : (S2 G).Adj (.inr ⟨(w,v),h.symm⟩) (.inr ⟨(v,w),h⟩) := rfl
  refine ⟨hc.1 rfl, hc.1 hmid, hc.1 rfl, ?_, ?_⟩
  · have hq := hc.2 (show (S2 G).Adj (.inr ⟨(v,w),h⟩) (.inl v) from rfl)
      hmid (by intro q; cases q)
    simpa [diff, Nat.dist_comm] using hq
  · have hq := hc.2 hrev
      (show (S2 G).Adj (.inr ⟨(w,v),h.symm⟩) (.inl w) from rfl)
      (by intro q; cases q)
    simpa [diff, Nat.dist_comm] using hq

/-- Faithful all-instance forward theorem, including empty cubic graphs. -/
theorem graceful4_s2_implies_pmc [Finite V] (hg : Cubic G) : Graceful4 (S2 G) → PMC G := by
  classical
  rintro ⟨c,hc⟩
  have he := orig_extreme hg c hc
  have hu := unique_port hg c hc
  have h13 : ∀ v w, G.Adj v w → port c v w = 1 → port c w v = 3 := by
    intro v w h hp
    have ht := path_one_three _ _ _ _ (he v) (he w) (subdivided_path c hc h)
    simpa only [← port_eq c h.symm] using ht (by simpa only [port_eq c h] using hp)
  have h31 := no_two_three G (port c) (fun v => hu v 1 (Or.inl rfl))
    (fun v => hu v 3 (Or.inr (Or.inr rfl))) h13
  have hopp {v w : V} (h : G.Adj v w) :
      c (.inl v) ≠ c (.inl w) ↔ port c v w = 2 := by
    have ht := path_opposite_iff _ _ _ _ (he v) (he w) (subdivided_path c hc h)
    simp only [← port_eq c h, ← port_eq c h.symm] at ht
    refine ⟨fun q => (ht.mp q).1, fun hp => ht.mpr ⟨hp,?_⟩⟩
    have hcases := path_two_cases _ _ _ _ (he v) (he w) (subdivided_path c hc h)
    simp only [← port_eq c h, ← port_eq c h.symm] at hcases
    rcases hcases hp with q|q
    · exact q
    · have bad := h31 w v h.symm q
      omega
  let side : V → Bool := fun v => decide (c (.inl v) = 0)
  have hs (v w : V) : side v ≠ side w ↔ c (.inl v) ≠ c (.inl w) := by
    dsimp [side]
    rcases he v with hv|hv <;> rcases he w with hw|hw <;> simp [hv,hw]
  refine ⟨side, fun v => ?_⟩
  obtain ⟨w,hw,uniq⟩ := hu v 2 (Or.inr (Or.inl rfl))
  refine ⟨w,⟨hw.1,(hs v w).2 ((hopp hw.1).2 hw.2)⟩,?_⟩
  rintro z ⟨hz,hsz⟩
  exact uniq z ⟨hz,(hopp hz).1 ((hs v z).1 hsz)⟩

#print axioms graceful4_s2_implies_pmc
end Antony24
