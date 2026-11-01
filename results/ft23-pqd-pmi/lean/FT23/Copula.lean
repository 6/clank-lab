import FT23.Definitions
import FT23.ConvexDifference

/- A derivative-free closed-square proof. GeneratorAdmissible.lean discharges its
   named core hypotheses for the exact generator; no copula theorem is assumed. -/
noncomputable section
open Set
namespace FT23

lemma C_nonnegative (hp : ∀ t, 0 ≤ psi t) (u v : ℝ) : 0 ≤ C u v := by
  unfold C
  split
  · exact hp _
  · exact le_rfl

lemma C_comm (u v : ℝ) : C u v = C v u := by
  simp only [C, and_comm, add_comm]

lemma C_monotone_right
    (hf : AntitoneOn phi (Ioc (0:ℝ) 1)) (hp : Antitone psi)
    (hn : ∀ t, 0 ≤ psi t)
    {u v w : ℝ} (hu : u ∈ Icc (0:ℝ) 1)
    (hv : v ∈ Icc (0:ℝ) 1) (hw : w ∈ Icc (0:ℝ) 1) (hvw : v ≤ w) :
    C u v ≤ C u w := by
  by_cases hu0 : u = 0
  · simp [C, hu0]
  have hu' : 0 < u := lt_of_le_of_ne hu.1 (Ne.symm hu0)
  by_cases hv0 : v = 0
  · simpa [C, hv0] using C_nonnegative hn u w
  have hv' : 0 < v := lt_of_le_of_ne hv.1 (Ne.symm hv0)
  have hw' : 0 < w := lt_of_lt_of_le hv' hvw
  rw [C, if_pos ⟨hu', hv'⟩, C, if_pos ⟨hu', hw'⟩]
  exact hp (add_le_add_left (hf ⟨hv', hv.2⟩ ⟨hw', hw.2⟩ hvw) _)

lemma C_monotone_left
    (hf : AntitoneOn phi (Ioc (0:ℝ) 1)) (hp : Antitone psi)
    (hn : ∀ t, 0 ≤ psi t)
    {u v w : ℝ} (hu : u ∈ Icc (0:ℝ) 1)
    (hv : v ∈ Icc (0:ℝ) 1) (hw : w ∈ Icc (0:ℝ) 1) (hvw : v ≤ w) :
    C v u ≤ C w u := by
  rw [C_comm v u, C_comm w u]
  exact C_monotone_right hf hp hn hu hv hw hvw

theorem copula_of_core
    (hc : ConvexOn ℝ univ psi)
    (hf : AntitoneOn phi (Ioc (0:ℝ) 1)) (hp : Antitone psi)
    (hn : ∀ t, 0 ≤ psi t) (hone : phi 1 = 0)
    (hinv : ∀ u ∈ Ioc (0:ℝ) 1, psi (phi u) = u) : IsCopula C := by
  constructor
  · intro v hv; simp [C]
  · intro u hu; simp [C]
  · intro v hv
    by_cases hz : v = 0
    · simp [C, hz]
    have hv' : 0 < v := lt_of_le_of_ne hv.1 (Ne.symm hz)
    simp [C, hv', hone, hinv v ⟨hv', hv.2⟩]
  · intro u hu
    rw [C_comm]
    by_cases hz : u = 0
    · simp [C, hz]
    have hu' : 0 < u := lt_of_le_of_ne hu.1 (Ne.symm hz)
    simp [C, hu', hone, hinv u ⟨hu', hu.2⟩]
  · intro a ha b hb d hd e he hab hde
    by_cases ha0 : a = 0
    · by_cases hd0 : d = 0
      · simpa [delta, C, ha0, hd0] using C_nonnegative hn b e
      · have hm := C_monotone_right hf hp hn hb hd he hde
        simpa [delta, C, ha0] using sub_nonneg.mpr hm
    by_cases hd0 : d = 0
    · have hm := C_monotone_left hf hp hn he ha hb hab
      simpa [delta, C, hd0] using sub_nonneg.mpr hm
    have ha' : 0 < a := lt_of_le_of_ne ha.1 (Ne.symm ha0)
    have hb' : 0 < b := lt_of_lt_of_le ha' hab
    have hd' : 0 < d := lt_of_le_of_ne hd.1 (Ne.symm hd0)
    have he' : 0 < e := lt_of_lt_of_le hd' hde
    have h := convex_ordered_rectangle hc
      (hf ⟨ha', ha.2⟩ ⟨hb', hb.2⟩ hab) (hf ⟨hd', hd.2⟩ ⟨he', he.2⟩ hde)
    simpa [delta, C, ha', hb', hd', he'] using h

end FT23
