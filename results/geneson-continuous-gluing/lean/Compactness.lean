import Gluing


noncomputable section
open Set Topology
namespace Geneson

abbrev BoundedMaps (R : Set Plane) (l u : ℝ) :=
  (X R → Icc l u) × (Y R → Icc l u)

def forget {R : Set Plane} {l u : ℝ} (w : BoundedMaps R l u) : Maps R :=
  (fun x => (w.1 x : ℝ), fun y => (w.2 y : ℝ))

def WitnessSpace (R K : Set Plane) (l u : ℝ) : Set (BoundedMaps R l u) :=
  {w | IsWitness R K (forget w)}

lemma continuous_imagePoint {R : Set Plane} {l u : ℝ} (p : R) :
    Continuous (fun w : BoundedMaps R l u => ImagePoint (forget w) p) := by
  exact ((continuous_apply _).comp continuous_fst).subtype_val.prodMk
    (((continuous_apply _).comp continuous_snd).subtype_val)

lemma isClosed_witnessSpace {R K : Set Plane} {l u : ℝ} (hK : IsClosed K) :
    IsClosed (WitnessSpace R K l u) := by
  have cx (x : X R) : Continuous (fun w : BoundedMaps R l u => (w.1 x : ℝ)) :=
    ((continuous_apply x).comp continuous_fst).subtype_val
  have cy (y : Y R) : Continuous (fun w : BoundedMaps R l u => (w.2 y : ℝ)) :=
    ((continuous_apply y).comp continuous_snd).subtype_val
  have hx : IsClosed {w : BoundedMaps R l u | Expands (forget w).1} := by
    simp only [Expands, forget, ofPred_forall]
    exact isClosed_iInter fun x => isClosed_iInter fun y =>
      isClosed_iInter fun _ => isClosed_le continuous_const ((cx y).sub (cx x))
  have hy : IsClosed {w : BoundedMaps R l u | Expands (forget w).2} := by
    simp only [Expands, forget, ofPred_forall]
    exact isClosed_iInter fun x => isClosed_iInter fun y =>
      isClosed_iInter fun _ => isClosed_le continuous_const ((cy y).sub (cy x))
  have hp : IsClosed {w : BoundedMaps R l u |
      ∀ p : R, ImagePoint (forget w) p ∈ K} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun p => hK.preimage (continuous_imagePoint p)
  exact hx.inter (hy.inter hp)

lemma isCompact_witnessSpace {R K : Set Plane} {l u : ℝ} (hK : IsClosed K) :
    IsCompact (WitnessSpace R K l u) :=
  (isClosed_witnessSpace hK).isCompact

end Geneson

namespace Geneson

lemma bounded_hasCopy_iff {R S : Set Plane} {l u : ℝ}
    (hS : S ⊆ Icc l u ×ˢ Icc l u) :
    HasCopy R S ↔ (WitnessSpace R S l u).Nonempty := by
  constructor
  · rintro ⟨w,hf,hg,hp⟩
    have hx : ∀ x : X R, w.1 x ∈ Icc l u := by
      rintro ⟨x,p,hpR,rfl⟩
      exact (hS (hp ⟨p,hpR⟩)).1
    have hy : ∀ y : Y R, w.2 y ∈ Icc l u := by
      rintro ⟨y,p,hpR,rfl⟩
      exact (hS (hp ⟨p,hpR⟩)).2
    exact ⟨(fun x => ⟨w.1 x,hx x⟩, fun y => ⟨w.2 y,hy y⟩),hf,hg,hp⟩
  · rintro ⟨w,hw⟩
    exact ⟨forget w,hw⟩

lemma witnessSpace_mono {R S T : Set Plane} {l u : ℝ} (hST : S ⊆ T) :
    WitnessSpace R S l u ⊆ WitnessSpace R T l u := by
  rintro w ⟨hf,hg,hp⟩
  exact ⟨hf,hg,fun p => hST (hp p)⟩

/-- Compact avoidance admits an ambient-open collar; arbitrary projection domains. -/
lemma exists_open_avoiding_superset {R C : Set Plane} {n : ℝ}
    (hC : IsCompact C) (hCi : C ⊆ Ioo 0 n ×ˢ Ioo 0 n)
    (havoid : ¬ Contains R C) :
    ∃ O : Set Plane, IsOpen O ∧ C ⊆ O ∧ O ⊆ Square n ∧ ¬ Contains R O := by
  classical
  let interiorBox : Set Plane := Ioo 0 n ×ˢ Ioo 0 n
  let O : ℝ → Set Plane := fun ε => Metric.thickening ε C ∩ interiorBox
  have hOopen : ∀ ε, IsOpen (O ε) := fun ε =>
    Metric.isOpen_thickening.inter (isOpen_Ioo.prod isOpen_Ioo)
  have hOC : ∀ ε, 0 < ε → C ⊆ O ε := fun ε hε z hz =>
    ⟨Metric.self_subset_thickening hε C hz, hCi hz⟩
  have hOsq : ∀ ε, O ε ⊆ Square n := by
    intro ε z hz
    exact ⟨⟨hz.2.1.1.le,hz.2.1.2.le⟩,⟨hz.2.2.1.le,hz.2.2.2.le⟩⟩
  by_contra h
  have hcopy : ∀ ε, 0 < ε → Contains R (O ε) := by
    intro ε hε
    by_contra hn
    exact h ⟨O ε,hOopen ε,hOC ε hε,hOsq ε,hn⟩
  let T : {ε : ℝ // 0 < ε} → Set (BoundedMaps R 0 n) :=
    fun ε => WitnessSpace R (Metric.cthickening ε.1 C ∩ Square n) 0 n
  have hTclosed : ∀ ε, IsClosed (T ε) := fun ε =>
    isClosed_witnessSpace (Metric.isClosed_cthickening.inter (isClosed_Icc.prod isClosed_Icc))
  have hTnonempty : ∀ ε, (T ε).Nonempty := by
    intro ε
    apply (bounded_hasCopy_iff (inter_subset_right :
      Metric.cthickening ε.1 C ∩ Square n ⊆ Square n)).1
    apply hasCopy_mono (S := O ε.1) _ (contains_iff_hasCopy.1 (hcopy ε.1 ε.2))
    intro z hz
    exact ⟨Metric.thickening_subset_cthickening _ _ hz.1, hOsq _ hz⟩
  have hTdir : Directed (· ⊇ ·) T := by
    intro ε δ
    refine ⟨⟨min ε.1 δ.1, lt_min ε.2 δ.2⟩,?_,?_⟩
    · exact witnessSpace_mono (inter_subset_inter_left _ (Metric.cthickening_mono (min_le_left _ _) C))
    · exact witnessSpace_mono (inter_subset_inter_left _ (Metric.cthickening_mono (min_le_right _ _) C))
  obtain ⟨w,hw⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    T hTdir hTnonempty (fun ε => (hTclosed ε).isCompact) hTclosed
  have hwε : ∀ ε, w ∈ T ε := mem_iInter.1 hw
  have hw1 := hwε ⟨1,by norm_num⟩
  apply havoid
  apply contains_iff_hasCopy.2
  refine ⟨forget w,hw1.1,hw1.2.1,?_⟩
  intro p
  rw [← hC.isClosed.closure_eq, Metric.closure_eq_iInter_cthickening]
  exact mem_iInter.2 fun ε => mem_iInter.2 fun hε => (hwε ⟨ε,hε⟩).2.2 p |>.1

/-- The anchor set is a compact image of an arbitrary-index compact witness space. -/
lemma isCompact_anchorSet {P K : Set Plane} {n : ℝ} (p : P)
    (hK : IsCompact K) (hKsq : K ⊆ Square n) :
    IsCompact (AnchorSet P K p) := by
  classical
  have heq : AnchorSet P K p =
      (fun w : BoundedMaps P 0 n => ImagePoint (forget w) p) ''
        WitnessSpace P K 0 n := by
    ext z
    constructor
    · rintro ⟨w,hw,rfl⟩
      have hx : ∀ x : X P, w.1 x ∈ Icc 0 n := by
        rintro ⟨x,q,hq,rfl⟩
        exact (hKsq (hw.2.2 ⟨q,hq⟩)).1
      have hy : ∀ y : Y P, w.2 y ∈ Icc 0 n := by
        rintro ⟨y,q,hq,rfl⟩
        exact (hKsq (hw.2.2 ⟨q,hq⟩)).2
      exact ⟨(fun x => ⟨w.1 x,hx x⟩,fun y => ⟨w.2 y,hy y⟩),hw,rfl⟩
    · rintro ⟨w,hw,rfl⟩
      exact ⟨forget w,hw,rfl⟩
  rw [heq]
  exact (isCompact_witnessSpace hK.isClosed).image (continuous_imagePoint p)

end Geneson
