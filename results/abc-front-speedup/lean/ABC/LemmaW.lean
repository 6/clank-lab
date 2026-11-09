import ABC.LemmaWAux

/-!
# Lemma W, graph form

`P` and `Pinv` are mutually inverse continuous maps on `R = h(B̄(0, ρ))`. `h` is a bi-Lipschitz
chart, and the closed curves `h(C_s)`, `s ∈ K`, are `P`-invariant radial graphs with a Lipschitz
label. Then `w(a) = Leb{s ∈ K : a ∈ h(Int C_s)}` is a nonnegative, nonzero, Lipschitz,
`P`-invariant function supported in `h(B(0, ρ))`. Here `Int C_s = {r (cos ψ, sin ψ) : 0 ≤ r <
g(ψ, s)}`.
-/

open MeasureTheory Set Metric

noncomputable section

namespace ABC

open LemmaWAux

section Helpers

variable {h : OpenPartialHomeomorph (E 2) (E 2)} {ρ L : ℝ} {K : Set ℝ} {g : ℝ → ℝ → ℝ}

private lemma mem_image_Ins_iff (hsrc : closedBall (0 : E 2) ρ ⊆ h.source) {s : ℝ}
    (hs : Good g ρ s) {x : E 2} (hx : x ∈ closedBall (0 : E 2) ρ) :
    h x ∈ h '' Ins g s ↔ x ∈ Ins g s := by
  refine ⟨fun ⟨y, hy, hyx⟩ => ?_, fun hx' => ⟨x, hx', rfl⟩⟩
  have hy' : y ∈ closedBall (0 : E 2) ρ := ball_subset_closedBall (hs.Ins_subset_ball hy)
  rwa [← h.injOn (hsrc hy') (hsrc hx) hyx]

private lemma isOpen_image_Ins (hsrc : closedBall (0 : E 2) ρ ⊆ h.source)
    (hopen : IsOpen (h '' ball (0 : E 2) ρ)) {s : ℝ} (hs : Good g ρ s) :
    IsOpen (h '' Ins g s) := by
  have heq : h '' Ins g s = h '' ball 0 ρ ∩ h.symm ⁻¹' Ins g s := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨⟨x, hs.Ins_subset_ball hx, rfl⟩, ?_⟩
      rw [mem_preimage, h.left_inv (hsrc (ball_subset_closedBall (hs.Ins_subset_ball hx)))]
      exact hx
    · rintro ⟨⟨x, hx, rfl⟩, hy⟩
      rw [mem_preimage, h.left_inv (hsrc (ball_subset_closedBall hx))] at hy
      exact ⟨x, hy, rfl⟩
  rw [heq]
  refine ContinuousOn.isOpen_inter_preimage ?_ hopen hs.isOpen_Ins
  refine h.continuousOn_symm.mono ?_
  rintro _ ⟨x, hx, rfl⟩
  exact h.map_source (hsrc (ball_subset_closedBall hx))

/-- A map continuous and injective on `R`, fixing `h 0` and mapping onto `h C_s`, maps the
inside `h I_s` into itself. -/
private lemma maps_inside (hsrc : closedBall (0 : E 2) ρ ⊆ h.source)
    (hopen : IsOpen (h '' ball (0 : E 2) ρ)) {s : ℝ} (hs : Good g ρ s) {Q : E 2 → E 2}
    (hQ : ContinuousOn Q (h '' closedBall 0 ρ)) (hinj : InjOn Q (h '' closedBall 0 ρ))
    (hQC : h '' Crv g s ⊆ Q '' (h '' Crv g s)) (hfix : Q (h 0) = h 0) :
    Q '' (h '' Ins g s) ⊆ h '' Ins g s := by
  have hIb : Ins g s ⊆ closedBall 0 ρ := hs.Ins_subset_ball.trans ball_subset_closedBall
  have hClb : {u : E 2 | ‖u‖ ≤ G g s u} ⊆ closedBall 0 ρ := fun u hu =>
    mem_closedBall_zero_iff.2 (le_trans hu (hs.G_lt u).le)
  have hCb : Crv g s ⊆ closedBall 0 ρ := fun u hu => hClb (le_of_eq hu)
  have hconn : IsPreconnected (Q '' (h '' Ins g s)) :=
    (hs.isPreconnected_Ins.image h (h.continuousOn.mono (hIb.trans hsrc))).image Q
      (hQ.mono (image_mono hIb))
  have h0 : h 0 ∈ h '' Ins g s := ⟨0, hs.zero_mem_Ins, rfl⟩
  refine hconn.subset_of_closure_inter_subset (isOpen_image_Ins hsrc hopen hs)
    ⟨h 0, ⟨h 0, h0, hfix⟩, h0⟩ ?_
  rintro y ⟨hycl, ⟨x, ⟨x0, hx0, rfl⟩, rfl⟩⟩
  have hcl : closure (h '' Ins g s) ⊆ h '' {u : E 2 | ‖u‖ ≤ G g s u} :=
    closure_minimal (image_mono fun u hu => show ‖u‖ ≤ G g s u from le_of_lt hu)
      (hs.isCompact_Cl.image_of_continuousOn (h.continuousOn.mono (hClb.trans hsrc))).isClosed
  obtain ⟨z, hz, hzy⟩ := hcl hycl
  rcases (show ‖z‖ ≤ G g s z from hz).lt_or_eq with hz' | hz'
  · exact ⟨z, hz', hzy⟩
  · exfalso
    obtain ⟨_, ⟨z', hz'C, rfl⟩, hQz'⟩ := hQC ⟨z, hz', hzy⟩
    have h1 : h z' = h x0 :=
      hinj ⟨z', hCb hz'C, rfl⟩ ⟨x0, hIb hx0, rfl⟩ hQz'
    have h2 : z' = x0 := h.injOn (hsrc (hCb hz'C)) (hsrc (hIb hx0)) h1
    subst h2
    exact (ne_of_lt (show ‖z'‖ < G g s z' from hx0)) hz'C

/-- The labels of the curves crossed by a segment have measure at most `L` times its length. -/
private lemma volume_crossed_le (hK : ∀ s ∈ K, Good g ρ s)
    (hlab : ∀ s ∈ K, ∀ s' ∈ K, ∀ ψ ψ' : ℝ,
      |s - s'| ≤ L * dist (polarPt (g ψ s) ψ) (polarPt (g ψ' s') ψ')) (u v : E 2) :
    volume {s ∈ K | u ∈ Ins g s ∧ v ∉ Ins g s} ≤ ENNReal.ofReal (L * dist u v) := by
  classical
  let J : E 2 → ℝ := fun z => if hz : ∃ s ∈ K, z ∈ curve g s then hz.choose else 0
  have hJ : ∀ s ∈ K, ∀ z ∈ curve g s, J z = s := by
    intro s hs z hz
    have hz' : ∃ s ∈ K, z ∈ curve g s := ⟨s, hs, hz⟩
    have hJz : J z = hz'.choose := by simp only [J, hz', ↓reduceDIte]
    rw [hJz]
    obtain ⟨hs', ψ', hψ'⟩ := hz'.choose_spec
    obtain ⟨ψ, rfl⟩ := hz
    have := hlab _ hs' s hs ψ' ψ
    have hψ'' : polarPt (g ψ' hz'.choose) ψ' = polarPt (g ψ s) ψ := hψ'
    rw [hψ'', dist_self, mul_zero] at this
    exact sub_eq_zero.1 (abs_nonpos_iff.1 this)
  let p : ℝ → E 2 := fun t => u + t • (v - u)
  let D : Set ℝ := {t ∈ Icc (0 : ℝ) 1 | ∃ s ∈ K, p t ∈ curve g s}
  have hlip : LipschitzOnWith (Real.toNNReal (L * dist u v)) (J ∘ p) D := by
    refine LipschitzOnWith.of_dist_le' fun t ht t' ht' => ?_
    obtain ⟨-, s, hs, hst⟩ := ht
    obtain ⟨-, s', hs', hst'⟩ := ht'
    simp only [Function.comp, hJ s hs _ hst, hJ s' hs' _ hst', Real.dist_eq]
    obtain ⟨ψ, hψ⟩ := hst
    obtain ⟨ψ', hψ'⟩ := hst'
    have hpp : dist (p t) (p t') = |t - t'| * dist u v := by
      simp only [p, dist_eq_norm, add_sub_add_left_eq_sub, ← sub_smul, norm_smul,
        Real.norm_eq_abs, norm_sub_rev v u]
    calc |s - s'| ≤ L * dist (p t) (p t') := by rw [← hψ, ← hψ']; exact hlab s hs s' hs' ψ ψ'
      _ = L * dist u v * |t - t'| := by rw [hpp]; ring
  have hsub : {s ∈ K | u ∈ Ins g s ∧ v ∉ Ins g s} ⊆ (J ∘ p) '' D := by
    rintro s ⟨hs, hu, hv⟩
    obtain ⟨t, ht, htC⟩ := (hK s hs).exists_Crv hu hv
    rw [(hK s hs).Crv_eq] at htC
    exact ⟨t, ⟨ht, s, hs, htC⟩, hJ s hs _ htC⟩
  calc volume {s ∈ K | u ∈ Ins g s ∧ v ∉ Ins g s} ≤ volume ((J ∘ p) '' D) := measure_mono hsub
    _ = μH[1] ((J ∘ p) '' D) := by rw [hausdorffMeasure_real]
    _ ≤ (Real.toNNReal (L * dist u v) : ENNReal) ^ (1 : ℝ) * μH[1] D :=
        hlip.hausdorffMeasure_image_le zero_le_one
    _ ≤ (Real.toNNReal (L * dist u v) : ENNReal) * 1 := by
        rw [ENNReal.rpow_one, hausdorffMeasure_real]
        gcongr
        calc volume D ≤ volume (Icc (0 : ℝ) 1) := measure_mono fun t ht => ht.1
          _ = 1 := by simp
    _ = ENNReal.ofReal (L * dist u v) := by rw [mul_one]; rfl

end Helpers

theorem lemmaW {P Pinv : E 2 → E 2} {h : OpenPartialHomeomorph (E 2) (E 2)} {ρ L : ℝ}
    {K : Set ℝ} {g : ℝ → ℝ → ℝ}
    (hρ : 0 < ρ) (hL : 0 < L) (hsrc : closedBall (0 : E 2) ρ ⊆ h.source)
    (hbil : ∀ u ∈ closedBall (0 : E 2) ρ, ∀ v ∈ closedBall (0 : E 2) ρ,
      dist (h u) (h v) ≤ L * dist u v ∧ dist u v ≤ L * dist (h u) (h v))
    (hK : IsCompact K) (hKpos : 0 < volume K)
    (hg : ∀ s ∈ K, Continuous (fun ψ => g ψ s) ∧ (∀ ψ, g (ψ + 2 * Real.pi) s = g ψ s) ∧
      ∀ ψ, 0 < g ψ s ∧ g ψ s < ρ)
    (hlab : ∀ s ∈ K, ∀ s' ∈ K, ∀ ψ ψ' : ℝ,
      |s - s'| ≤ L * dist (polarPt (g ψ s) ψ) (polarPt (g ψ' s') ψ'))
    (hP : ContinuousOn P (h '' closedBall 0 ρ)) (hPinv : ContinuousOn Pinv (h '' closedBall 0 ρ))
    (hPPinv : ∀ a ∈ h '' closedBall 0 ρ, P (Pinv a) = a)
    (hPinvP : ∀ a ∈ h '' closedBall 0 ρ, Pinv (P a) = a)
    (hinv : ∀ s ∈ K, P '' (h '' curve g s) = h '' curve g s)
    (hfix : P (h 0) = h 0) :
    ∃ w : E 2 → ℝ, (∃ C, LipschitzWith C w) ∧ (∀ a, 0 ≤ w a) ∧ w (h 0) ≠ 0 ∧
      (∀ a, w a ≠ 0 → a ∈ h '' ball 0 ρ) ∧
      (∀ a ∈ h '' closedBall 0 ρ, w (P a) = w a) ∧
      (∀ a ∈ h '' closedBall 0 ρ, w (Pinv a) = w a) := by
  classical
  have hKg : ∀ s ∈ K, Good g ρ s := hg
  have hopen : IsOpen (h '' ball (0 : E 2) ρ) :=
    h.isOpen_image_of_subset_source isOpen_ball (ball_subset_closedBall.trans hsrc)
  let R := h '' closedBall (0 : E 2) ρ
  let S : E 2 → Set ℝ := fun a => {s ∈ K | a ∈ h '' Ins g s}
  let w : E 2 → ℝ := fun a => (volume (S a)).toReal
  have hKfin : volume K ≠ ⊤ := hK.measure_lt_top.ne
  have hSfin : ∀ a, volume (S a) ≠ ⊤ := fun a =>
    ne_top_of_le_ne_top hKfin (measure_mono (sep_subset _ _))
  have hw_nonneg : ∀ a, 0 ≤ w a := fun a => ENNReal.toReal_nonneg
  have h0R : (0 : E 2) ∈ closedBall (0 : E 2) ρ := mem_closedBall_self hρ.le
  have h0R' : h 0 ∈ R := ⟨0, h0R, rfl⟩
  have hballR : h '' ball (0 : E 2) ρ ⊆ R := image_mono ball_subset_closedBall
  have hw_out : ∀ a, a ∉ h '' ball 0 ρ → w a = 0 := by
    intro a ha
    have : S a = ∅ := by
      ext s
      simp only [S, mem_sep_iff, mem_empty_iff_false, iff_false, not_and]
      exact fun hs haI => ha (image_mono (hKg s hs).Ins_subset_ball haI)
    simp [w, this]
  -- the estimate inside `R`, from the chart
  have hin : ∀ a ∈ R, ∀ b ∈ R, w a ≤ w b + L ^ 2 * dist a b := by
    rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    have hsub : S (h u) ⊆ S (h v) ∪ {s ∈ K | u ∈ Ins g s ∧ v ∉ Ins g s} := by
      rintro s ⟨hs, has⟩
      rw [mem_image_Ins_iff hsrc (hKg s hs) hu] at has
      by_cases hvs : v ∈ Ins g s
      · exact Or.inl ⟨hs, (mem_image_Ins_iff hsrc (hKg s hs) hv).2 hvs⟩
      · exact Or.inr ⟨hs, has, hvs⟩
    have h1 : volume (S (h u)) ≤
        volume (S (h v)) + ENNReal.ofReal (L ^ 2 * dist (h u) (h v)) := by
      calc volume (S (h u))
          ≤ volume (S (h v)) + volume {s ∈ K | u ∈ Ins g s ∧ v ∉ Ins g s} :=
            (measure_mono hsub).trans (measure_union_le _ _)
        _ ≤ volume (S (h v)) + ENNReal.ofReal (L * dist u v) := by
            gcongr; exact volume_crossed_le hKg hlab u v
        _ ≤ _ := by
            refine add_le_add_right (ENNReal.ofReal_le_ofReal ?_) _
            calc L * dist u v ≤ L * (L * dist (h u) (h v)) := by
                  gcongr; exact (hbil u hu v hv).2
              _ = L ^ 2 * dist (h u) (h v) := by ring
    have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hSfin _, ENNReal.ofReal_ne_top⟩) h1
    rwa [ENNReal.toReal_add (hSfin _) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (by positivity)] at this
  have hRclosed : IsClosed R :=
    ((isCompact_closedBall (0 : E 2) ρ).image_of_continuousOn (h.continuousOn.mono hsrc)).isClosed
  -- the estimate everywhere: a segment leaving `R` crosses `h '' sphere 0 ρ`, where `w = 0`
  have hall : ∀ a b, w a ≤ w b + L ^ 2 * dist a b := by
    intro a b
    by_cases ha : a ∈ R
    · by_cases hb : b ∈ R
      · exact hin a ha b hb
      obtain ⟨c, hcseg, z, hz, rfl⟩ : ∃ c ∈ segment ℝ a b, c ∈ h '' sphere 0 ρ := by
        by_contra hne
        push Not at hne
        have hsub : segment ℝ a b ⊆ h '' ball 0 ρ ∪ Rᶜ := by
          intro c hc
          by_cases hcR : c ∈ R
          · obtain ⟨z, hz, rfl⟩ := hcR
            left
            refine ⟨z, ?_, rfl⟩
            rcases (mem_closedBall_zero_iff.1 hz).lt_or_eq with hz' | hz'
            · exact mem_ball_zero_iff.2 hz'
            · exact absurd ⟨z, mem_sphere_zero_iff_norm.2 hz', rfl⟩ (hne _ hc)
          · exact Or.inr hcR
        have haU : a ∈ h '' ball 0 ρ := by
          rcases hsub (left_mem_segment ℝ a b) with h' | h'
          · exact h'
          · exact absurd ha h'
        obtain ⟨x, -, hx1, hx2⟩ := (convex_segment a b).isPreconnected _ _ hopen
          hRclosed.isOpen_compl hsub ⟨a, left_mem_segment ℝ a b, haU⟩
          ⟨b, right_mem_segment ℝ a b, hb⟩
        exact hx2 (hballR hx1)
      have hzR : z ∈ closedBall (0 : E 2) ρ := sphere_subset_closedBall hz
      have hwc : w (h z) = 0 := by
        apply hw_out
        rintro ⟨y, hy, hyz⟩
        have := h.injOn (hsrc (ball_subset_closedBall hy)) (hsrc hzR) hyz
        rw [this, mem_ball_zero_iff, mem_sphere_zero_iff_norm.1 hz] at hy
        exact lt_irrefl _ hy
      have hdist : dist a (h z) ≤ dist a b := by
        have := (convex_closedBall a (dist a b)).segment_subset
          (mem_closedBall_self dist_nonneg) (by rw [mem_closedBall, dist_comm]) hcseg
        rwa [mem_closedBall, dist_comm] at this
      calc w a ≤ w (h z) + L ^ 2 * dist a (h z) := hin a ha _ ⟨z, hzR, rfl⟩
        _ ≤ w b + L ^ 2 * dist a b := by
            rw [hwc, zero_add]
            exact le_add_of_nonneg_of_le (hw_nonneg b)
              (mul_le_mul_of_nonneg_left hdist (sq_nonneg L))
    · rw [hw_out a fun h' => ha (hballR h')]
      exact add_nonneg (hw_nonneg b) (by positivity)
  -- invariance
  have hPinj : InjOn P R := fun a ha b hb hab => by
    rw [← hPinvP a ha, ← hPinvP b hb, hab]
  have hPinvinj : InjOn Pinv R := fun a ha b hb hab => by
    rw [← hPPinv a ha, ← hPPinv b hb, hab]
  have hfix' : Pinv (h 0) = h 0 := by
    calc Pinv (h 0) = Pinv (P (h 0)) := by rw [hfix]
      _ = h 0 := hPinvP _ h0R'
  have hCR : ∀ s ∈ K, h '' curve g s ⊆ R := fun s hs => image_mono fun u hu =>
    mem_closedBall_zero_iff.2 (by
      rw [← (hKg s hs).Crv_eq] at hu
      exact (le_of_eq hu).trans ((hKg s hs).G_lt u).le)
  have hPin : ∀ s ∈ K, P '' (h '' Ins g s) ⊆ h '' Ins g s := fun s hs =>
    maps_inside hsrc hopen (hKg s hs) hP hPinj
      (by rw [(hKg s hs).Crv_eq, hinv s hs]) hfix
  have hPinvin : ∀ s ∈ K, Pinv '' (h '' Ins g s) ⊆ h '' Ins g s := by
    intro s hs
    refine maps_inside hsrc hopen (hKg s hs) hPinv hPinvinj ?_ hfix'
    rw [(hKg s hs).Crv_eq]
    intro y hy
    refine ⟨P y, ?_, hPinvP y (hCR s hs hy)⟩
    rw [← hinv s hs]
    exact mem_image_of_mem P hy
  have hSP : ∀ a ∈ R, S (P a) = S a := by
    intro a ha
    ext s
    refine and_congr_right fun hs => ⟨fun hPa => ?_, fun ha' => hPin s hs ⟨a, ha', rfl⟩⟩
    have := hPinvin s hs ⟨_, hPa, rfl⟩
    rwa [hPinvP a ha] at this
  have hSPinv : ∀ a ∈ R, S (Pinv a) = S a := by
    intro a ha
    ext s
    refine and_congr_right fun hs => ⟨fun hPa => ?_, fun ha' => hPinvin s hs ⟨a, ha', rfl⟩⟩
    have := hPin s hs ⟨_, hPa, rfl⟩
    rwa [hPPinv a ha] at this
  have hS0 : S (h 0) = K := by
    ext s
    exact ⟨fun hs => hs.1, fun hs => ⟨hs, 0, (hKg s hs).zero_mem_Ins, rfl⟩⟩
  refine ⟨w, ⟨_, LipschitzWith.of_le_add_mul' (L ^ 2) hall⟩, hw_nonneg, ?_, ?_, ?_, ?_⟩
  · show (volume (S (h 0))).toReal ≠ 0
    rw [hS0]
    exact (ENNReal.toReal_pos hKpos.ne' hKfin).ne'
  · intro a ha
    by_contra ha'
    exact ha (hw_out a ha')
  · intro a ha
    show (volume (S (P a))).toReal = (volume (S a)).toReal
    rw [hSP a ha]
  · intro a ha
    show (volume (S (Pinv a))).toReal = (volume (S a)).toReal
    rw [hSPinv a ha]

end ABC
