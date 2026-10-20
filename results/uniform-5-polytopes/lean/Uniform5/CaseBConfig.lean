import Uniform5.CaseBInputs
import Uniform5.CaseBRadius
import Mathlib.Data.List.GetD

/-!
# List configurations and the finite type-(i) radius API

These are bridges for the exact definitions in `CaseBInputs`, including its
choice-defined radius. No numerical separation input is proved here: the B2
corollary consumes a supplied `B2` and a geometric root/radius identity.
-/
noncomputable section
namespace Uniform5.CaseB
open Set InnerProductGeometry
open scoped BigOperators RealInnerProductSpace

/-- List sums, including repeated entries, equal the corresponding Fin sum. -/
theorem configArcSum_eq_arcSum (c : List ℝ) (S : ℝ) :
    configArcSum c S = arcSum (fun i : Fin c.length => Real.cos (Real.pi / c[i.val])) S := by
  exact (Fin.sum_univ_fun_getElem c
    (fun q => 2 * Real.arcsin (Real.cos (Real.pi / q) / S))).symm

private theorem foldr_max_le_bound (l : List ℝ) {M : ℝ} (h0 : 0 ≤ M)
    (hl : ∀ x ∈ l, x ≤ M) : l.foldr max 0 ≤ M := by
  induction l with
  | nil => exact h0
  | cons x l ih =>
    exact max_le (hl x (by simp)) (ih (fun y hy => hl y (by simp [hy])))

/-- The zero seed disappears for a nonempty list of positive entries. -/
theorem foldr_map_max_eq_maxCos {α : Type*} (c : List α) [NeZero c.length]
    (f : α → ℝ) (hf : ∀ x ∈ c, 0 < f x) :
    (c.map f).foldr max 0 = maxCos (fun i : Fin c.length => f c[i.val]) := by
  have hpos : ∀ i : Fin c.length, 0 < f c[i.val] :=
    fun i => hf c[i.val] (List.getElem_mem i.isLt)
  apply le_antisymm
  · apply foldr_max_le_bound _ (maxCos_pos hpos).le
    intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
    exact le_maxCos (fun j : Fin c.length => f c[j.val]) ⟨i, hi⟩
  · apply (Finset.sup'_le_iff Finset.univ_nonempty (fun i : Fin c.length => f c[i.val])).mpr
    intro i _
    exact List.le_max_of_le' 0
      (List.mem_map.mpr ⟨c[i.val], List.getElem_mem i.isLt, rfl⟩) le_rfl

/-- Real-parameter counterpart of the Nat polygon angle bounds. -/
theorem configEntryAngle_bounds {q : ℝ} (hq : 3 ≤ q) :
    0 < Real.pi / q ∧ Real.pi / q < Real.pi / 2 := by
  exact ⟨div_pos Real.pi_pos (by linarith),
    div_lt_div_of_pos_left Real.pi_pos (by norm_num) (by linarith)⟩

theorem configEntryCos_bounds {q : ℝ} (hq : 3 ≤ q) :
    0 < Real.cos (Real.pi / q) ∧ Real.cos (Real.pi / q) < 1 := by
  obtain ⟨h0, h1⟩ := configEntryAngle_bounds hq
  refine ⟨Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h1⟩, ?_⟩
  simpa using Real.cos_lt_cos_of_nonneg_of_le_pi (by norm_num : (0 : ℝ) ≤ 0)
    (by linarith [Real.pi_pos] : Real.pi / q ≤ Real.pi) h0

theorem configMax_eq_maxCos {c : List ℝ} [NeZero c.length]
    (hq : ∀ q ∈ c, 3 ≤ q) :
    configMax c = maxCos (fun i : Fin c.length => Real.cos (Real.pi / c[i.val])) :=
  foldr_map_max_eq_maxCos c _ (fun q hq' => (configEntryCos_bounds (hq q hq')).1)

/-- Direct Nat-list sum bridge requested by the computation interface. -/
theorem configArcSum_realConfig (c : List ℕ) (S : ℝ) :
    configArcSum (realConfig c) S =
      arcSum (fun i : Fin c.length => polygonCos c[i.val]) S := by
  rw [configArcSum, realConfig, List.map_map]
  exact (Fin.sum_univ_fun_getElem c
    (fun q => 2 * Real.arcsin (polygonCos q / S))).symm

/-- Direct Nat-list maximum bridge; nonemptiness is expressed by NeZero. -/
theorem configMax_realConfig {c : List ℕ} [NeZero c.length]
    (hq : ∀ q ∈ c, 3 ≤ q) :
    configMax (realConfig c) = maxCos (fun i : Fin c.length => polygonCos c[i.val]) := by
  rw [configMax, realConfig, List.map_map]
  exact foldr_map_max_eq_maxCos c polygonCos (fun q hq' => (polygonCos_bounds (hq q hq')).1)

theorem configRoot_iff_finite {c : List ℝ} [NeZero c.length]
    (hq : ∀ q ∈ c, 3 ≤ q) (S : ℝ) :
    ConfigRoot c S ↔
      S ∈ Ioo (maxCos (fun i : Fin c.length => Real.cos (Real.pi / c[i.val]))) 1 ∧
      arcSum (fun i : Fin c.length => Real.cos (Real.pi / c[i.val])) S = 2 * Real.pi := by
  rw [ConfigRoot, configMax_eq_maxCos hq, configArcSum_eq_arcSum]
  simp only [mem_Ioo, and_assoc]

theorem closable_iff_finite {c : List ℝ} [NeZero c.length]
    (hq : ∀ q ∈ c, 3 ≤ q) :
    Closable c ↔ 2 * Real.pi <
      arcSum (fun i : Fin c.length => Real.cos (Real.pi / c[i.val]))
        (maxCos (fun i : Fin c.length => Real.cos (Real.pi / c[i.val]))) := by
  rw [Closable, configMax_eq_maxCos hq, configArcSum_eq_arcSum]

theorem configRoot_realConfig_iff {c : List ℕ} [NeZero c.length]
    (hq : ∀ q ∈ c, 3 ≤ q) (S : ℝ) :
    ConfigRoot (realConfig c) S ↔
      S ∈ Ioo (maxCos (fun i : Fin c.length => polygonCos c[i.val])) 1 ∧
      arcSum (fun i : Fin c.length => polygonCos c[i.val]) S = 2 * Real.pi := by
  rw [ConfigRoot, configMax_realConfig hq, configArcSum_realConfig]
  simp only [mem_Ioo, and_assoc]

theorem closable_realConfig_iff {c : List ℕ} [NeZero c.length]
    (hq : ∀ q ∈ c, 3 ≤ q) :
    Closable (realConfig c) ↔ 2 * Real.pi <
      arcSum (fun i : Fin c.length => polygonCos c[i.val])
        (maxCos (fun i : Fin c.length => polygonCos c[i.val])) := by
  rw [Closable, configMax_realConfig hq, configArcSum_realConfig]

/-- Exact upper endpoint for real lists, including the mixed real/Nat lists
used by delta and the compact parameter charts. -/
theorem configArcSum_one {c : List ℝ} (hq : ∀ q ∈ c, 3 ≤ q) :
    configArcSum c 1 = Real.pi * (c.map (fun q => 1 - 2 / q)).sum := by
  rw [configArcSum_eq_arcSum, arcSum, ← Fin.sum_univ_fun_getElem c (fun q => 1 - 2 / q),
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  obtain ⟨h0, h1⟩ := configEntryAngle_bounds (hq c[i.val] (List.getElem_mem i.isLt))
  rw [centralArc, div_one, Real.arcsin_eq_pi_div_two_sub_arccos,
    Real.arccos_cos h0.le (by linarith [Real.pi_pos])]
  ring

/-- Every actual root forces strict closability; endpoint equality is excluded. -/
theorem closable_of_ConfigRoot {c : List ℝ} [NeZero c.length]
    (hq : ∀ q ∈ c, 3 ≤ q) {S : ℝ} (hroot : ConfigRoot c S) : Closable c := by
  obtain ⟨hmem, hr⟩ := (configRoot_iff_finite hq S).mp hroot
  rw [closable_iff_finite hq]
  exact closable_of_root (fun i : Fin c.length => (configEntryCos_bounds
    (hq c[i.val] (List.getElem_mem i.isLt))).1) hmem hr

/-- The choice-defined list radius agrees with the analytic radius for any
actual root; no selected-root equality is assumed. -/
theorem configRadius_eq_radiusFromCircle_of_root {c : List ℝ} [NeZero c.length]
    (hq : ∀ q ∈ c, 3 ≤ q) {S : ℝ} (hroot : ConfigRoot c S) :
    configRadius c = radiusFromCircle S := by
  have hex : ∃ T, ConfigRoot c T := ⟨S, hroot⟩
  rw [configRadius, dif_pos hex]
  change radiusFromCircle (Classical.choose hex) = radiusFromCircle S
  apply congrArg radiusFromCircle
  have hT := (configRoot_iff_finite hq (Classical.choose hex)).mp (Classical.choose_spec hex)
  have hS := (configRoot_iff_finite hq S).mp hroot
  exact (arcSum_strictAntiOn (fun i : Fin c.length => (configEntryCos_bounds
    (hq c[i.val] (List.getElem_mem i.isLt))).1)).injOn
    (Ioo_subset_Icc_self hT.1) (Ioo_subset_Icc_self hS.1) (hT.2.trans hS.2.symm)

/-- The angle condition and closability give exactly one root of the list
function used by B2 and P1. -/
theorem angleCondition_unique_root_iff {c : List ℝ} (ha : AngleCondition c) :
    (∃! S, ConfigRoot c S) ↔ Closable c := by
  letI : NeZero c.length := ⟨by have := ha.2.1; omega⟩
  simp_rw [configRoot_iff_finite ha.1]
  rw [closable_iff_finite ha.1]
  apply unique_root_iff
    (fun i : Fin c.length => (configEntryCos_bounds (ha.1 c[i.val] (List.getElem_mem i.isLt))).1)
    (fun i : Fin c.length => (configEntryCos_bounds (ha.1 c[i.val] (List.getElem_mem i.isLt))).2)
  rw [← configArcSum_eq_arcSum, configArcSum_one ha.1]
  nlinarith [ha.2.2.2, Real.pi_pos]

/-- Use the supplied B2 separation on an actual nonnegative geometric radius.
Only the root equation and its Pythagorean radius decomposition are supplied. -/
theorem B2.type_i_excludes_radius_of_root {Ω : Set ℝ} (b2 : B2 Ω)
    {n : ℕ} (hn : 17 ≤ n) {c : List ℕ} (ha : AngleCondition (realConfig c))
    {S R : ℝ} (hroot : ConfigRoot (realConfig c) S) (hR0 : 0 ≤ R)
    (hR : R ^ 2 = polygonRadius n ^ 2 + radiusFromCircle S ^ 2) : R ∉ Ω := by
  letI : NeZero (realConfig c).length := ⟨by have := ha.2.1; omega⟩
  have hclose := closable_of_ConfigRoot ha.1 hroot
  have heq := configRadius_eq_radiusFromCircle_of_root ha.1 hroot
  have hR' : R = Real.sqrt (polygonRadius n ^ 2 + configRadius (realConfig c) ^ 2) := by
    rw [heq, ← hR, Real.sqrt_sq_eq_abs, abs_of_nonneg hR0]
  rw [hR']
  exact b2.type_i n hn c ha hclose


/-- Nat-list version without requiring a separate instance for the length of
its cast-to-real list. -/
theorem configRadius_realConfig_eq_of_root {c : List ℕ} [NeZero c.length]
    (hq : ∀ q ∈ c, 3 ≤ q) {S : ℝ} (hroot : ConfigRoot (realConfig c) S) :
    configRadius (realConfig c) = radiusFromCircle S := by
  letI : NeZero (realConfig c).length := ⟨by
    simpa [realConfig] using (NeZero.ne c.length)⟩
  apply configRadius_eq_radiusFromCircle_of_root _ hroot
  intro q hq'
  obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hq'
  exact_mod_cast hq m hm

/-- An admissible root of the finite API identifies the exact list radius. -/
theorem configRadius_realConfig_eq_of_finite_root {c : List ℕ} [NeZero c.length]
    (hq : ∀ q ∈ c, 3 ≤ q) {S : ℝ}
    (hS : S ∈ Ioo (maxCos (fun i : Fin c.length => polygonCos c[i.val])) 1)
    (hr : arcSum (fun i : Fin c.length => polygonCos c[i.val]) S = 2 * Real.pi) :
    configRadius (realConfig c) = radiusFromCircle S :=
  configRadius_realConfig_eq_of_root hq ((configRoot_realConfig_iff hq S).mpr ⟨hS, hr⟩)

/-- Apply B2 directly to actual unit-ray geometry of a type-(i) fan. The root
and closability are derived, and the radius is the norm of the full centre
 displacement. The only global angular input is existing SphericalFanData. -/
theorem B2.type_i_excludes_unit_ray_radius
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {Ω : Set ℝ} (b2 : B2 Ω) {n : ℕ} (hn : 17 ≤ n) {c : List ℕ}
    (ha : AngleCondition (realConfig c))
    {x W : E} {u : ℕ → E}
    (hu : ∀ i ≤ c.length, ‖u i‖ = 1)
    (hproj : ∀ i ≤ c.length, ⟪u i, W⟫ = 1 / 2)
    (hchord : ∀ i : Fin c.length,
      dist (u i) (u (i.val + 1)) = polygonChord c[i.val])
    (fan : SphericalFanData c.length
      (fun i => angle (sphericalTangent (‖W‖⁻¹ • W) (u i))
        (sphericalTangent (‖W‖⁻¹ • W) (u (i + 1)))))
    (hx : ‖x‖ = polygonRadius n) (horth : ⟪x, W⟫ = 0) :
    ‖x - W‖ ∉ Ω := by
  have hlen : 3 ≤ c.length := by simpa [realConfig] using ha.2.1
  letI : NeZero c.length := ⟨by omega⟩
  have hq : ∀ q ∈ c, 3 ≤ q := by
    intro q hqc
    have hreal := ha.1 (q : ℝ) (List.mem_map.mpr ⟨q, hqc, rfl⟩)
    exact_mod_cast hreal
  let q : ℕ → ℕ := fun i => c.getD i 3
  have heq : (fun i : Fin c.length => polygonCos (q i)) =
      (fun i : Fin c.length => polygonCos c[i.val]) := by
    funext i
    dsimp [q]
    rw [List.getD_eq_getElem c 3 i.isLt]
  have hc : ∀ i < c.length, 0 < polygonCos (q i) := by
    intro i hi
    dsimp [q]
    rw [List.getD_eq_getElem c 3 hi]
    exact (polygonCos_bounds (hq c[i] (List.getElem_mem hi))).1
  have hchord' : ∀ i < c.length, dist (u i) (u (i + 1)) = 2 * polygonCos (q i) := by
    intro i hi
    dsimp [q]
    rw [List.getD_eq_getElem c 3 hi]
    exact hchord ⟨i, hi⟩
  obtain ⟨hmem, hr, _, _, _, hheight⟩ :=
    typeI_from_unit_rays hu hproj hc hchord' fan
  rw [heq] at hmem hr
  have hlistroot := (configRoot_realConfig_iff hq _).mpr ⟨hmem, hr⟩
  apply b2.type_i_excludes_radius_of_root hn ha hlistroot (norm_nonneg _)
  calc
    _ = ‖x‖ ^ 2 + ‖W‖ ^ 2 := by rw [norm_sub_sq_real, horth]; ring
    _ = polygonRadius n ^ 2 + radiusFromCircle _ ^ 2 := by
      exact congrArg₂ (fun a b : ℝ => a ^ 2 + b ^ 2) hx hheight


/-- The actual list arcsine sum is invariant under arbitrary permutations. -/
theorem configArcSum_perm {c d : List ℝ} (hp : c.Perm d) (S : ℝ) :
    configArcSum c S = configArcSum d S :=
  (hp.map (fun q => 2 * Real.arcsin (Real.cos (Real.pi / q) / S))).sum_eq

/-- The zero-seeded maximum is permutation invariant even outside the
admissible domain. -/
theorem configMax_perm {c d : List ℝ} (hp : c.Perm d) : configMax c = configMax d := by
  exact (hp.map (fun q => Real.cos (Real.pi / q))).foldr_eq'
    (fun x _ y _ z => max_left_comm y x z) 0

theorem configRoot_perm {c d : List ℝ} (hp : c.Perm d) (S : ℝ) :
    ConfigRoot c S ↔ ConfigRoot d S := by
  simp only [ConfigRoot, configMax_perm hp, configArcSum_perm hp]

theorem closable_perm {c d : List ℝ} (hp : c.Perm d) : Closable c ↔ Closable d := by
  simp only [Closable, configMax_perm hp, configArcSum_perm hp]

/-- Exact permutation invariance of the parent's choice-defined radius,
including its zero value outside the root domain. No validity hypothesis is
needed: permutation gives exactly the same predicate for the choice. -/
theorem configRadius_perm {c d : List ℝ} (hp : c.Perm d) : configRadius c = configRadius d := by
  classical
  have heq : ConfigRoot c = ConfigRoot d := funext (fun S => propext (configRoot_perm hp S))
  let rad : (ℝ → Prop) → ℝ := fun P =>
    if h : ∃ S, P S then radiusFromCircle (Classical.choose h) else 0
  change rad (ConfigRoot c) = rad (ConfigRoot d)
  exact congrArg rad heq

theorem configRadius_realConfig_perm {c d : List ℕ} (hp : c.Perm d) :
    configRadius (realConfig c) = configRadius (realConfig d) :=
  configRadius_perm (hp.map Nat.cast)

end Uniform5.CaseB
