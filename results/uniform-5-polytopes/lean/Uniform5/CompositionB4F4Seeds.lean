import Uniform5.CompositionB4F4Orbit
import Uniform5.CompositionD4B4Seeds

/-! Signed mirror equations on the fixed slice of D4 triality. -/
noncomputable section
namespace Uniform5.Composition
open scoped RealInnerProductSpace

theorem b4_initial_inner (x : ModelSpace 4) : ⟪rootsB4 0, x⟫ = x 0 - x 1 := by
  change ⟪coordinateVector (0 : Fin 4) - coordinateVector 1, x⟫ = _
  simp [inner_sub_left, coordinateVector, EuclideanSpace.inner_single_left]

theorem b4_penultimate_inner (x : ModelSpace 4) : ⟪rootsB4 2, x⟫ = x 2 - x 3 := by
  change ⟪coordinateVector (2 : Fin 4) - coordinateVector 3, x⟫ = _
  simp [inner_sub_left, coordinateVector, EuclideanSpace.inner_single_left]

theorem b4_long_norm_eq : ‖rootsB4 0‖ = ‖rootsB4 2‖ := by
  change ‖rootsB4 (⟨0, by decide⟩ : Fin 4)‖ = ‖rootsB4 (⟨2, by decide⟩ : Fin 4)‖
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, rootsB4_gram, rootsB4_gram]
  norm_num

theorem f4_seed_fixed_slice {J : Finset (Fin 4)} (h2 : 2 ∉ J) (h3 : 3 ∉ J)
    {x : ModelSpace 4} (hx : WythoffSeed rootsF4 J x) : x 3 = 0 ∧ d4Triality x = x := by
  have he2 := hx 2
  rw [if_neg h2] at he2
  change ⟪rootsB4 3, x⟫ = 0 at he2
  rw [b4_terminal_inner] at he2
  have he3 := hx 3
  rw [if_neg h3] at he3
  refine ⟨he2, ?_⟩
  rw [← f4_terminal_apply, mirrorReflection_formula, he3]
  simp

theorem f4_b4_seed_iff {J K : Finset (Fin 4)}
    (hJ2 : 2 ∉ J) (hJ3 : 3 ∉ J)
    (hK0 : 0 ∈ K ↔ 1 ∈ J) (hK1 : 1 ∈ K ↔ 0 ∈ J)
    (hK2 : 2 ∈ K ↔ 1 ∈ J) (hK3 : 3 ∉ K) {x : ModelSpace 4} :
    WythoffSeed rootsF4 J x ↔ WythoffSeed rootsB4 K x := by
  classical
  constructor
  · intro hx i
    have hz := (f4_seed_fixed_slice hJ2 hJ3 hx).1
    have hs := hx 3
    rw [if_neg hJ3, f4_terminal_inner] at hs
    fin_cases i
    · change ⟪rootsB4 0, x⟫ = if 0 ∈ K then ‖rootsB4 0‖ / 2 else 0
      rw [b4_initial_inner, b4_long_norm_eq]
      simp only [hK0]
      have hh := hx 1
      change ⟪rootsB4 2, x⟫ = if 1 ∈ J then ‖rootsB4 2‖ / 2 else 0 at hh
      rw [b4_penultimate_inner] at hh
      linarith
    · change ⟪rootsF4 0, x⟫ = if 1 ∈ K then ‖rootsF4 0‖ / 2 else 0
      simpa only [hK1] using hx 0
    · change ⟪rootsF4 1, x⟫ = if 2 ∈ K then ‖rootsF4 1‖ / 2 else 0
      simpa only [hK2] using hx 1
    · change ⟪rootsB4 3, x⟫ = if 3 ∈ K then ‖rootsB4 3‖ / 2 else 0
      rw [b4_terminal_inner, hz, if_neg hK3]
  · intro hx i
    have hz := hx 3
    rw [if_neg hK3, b4_terminal_inner] at hz
    fin_cases i
    · change ⟪rootsB4 1, x⟫ = if 0 ∈ J then ‖rootsB4 1‖ / 2 else 0
      simpa only [hK1] using hx 1
    · change ⟪rootsB4 2, x⟫ = if 1 ∈ J then ‖rootsB4 2‖ / 2 else 0
      simpa only [hK2] using hx 2
    · change ⟪rootsB4 3, x⟫ = if 2 ∈ J then ‖rootsB4 3‖ / 2 else 0
      rw [b4_terminal_inner, hz, if_neg hJ2]
    · change ⟪rootsF4 3, x⟫ = if 3 ∈ J then ‖rootsF4 3‖ / 2 else 0
      rw [if_neg hJ3, f4_terminal_inner]
      have he0 := hx 0
      have he2 := hx 2
      rw [b4_initial_inner, b4_long_norm_eq] at he0
      rw [b4_penultimate_inner] at he2
      simp only [hK0] at he0
      simp only [hK2] at he2
      linarith

variable {E : Type*} [PseudoMetricSpace E]

theorem f4_b4_named_slice_iff {m n : Fin 15}
    (hJ2 : 2 ∉ libraryRingSet m) (hJ3 : 3 ∉ libraryRingSet m)
    (hK0 : 0 ∈ libraryRingSet n ↔ 1 ∈ libraryRingSet m)
    (hK1 : 1 ∈ libraryRingSet n ↔ 0 ∈ libraryRingSet m)
    (hK2 : 2 ∈ libraryRingSet n ↔ 1 ∈ libraryRingSet m)
    (hK3 : 3 ∉ libraryRingSet n) (P : Set E) :
    NamedWythoff4Model 3 m P ↔ NamedWythoff4Model 1 n P := by
  have he (x : ModelSpace 4) : WythoffSeed rootsF4 (libraryRingSet m) x ↔
      WythoffSeed rootsB4 (libraryRingSet n) x :=
    f4_b4_seed_iff hJ2 hJ3 hK0 hK1 hK2 hK3
  constructor
  · rintro ⟨x, hx, hcongr⟩
    obtain ⟨hz, ht⟩ := f4_seed_fixed_slice hJ2 hJ3 hx
    refine ⟨x, (he x).mp hx, ?_⟩
    rwa [b4_f4_hull_eq hz ht]
  · rintro ⟨x, hx, hcongr⟩
    have hs := (he x).mpr hx
    obtain ⟨hz, ht⟩ := f4_seed_fixed_slice hJ2 hJ3 hs
    refine ⟨x, hs, ?_⟩
    rwa [← b4_f4_hull_eq hz ht]

end Uniform5.Composition
