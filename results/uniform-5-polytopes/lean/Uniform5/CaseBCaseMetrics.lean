import Uniform5.CaseBCases
import Uniform5.CaseBMetric

/-!
# Euclidean metric specializations of the finite Case B arguments

The combinatorial proofs are in `CaseBCases.lean`. This module supplies the
numerical tests from `CaseBMetric.lean`, using actual distances between
realized finite vertices. Local fan distance identities remain geometric
inputs. No fan exclusion or product classification is an input.
-/

noncomputable section
namespace Uniform5.CaseB

open Finset

/-- Exact triangular chord, used to remove the diagonal-versus-unit test. -/
theorem case_chord_three : chord 3 = 1 := by
  norm_num [chord, Real.cos_pi_div_three]

/-- All admissible polygon chords are positive. -/
theorem case_chord_pos {q : ℝ} (hq : 3 ≤ q) : 0 < chord q := by
  have h := chord_mono (m := 3) (by norm_num) hq
  rw [case_chord_three] at h
  linarith

/-- Natural-number version of the parent's exact square-chord criterion. -/
theorem case_chord_nat_eq_sqrt_two_iff {q : ℕ} (hq : 3 ≤ q) :
    chord (q : ℝ) = Real.sqrt 2 ↔ q = 4 := by
  constructor
  · intro h
    have h' := (chord_eq_sqrt_two_iff (q := (q : ℝ)) (by exact_mod_cast hq)).mp h
    exact_mod_cast h'
  · rintro rfl
    exact chord_four

/-- A large antiprism's trapezoid diagonal is not a unit edge. -/
theorem case_antiprism_diagonal_ne_one {n : ℝ} (hn : 17 ≤ n) :
    Real.sqrt (1 + chord n) ≠ 1 := by
  simpa only [Nat.cast_ofNat, case_chord_three] using
    (antiprism_diagonal_not_chord hn (q := 3) (by decide))

/-- The exact nonnegative radicand for converting squared diagonal data. -/
theorem case_antiprism_diagonal_sq_nonneg {n : ℝ} (hn : 17 ≤ n) :
    0 ≤ 1 + chord n := by
  have h := case_chord_pos (q := n) (by linarith)
  linarith

section RealizedVertices
variable {V F E : Type*} [Fintype V] [DecidableEq V] [PseudoMetricSpace E]

/-- Recover a nonnegative distance from its square. -/
theorem case_dist_eq_of_sq_eq {x y : E} {r : ℝ} (hr : 0 ≤ r)
    (h : dist x y ^ 2 = r ^ 2) : dist x y = r := by
  nlinarith [dist_nonneg (x := x) (y := y)]

/-- Recover a distance from a nonnegative squared-distance value. -/
theorem case_dist_eq_sqrt_of_sq_eq {x y : E} {s : ℝ} (hs : 0 ≤ s)
    (h : dist x y ^ 2 = s) : dist x y = Real.sqrt s := by
  apply case_dist_eq_of_sq_eq (Real.sqrt_nonneg s)
  rw [Real.sq_sqrt hs]
  exact h

/-- Euclidean-distance specialization of the (i)/(i), k4 exclusion. The
unit-versus-`sqrt 2` comparison is proved by the combinatorial theorem. -/
theorem paired_i_i_k4_dist_impossible
    (G : FacetSystem V F) (L : G.Laws) (p : Fin 6 ↪ V) (S : Finset V)
    (fan : ∀ f, p 2 ∈ G.vertices f → p 3 ∈ G.vertices f → G.vertices f ⊆ S)
    (off_u : p 4 ∉ S → G.neighbours (p 4) = {p 0, p 1, p 3, p 5})
    (off_v : p 5 ∉ S → G.neighbours (p 5) = {p 0, p 1, p 4, p 2})
    (pos : V → E)
    (partner_metric : ∀ z ∈ S, z ≠ p 2 → z ≠ p 3 →
      dist (pos z) (pos (p 2)) = Real.sqrt 2 ∧
      dist (pos z) (pos (p 3)) = Real.sqrt 2)
    (unit_u : dist (pos (p 4)) (pos (p 3)) = 1)
    (unit_v : dist (pos (p 5)) (pos (p 2)) = 1) : False := by
  exact paired_i_i_k4_impossible G L p S fan off_u off_v
    (fun z w => dist (pos z) (pos w)) partner_metric unit_u unit_v

/-- Mixed k3 exclusion with the concrete chord and antiprism diagonal.
The non-chord metric test is discharged, rather than a premise. -/
theorem paired_i_ii_k3_dist_impossible
    (G : FacetSystem V F) (L : G.Laws) (p : Fin 5 ↪ V) (x' y' : V)
    (fan : ∀ f, p 2 ∈ G.vertices f → p 3 ∈ G.vertices f →
      G.vertices f ⊆ {p 0, p 1, p 2, p 3, x', y'})
    (off : p 4 ∉ ({p 0, p 1, p 2, p 3, x', y'} : Finset V) →
      G.neighbours (p 4) = {p 0, p 1, p 2, p 3})
    (pos : V → E) (m : ℝ) (hm : 17 ≤ m) (q₂ q₃ : ℕ)
    (hq₂ : 3 ≤ q₂) (hq₃ : 3 ≤ q₃)
    (zc : dist (pos (p 4)) (pos (p 2)) = chord q₃)
    (zd : dist (pos (p 4)) (pos (p 3)) = chord q₂)
    (xc : dist (pos x') (pos (p 2)) = Real.sqrt (1 + chord m))
    (yd : dist (pos y') (pos (p 3)) = Real.sqrt (1 + chord m)) : False := by
  exact paired_i_ii_k3_impossible G L p x' y' fan off
    (fun z w => dist (pos z) (pos w)) (fun q => chord (q : ℝ))
    q₂ q₃ hq₂ hq₃ (Real.sqrt (1 + chord m)) zc zd xc yd
    (fun q hq => antiprism_diagonal_not_chord hm hq)

/-- The (ii)/(ii) distance contradiction, with the exact diagonal versus
`sqrt 2` test supplied by the parent's metric theorem. -/
theorem paired_ii_ii_dist_impossible
    (G : FacetSystem V F) (L : G.Laws) (p : Fin 5 ↪ V) (x' y' : V)
    (fan : ∀ f, p 2 ∈ G.vertices f → p 3 ∈ G.vertices f →
      G.vertices f ⊆ {p 0, p 1, p 2, p 3, x', y'})
    (off : p 4 ∉ ({p 0, p 1, p 2, p 3, x', y'} : Finset V) →
      ∃ t, ({p 0, t, p 2, p 3} : Finset V).card = 4 ∧
        G.neighbours (p 4) = {p 0, t, p 2, p 3})
    (pos : V → E) (m : ℝ) (hm : 17 ≤ m)
    (xc : dist (pos (p 4)) (pos (p 2)) = Real.sqrt 2)
    (x'c : dist (pos x') (pos (p 2)) = 1)
    (y'c : dist (pos y') (pos (p 2)) = Real.sqrt (1 + chord m)) : False := by
  exact paired_ii_ii_impossible G L p x' y' fan off
    (fun z w => dist (pos z) (pos w)) (Real.sqrt (1 + chord m))
    xc x'c y'c (antiprism_diagonal_ne_sqrt_two hm)

/-- In the surviving paired type-(i) k3 pattern the two small parameters
are 4, using the actual polygon chord function and Euclidean distances. -/
theorem paired_i_i_k3_dist_parameters
    (G : FacetSystem V F) (L : G.Laws) (p : Fin 5 ↪ V) (S : Finset V)
    (fan : ∀ f, p 2 ∈ G.vertices f → p 3 ∈ G.vertices f → G.vertices f ⊆ S)
    (off : p 4 ∉ S → G.neighbours (p 4) = {p 0, p 1, p 2, p 3})
    (pos : V → E) (q₂ q₃ : ℕ) (hq₂ : 3 ≤ q₂) (hq₃ : 3 ≤ q₃)
    (partner_metric : ∀ z ∈ S, z ≠ p 2 → z ≠ p 3 →
      dist (pos z) (pos (p 2)) = Real.sqrt 2 ∧
      dist (pos z) (pos (p 3)) = Real.sqrt 2)
    (zc : dist (pos (p 4)) (pos (p 2)) = chord q₃)
    (zd : dist (pos (p 4)) (pos (p 3)) = chord q₂) : q₂ = 4 ∧ q₃ = 4 := by
  exact paired_i_i_k3_parameters G L p S fan off
    (fun z w => dist (pos z) (pos w)) (fun q => chord (q : ℝ))
    q₂ q₃ hq₂ hq₃ partner_metric zc zd
    (fun q hq => case_chord_nat_eq_sqrt_two_iff hq)

/-- Mixed k4 identification with actual fan distances. The diagonal is
proved different from 1; no numerical exclusion remains as a premise. -/
theorem paired_mixed_k4_dist_completion
    (G : FacetSystem V F) (L : G.Laws) (B : FacetBoundary G)
    (p : Fin 6 ↪ V) (q : Fin 5 ↪ V)
    (qa : q 0 = p 0) (qc : q 1 = p 2) (qd : q 2 = p 3)
    (P : F) (vertices : G.vertices P = {q 0, q 1, q 2, q 3, q 4})
    (ridges : B.ridges P = pyramidRidges (q 0) (q 1) (q 2) (q 3) (q 4))
    (fan : ∀ f, p 2 ∈ G.vertices f → p 3 ∈ G.vertices f →
      G.vertices f ⊆ {p 0, p 1, p 2, p 3, q 3, q 4})
    (off_u : p 4 ∉ ({p 0, p 1, p 2, p 3, q 3, q 4} : Finset V) →
      G.neighbours (p 4) = {p 0, p 1, p 3, p 5})
    (off_v : p 5 ∉ ({p 0, p 1, p 2, p 3, q 3, q 4} : Finset V) →
      G.neighbours (p 5) = {p 0, p 1, p 4, p 2})
    (pos : V → E) (m : ℝ) (hm : 17 ≤ m)
    (ud : dist (pos (p 4)) (pos (p 3)) = 1)
    (vc : dist (pos (p 5)) (pos (p 2)) = 1)
    (xd : dist (pos (q 4)) (pos (p 3)) = Real.sqrt (1 + chord m))
    (yc : dist (pos (q 3)) (pos (p 2)) = Real.sqrt (1 + chord m)) :
    p 4 = q 3 ∧ p 5 = q 4 := by
  exact paired_mixed_k4_completion G L B p q qa qc qd P vertices ridges fan off_u off_v
    (fun z w => dist (pos z) (pos w)) (Real.sqrt (1 + chord m))
    (case_antiprism_diagonal_ne_one hm) ud vc xd yc


/-- Squared-distance form of the mixed k3 exclusion. All four square-root
choices are justified by nonnegativity, rather than assumed sign tests. -/
theorem paired_i_ii_k3_sqdist_impossible
    (G : FacetSystem V F) (L : G.Laws) (p : Fin 5 ↪ V) (x' y' : V)
    (fan : ∀ f, p 2 ∈ G.vertices f → p 3 ∈ G.vertices f →
      G.vertices f ⊆ {p 0, p 1, p 2, p 3, x', y'})
    (off : p 4 ∉ ({p 0, p 1, p 2, p 3, x', y'} : Finset V) →
      G.neighbours (p 4) = {p 0, p 1, p 2, p 3})
    (pos : V → E) (m : ℝ) (hm : 17 ≤ m) (q₂ q₃ : ℕ)
    (hq₂ : 3 ≤ q₂) (hq₃ : 3 ≤ q₃)
    (zc : dist (pos (p 4)) (pos (p 2)) ^ 2 = chord q₃ ^ 2)
    (zd : dist (pos (p 4)) (pos (p 3)) ^ 2 = chord q₂ ^ 2)
    (xc : dist (pos x') (pos (p 2)) ^ 2 = 1 + chord m)
    (yd : dist (pos y') (pos (p 3)) ^ 2 = 1 + chord m) : False := by
  apply paired_i_ii_k3_dist_impossible G L p x' y' fan off pos m hm q₂ q₃ hq₂ hq₃
  · exact case_dist_eq_of_sq_eq (case_chord_pos (by exact_mod_cast hq₃)).le zc
  · exact case_dist_eq_of_sq_eq (case_chord_pos (by exact_mod_cast hq₂)).le zd
  · exact case_dist_eq_sqrt_of_sq_eq (case_antiprism_diagonal_sq_nonneg hm) xc
  · exact case_dist_eq_sqrt_of_sq_eq (case_antiprism_diagonal_sq_nonneg hm) yd

/-- Squared-distance form of the (ii)/(ii) exclusion. -/
theorem paired_ii_ii_sqdist_impossible
    (G : FacetSystem V F) (L : G.Laws) (p : Fin 5 ↪ V) (x' y' : V)
    (fan : ∀ f, p 2 ∈ G.vertices f → p 3 ∈ G.vertices f →
      G.vertices f ⊆ {p 0, p 1, p 2, p 3, x', y'})
    (off : p 4 ∉ ({p 0, p 1, p 2, p 3, x', y'} : Finset V) →
      ∃ t, ({p 0, t, p 2, p 3} : Finset V).card = 4 ∧
        G.neighbours (p 4) = {p 0, t, p 2, p 3})
    (pos : V → E) (m : ℝ) (hm : 17 ≤ m)
    (xc : dist (pos (p 4)) (pos (p 2)) ^ 2 = 2)
    (x'c : dist (pos x') (pos (p 2)) ^ 2 = 1)
    (y'c : dist (pos y') (pos (p 2)) ^ 2 = 1 + chord m) : False := by
  apply paired_ii_ii_dist_impossible G L p x' y' fan off pos m hm
  · exact case_dist_eq_sqrt_of_sq_eq (by norm_num) xc
  · apply case_dist_eq_of_sq_eq (by norm_num : (0 : ℝ) ≤ 1)
    simpa using x'c
  · exact case_dist_eq_sqrt_of_sq_eq (case_antiprism_diagonal_sq_nonneg hm) y'c

/-- Squared-distance form of the (i)/(i), k4 exclusion. -/
theorem paired_i_i_k4_sqdist_impossible
    (G : FacetSystem V F) (L : G.Laws) (p : Fin 6 ↪ V) (S : Finset V)
    (fan : ∀ f, p 2 ∈ G.vertices f → p 3 ∈ G.vertices f → G.vertices f ⊆ S)
    (off_u : p 4 ∉ S → G.neighbours (p 4) = {p 0, p 1, p 3, p 5})
    (off_v : p 5 ∉ S → G.neighbours (p 5) = {p 0, p 1, p 4, p 2})
    (pos : V → E)
    (partner_metric : ∀ z ∈ S, z ≠ p 2 → z ≠ p 3 →
      dist (pos z) (pos (p 2)) ^ 2 = 2 ∧ dist (pos z) (pos (p 3)) ^ 2 = 2)
    (unit_u : dist (pos (p 4)) (pos (p 3)) ^ 2 = 1)
    (unit_v : dist (pos (p 5)) (pos (p 2)) ^ 2 = 1) : False := by
  apply paired_i_i_k4_dist_impossible G L p S fan off_u off_v pos
  · intro z hz hzc hzd
    have h := partner_metric z hz hzc hzd
    exact ⟨case_dist_eq_sqrt_of_sq_eq (by norm_num) h.1,
      case_dist_eq_sqrt_of_sq_eq (by norm_num) h.2⟩
  · apply case_dist_eq_of_sq_eq (by norm_num : (0 : ℝ) ≤ 1)
    simpa using unit_u
  · apply case_dist_eq_of_sq_eq (by norm_num : (0 : ℝ) ≤ 1)
    simpa using unit_v

/-- Squared-distance form of the surviving paired k3 parameter conclusion. -/
theorem paired_i_i_k3_sqdist_parameters
    (G : FacetSystem V F) (L : G.Laws) (p : Fin 5 ↪ V) (S : Finset V)
    (fan : ∀ f, p 2 ∈ G.vertices f → p 3 ∈ G.vertices f → G.vertices f ⊆ S)
    (off : p 4 ∉ S → G.neighbours (p 4) = {p 0, p 1, p 2, p 3})
    (pos : V → E) (q₂ q₃ : ℕ) (hq₂ : 3 ≤ q₂) (hq₃ : 3 ≤ q₃)
    (partner_metric : ∀ z ∈ S, z ≠ p 2 → z ≠ p 3 →
      dist (pos z) (pos (p 2)) ^ 2 = 2 ∧ dist (pos z) (pos (p 3)) ^ 2 = 2)
    (zc : dist (pos (p 4)) (pos (p 2)) ^ 2 = chord q₃ ^ 2)
    (zd : dist (pos (p 4)) (pos (p 3)) ^ 2 = chord q₂ ^ 2) : q₂ = 4 ∧ q₃ = 4 := by
  apply paired_i_i_k3_dist_parameters G L p S fan off pos q₂ q₃ hq₂ hq₃
  · intro z hz hzc hzd
    have h := partner_metric z hz hzc hzd
    exact ⟨case_dist_eq_sqrt_of_sq_eq (by norm_num) h.1,
      case_dist_eq_sqrt_of_sq_eq (by norm_num) h.2⟩
  · exact case_dist_eq_of_sq_eq (case_chord_pos (by exact_mod_cast hq₃)).le zc
  · exact case_dist_eq_of_sq_eq (case_chord_pos (by exact_mod_cast hq₂)).le zd

/-- Mixed k4 forced identification from actual squared distances. -/
theorem paired_mixed_k4_sqdist_completion
    (G : FacetSystem V F) (L : G.Laws) (B : FacetBoundary G)
    (p : Fin 6 ↪ V) (q : Fin 5 ↪ V)
    (qa : q 0 = p 0) (qc : q 1 = p 2) (qd : q 2 = p 3)
    (P : F) (vertices : G.vertices P = {q 0, q 1, q 2, q 3, q 4})
    (ridges : B.ridges P = pyramidRidges (q 0) (q 1) (q 2) (q 3) (q 4))
    (fan : ∀ f, p 2 ∈ G.vertices f → p 3 ∈ G.vertices f →
      G.vertices f ⊆ {p 0, p 1, p 2, p 3, q 3, q 4})
    (off_u : p 4 ∉ ({p 0, p 1, p 2, p 3, q 3, q 4} : Finset V) →
      G.neighbours (p 4) = {p 0, p 1, p 3, p 5})
    (off_v : p 5 ∉ ({p 0, p 1, p 2, p 3, q 3, q 4} : Finset V) →
      G.neighbours (p 5) = {p 0, p 1, p 4, p 2})
    (pos : V → E) (m : ℝ) (hm : 17 ≤ m)
    (ud : dist (pos (p 4)) (pos (p 3)) ^ 2 = 1)
    (vc : dist (pos (p 5)) (pos (p 2)) ^ 2 = 1)
    (xd : dist (pos (q 4)) (pos (p 3)) ^ 2 = 1 + chord m)
    (yc : dist (pos (q 3)) (pos (p 2)) ^ 2 = 1 + chord m) :
    p 4 = q 3 ∧ p 5 = q 4 := by
  apply paired_mixed_k4_dist_completion G L B p q qa qc qd P vertices ridges
    fan off_u off_v pos m hm
  · apply case_dist_eq_of_sq_eq (by norm_num : (0 : ℝ) ≤ 1)
    simpa using ud
  · apply case_dist_eq_of_sq_eq (by norm_num : (0 : ℝ) ≤ 1)
    simpa using vc
  · exact case_dist_eq_sqrt_of_sq_eq (case_antiprism_diagonal_sq_nonneg hm) xd
  · exact case_dist_eq_sqrt_of_sq_eq (case_antiprism_diagonal_sq_nonneg hm) yc

end RealizedVertices
end Uniform5.CaseB
