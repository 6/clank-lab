import Uniform5.CompositionAntiprismMetric

/-! The two lower-layer neighbors of upper vertex one are exhaustive. -/
noncomputable section
namespace Uniform5.Composition
open Set

/-- Cosine decreases away from both nearest ends of a full circular arc. -/
theorem cos_lt_of_inner_arc {θ φ : ℝ} (hθ : 0 ≤ θ) (hθφ : θ < φ)
    (hφ : φ < 2 * Real.pi - θ) : Real.cos φ < Real.cos θ := by
  by_cases hp : φ ≤ Real.pi
  · exact Real.cos_lt_cos_of_nonneg_of_le_pi hθ hp hθφ
  · have he : Real.cos φ = Real.cos (2 * Real.pi - φ) := (Real.cos_two_pi_sub φ).symm
    rw [he]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi hθ (by linarith) (by linarith)

/-- Exact unit-distance classification across the two layers. -/
theorem antiprism_one_cross_unit_iff {n : ℕ} (hn : 3 ≤ n) (j : Fin n) :
    dist (antiprismPoint n false ⟨1, by omega⟩) (antiprismPoint n true j) = 1 ↔
      j.val = 0 ∨ j.val = 1 := by
  constructor
  · intro hd
    by_contra hj
    have hj2 : 2 ≤ j.val := by omega
    let θ := Real.pi / n
    let φ := 2 * Real.pi * (j : ℕ) / n - Real.pi / n
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hθ : 0 < θ := div_pos Real.pi_pos hn0
    have hmul : (n : ℝ) * θ = Real.pi := by dsimp [θ]; field_simp
    have hφ : φ = (2 * (j : ℕ) - 1) * θ := by dsimp [φ, θ]; ring
    have hjR : (2 : ℝ) ≤ j.val := by exact_mod_cast hj2
    have hjlt : (j.val : ℝ) < n := by exact_mod_cast j.isLt
    have hlow : θ < φ := by rw [hφ]; nlinarith
    have hupp : φ < 2 * Real.pi - θ := by rw [hφ]; nlinarith
    have hcos := cos_lt_of_inner_arc hθ.le hlow hupp
    have he := antiprism_cross_dist_sq hn (⟨1, by omega⟩ : Fin n) j
    rw [hd] at he
    have hang : 2 * Real.pi * ((⟨1, by omega⟩ : Fin n) : ℕ) / n -
        (2 * Real.pi * (j : ℕ) / n + Real.pi / n) = -φ := by dsimp [φ]; norm_num; ring
    rw [hang, Real.cos_neg] at he
    have hr := sq_pos_of_pos (unitPolygonRadius_pos hn)
    change Real.cos φ < Real.cos (Real.pi / n) at hcos
    nlinarith only [he, hr, hcos]
  · rintro (hj | hj)
    · have he : j = ⟨0, by omega⟩ := Fin.ext hj
      rw [he]
      exact antiprism_cross_one_zero_dist hn
    · have he : j = ⟨1, by omega⟩ := Fin.ext hj
      rw [he]
      exact antiprism_cross_same_dist hn _

/-- In an actual uniform antiprism, the metric test is the actual edge
predicate, so no assumed adjacency list is used. -/
theorem antiprism_one_cross_edge_iff {n : ℕ} (hn : 3 ≤ n)
    (hA : UnitUniform 3 (antiprismModel n)) (j : Fin n) :
    Edge (antiprismModel n) (antiprismPoint n false ⟨1, by omega⟩)
      (antiprismPoint n true j) ↔ j.val = 0 ∨ j.val = 1 := by
  have hv : ∀ b i, antiprismPoint n b i ∈ (antiprismModel n).extremePoints ℝ := by
    intro b i
    rw [antiprism_extremePoints]
    exact ⟨(b, i), rfl⟩
  rw [unitUniform_edge_iff_dist_one hA (hv false _) (hv true j)]
  exact antiprism_one_cross_unit_iff hn j

end Uniform5.Composition
