/- Adapted from proof/lean/ThomsonN9/Endgame.lean,
 aravindkarthigeyan/thomson-n9-lean @ 168ff0c98cab4dfda0460ba55f8d169070ac385e (MIT). -/
import ThomsonN10.Local.CentroidBound
namespace ThomsonN10.Local
theorem coulombEnergy_eq_half_double_sum (x : Configuration) :
    coulombEnergy x = (∑ i, ∑ j, (‖x i - x j‖)⁻¹) / 2 := by
  have h := twice_pairSum (fun i j => (‖x i - x j‖)⁻¹)
    (fun i j => by rw [norm_sub_rev]) (fun i => by simp)
  change 2 * coulombEnergy x = _ at h
  linarith

theorem congruent_energy {x y : Configuration} (h : Congruent x y) :
    coulombEnergy x = coulombEnergy y := by
  rcases h with ⟨g, p, hp⟩
  rw [coulombEnergy_eq_half_double_sum, coulombEnergy_eq_half_double_sum]
  have hd (i j : Fin 10) : ‖x i - x j‖ = ‖y (p i) - y (p j)‖ := by
    rw [hp i, hp j, ← g.map_sub, g.norm_map]
  simp_rw [hd]
  congr 1
  calc
    (∑ i, ∑ j, (‖y (p i) - y (p j)‖)⁻¹) =
        ∑ i, ∑ j, (‖y (p i) - y j‖)⁻¹ := by
      apply Finset.sum_congr rfl
      intro i _
      exact Equiv.sum_comp p (fun j => (‖y (p i) - y j‖)⁻¹)
    _ = ∑ i, ∑ j, (‖y i - y j‖)⁻¹ :=
      Equiv.sum_comp p (fun i => ∑ j, (‖y i - y j‖)⁻¹)

theorem sphere_relabel {x : Configuration} (hx : IsSphereConfiguration x)
    (p : Equiv.Perm (Fin 10)) : IsSphereConfiguration (fun i => x (p i)) :=
  ⟨fun i => hx.1 (p i), hx.2.comp p.injective⟩

theorem relabel_energy (x : Configuration) (p : Equiv.Perm (Fin 10)) :
    coulombEnergy (fun i => x (p i)) = coulombEnergy x :=
  congruent_energy ⟨LinearIsometryEquiv.refl ℝ R3, p, fun _ => rfl⟩

theorem congruent_of_relabel {x y : Configuration} (p : Equiv.Perm (Fin 10))
    (h : Congruent (fun i => x (p i)) y) : Congruent x y := by
  rcases h with ⟨g, q, hq⟩
  refine ⟨g, p.symm.trans q, ?_⟩
  intro i
  simpa using hq (p.symm i)

end ThomsonN10.Local
