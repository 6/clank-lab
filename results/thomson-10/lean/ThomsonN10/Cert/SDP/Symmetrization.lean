/- Adapted from global-soundness/n10/project/Thomson10Soundness/SDP/Symmetrization.lean (supplied accepted N10 port of proof/lean/ThomsonN9/SDP/Symmetrization.lean, aravindkarthigeyan/thomson-n9-lean, commit 168ff0c98cab4dfda0460ba55f8d169070ac385e, MIT). -/
import ThomsonN10.Cert.SDP.RepeatedIndices

namespace ThomsonN10.Cert.SDP
open ThomsonN10 ThomsonN10.Interfaces

noncomputable def edgeSymmetrize (F : ℝ → ℝ → ℝ → ℝ) (u v t : ℝ) : ℝ :=
  (F u v t+F v u t+F u t v+F t u v+F v t u+F t v u)/6

theorem edgeSymmetrize_swap_first (F : ℝ → ℝ → ℝ → ℝ) (u v t : ℝ) :
    edgeSymmetrize F v u t = edgeSymmetrize F u v t := by
  unfold edgeSymmetrize
  ring

theorem edgeSymmetrize_swap_last (F : ℝ → ℝ → ℝ → ℝ) (u v t : ℝ) :
    edgeSymmetrize F u t v = edgeSymmetrize F u v t := by
  unfold edgeSymmetrize
  ring

theorem edgeSymmetrize_cycle (F : ℝ → ℝ → ℝ → ℝ) (u v t : ℝ) :
    edgeSymmetrize F t u v = edgeSymmetrize F u v t := by
  unfold edgeSymmetrize
  ring

noncomputable def vertexSymmetrize (T : Fin 10 → Fin 10 → Fin 10 → ℝ)
    (i j k : Fin 10) : ℝ :=
  (T i j k+T i k j+T j i k+T j k i+T k i j+T k j i)/6

theorem fullSum_swap_first (T : Fin 10 → Fin 10 → Fin 10 → ℝ) :
    fullSum (fun i j k => T j i k) = fullSum T := by
  unfold fullSum
  rw [Finset.sum_comm]

theorem fullSum_swap_last (T : Fin 10 → Fin 10 → Fin 10 → ℝ) :
    fullSum (fun i j k => T i k j) = fullSum T := by
  unfold fullSum
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]

theorem fullSum_cycle (T : Fin 10 → Fin 10 → Fin 10 → ℝ) :
    fullSum (fun i j k => T j k i) = fullSum T := by
  calc
    _ = fullSum (fun i j k => T i k j) := fullSum_swap_first _
    _ = fullSum T := fullSum_swap_last T

theorem fullSum_reverse_cycle (T : Fin 10 → Fin 10 → Fin 10 → ℝ) :
    fullSum (fun i j k => T k i j) = fullSum T := by
  calc
    _ = fullSum (fun i j k => T j i k) := fullSum_swap_last _
    _ = fullSum T := fullSum_swap_first T

theorem fullSum_swap_outer (T : Fin 10 → Fin 10 → Fin 10 → ℝ) :
    fullSum (fun i j k => T k j i) = fullSum T := by
  calc
    _ = fullSum (fun i j k => T k i j) := fullSum_swap_first _
    _ = fullSum T := fullSum_reverse_cycle T

theorem fullSum_vertexSymmetrize (T : Fin 10 → Fin 10 → Fin 10 → ℝ) :
    fullSum (vertexSymmetrize T) = fullSum T := by
  have h₁ := fullSum_swap_first T
  have h₂ := fullSum_swap_last T
  have h₃ := fullSum_cycle T
  have h₄ := fullSum_reverse_cycle T
  have h₅ := fullSum_swap_outer T
  unfold fullSum vertexSymmetrize
  simp only [← Finset.sum_div, Finset.sum_add_distrib]
  change (fullSum T+fullSum (fun i j k => T i k j)+
    fullSum (fun i j k => T j i k)+fullSum (fun i j k => T j k i)+
    fullSum (fun i j k => T k i j)+fullSum (fun i j k => T k j i))/6 = fullSum T
  rw [h₁, h₂, h₃, h₄, h₅]
  ring

theorem fullSum_vertexSymmetrize_nonneg (T : Fin 10 → Fin 10 → Fin 10 → ℝ)
    (h : 0 ≤ fullSum T) : 0 ≤ fullSum (vertexSymmetrize T) := by
  rwa [fullSum_vertexSymmetrize]

end ThomsonN10.Cert.SDP
