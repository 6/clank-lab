import FT23.Definitions
import Mathlib.Tactic
namespace FT23

def independence (u v : ℝ) : ℝ := u*v

lemma independence_E (u v : ℝ) : E independence u v = 0 := by
  rw [E_expanded]
  unfold independence
  ring

lemma independence_delta (a b d e : ℝ) : delta (E independence) a b d e = 0 := by
  simp [delta, independence_E]

lemma independence_PQD : PQD independence := by
  intro u hu v hv
  exact le_rfl

end FT23
