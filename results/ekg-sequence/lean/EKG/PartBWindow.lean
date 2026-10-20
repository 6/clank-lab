import EKG.PartBInjection
import EKG.PartACapacity

/-! Fixed-modulus capacity for the complete actual successor injection.
The source window H is fixed first; delta and its value cutoff precede eta;
C and the fixed modulus precede every observed prefix, hole and factor. -/
namespace EKG.PartB

theorem window_gap_bound :
    ∃ H : ℝ, 0 < H ∧ ∀ delta : ℝ, 0 < delta → ∃ X : ℝ,
      ∀ eta : ℝ, 0 < eta → ∃ C : ℝ, 0 ≤ C ∧
      ∀ t h s M : ℕ, ∀ B : ℝ,
      X ≤ (frontier canonical t : ℝ) →
      2 ≤ h → h < frontier canonical t →
      ¬ UsedBefore canonical.a (t+1) h →
      s.Prime → s ∣ h → 2 ≤ M → 3 < B → (M : ℝ) < B →
      delta*logRate (frontier canonical t) ≤ (frontier canonical t : ℝ)-(h : ℝ) →
      (frontier canonical t : ℝ)-(h : ℝ) ≤ 1604*logRate (frontier canonical t) →
      2*B*(13*Nat.primeCounting (Nat.sqrt (frontier canonical t))+724 : ℕ) ≤
        delta/3*logRate (frontier canonical t) →
      (frontier canonical t : ℝ) ≤ (2*s*M : ℕ)*B →
      (frontier canonical t : ℝ) < B^3 →
      (frontier canonical t : ℝ)-(h : ℝ) ≤
        4*H*eta*(M : ℝ)*logRate (frontier canonical t) +
          4*(s : ℝ)*M*(C+2) := by
  classical
  obtain ⟨H,hH,hinjection⟩ := many_prime_successors
  refine ⟨H,hH,?_⟩
  intro delta hdelta
  obtain ⟨X,hinj⟩ := hinjection delta hdelta
  refine ⟨max 3 X,?_⟩
  intro eta heta
  obtain ⟨C,hC,hcapacity⟩ := PartA.prime_capacity_real_windows eta heta
  refine ⟨C,hC,?_⟩
  intro t h s M B hX hh hbelow hfree hs hsh hM hB hMB hgap hupper hscale hstride hcube
  let e : ℝ := frontier canonical t
  have he3 : 3 ≤ e := (le_max_left _ _).trans hX
  have heX : X ≤ e := (le_max_right _ _).trans hX
  have hL : 0 ≤ logRate e := logRate_nonneg (by linarith)
  have hsreal : (0:ℝ) < s := by exact_mod_cast hs.pos
  obtain ⟨index,cofactor,hw,hcofactor⟩ :=
    hinj t h s M B heX hh hbelow hfree hs hsh hM hB hMB
      hgap hupper hscale hstride hcube
  let F := (successorRungs t h s M).image cofactor
  have hcard : F.card=(successorRungs t h s M).card :=
    Finset.card_image_of_injOn hcofactor
  have hmembers : ∀ q ∈ F, q.Prime ∧
      (e-H*logRate e)/(s : ℝ) ≤ (q : ℝ) ∧
      (q : ℝ) ≤ (e-H*logRate e)/(s : ℝ)+H*logRate e/(s : ℝ) := by
    intro q hq
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hq
    have w := hw j hj
    have heq : (canonical.a (index j+1) : ℝ)=(s : ℝ)*(cofactor j : ℝ) := by
      exact_mod_cast w.successor_eq
    refine ⟨w.cofactor_prime,?_,?_⟩
    · apply (div_le_iff₀ hsreal).mpr
      nlinarith only [w.window_lower,heq]
    · have hu : (canonical.a (index j+1) : ℝ) ≤ e := by
        dsimp [e]
        exact_mod_cast (le_trans w.successor_lt.le hbelow.le)
      have hupperq : (cofactor j : ℝ) ≤ e/(s : ℝ) := by
        apply (le_div_iff₀ hsreal).mpr
        nlinarith only [hu,heq]
      have hid : (e-H*logRate e)/(s : ℝ)+H*logRate e/(s : ℝ)=e/(s : ℝ) := by ring
      rwa [hid]
  have hcap := hcapacity F ((e-H*logRate e)/(s : ℝ))
    (H*logRate e/(s : ℝ)) (by positivity) hmembers
  rw [hcard] at hcap
  have hcount : e-(h : ℝ) ≤ 4*(s : ℝ)*(M : ℝ)*
      (((successorRungs t h s M).card : ℝ)+2) := by
    simpa only [Nat.cast_add,Nat.cast_ofNat] using
      (successor_rungs_count (t:=t) (h:=h) hs.pos (by omega : 0<M))
  have hmulpos : (0:ℝ) ≤ 4*(s : ℝ)*M := by positivity
  calc
    e-(h : ℝ) ≤ 4*(s : ℝ)*(M : ℝ)*
        (((successorRungs t h s M).card : ℝ)+2) := hcount
    _ ≤ 4*(s : ℝ)*(M : ℝ)*(eta*(H*logRate e/(s : ℝ))+C+2) :=
      mul_le_mul_of_nonneg_left (by linarith) hmulpos
    _ = 4*H*eta*(M : ℝ)*logRate e+4*(s : ℝ)*M*(C+2) := by
      field_simp [ne_of_gt hsreal]
      <;> ring

end EKG.PartB
