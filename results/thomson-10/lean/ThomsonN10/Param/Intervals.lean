/- Ported from root-parameter/project/N10Root/Intervals.lean (our earlier N10 root proof, Lean 4.33). -/
import ThomsonN10.Param.Definitions

namespace ThomsonN10.Param
noncomputable section

/-- Small project-specific real interval rules; every premise is proved for the inputs. -/
theorem sqrt_enclosure {x l u sl su : ℝ} (hx : l ≤ x ∧ x ≤ u)
    (_hsl : 0 ≤ sl) (hsu : 0 ≤ su) (hl : sl^2 ≤ l) (hu : u ≤ su^2) :
    sl ≤ Real.sqrt x ∧ Real.sqrt x ≤ su := by
  exact ⟨Real.le_sqrt_of_sq_le (hl.trans hx.1),
    Real.sqrt_le_iff.mpr ⟨hsu,hx.2.trans hu⟩⟩

theorem mul_enclosure {x y xl xu yl yu : ℝ} (hx : xl ≤ x ∧ x ≤ xu)
    (hy : yl ≤ y ∧ y ≤ yu) (hxl : 0 ≤ xl) (hyl : 0 ≤ yl) :
    xl*yl ≤ x*y ∧ x*y ≤ xu*yu := by
  exact ⟨mul_le_mul hx.1 hy.1 hyl (hxl.trans hx.1),
    mul_le_mul hx.2 hy.2 (hyl.trans hy.1) (hxl.trans (hx.1.trans hx.2))⟩

theorem div_enclosure {x y xl xu yl yu : ℝ} (hx : xl ≤ x ∧ x ≤ xu)
    (hy : yl ≤ y ∧ y ≤ yu) (hxl : 0 ≤ xl) (hyl : 0 < yl) :
    xl/yu ≤ x/y ∧ x/y ≤ xu/yl := by
  have hxp := hxl.trans hx.1
  have hyp := hyl.trans_le hy.1
  exact ⟨div_le_div₀ hxp hx.1 hyp hy.2,
    div_le_div₀ (hxp.trans hx.2) hx.2 hyl hy.1⟩

/-- Outward rounding never changes the underlying real enclosure. -/
theorem weaken_enclosure {x l u l' u' : ℝ} (hx : l ≤ x ∧ x ≤ u)
    (hl : l' ≤ l) (hu : u ≤ u') : l' ≤ x ∧ x ≤ u' :=
  ⟨hl.trans hx.1,hx.2.trans hu⟩
theorem add_enclosure {x y xl xu yl yu : ℝ} (hx : xl ≤ x ∧ x ≤ xu)
    (hy : yl ≤ y ∧ y ≤ yu) : xl+yl ≤ x+y ∧ x+y ≤ xu+yu := by
  constructor <;> linarith [hx.1,hx.2,hy.1,hy.2]

theorem sub_enclosure {x y xl xu yl yu : ℝ} (hx : xl ≤ x ∧ x ≤ xu)
    (hy : yl ≤ y ∧ y ≤ yu) : xl-yu ≤ x-y ∧ x-y ≤ xu-yl := by
  constructor <;> linarith [hx.1,hx.2,hy.1,hy.2]

end
end ThomsonN10.Param
