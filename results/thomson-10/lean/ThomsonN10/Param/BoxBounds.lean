/- Ported from root-parameter/project/N10Root/BoxBounds.lean (our earlier N10 root proof, Lean 4.33). -/
import ThomsonN10.Param.Endpoints
namespace ThomsonN10.Param
noncomputable section

variable {h : ℝ}

def box_b0L : ℝ := (21134371202199 / 50000000000000 : ℝ)
def box_b0U : ℝ := (105671856011 / 250000000000 : ℝ)

theorem box_b0_enclosure (hh : h ∈ Set.Icc coarseLeft coarseRight) : box_b0L ≤ h ∧ h ≤ box_b0U := by
  norm_num [Set.mem_Icc,box_b0L,box_b0U,coarseLeft,coarseRight] at hh ⊢
  exact hh

def box_b1L : ℝ := (1709679290002018430137083 / 1208925819614629174706176 : ℝ)
def box_b1U : ℝ := (427419822500504607534271 / 302231454903657293676544 : ℝ)

theorem box_b1_enclosure (hh : h ∈ Set.Icc coarseLeft coarseRight) : box_b1L ≤ r ∧ r ≤ box_b1U := by
  exact weaken_enclosure r_enclosure (by norm_num [box_b1L,rBoundL]) (by norm_num [rBoundU,box_b1U])

def box_b2L : ℝ := (107996159323355630127909 / 604462909807314587353088 : ℝ)
def box_b2U : ℝ := (215992318646731700165441 / 1208925819614629174706176 : ℝ)

theorem box_b2_enclosure (hh : h ∈ Set.Icc coarseLeft coarseRight) : box_b2L ≤ (h) * (h) ∧ (h) * (h) ≤ box_b2U := by
  have hh0 := mul_enclosure (box_b0_enclosure hh) (box_b0_enclosure hh) (by norm_num [box_b0L]) (by norm_num [box_b0L])
  exact weaken_enclosure hh0 (by norm_num [box_b0L,box_b0U,box_b0L,box_b0U,box_b2L])
    (by norm_num [box_b0L,box_b0U,box_b0L,box_b0U,box_b2U])

def box_b3L : ℝ := (2 : ℝ)
def box_b3U : ℝ := (2 : ℝ)

theorem box_b3_enclosure (hh : h ∈ Set.Icc coarseLeft coarseRight) : box_b3L ≤ (2 : ℝ) ∧ (2 : ℝ) ≤ box_b3U := by
  norm_num [box_b3L,box_b3U]

def box_b4L : ℝ := (4127530929231276779549435 / 1208925819614629174706176 : ℝ)
def box_b4U : ℝ := (1031882732307819194887359 / 302231454903657293676544 : ℝ)

theorem box_b4_enclosure (hh : h ∈ Set.Icc coarseLeft coarseRight) : box_b4L ≤ ((2 : ℝ)) + (r) ∧ ((2 : ℝ)) + (r) ≤ box_b4U := by
  have hh0 := add_enclosure (box_b3_enclosure hh) (box_b1_enclosure hh)
  exact weaken_enclosure hh0 (by norm_num [box_b3L,box_b3U,box_b1L,box_b1U,box_b4L])
    (by norm_num [box_b3L,box_b3U,box_b1L,box_b1U,box_b4U])

def box_b5L : ℝ := (177043087306809979818817 / 302231454903657293676544 : ℝ)
def box_b5U : ℝ := (708172349227239919275269 / 1208925819614629174706176 : ℝ)

theorem box_b5_enclosure (hh : h ∈ Set.Icc coarseLeft coarseRight) : box_b5L ≤ ((2 : ℝ)) - (r) ∧ ((2 : ℝ)) - (r) ≤ box_b5U := by
  have hh0 := sub_enclosure (box_b3_enclosure hh) (box_b1_enclosure hh)
  exact weaken_enclosure hh0 (by norm_num [box_b3L,box_b3U,box_b1L,box_b1U,box_b5L])
    (by norm_num [box_b3L,box_b3U,box_b1L,box_b1U,box_b5U])

def box_b6L : ℝ := (4 : ℝ)
def box_b6U : ℝ := (4 : ℝ)

theorem box_b6_enclosure (hh : h ∈ Set.Icc coarseLeft coarseRight) : box_b6L ≤ (4 : ℝ) ∧ (4 : ℝ) ≤ box_b6U := by
  norm_num [box_b6L,box_b6U]

def box_b7L : ℝ := (1709679290002018430137083 / 302231454903657293676544 : ℝ)
def box_b7U : ℝ := (427419822500504607534271 / 75557863725914323419136 : ℝ)

theorem box_b7_enclosure (hh : h ∈ Set.Icc coarseLeft coarseRight) : box_b7L ≤ ((4 : ℝ)) * (r) ∧ ((4 : ℝ)) * (r) ≤ box_b7U := by
  have hh0 := mul_enclosure (box_b6_enclosure hh) (box_b1_enclosure hh) (by norm_num [box_b6L]) (by norm_num [box_b1L])
  exact weaken_enclosure hh0 (by norm_num [box_b6L,box_b6U,box_b1L,box_b1U,box_b7L])
    (by norm_num [box_b6L,box_b6U,box_b1L,box_b1U,box_b7U])

def box_b8L : ℝ := (2314142199809333017490171 / 302231454903657293676544 : ℝ)
def box_b8U : ℝ := (578535549952333254372543 / 75557863725914323419136 : ℝ)

theorem box_b8_enclosure (hh : h ∈ Set.Icc coarseLeft coarseRight) : box_b8L ≤ (((4 : ℝ)) * (r)) + ((2 : ℝ)) ∧ (((4 : ℝ)) * (r)) + ((2 : ℝ)) ≤ box_b8U := by
  have hh0 := add_enclosure (box_b7_enclosure hh) (box_b3_enclosure hh)
  exact weaken_enclosure hh0 (by norm_num [box_b7L,box_b7U,box_b3L,box_b3U,box_b8L])
    (by norm_num [box_b7L,box_b7U,box_b3L,box_b3U,box_b8U])

def box_b9L : ℝ := (1 : ℝ)
def box_b9U : ℝ := (1 : ℝ)

theorem box_b9_enclosure (hh : h ∈ Set.Icc coarseLeft coarseRight) : box_b9L ≤ (1 : ℝ) ∧ (1 : ℝ) ≤ box_b9U := by
  norm_num [box_b9L,box_b9U]

def box_b10L : ℝ := (992933500967897474540735 / 1208925819614629174706176 : ℝ)
def box_b10U : ℝ := (496466750483958957225179 / 604462909807314587353088 : ℝ)

theorem box_b10_enclosure (hh : h ∈ Set.Icc coarseLeft coarseRight) : box_b10L ≤ ((1 : ℝ)) - ((h) * (h)) ∧ ((1 : ℝ)) - ((h) * (h)) ≤ box_b10U := by
  have hh0 := sub_enclosure (box_b9_enclosure hh) (box_b2_enclosure hh)
  exact weaken_enclosure hh0 (by norm_num [box_b9L,box_b9U,box_b2L,box_b2U,box_b10L])
    (by norm_num [box_b9L,box_b9U,box_b2L,box_b2U,box_b10U])

def box_b11L : ℝ := (368721951846006368064905 / 604462909807314587353088 : ℝ)
def box_b11U : ℝ := (737443903692082522346459 / 1208925819614629174706176 : ℝ)

theorem box_b11_enclosure (hh : h ∈ Set.Icc coarseLeft coarseRight) : box_b11L ≤ (((2 : ℝ)) + (r)) * ((h) * (h)) ∧ (((2 : ℝ)) + (r)) * ((h) * (h)) ≤ box_b11U := by
  have hh0 := mul_enclosure (box_b4_enclosure hh) (box_b2_enclosure hh) (by norm_num [box_b4L]) (by norm_num [box_b2L])
  exact weaken_enclosure hh0 (by norm_num [box_b4L,box_b4U,box_b2L,box_b2U,box_b11L])
    (by norm_num [box_b4L,box_b4U,box_b2L,box_b2U,box_b11U])

def box_b12L : ℝ := (722808126459626327702539 / 604462909807314587353088 : ℝ)
def box_b12U : ℝ := (45175507903728826300679 / 37778931862957161709568 : ℝ)

theorem box_b12_enclosure (hh : h ∈ Set.Icc coarseLeft coarseRight) : box_b12L ≤ (((2 : ℝ)) - (r)) + ((((2 : ℝ)) + (r)) * ((h) * (h))) ∧ (((2 : ℝ)) - (r)) + ((((2 : ℝ)) + (r)) * ((h) * (h))) ≤ box_b12U := by
  have hh0 := add_enclosure (box_b5_enclosure hh) (box_b11_enclosure hh)
  exact weaken_enclosure hh0 (by norm_num [box_b5L,box_b5U,box_b11L,box_b11U,box_b12L])
    (by norm_num [box_b5L,box_b5U,box_b11L,box_b11U,box_b12U])

def box_b13L : ℝ := (126525370894832304893461 / 1208925819614629174706176 : ℝ)
def box_b13U : ℝ := (63262685447422139157653 / 604462909807314587353088 : ℝ)

theorem box_b13_enclosure (hh : h ∈ Set.Icc coarseLeft coarseRight) : box_b13L ≤ (((2 : ℝ)) - (r)) * ((h) * (h)) ∧ (((2 : ℝ)) - (r)) * ((h) * (h)) ≤ box_b13U := by
  have hh0 := mul_enclosure (box_b5_enclosure hh) (box_b2_enclosure hh) (by norm_num [box_b5L]) (by norm_num [box_b2L])
  exact weaken_enclosure hh0 (by norm_num [box_b5L,box_b5U,box_b2L,box_b2U,box_b13L])
    (by norm_num [box_b5L,box_b5U,box_b2L,box_b2U,box_b13U])

def box_b14L : ℝ := (265878518757881817777681 / 75557863725914323419136 : ℝ)
def box_b14U : ℝ := (2127028150063060528932371 / 604462909807314587353088 : ℝ)

theorem box_b14_enclosure (hh : h ∈ Set.Icc coarseLeft coarseRight) : box_b14L ≤ (((2 : ℝ)) + (r)) + ((((2 : ℝ)) - (r)) * ((h) * (h))) ∧ (((2 : ℝ)) + (r)) + ((((2 : ℝ)) - (r)) * ((h) * (h))) ≤ box_b14U := by
  have hh0 := add_enclosure (box_b4_enclosure hh) (box_b13_enclosure hh)
  exact weaken_enclosure hh0 (by norm_num [box_b4L,box_b4U,box_b13L,box_b13U,box_b14L])
    (by norm_num [box_b4L,box_b4U,box_b13L,box_b13U,box_b14U])

def box_b15L : ℝ := (1021995481106329672236901 / 1208925819614629174706176 : ℝ)
def box_b15U : ℝ := (1021995481106378029269687 / 1208925819614629174706176 : ℝ)

theorem box_b15_enclosure (hh : h ∈ Set.Icc coarseLeft coarseRight) : box_b15L ≤ ((2 : ℝ)) * (h) ∧ ((2 : ℝ)) * (h) ≤ box_b15U := by
  have hh0 := mul_enclosure (box_b3_enclosure hh) (box_b0_enclosure hh) (by norm_num [box_b3L]) (by norm_num [box_b0L])
  exact weaken_enclosure hh0 (by norm_num [box_b3L,box_b3U,box_b0L,box_b0U,box_b15L])
    (by norm_num [box_b3L,box_b3U,box_b0L,box_b0U,box_b15U])

def box_b16L : ℝ := (1395856158122880320142665 / 1208925819614629174706176 : ℝ)
def box_b16U : ℝ := (1395856158122928677175451 / 1208925819614629174706176 : ℝ)

theorem box_b16_enclosure (hh : h ∈ Set.Icc coarseLeft coarseRight) : box_b16L ≤ ((2 : ℝ)) - (((2 : ℝ)) * (h)) ∧ ((2 : ℝ)) - (((2 : ℝ)) * (h)) ≤ box_b16U := by
  have hh0 := sub_enclosure (box_b3_enclosure hh) (box_b15_enclosure hh)
  exact weaken_enclosure hh0 (by norm_num [box_b3L,box_b3U,box_b15L,box_b15U,box_b16L])
    (by norm_num [box_b3L,box_b3U,box_b15L,box_b15U,box_b16U])

def box_b17L : ℝ := (3439847120335588021649253 / 1208925819614629174706176 : ℝ)
def box_b17U : ℝ := (3439847120335636378682039 / 1208925819614629174706176 : ℝ)

theorem box_b17_enclosure (hh : h ∈ Set.Icc coarseLeft coarseRight) : box_b17L ≤ ((2 : ℝ)) + (((2 : ℝ)) * (h)) ∧ ((2 : ℝ)) + (((2 : ℝ)) * (h)) ≤ box_b17U := by
  have hh0 := add_enclosure (box_b3_enclosure hh) (box_b15_enclosure hh)
  exact weaken_enclosure hh0 (by norm_num [box_b3L,box_b3U,box_b15L,box_b15U,box_b17L])
    (by norm_num [box_b3L,box_b3U,box_b15L,box_b15U,box_b17U])

def box_b18L : ℝ := (547809945711201615583113 / 604462909807314587353088 : ℝ)
def box_b18U : ℝ := (547809945711207254020013 / 604462909807314587353088 : ℝ)

theorem box_b18_enclosure (hh : h ∈ Set.Icc coarseLeft coarseRight) : box_b18L ≤ Real.sqrt (((1 : ℝ)) - ((h) * (h))) ∧ Real.sqrt (((1 : ℝ)) - ((h) * (h))) ≤ box_b18U := by
  apply sqrt_enclosure (box_b10_enclosure hh) <;> norm_num [box_b10L,box_b10U,box_b18L,box_b18U]

def box_b19L : ℝ := (660992211264368186612705 / 604462909807314587353088 : ℝ)
def box_b19U : ℝ := (1321984422528768282209255 / 1208925819614629174706176 : ℝ)

theorem box_b19_enclosure (hh : h ∈ Set.Icc coarseLeft coarseRight) : box_b19L ≤ Real.sqrt ((((2 : ℝ)) - (r)) + ((((2 : ℝ)) + (r)) * ((h) * (h)))) ∧ Real.sqrt ((((2 : ℝ)) - (r)) + ((((2 : ℝ)) + (r)) * ((h) * (h)))) ≤ box_b19U := by
  apply sqrt_enclosure (box_b12_enclosure hh) <;> norm_num [box_b12L,box_b12U,box_b19L,box_b19U]

def box_b20L : ℝ := (1133891363768673976433903 / 604462909807314587353088 : ℝ)
def box_b20U : ℝ := (2267782727537351144306441 / 1208925819614629174706176 : ℝ)

theorem box_b20_enclosure (hh : h ∈ Set.Icc coarseLeft coarseRight) : box_b20L ≤ Real.sqrt ((((2 : ℝ)) + (r)) + ((((2 : ℝ)) - (r)) * ((h) * (h)))) ∧ Real.sqrt ((((2 : ℝ)) + (r)) + ((((2 : ℝ)) - (r)) * ((h) * (h)))) ≤ box_b20U := by
  apply sqrt_enclosure (box_b14_enclosure hh) <;> norm_num [box_b14L,box_b14U,box_b20L,box_b20U]

def box_b21L : ℝ := (162379116095964528908465 / 151115727451828646838272 : ℝ)
def box_b21U : ℝ := (649516464383869366323547 / 604462909807314587353088 : ℝ)

theorem box_b21_enclosure (hh : h ∈ Set.Icc coarseLeft coarseRight) : box_b21L ≤ Real.sqrt (((2 : ℝ)) - (((2 : ℝ)) * (h))) ∧ Real.sqrt (((2 : ℝ)) - (((2 : ℝ)) * (h))) ≤ box_b21U := by
  apply sqrt_enclosure (box_b16_enclosure hh) <;> norm_num [box_b16L,box_b16U,box_b21L,box_b21U]

def box_b22L : ℝ := (2039244958140321773100713 / 1208925819614629174706176 : ℝ)
def box_b22U : ℝ := (2039244958140336106853327 / 1208925819614629174706176 : ℝ)

theorem box_b22_enclosure (hh : h ∈ Set.Icc coarseLeft coarseRight) : box_b22L ≤ Real.sqrt (((2 : ℝ)) + (((2 : ℝ)) * (h))) ∧ Real.sqrt (((2 : ℝ)) + (((2 : ℝ)) * (h))) ≤ box_b22U := by
  apply sqrt_enclosure (box_b17_enclosure hh) <;> norm_num [box_b17L,box_b17U,box_b22L,box_b22U]

def box_b23L : ℝ := (107996159323355630127909 / 302231454903657293676544 : ℝ)
def box_b23U : ℝ := (215992318646731700165441 / 604462909807314587353088 : ℝ)

theorem box_b23_enclosure (hh : h ∈ Set.Icc coarseLeft coarseRight) : box_b23L ≤ ((2 : ℝ)) * ((h) * (h)) ∧ ((2 : ℝ)) * ((h) * (h)) ≤ box_b23U := by
  have hh0 := mul_enclosure (box_b3_enclosure hh) (box_b2_enclosure hh) (by norm_num [box_b3L]) (by norm_num [box_b2L])
  exact weaken_enclosure hh0 (by norm_num [box_b3L,box_b3U,box_b2L,box_b2U,box_b23L])
    (by norm_num [box_b3L,box_b3U,box_b2L,box_b2U,box_b23U])

def box_b24L : ℝ := (410227614227012923804453 / 302231454903657293676544 : ℝ)
def box_b24U : ℝ := (820455228454046287518529 / 604462909807314587353088 : ℝ)

theorem box_b24_enclosure (hh : h ∈ Set.Icc coarseLeft coarseRight) : box_b24L ≤ ((1 : ℝ)) + (((2 : ℝ)) * ((h) * (h))) ∧ ((1 : ℝ)) + (((2 : ℝ)) * ((h) * (h))) ≤ box_b24U := by
  have hh0 := add_enclosure (box_b9_enclosure hh) (box_b23_enclosure hh)
  exact weaken_enclosure hh0 (by norm_num [box_b9L,box_b9U,box_b23L,box_b23U,box_b24L])
    (by norm_num [box_b9L,box_b9U,box_b23L,box_b23U,box_b24U])

def box_b25L : ℝ := (3141053051253224708982337 / 302231454903657293676544 : ℝ)
def box_b25U : ℝ := (6282106102506605923373533 / 604462909807314587353088 : ℝ)

theorem box_b25_enclosure (hh : h ∈ Set.Icc coarseLeft coarseRight) : box_b25L ≤ ((((4 : ℝ)) * (r)) + ((2 : ℝ))) * (((1 : ℝ)) + (((2 : ℝ)) * ((h) * (h)))) ∧ ((((4 : ℝ)) * (r)) + ((2 : ℝ))) * (((1 : ℝ)) + (((2 : ℝ)) * ((h) * (h)))) ≤ box_b25U := by
  have hh0 := mul_enclosure (box_b8_enclosure hh) (box_b24_enclosure hh) (by norm_num [box_b8L]) (by norm_num [box_b24L])
  exact weaken_enclosure hh0 (by norm_num [box_b8L,box_b8U,box_b24L,box_b24U,box_b25L])
    (by norm_num [box_b8L,box_b8U,box_b24L,box_b24U,box_b25U])

def box_b26L : ℝ := (8 : ℝ)
def box_b26U : ℝ := (8 : ℝ)

theorem box_b26_enclosure (hh : h ∈ Set.Icc coarseLeft coarseRight) : box_b26L ≤ (8 : ℝ) ∧ (8 : ℝ) ≤ box_b26U := by
  norm_num [box_b26L,box_b26U]

def box_b27L : ℝ := (4127530929231276779549435 / 151115727451828646838272 : ℝ)
def box_b27U : ℝ := (1031882732307819194887359 / 37778931862957161709568 : ℝ)

theorem box_b27_enclosure (hh : h ∈ Set.Icc coarseLeft coarseRight) : box_b27L ≤ ((8 : ℝ)) * (((2 : ℝ)) + (r)) ∧ ((8 : ℝ)) * (((2 : ℝ)) + (r)) ≤ box_b27U := by
  have hh0 := mul_enclosure (box_b26_enclosure hh) (box_b4_enclosure hh) (by norm_num [box_b26L]) (by norm_num [box_b4L])
  exact weaken_enclosure hh0 (by norm_num [box_b26L,box_b26U,box_b4L,box_b4U,box_b27L])
    (by norm_num [box_b26L,box_b26U,box_b4L,box_b4U,box_b27U])

def box_b28L : ℝ := (4127530929231276779549435 / 604462909807314587353088 : ℝ)
def box_b28U : ℝ := (1031882732307819194887359 / 151115727451828646838272 : ℝ)

theorem box_b28_enclosure (hh : h ∈ Set.Icc coarseLeft coarseRight) : box_b28L ≤ ((2 : ℝ)) * (((2 : ℝ)) + (r)) ∧ ((2 : ℝ)) * (((2 : ℝ)) + (r)) ≤ box_b28U := by
  have hh0 := mul_enclosure (box_b3_enclosure hh) (box_b4_enclosure hh) (by norm_num [box_b3L]) (by norm_num [box_b4L])
  exact weaken_enclosure hh0 (by norm_num [box_b3L,box_b3U,box_b4L,box_b4U,box_b28L])
    (by norm_num [box_b3L,box_b3U,box_b4L,box_b4U,box_b28U])

def box_b29L : ℝ := (368721951846006368064905 / 302231454903657293676544 : ℝ)
def box_b29U : ℝ := (737443903692082522346459 / 604462909807314587353088 : ℝ)

theorem box_b29_enclosure (hh : h ∈ Set.Icc coarseLeft coarseRight) : box_b29L ≤ (((2 : ℝ)) * (((2 : ℝ)) + (r))) * ((h) * (h)) ∧ (((2 : ℝ)) * (((2 : ℝ)) + (r))) * ((h) * (h)) ≤ box_b29U := by
  have hh0 := mul_enclosure (box_b28_enclosure hh) (box_b2_enclosure hh) (by norm_num [box_b28L]) (by norm_num [box_b2L])
  exact weaken_enclosure hh0 (by norm_num [box_b28L,box_b28U,box_b2L,box_b2U,box_b29L])
    (by norm_num [box_b28L,box_b28U,box_b2L,box_b2U,box_b29U])

def box_b30L : ℝ := (766715458156785552984351 / 1208925819614629174706176 : ℝ)
def box_b30U : ℝ := (383357729078462562708825 / 604462909807314587353088 : ℝ)

theorem box_b30_enclosure (hh : h ∈ Set.Icc coarseLeft coarseRight) : box_b30L ≤ ((((2 : ℝ)) * (((2 : ℝ)) + (r))) * ((h) * (h))) - (((2 : ℝ)) - (r)) ∧ ((((2 : ℝ)) * (((2 : ℝ)) + (r))) * ((h) * (h))) - (((2 : ℝ)) - (r)) ≤ box_b30U := by
  have hh0 := sub_enclosure (box_b29_enclosure hh) (box_b5_enclosure hh)
  exact weaken_enclosure hh0 (by norm_num [box_b29L,box_b29U,box_b5L,box_b5U,box_b30L])
    (by norm_num [box_b29L,box_b29U,box_b5L,box_b5U,box_b30U])

def box_b31L : ℝ := (20941842525759987988822845 / 1208925819614629174706176 : ℝ)
def box_b31U : ℝ := (10470921262881900114790237 / 604462909807314587353088 : ℝ)

theorem box_b31_enclosure (hh : h ∈ Set.Icc coarseLeft coarseRight) : box_b31L ≤ (((8 : ℝ)) * (((2 : ℝ)) + (r))) * (((((2 : ℝ)) * (((2 : ℝ)) + (r))) * ((h) * (h))) - (((2 : ℝ)) - (r))) ∧ (((8 : ℝ)) * (((2 : ℝ)) + (r))) * (((((2 : ℝ)) * (((2 : ℝ)) + (r))) * ((h) * (h))) - (((2 : ℝ)) - (r))) ≤ box_b31U := by
  have hh0 := mul_enclosure (box_b27_enclosure hh) (box_b30_enclosure hh) (by norm_num [box_b27L]) (by norm_num [box_b30L])
  exact weaken_enclosure hh0 (by norm_num [box_b27L,box_b27U,box_b30L,box_b30U,box_b31L])
    (by norm_num [box_b27L,box_b27U,box_b30L,box_b30U,box_b31U])

def box_b32L : ℝ := (177043087306809979818817 / 37778931862957161709568 : ℝ)
def box_b32U : ℝ := (708172349227239919275269 / 151115727451828646838272 : ℝ)

theorem box_b32_enclosure (hh : h ∈ Set.Icc coarseLeft coarseRight) : box_b32L ≤ ((8 : ℝ)) * (((2 : ℝ)) - (r)) ∧ ((8 : ℝ)) * (((2 : ℝ)) - (r)) ≤ box_b32U := by
  have hh0 := mul_enclosure (box_b26_enclosure hh) (box_b5_enclosure hh) (by norm_num [box_b26L]) (by norm_num [box_b5L])
  exact weaken_enclosure hh0 (by norm_num [box_b26L,box_b26U,box_b5L,box_b5U,box_b32L])
    (by norm_num [box_b26L,box_b26U,box_b5L,box_b5U,box_b32U])

def box_b33L : ℝ := (177043087306809979818817 / 151115727451828646838272 : ℝ)
def box_b33U : ℝ := (708172349227239919275269 / 604462909807314587353088 : ℝ)

theorem box_b33_enclosure (hh : h ∈ Set.Icc coarseLeft coarseRight) : box_b33L ≤ ((2 : ℝ)) * (((2 : ℝ)) - (r)) ∧ ((2 : ℝ)) * (((2 : ℝ)) - (r)) ≤ box_b33U := by
  have hh0 := mul_enclosure (box_b3_enclosure hh) (box_b5_enclosure hh) (by norm_num [box_b3L]) (by norm_num [box_b5L])
  exact weaken_enclosure hh0 (by norm_num [box_b3L,box_b3U,box_b5L,box_b5U,box_b33L])
    (by norm_num [box_b3L,box_b3U,box_b5L,box_b5U,box_b33U])

def box_b34L : ℝ := (253050741789664609786923 / 1208925819614629174706176 : ℝ)
def box_b34U : ℝ := (253050741789688556630611 / 1208925819614629174706176 : ℝ)

theorem box_b34_enclosure (hh : h ∈ Set.Icc coarseLeft coarseRight) : box_b34L ≤ (((2 : ℝ)) * (((2 : ℝ)) - (r))) * ((h) * (h)) ∧ (((2 : ℝ)) * (((2 : ℝ)) - (r))) * ((h) * (h)) ≤ box_b34U := by
  have hh0 := mul_enclosure (box_b33_enclosure hh) (box_b2_enclosure hh) (by norm_num [box_b33L]) (by norm_num [box_b2L])
  exact weaken_enclosure hh0 (by norm_num [box_b33L,box_b33U,box_b2L,box_b2U,box_b34L])
    (by norm_num [box_b33L,box_b33U,box_b2L,box_b2U,box_b34U])

def box_b35L : ℝ := (484310023430198527864853 / 151115727451828646838272 : ℝ)
def box_b35U : ℝ := (3874480187441612169762513 / 1208925819614629174706176 : ℝ)

theorem box_b35_enclosure (hh : h ∈ Set.Icc coarseLeft coarseRight) : box_b35L ≤ (((2 : ℝ)) + (r)) - ((((2 : ℝ)) * (((2 : ℝ)) - (r))) * ((h) * (h))) ∧ (((2 : ℝ)) + (r)) - ((((2 : ℝ)) * (((2 : ℝ)) - (r))) * ((h) * (h))) ≤ box_b35U := by
  have hh0 := sub_enclosure (box_b4_enclosure hh) (box_b34_enclosure hh)
  exact weaken_enclosure hh0 (by norm_num [box_b4L,box_b4U,box_b34L,box_b34U,box_b35L])
    (by norm_num [box_b4L,box_b4U,box_b34L,box_b34U,box_b35U])

def box_b36L : ℝ := (18156943573259447388413355 / 1208925819614629174706176 : ℝ)
def box_b36U : ℝ := (9078471786629779805151719 / 604462909807314587353088 : ℝ)

theorem box_b36_enclosure (hh : h ∈ Set.Icc coarseLeft coarseRight) : box_b36L ≤ (((8 : ℝ)) * (((2 : ℝ)) - (r))) * ((((2 : ℝ)) + (r)) - ((((2 : ℝ)) * (((2 : ℝ)) - (r))) * ((h) * (h)))) ∧ (((8 : ℝ)) * (((2 : ℝ)) - (r))) * ((((2 : ℝ)) + (r)) - ((((2 : ℝ)) * (((2 : ℝ)) - (r))) * ((h) * (h)))) ≤ box_b36U := by
  have hh0 := mul_enclosure (box_b32_enclosure hh) (box_b35_enclosure hh) (by norm_num [box_b32L]) (by norm_num [box_b35L])
  exact weaken_enclosure hh0 (by norm_num [box_b32L,box_b32U,box_b35L,box_b35U,box_b36L])
    (by norm_num [box_b32L,box_b32U,box_b35L,box_b35U,box_b36U])

def box_b37L : ℝ := (24 : ℝ)
def box_b37U : ℝ := (24 : ℝ)

theorem box_b37_enclosure (hh : h ∈ Set.Icc coarseLeft coarseRight) : box_b37L ≤ (24 : ℝ) ∧ (24 : ℝ) ≤ box_b37U := by
  norm_num [box_b37L,box_b37U]

def box_b38L : ℝ := (815531376158917388739353 / 1208925819614629174706176 : ℝ)
def box_b38U : ℝ := (815531376158950964779657 / 1208925819614629174706176 : ℝ)

theorem box_b38_enclosure (hh : h ∈ Set.Icc coarseLeft coarseRight) : box_b38L ≤ (((1 : ℝ)) - ((h) * (h))) * (((1 : ℝ)) - ((h) * (h))) ∧ (((1 : ℝ)) - ((h) * (h))) * (((1 : ℝ)) - ((h) * (h))) ≤ box_b38U := by
  have hh0 := mul_enclosure (box_b10_enclosure hh) (box_b10_enclosure hh) (by norm_num [box_b10L]) (by norm_num [box_b10L])
  exact weaken_enclosure hh0 (by norm_num [box_b10L,box_b10U,box_b10L,box_b10U,box_b38L])
    (by norm_num [box_b10L,box_b10U,box_b10L,box_b10U,box_b38U])

def box_b39L : ℝ := (369548066267466370724897 / 604462909807314587353088 : ℝ)
def box_b39U : ℝ := (369548066267485388939785 / 604462909807314587353088 : ℝ)

theorem box_b39_enclosure (hh : h ∈ Set.Icc coarseLeft coarseRight) : box_b39L ≤ ((((1 : ℝ)) - ((h) * (h))) * (((1 : ℝ)) - ((h) * (h)))) * (Real.sqrt (((1 : ℝ)) - ((h) * (h)))) ∧ ((((1 : ℝ)) - ((h) * (h))) * (((1 : ℝ)) - ((h) * (h)))) * (Real.sqrt (((1 : ℝ)) - ((h) * (h)))) ≤ box_b39U := by
  have hh0 := mul_enclosure (box_b38_enclosure hh) (box_b18_enclosure hh) (by norm_num [box_b38L]) (by norm_num [box_b18L])
  exact weaken_enclosure hh0 (by norm_num [box_b38L,box_b38U,box_b18L,box_b18U,box_b39L])
    (by norm_num [box_b38L,box_b38U,box_b18L,box_b18U,box_b39U])

def box_b40L : ℝ := (1284440537327417608756065 / 75557863725914323419136 : ℝ)
def box_b40U : ℝ := (20551048597240251353744147 / 1208925819614629174706176 : ℝ)

theorem box_b40_enclosure (hh : h ∈ Set.Icc coarseLeft coarseRight) : box_b40L ≤ (((((4 : ℝ)) * (r)) + ((2 : ℝ))) * (((1 : ℝ)) + (((2 : ℝ)) * ((h) * (h))))) / (((((1 : ℝ)) - ((h) * (h))) * (((1 : ℝ)) - ((h) * (h)))) * (Real.sqrt (((1 : ℝ)) - ((h) * (h))))) ∧ (((((4 : ℝ)) * (r)) + ((2 : ℝ))) * (((1 : ℝ)) + (((2 : ℝ)) * ((h) * (h))))) / (((((1 : ℝ)) - ((h) * (h))) * (((1 : ℝ)) - ((h) * (h)))) * (Real.sqrt (((1 : ℝ)) - ((h) * (h))))) ≤ box_b40U := by
  have hh0 := div_enclosure (box_b25_enclosure hh) (box_b39_enclosure hh) (by norm_num [box_b25L]) (by norm_num [box_b39L])
  exact weaken_enclosure hh0 (by norm_num [box_b25L,box_b25U,box_b39L,box_b39U,box_b40L])
    (by norm_num [box_b25L,box_b25U,box_b39L,box_b39U,box_b40U])

def box_b41L : ℝ := (1728647297292790799306577 / 1208925819614629174706176 : ℝ)
def box_b41U : ℝ := (1728647297292957698031681 / 1208925819614629174706176 : ℝ)

theorem box_b41_enclosure (hh : h ∈ Set.Icc coarseLeft coarseRight) : box_b41L ≤ ((((2 : ℝ)) - (r)) + ((((2 : ℝ)) + (r)) * ((h) * (h)))) * ((((2 : ℝ)) - (r)) + ((((2 : ℝ)) + (r)) * ((h) * (h)))) ∧ ((((2 : ℝ)) - (r)) + ((((2 : ℝ)) + (r)) * ((h) * (h)))) * ((((2 : ℝ)) - (r)) + ((((2 : ℝ)) + (r)) * ((h) * (h)))) ≤ box_b41U := by
  have hh0 := mul_enclosure (box_b12_enclosure hh) (box_b12_enclosure hh) (by norm_num [box_b12L]) (by norm_num [box_b12L])
  exact weaken_enclosure hh0 (by norm_num [box_b12L,box_b12U,box_b12L,box_b12U,box_b41L])
    (by norm_num [box_b12L,box_b12U,box_b12L,box_b12U,box_b41U])

def box_b42L : ℝ := (1890310192726251236140331 / 1208925819614629174706176 : ℝ)
def box_b42U : ℝ := (1890310192726479369983563 / 1208925819614629174706176 : ℝ)

theorem box_b42_enclosure (hh : h ∈ Set.Icc coarseLeft coarseRight) : box_b42L ≤ (((((2 : ℝ)) - (r)) + ((((2 : ℝ)) + (r)) * ((h) * (h)))) * ((((2 : ℝ)) - (r)) + ((((2 : ℝ)) + (r)) * ((h) * (h))))) * (Real.sqrt ((((2 : ℝ)) - (r)) + ((((2 : ℝ)) + (r)) * ((h) * (h))))) ∧ (((((2 : ℝ)) - (r)) + ((((2 : ℝ)) + (r)) * ((h) * (h)))) * ((((2 : ℝ)) - (r)) + ((((2 : ℝ)) + (r)) * ((h) * (h))))) * (Real.sqrt ((((2 : ℝ)) - (r)) + ((((2 : ℝ)) + (r)) * ((h) * (h))))) ≤ box_b42U := by
  have hh0 := mul_enclosure (box_b41_enclosure hh) (box_b19_enclosure hh) (by norm_num [box_b41L]) (by norm_num [box_b19L])
  exact weaken_enclosure hh0 (by norm_num [box_b41L,box_b41U,box_b19L,box_b19U,box_b42L])
    (by norm_num [box_b41L,box_b41U,box_b19L,box_b19U,box_b42U])

def box_b43L : ℝ := (6696555474627909814686397 / 604462909807314587353088 : ℝ)
def box_b43U : ℝ := (6696555474629937031749941 / 604462909807314587353088 : ℝ)

theorem box_b43_enclosure (hh : h ∈ Set.Icc coarseLeft coarseRight) : box_b43L ≤ ((((8 : ℝ)) * (((2 : ℝ)) + (r))) * (((((2 : ℝ)) * (((2 : ℝ)) + (r))) * ((h) * (h))) - (((2 : ℝ)) - (r)))) / ((((((2 : ℝ)) - (r)) + ((((2 : ℝ)) + (r)) * ((h) * (h)))) * ((((2 : ℝ)) - (r)) + ((((2 : ℝ)) + (r)) * ((h) * (h))))) * (Real.sqrt ((((2 : ℝ)) - (r)) + ((((2 : ℝ)) + (r)) * ((h) * (h)))))) ∧ ((((8 : ℝ)) * (((2 : ℝ)) + (r))) * (((((2 : ℝ)) * (((2 : ℝ)) + (r))) * ((h) * (h))) - (((2 : ℝ)) - (r)))) / ((((((2 : ℝ)) - (r)) + ((((2 : ℝ)) + (r)) * ((h) * (h)))) * ((((2 : ℝ)) - (r)) + ((((2 : ℝ)) + (r)) * ((h) * (h))))) * (Real.sqrt ((((2 : ℝ)) - (r)) + ((((2 : ℝ)) + (r)) * ((h) * (h)))))) ≤ box_b43U := by
  have hh0 := div_enclosure (box_b31_enclosure hh) (box_b42_enclosure hh) (by norm_num [box_b31L]) (by norm_num [box_b42L])
  exact weaken_enclosure hh0 (by norm_num [box_b31L,box_b31U,box_b42L,box_b42U,box_b43L])
    (by norm_num [box_b31L,box_b31U,box_b42L,box_b42U,box_b43U])

def box_b44L : ℝ := (1871185426663672638279433 / 151115727451828646838272 : ℝ)
def box_b44U : ℝ := (7484741706654732686067341 / 604462909807314587353088 : ℝ)

theorem box_b44_enclosure (hh : h ∈ Set.Icc coarseLeft coarseRight) : box_b44L ≤ ((((2 : ℝ)) + (r)) + ((((2 : ℝ)) - (r)) * ((h) * (h)))) * ((((2 : ℝ)) + (r)) + ((((2 : ℝ)) - (r)) * ((h) * (h)))) ∧ ((((2 : ℝ)) + (r)) + ((((2 : ℝ)) - (r)) * ((h) * (h)))) * ((((2 : ℝ)) + (r)) + ((((2 : ℝ)) - (r)) * ((h) * (h)))) ≤ box_b44U := by
  have hh0 := mul_enclosure (box_b14_enclosure hh) (box_b14_enclosure hh) (by norm_num [box_b14L]) (by norm_num [box_b14L])
  exact weaken_enclosure hh0 (by norm_num [box_b14L,box_b14U,box_b14L,box_b14U,box_b44L])
    (by norm_num [box_b14L,box_b14U,box_b14L,box_b14U,box_b44U])

def box_b45L : ℝ := (7020185890247868344886295 / 302231454903657293676544 : ℝ)
def box_b45U : ℝ := (28080743560991670968954393 / 1208925819614629174706176 : ℝ)

theorem box_b45_enclosure (hh : h ∈ Set.Icc coarseLeft coarseRight) : box_b45L ≤ (((((2 : ℝ)) + (r)) + ((((2 : ℝ)) - (r)) * ((h) * (h)))) * ((((2 : ℝ)) + (r)) + ((((2 : ℝ)) - (r)) * ((h) * (h))))) * (Real.sqrt ((((2 : ℝ)) + (r)) + ((((2 : ℝ)) - (r)) * ((h) * (h))))) ∧ (((((2 : ℝ)) + (r)) + ((((2 : ℝ)) - (r)) * ((h) * (h)))) * ((((2 : ℝ)) + (r)) + ((((2 : ℝ)) - (r)) * ((h) * (h))))) * (Real.sqrt ((((2 : ℝ)) + (r)) + ((((2 : ℝ)) - (r)) * ((h) * (h))))) ≤ box_b45U := by
  have hh0 := mul_enclosure (box_b44_enclosure hh) (box_b20_enclosure hh) (by norm_num [box_b44L]) (by norm_num [box_b20L])
  exact weaken_enclosure hh0 (by norm_num [box_b44L,box_b44U,box_b20L,box_b20U,box_b45L])
    (by norm_num [box_b44L,box_b44U,box_b20L,box_b20U,box_b45U])

def box_b46L : ℝ := (781688627415536757908211 / 1208925819614629174706176 : ℝ)
def box_b46U : ℝ := (390844313707773544795493 / 604462909807314587353088 : ℝ)

theorem box_b46_enclosure (hh : h ∈ Set.Icc coarseLeft coarseRight) : box_b46L ≤ ((((8 : ℝ)) * (((2 : ℝ)) - (r))) * ((((2 : ℝ)) + (r)) - ((((2 : ℝ)) * (((2 : ℝ)) - (r))) * ((h) * (h))))) / ((((((2 : ℝ)) + (r)) + ((((2 : ℝ)) - (r)) * ((h) * (h)))) * ((((2 : ℝ)) + (r)) + ((((2 : ℝ)) - (r)) * ((h) * (h))))) * (Real.sqrt ((((2 : ℝ)) + (r)) + ((((2 : ℝ)) - (r)) * ((h) * (h)))))) ∧ ((((8 : ℝ)) * (((2 : ℝ)) - (r))) * ((((2 : ℝ)) + (r)) - ((((2 : ℝ)) * (((2 : ℝ)) - (r))) * ((h) * (h))))) / ((((((2 : ℝ)) + (r)) + ((((2 : ℝ)) - (r)) * ((h) * (h)))) * ((((2 : ℝ)) + (r)) + ((((2 : ℝ)) - (r)) * ((h) * (h))))) * (Real.sqrt ((((2 : ℝ)) + (r)) + ((((2 : ℝ)) - (r)) * ((h) * (h)))))) ≤ box_b46U := by
  have hh0 := div_enclosure (box_b36_enclosure hh) (box_b45_enclosure hh) (by norm_num [box_b36L]) (by norm_num [box_b45L])
  exact weaken_enclosure hh0 (by norm_num [box_b36L,box_b36U,box_b45L,box_b45U,box_b46L])
    (by norm_num [box_b36L,box_b36U,box_b45L,box_b45U,box_b46U])

def box_b47L : ℝ := (1611690628619931382407719 / 1208925819614629174706176 : ℝ)
def box_b47U : ℝ := (1611690628620043050900373 / 1208925819614629174706176 : ℝ)

theorem box_b47_enclosure (hh : h ∈ Set.Icc coarseLeft coarseRight) : box_b47L ≤ (((2 : ℝ)) - (((2 : ℝ)) * (h))) * (((2 : ℝ)) - (((2 : ℝ)) * (h))) ∧ (((2 : ℝ)) - (((2 : ℝ)) * (h))) * (((2 : ℝ)) - (((2 : ℝ)) * (h))) ≤ box_b47U := by
  have hh0 := mul_enclosure (box_b16_enclosure hh) (box_b16_enclosure hh) (by norm_num [box_b16L]) (by norm_num [box_b16L])
  exact weaken_enclosure hh0 (by norm_num [box_b16L,box_b16U,box_b16L,box_b16U,box_b47L])
    (by norm_num [box_b16L,box_b16U,box_b16L,box_b16U,box_b47U])

def box_b48L : ℝ := (1731817753905713714761195 / 1208925819614629174706176 : ℝ)
def box_b48U : ℝ := (1731817753905863704370475 / 1208925819614629174706176 : ℝ)

theorem box_b48_enclosure (hh : h ∈ Set.Icc coarseLeft coarseRight) : box_b48L ≤ ((((2 : ℝ)) - (((2 : ℝ)) * (h))) * (((2 : ℝ)) - (((2 : ℝ)) * (h)))) * (Real.sqrt (((2 : ℝ)) - (((2 : ℝ)) * (h)))) ∧ ((((2 : ℝ)) - (((2 : ℝ)) * (h))) * (((2 : ℝ)) - (((2 : ℝ)) * (h)))) * (Real.sqrt (((2 : ℝ)) - (((2 : ℝ)) * (h)))) ≤ box_b48U := by
  have hh0 := mul_enclosure (box_b47_enclosure hh) (box_b21_enclosure hh) (by norm_num [box_b47L]) (by norm_num [box_b21L])
  exact weaken_enclosure hh0 (by norm_num [box_b47L,box_b47U,box_b21L,box_b21U,box_b48L])
    (by norm_num [box_b47L,box_b47U,box_b21L,box_b21U,box_b48U])

def box_b49L : ℝ := (2531735745348547211620179 / 151115727451828646838272 : ℝ)
def box_b49U : ℝ := (632933936337191620170659 / 37778931862957161709568 : ℝ)

theorem box_b49_enclosure (hh : h ∈ Set.Icc coarseLeft coarseRight) : box_b49L ≤ ((24 : ℝ)) / (((((2 : ℝ)) - (((2 : ℝ)) * (h))) * (((2 : ℝ)) - (((2 : ℝ)) * (h)))) * (Real.sqrt (((2 : ℝ)) - (((2 : ℝ)) * (h))))) ∧ ((24 : ℝ)) / (((((2 : ℝ)) - (((2 : ℝ)) * (h))) * (((2 : ℝ)) - (((2 : ℝ)) * (h)))) * (Real.sqrt (((2 : ℝ)) - (((2 : ℝ)) * (h))))) ≤ box_b49U := by
  have hh0 := div_enclosure (box_b37_enclosure hh) (box_b48_enclosure hh) (by norm_num [box_b37L]) (by norm_num [box_b48L])
  exact weaken_enclosure hh0 (by norm_num [box_b37L,box_b37U,box_b48L,box_b48U,box_b49L])
    (by norm_num [box_b37L,box_b37U,box_b48L,box_b48U,box_b49U])

def box_b50L : ℝ := (2446913619367670107198895 / 302231454903657293676544 : ℝ)
def box_b50U : ℝ := (305864202420967363017663 / 37778931862957161709568 : ℝ)

theorem box_b50_enclosure (hh : h ∈ Set.Icc coarseLeft coarseRight) : box_b50L ≤ (((2 : ℝ)) + (((2 : ℝ)) * (h))) * (((2 : ℝ)) + (((2 : ℝ)) * (h))) ∧ (((2 : ℝ)) + (((2 : ℝ)) * (h))) * (((2 : ℝ)) + (((2 : ℝ)) * (h))) ≤ box_b50U := by
  have hh0 := mul_enclosure (box_b17_enclosure hh) (box_b17_enclosure hh) (by norm_num [box_b17L]) (by norm_num [box_b17L])
  exact weaken_enclosure hh0 (by norm_num [box_b17L,box_b17U,box_b17L,box_b17U,box_b50L])
    (by norm_num [box_b17L,box_b17U,box_b17L,box_b17U,box_b50U])

def box_b51L : ℝ := (8255024717548063480218873 / 604462909807314587353088 : ℝ)
def box_b51U : ℝ := (16510049435096707202069071 / 1208925819614629174706176 : ℝ)

theorem box_b51_enclosure (hh : h ∈ Set.Icc coarseLeft coarseRight) : box_b51L ≤ ((((2 : ℝ)) + (((2 : ℝ)) * (h))) * (((2 : ℝ)) + (((2 : ℝ)) * (h)))) * (Real.sqrt (((2 : ℝ)) + (((2 : ℝ)) * (h)))) ∧ ((((2 : ℝ)) + (((2 : ℝ)) * (h))) * (((2 : ℝ)) + (((2 : ℝ)) * (h)))) * (Real.sqrt (((2 : ℝ)) + (((2 : ℝ)) * (h)))) ≤ box_b51U := by
  have hh0 := mul_enclosure (box_b50_enclosure hh) (box_b22_enclosure hh) (by norm_num [box_b50L]) (by norm_num [box_b22L])
  exact weaken_enclosure hh0 (by norm_num [box_b50L,box_b50U,box_b22L,box_b22U,box_b51L])
    (by norm_num [box_b50L,box_b50U,box_b22L,box_b22U,box_b51U])

def box_b52L : ℝ := (2124526606284883786786391 / 1208925819614629174706176 : ℝ)
def box_b52U : ℝ := (2124526606284958452752031 / 1208925819614629174706176 : ℝ)

theorem box_b52_enclosure (hh : h ∈ Set.Icc coarseLeft coarseRight) : box_b52L ≤ ((24 : ℝ)) / (((((2 : ℝ)) + (((2 : ℝ)) * (h))) * (((2 : ℝ)) + (((2 : ℝ)) * (h)))) * (Real.sqrt (((2 : ℝ)) + (((2 : ℝ)) * (h))))) ∧ ((24 : ℝ)) / (((((2 : ℝ)) + (((2 : ℝ)) * (h))) * (((2 : ℝ)) + (((2 : ℝ)) * (h)))) * (Real.sqrt (((2 : ℝ)) + (((2 : ℝ)) * (h))))) ≤ box_b52U := by
  have hh0 := div_enclosure (box_b37_enclosure hh) (box_b51_enclosure hh) (by norm_num [box_b37L]) (by norm_num [box_b51L])
  exact weaken_enclosure hh0 (by norm_num [box_b37L,box_b37U,box_b51L,box_b51U,box_b52L])
    (by norm_num [box_b37L,box_b37U,box_b51L,box_b51U,box_b52U])

def box_b53L : ℝ := (5106928557087831322360837 / 604462909807314587353088 : ℝ)
def box_b53U : ℝ := (10213857114175767772767081 / 1208925819614629174706176 : ℝ)

theorem box_b53_enclosure (hh : h ∈ Set.Icc coarseLeft coarseRight) : box_b53L ≤ ((((4 : ℝ)) * (r)) + ((2 : ℝ))) / (Real.sqrt (((1 : ℝ)) - ((h) * (h)))) ∧ ((((4 : ℝ)) * (r)) + ((2 : ℝ))) / (Real.sqrt (((1 : ℝ)) - ((h) * (h)))) ≤ box_b53U := by
  have hh0 := div_enclosure (box_b8_enclosure hh) (box_b18_enclosure hh) (by norm_num [box_b8L]) (by norm_num [box_b18L])
  exact weaken_enclosure hh0 (by norm_num [box_b8L,box_b8U,box_b18L,box_b18U,box_b53L])
    (by norm_num [box_b8L,box_b8U,box_b18L,box_b18U,box_b53U])

def box_b54L : ℝ := (4422144807229295595599331 / 604462909807314587353088 : ℝ)
def box_b54U : ℝ := (4422144807229402333730893 / 604462909807314587353088 : ℝ)

theorem box_b54_enclosure (hh : h ∈ Set.Icc coarseLeft coarseRight) : box_b54L ≤ ((8 : ℝ)) / (Real.sqrt ((((2 : ℝ)) - (r)) + ((((2 : ℝ)) + (r)) * ((h) * (h))))) ∧ ((8 : ℝ)) / (Real.sqrt ((((2 : ℝ)) - (r)) + ((((2 : ℝ)) + (r)) * ((h) * (h))))) ≤ box_b54U := by
  have hh0 := div_enclosure (box_b26_enclosure hh) (box_b19_enclosure hh) (by norm_num [box_b26L]) (by norm_num [box_b19L])
  exact weaken_enclosure hh0 (by norm_num [box_b26L,box_b26U,box_b19L,box_b19U,box_b54L])
    (by norm_num [box_b26L,box_b26U,box_b19L,box_b19U,box_b54U])

def box_b55L : ℝ := (1288925627295864034356427 / 302231454903657293676544 : ℝ)
def box_b55U : ℝ := (2577851254591731696509287 / 604462909807314587353088 : ℝ)

theorem box_b55_enclosure (hh : h ∈ Set.Icc coarseLeft coarseRight) : box_b55L ≤ ((8 : ℝ)) / (Real.sqrt ((((2 : ℝ)) + (r)) + ((((2 : ℝ)) - (r)) * ((h) * (h))))) ∧ ((8 : ℝ)) / (Real.sqrt ((((2 : ℝ)) + (r)) + ((((2 : ℝ)) - (r)) * ((h) * (h))))) ≤ box_b55U := by
  have hh0 := div_enclosure (box_b26_enclosure hh) (box_b20_enclosure hh) (by norm_num [box_b26L]) (by norm_num [box_b20L])
  exact weaken_enclosure hh0 (by norm_num [box_b26L,box_b26U,box_b20L,box_b20U,box_b55L])
    (by norm_num [box_b26L,box_b26U,box_b20L,box_b20U,box_b55U])

def box_b56L : ℝ := (1125068968588257290210247 / 151115727451828646838272 : ℝ)
def box_b56U : ℝ := (9000551748706214225989703 / 1208925819614629174706176 : ℝ)

theorem box_b56_enclosure (hh : h ∈ Set.Icc coarseLeft coarseRight) : box_b56L ≤ ((8 : ℝ)) / (Real.sqrt (((2 : ℝ)) - (((2 : ℝ)) * (h)))) ∧ ((8 : ℝ)) / (Real.sqrt (((2 : ℝ)) - (((2 : ℝ)) * (h)))) ≤ box_b56U := by
  have hh0 := div_enclosure (box_b26_enclosure hh) (box_b21_enclosure hh) (by norm_num [box_b26L]) (by norm_num [box_b21L])
  exact weaken_enclosure hh0 (by norm_num [box_b26L,box_b26U,box_b21L,box_b21U,box_b56L])
    (by norm_num [box_b26L,box_b26U,box_b21L,box_b21U,box_b56U])

def box_b57L : ℝ := (5733501045067978601482537 / 1208925819614629174706176 : ℝ)
def box_b57U : ℝ := (5733501045068018901979673 / 1208925819614629174706176 : ℝ)

theorem box_b57_enclosure (hh : h ∈ Set.Icc coarseLeft coarseRight) : box_b57L ≤ ((8 : ℝ)) / (Real.sqrt (((2 : ℝ)) + (((2 : ℝ)) * (h)))) ∧ ((8 : ℝ)) / (Real.sqrt (((2 : ℝ)) + (((2 : ℝ)) * (h)))) ≤ box_b57U := by
  have hh0 := div_enclosure (box_b26_enclosure hh) (box_b22_enclosure hh) (by norm_num [box_b26L]) (by norm_num [box_b22L])
  exact weaken_enclosure hh0 (by norm_num [box_b26L,box_b26U,box_b22L,box_b22U,box_b57L])
    (by norm_num [box_b26L,box_b26U,box_b22L,box_b22U,box_b57U])

theorem coarse_second_positive {h : ℝ} (hh : h ∈ Set.Icc coarseLeft coarseRight) : 0 < second h := by
  have h0 := (box_b40_enclosure hh).1
  have h1 := (box_b43_enclosure hh).1
  have h2 := (box_b46_enclosure hh).2
  have h3 := (box_b49_enclosure hh).1
  have h4 := (box_b52_enclosure hh).1
  have hsum : box_b40L + box_b43L - box_b46U + box_b49L + box_b52L > 0 := by norm_num [box_b40L,box_b43L,box_b46U,box_b49L,box_b52L]
  have hid : second h = (((((4 : ℝ)) * (r)) + ((2 : ℝ))) * (((1 : ℝ)) + (((2 : ℝ)) * ((h) * (h))))) / (((((1 : ℝ)) - ((h) * (h))) * (((1 : ℝ)) - ((h) * (h)))) * (Real.sqrt (((1 : ℝ)) - ((h) * (h))))) + ((((8 : ℝ)) * (((2 : ℝ)) + (r))) * (((((2 : ℝ)) * (((2 : ℝ)) + (r))) * ((h) * (h))) - (((2 : ℝ)) - (r)))) / ((((((2 : ℝ)) - (r)) + ((((2 : ℝ)) + (r)) * ((h) * (h)))) * ((((2 : ℝ)) - (r)) + ((((2 : ℝ)) + (r)) * ((h) * (h))))) * (Real.sqrt ((((2 : ℝ)) - (r)) + ((((2 : ℝ)) + (r)) * ((h) * (h)))))) - ((((8 : ℝ)) * (((2 : ℝ)) - (r))) * ((((2 : ℝ)) + (r)) - ((((2 : ℝ)) * (((2 : ℝ)) - (r))) * ((h) * (h))))) / ((((((2 : ℝ)) + (r)) + ((((2 : ℝ)) - (r)) * ((h) * (h)))) * ((((2 : ℝ)) + (r)) + ((((2 : ℝ)) - (r)) * ((h) * (h))))) * (Real.sqrt ((((2 : ℝ)) + (r)) + ((((2 : ℝ)) - (r)) * ((h) * (h)))))) + ((24 : ℝ)) / (((((2 : ℝ)) - (((2 : ℝ)) * (h))) * (((2 : ℝ)) - (((2 : ℝ)) * (h)))) * (Real.sqrt (((2 : ℝ)) - (((2 : ℝ)) * (h))))) + ((24 : ℝ)) / (((((2 : ℝ)) + (((2 : ℝ)) * (h))) * (((2 : ℝ)) + (((2 : ℝ)) * (h)))) * (Real.sqrt (((2 : ℝ)) + (((2 : ℝ)) * (h))))) := by
    dsimp [second,z,dc,dd,capMinus,capPlus]
    simp only [pow_two]
    ring
  rw [hid]
  linarith only [h0,h1,h2,h3,h4,hsum]

theorem coarse_energy_bound {h : ℝ} (hh : h ∈ Set.Icc coarseLeft coarseRight) : energy h < 32717/1000 := by
  have h0 := (box_b53_enclosure hh).2
  have h1 := (box_b54_enclosure hh).2
  have h2 := (box_b55_enclosure hh).2
  have h3 := (box_b56_enclosure hh).2
  have h4 := (box_b57_enclosure hh).2
  have hsum : (1/2 : ℝ) + box_b53U + box_b54U + box_b55U + box_b56U + box_b57U < 32717/1000 := by norm_num [box_b53U,box_b54U,box_b55U,box_b56U,box_b57U]
  dsimp [energy,z,dc,dd,capMinus,capPlus]
  simp only [pow_two]
  linarith only [h0,h1,h2,h3,h4,hsum]

end
end ThomsonN10.Param
