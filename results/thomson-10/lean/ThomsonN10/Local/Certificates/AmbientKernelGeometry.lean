/- Adapted from proof/ambient_circuit/export_lean_geometry.py,
 aravindkarthigeyan/thomson-n9-lean @ 168ff0c98cab4dfda0460ba55f8d169070ac385e (MIT). -/
import ThomsonN10.Local.Certificates.AmbientKernelData
import ThomsonN10.Local.Certificates.CircuitRadial
import ThomsonN10.Local.Certificates.CircuitMatrices
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace ThomsonN10.Local.Certificates.AmbientKernel
open IntervalCircuit
-- Witness JSON SHA256: e65b0175efc9cd7bd1298607cad41c642809c70078039ecb78e5c31179fb00f7
def pairBlock_1_0 : PairBlockRecipe where
  distance := {
    difference := ![11,11,16]
    squares := {
      left := fun i => #[11,11,16][i]?.getD 0
      right := fun i => #[11,11,16][i]?.getD 0
      product := fun i => #[11,11,17][i]?.getD 0
      accumulator := fun i => #[11,11,11,17][i]?.getD 0 }
    root := 18
    inverse := 19 }
  powers := { base := 19, accumulator := fun i => #[2,19,20,21,22,23][i]?.getD 0 }
  three := 24
  scaledFifth := 25
  timesFirst := ![11,11,28]
  numerator := ![![11,11,11],![11,11,11],![11,11,29]]
  delta := ![![2,11,11],![11,2,11],![11,11,2]]
  diagonalTerm := ![![21,11,11],![11,21,11],![11,11,21]]
  negativeDiagonal := ![![26,11,11],![11,26,11],![11,11,26]]
  block := ![![26,11,11],![11,26,11],![11,11,30]]
theorem pairBlock_1_0_check : pairBlock_1_0.Check nodes := by
  constructor <;> decide
#print axioms pairBlock_1_0_check
def difference_1_0 : DifferenceRecipe where
  left := ![11,11,15]
  right := ![11,11,2]
  negative := ![11,11,15]
  output := ![11,11,16]
theorem difference_1_0_check : difference_1_0.Check nodes := by decide
def halfInverse_1_0 : HalfInverseRecipe where
  distance := pairBlock_1_0.distance
  two := 6
  twice := 32
  inverse := 33
  negative := 34
theorem halfInverse_1_0_check : halfInverse_1_0.Check nodes := by
  constructor
  · exact pairBlock_1_0_check.distance
  all_goals decide
def pairBlock_2_0 : PairBlockRecipe where
  distance := {
    difference := ![5,11,35]
    squares := {
      left := fun i => #[5,11,35][i]?.getD 0
      right := fun i => #[5,11,35][i]?.getD 0
      product := fun i => #[36,11,37][i]?.getD 0
      accumulator := fun i => #[11,36,36,38][i]?.getD 0 }
    root := 39
    inverse := 40 }
  powers := { base := 40, accumulator := fun i => #[2,40,41,42,43,44][i]?.getD 0 }
  three := 24
  scaledFifth := 45
  timesFirst := ![46,11,56]
  numerator := ![![47,11,52],![11,11,11],![57,11,59]]
  delta := ![![2,11,11],![11,2,11],![11,11,2]]
  diagonalTerm := ![![42,11,11],![11,42,11],![11,11,42]]
  negativeDiagonal := ![![48,11,11],![11,48,11],![11,11,48]]
  block := ![![49,11,52],![11,48,11],![57,11,60]]
theorem pairBlock_2_0_check : pairBlock_2_0.Check nodes := by
  constructor <;> decide
#print axioms pairBlock_2_0_check
def difference_2_0 : DifferenceRecipe where
  left := ![5,11,0]
  right := ![11,11,2]
  negative := ![11,11,15]
  output := ![5,11,35]
theorem difference_2_0_check : difference_2_0.Check nodes := by decide
def halfInverse_2_0 : HalfInverseRecipe where
  distance := pairBlock_2_0.distance
  two := 6
  twice := 63
  inverse := 64
  negative := 65
theorem halfInverse_2_0_check : halfInverse_2_0.Check nodes := by
  constructor
  · exact pairBlock_2_0_check.distance
  all_goals decide
def pairBlock_2_1 : PairBlockRecipe where
  distance := {
    difference := ![5,11,67]
    squares := {
      left := fun i => #[5,11,67][i]?.getD 0
      right := fun i => #[5,11,67][i]?.getD 0
      product := fun i => #[36,11,68][i]?.getD 0
      accumulator := fun i => #[11,36,36,69][i]?.getD 0 }
    root := 70
    inverse := 71 }
  powers := { base := 71, accumulator := fun i => #[2,71,72,73,74,75][i]?.getD 0 }
  three := 24
  scaledFifth := 76
  timesFirst := ![77,11,90]
  numerator := ![![78,11,84],![11,11,11],![91,11,94]]
  delta := ![![2,11,11],![11,2,11],![11,11,2]]
  diagonalTerm := ![![73,11,11],![11,73,11],![11,11,73]]
  negativeDiagonal := ![![79,11,11],![11,79,11],![11,11,79]]
  block := ![![80,11,84],![11,79,11],![91,11,95]]
theorem pairBlock_2_1_check : pairBlock_2_1.Check nodes := by
  constructor <;> decide
#print axioms pairBlock_2_1_check
def difference_2_1 : DifferenceRecipe where
  left := ![5,11,0]
  right := ![11,11,15]
  negative := ![11,11,2]
  output := ![5,11,67]
theorem difference_2_1_check : difference_2_1.Check nodes := by decide
def halfInverse_2_1 : HalfInverseRecipe where
  distance := pairBlock_2_1.distance
  two := 6
  twice := 99
  inverse := 100
  negative := 101
theorem halfInverse_2_1_check : halfInverse_2_1.Check nodes := by
  constructor
  · exact pairBlock_2_1_check.distance
  all_goals decide
def pairBlock_3_0 : PairBlockRecipe where
  distance := {
    difference := ![11,5,35]
    squares := {
      left := fun i => #[11,5,35][i]?.getD 0
      right := fun i => #[11,5,35][i]?.getD 0
      product := fun i => #[11,36,37][i]?.getD 0
      accumulator := fun i => #[11,11,36,38][i]?.getD 0 }
    root := 39
    inverse := 40 }
  powers := { base := 40, accumulator := fun i => #[2,40,41,42,43,44][i]?.getD 0 }
  three := 24
  scaledFifth := 45
  timesFirst := ![11,46,56]
  numerator := ![![11,11,11],![11,47,52],![11,57,59]]
  delta := ![![2,11,11],![11,2,11],![11,11,2]]
  diagonalTerm := ![![42,11,11],![11,42,11],![11,11,42]]
  negativeDiagonal := ![![48,11,11],![11,48,11],![11,11,48]]
  block := ![![48,11,11],![11,49,52],![11,57,60]]
theorem pairBlock_3_0_check : pairBlock_3_0.Check nodes := by
  constructor <;> decide
#print axioms pairBlock_3_0_check
def difference_3_0 : DifferenceRecipe where
  left := ![11,5,0]
  right := ![11,11,2]
  negative := ![11,11,15]
  output := ![11,5,35]
theorem difference_3_0_check : difference_3_0.Check nodes := by decide
def halfInverse_3_0 : HalfInverseRecipe where
  distance := pairBlock_3_0.distance
  two := 6
  twice := 63
  inverse := 64
  negative := 65
theorem halfInverse_3_0_check : halfInverse_3_0.Check nodes := by
  constructor
  · exact pairBlock_3_0_check.distance
  all_goals decide
def pairBlock_3_1 : PairBlockRecipe where
  distance := {
    difference := ![11,5,67]
    squares := {
      left := fun i => #[11,5,67][i]?.getD 0
      right := fun i => #[11,5,67][i]?.getD 0
      product := fun i => #[11,36,68][i]?.getD 0
      accumulator := fun i => #[11,11,36,69][i]?.getD 0 }
    root := 70
    inverse := 71 }
  powers := { base := 71, accumulator := fun i => #[2,71,72,73,74,75][i]?.getD 0 }
  three := 24
  scaledFifth := 76
  timesFirst := ![11,77,90]
  numerator := ![![11,11,11],![11,78,84],![11,91,94]]
  delta := ![![2,11,11],![11,2,11],![11,11,2]]
  diagonalTerm := ![![73,11,11],![11,73,11],![11,11,73]]
  negativeDiagonal := ![![79,11,11],![11,79,11],![11,11,79]]
  block := ![![79,11,11],![11,80,84],![11,91,95]]
theorem pairBlock_3_1_check : pairBlock_3_1.Check nodes := by
  constructor <;> decide
#print axioms pairBlock_3_1_check
def difference_3_1 : DifferenceRecipe where
  left := ![11,5,0]
  right := ![11,11,15]
  negative := ![11,11,2]
  output := ![11,5,67]
theorem difference_3_1_check : difference_3_1.Check nodes := by decide
def halfInverse_3_1 : HalfInverseRecipe where
  distance := pairBlock_3_1.distance
  two := 6
  twice := 99
  inverse := 100
  negative := 101
theorem halfInverse_3_1_check : halfInverse_3_1.Check nodes := by
  constructor
  · exact pairBlock_3_1_check.distance
  all_goals decide
def pairBlock_3_2 : PairBlockRecipe where
  distance := {
    difference := ![13,5,112]
    squares := {
      left := fun i => #[13,5,112][i]?.getD 0
      right := fun i => #[13,5,112][i]?.getD 0
      product := fun i => #[113,36,115][i]?.getD 0
      accumulator := fun i => #[11,113,114,116][i]?.getD 0 }
    root := 117
    inverse := 118 }
  powers := { base := 118, accumulator := fun i => #[2,118,119,120,121,122][i]?.getD 0 }
  three := 24
  scaledFifth := 123
  timesFirst := ![124,136,147]
  numerator := ![![125,131,133],![137,139,144],![148,151,154]]
  delta := ![![2,11,11],![11,2,11],![11,11,2]]
  diagonalTerm := ![![120,11,11],![11,120,11],![11,11,120]]
  negativeDiagonal := ![![126,11,11],![11,126,11],![11,11,126]]
  block := ![![127,131,133],![137,140,144],![148,151,155]]
theorem pairBlock_3_2_check : pairBlock_3_2.Check nodes := by
  constructor <;> decide
#print axioms pairBlock_3_2_check
def difference_3_2 : DifferenceRecipe where
  left := ![11,5,0]
  right := ![5,11,0]
  negative := ![13,11,12]
  output := ![13,5,112]
theorem difference_3_2_check : difference_3_2.Check nodes := by decide
def halfInverse_3_2 : HalfInverseRecipe where
  distance := pairBlock_3_2.distance
  two := 6
  twice := 158
  inverse := 159
  negative := 160
theorem halfInverse_3_2_check : halfInverse_3_2.Check nodes := by
  constructor
  · exact pairBlock_3_2_check.distance
  all_goals decide
def pairBlock_4_0 : PairBlockRecipe where
  distance := {
    difference := ![13,11,35]
    squares := {
      left := fun i => #[13,11,35][i]?.getD 0
      right := fun i => #[13,11,35][i]?.getD 0
      product := fun i => #[113,11,37][i]?.getD 0
      accumulator := fun i => #[11,113,113,162][i]?.getD 0 }
    root := 163
    inverse := 164 }
  powers := { base := 164, accumulator := fun i => #[2,164,165,166,167,168][i]?.getD 0 }
  three := 24
  scaledFifth := 169
  timesFirst := ![170,11,181]
  numerator := ![![171,11,176],![11,11,11],![182,11,185]]
  delta := ![![2,11,11],![11,2,11],![11,11,2]]
  diagonalTerm := ![![166,11,11],![11,166,11],![11,11,166]]
  negativeDiagonal := ![![172,11,11],![11,172,11],![11,11,172]]
  block := ![![173,11,176],![11,172,11],![182,11,186]]
theorem pairBlock_4_0_check : pairBlock_4_0.Check nodes := by
  constructor <;> decide
#print axioms pairBlock_4_0_check
def difference_4_0 : DifferenceRecipe where
  left := ![13,11,0]
  right := ![11,11,2]
  negative := ![11,11,15]
  output := ![13,11,35]
theorem difference_4_0_check : difference_4_0.Check nodes := by decide
def halfInverse_4_0 : HalfInverseRecipe where
  distance := pairBlock_4_0.distance
  two := 6
  twice := 189
  inverse := 190
  negative := 191
theorem halfInverse_4_0_check : halfInverse_4_0.Check nodes := by
  constructor
  · exact pairBlock_4_0_check.distance
  all_goals decide
def pairBlock_4_1 : PairBlockRecipe where
  distance := {
    difference := ![13,11,67]
    squares := {
      left := fun i => #[13,11,67][i]?.getD 0
      right := fun i => #[13,11,67][i]?.getD 0
      product := fun i => #[113,11,68][i]?.getD 0
      accumulator := fun i => #[11,113,113,193][i]?.getD 0 }
    root := 194
    inverse := 195 }
  powers := { base := 195, accumulator := fun i => #[2,195,196,197,198,199][i]?.getD 0 }
  three := 24
  scaledFifth := 200
  timesFirst := ![201,11,215]
  numerator := ![![202,11,208],![11,11,11],![216,11,220]]
  delta := ![![2,11,11],![11,2,11],![11,11,2]]
  diagonalTerm := ![![197,11,11],![11,197,11],![11,11,197]]
  negativeDiagonal := ![![203,11,11],![11,203,11],![11,11,203]]
  block := ![![204,11,208],![11,203,11],![216,11,221]]
theorem pairBlock_4_1_check : pairBlock_4_1.Check nodes := by
  constructor <;> decide
#print axioms pairBlock_4_1_check
def difference_4_1 : DifferenceRecipe where
  left := ![13,11,0]
  right := ![11,11,15]
  negative := ![11,11,2]
  output := ![13,11,67]
theorem difference_4_1_check : difference_4_1.Check nodes := by decide
def halfInverse_4_1 : HalfInverseRecipe where
  distance := pairBlock_4_1.distance
  two := 6
  twice := 225
  inverse := 226
  negative := 227
theorem halfInverse_4_1_check : halfInverse_4_1.Check nodes := by
  constructor
  · exact pairBlock_4_1_check.distance
  all_goals decide
def pairBlock_4_2 : PairBlockRecipe where
  distance := {
    difference := ![230,11,112]
    squares := {
      left := fun i => #[230,11,112][i]?.getD 0
      right := fun i => #[230,11,112][i]?.getD 0
      product := fun i => #[231,11,115][i]?.getD 0
      accumulator := fun i => #[11,231,231,232][i]?.getD 0 }
    root := 233
    inverse := 234 }
  powers := { base := 234, accumulator := fun i => #[2,234,235,236,237,238][i]?.getD 0 }
  three := 24
  scaledFifth := 239
  timesFirst := ![240,11,254]
  numerator := ![![241,11,247],![11,11,11],![255,11,259]]
  delta := ![![2,11,11],![11,2,11],![11,11,2]]
  diagonalTerm := ![![236,11,11],![11,236,11],![11,11,236]]
  negativeDiagonal := ![![242,11,11],![11,242,11],![11,11,242]]
  block := ![![243,11,247],![11,242,11],![255,11,260]]
theorem pairBlock_4_2_check : pairBlock_4_2.Check nodes := by
  constructor <;> decide
#print axioms pairBlock_4_2_check
def difference_4_2 : DifferenceRecipe where
  left := ![13,11,0]
  right := ![5,11,0]
  negative := ![13,11,12]
  output := ![230,11,112]
theorem difference_4_2_check : difference_4_2.Check nodes := by decide
def halfInverse_4_2 : HalfInverseRecipe where
  distance := pairBlock_4_2.distance
  two := 6
  twice := 264
  inverse := 265
  negative := 266
theorem halfInverse_4_2_check : halfInverse_4_2.Check nodes := by
  constructor
  · exact pairBlock_4_2_check.distance
  all_goals decide
def pairBlock_4_3 : PairBlockRecipe where
  distance := {
    difference := ![13,13,112]
    squares := {
      left := fun i => #[13,13,112][i]?.getD 0
      right := fun i => #[13,13,112][i]?.getD 0
      product := fun i => #[113,113,115][i]?.getD 0
      accumulator := fun i => #[11,113,269,270][i]?.getD 0 }
    root := 271
    inverse := 272 }
  powers := { base := 272, accumulator := fun i => #[2,272,273,274,275,276][i]?.getD 0 }
  three := 24
  scaledFifth := 277
  timesFirst := ![278,278,295]
  numerator := ![![279,279,287],![279,279,287],![296,296,301]]
  delta := ![![2,11,11],![11,2,11],![11,11,2]]
  diagonalTerm := ![![274,11,11],![11,274,11],![11,11,274]]
  negativeDiagonal := ![![280,11,11],![11,280,11],![11,11,280]]
  block := ![![281,279,287],![279,281,287],![296,296,302]]
theorem pairBlock_4_3_check : pairBlock_4_3.Check nodes := by
  constructor <;> decide
#print axioms pairBlock_4_3_check
def difference_4_3 : DifferenceRecipe where
  left := ![13,11,0]
  right := ![11,5,0]
  negative := ![11,13,12]
  output := ![13,13,112]
theorem difference_4_3_check : difference_4_3.Check nodes := by decide
def halfInverse_4_3 : HalfInverseRecipe where
  distance := pairBlock_4_3.distance
  two := 6
  twice := 306
  inverse := 307
  negative := 308
theorem halfInverse_4_3_check : halfInverse_4_3.Check nodes := by
  constructor
  · exact pairBlock_4_3_check.distance
  all_goals decide
def pairBlock_5_0 : PairBlockRecipe where
  distance := {
    difference := ![11,13,35]
    squares := {
      left := fun i => #[11,13,35][i]?.getD 0
      right := fun i => #[11,13,35][i]?.getD 0
      product := fun i => #[11,113,37][i]?.getD 0
      accumulator := fun i => #[11,11,113,162][i]?.getD 0 }
    root := 163
    inverse := 164 }
  powers := { base := 164, accumulator := fun i => #[2,164,165,166,167,168][i]?.getD 0 }
  three := 24
  scaledFifth := 169
  timesFirst := ![11,170,181]
  numerator := ![![11,11,11],![11,171,176],![11,182,185]]
  delta := ![![2,11,11],![11,2,11],![11,11,2]]
  diagonalTerm := ![![166,11,11],![11,166,11],![11,11,166]]
  negativeDiagonal := ![![172,11,11],![11,172,11],![11,11,172]]
  block := ![![172,11,11],![11,173,176],![11,182,186]]
theorem pairBlock_5_0_check : pairBlock_5_0.Check nodes := by
  constructor <;> decide
#print axioms pairBlock_5_0_check
def difference_5_0 : DifferenceRecipe where
  left := ![11,13,0]
  right := ![11,11,2]
  negative := ![11,11,15]
  output := ![11,13,35]
theorem difference_5_0_check : difference_5_0.Check nodes := by decide
def halfInverse_5_0 : HalfInverseRecipe where
  distance := pairBlock_5_0.distance
  two := 6
  twice := 189
  inverse := 190
  negative := 191
theorem halfInverse_5_0_check : halfInverse_5_0.Check nodes := by
  constructor
  · exact pairBlock_5_0_check.distance
  all_goals decide
def pairBlock_5_1 : PairBlockRecipe where
  distance := {
    difference := ![11,13,67]
    squares := {
      left := fun i => #[11,13,67][i]?.getD 0
      right := fun i => #[11,13,67][i]?.getD 0
      product := fun i => #[11,113,68][i]?.getD 0
      accumulator := fun i => #[11,11,113,193][i]?.getD 0 }
    root := 194
    inverse := 195 }
  powers := { base := 195, accumulator := fun i => #[2,195,196,197,198,199][i]?.getD 0 }
  three := 24
  scaledFifth := 200
  timesFirst := ![11,201,215]
  numerator := ![![11,11,11],![11,202,208],![11,216,220]]
  delta := ![![2,11,11],![11,2,11],![11,11,2]]
  diagonalTerm := ![![197,11,11],![11,197,11],![11,11,197]]
  negativeDiagonal := ![![203,11,11],![11,203,11],![11,11,203]]
  block := ![![203,11,11],![11,204,208],![11,216,221]]
theorem pairBlock_5_1_check : pairBlock_5_1.Check nodes := by
  constructor <;> decide
#print axioms pairBlock_5_1_check
def difference_5_1 : DifferenceRecipe where
  left := ![11,13,0]
  right := ![11,11,15]
  negative := ![11,11,2]
  output := ![11,13,67]
theorem difference_5_1_check : difference_5_1.Check nodes := by decide
def halfInverse_5_1 : HalfInverseRecipe where
  distance := pairBlock_5_1.distance
  two := 6
  twice := 225
  inverse := 226
  negative := 227
theorem halfInverse_5_1_check : halfInverse_5_1.Check nodes := by
  constructor
  · exact pairBlock_5_1_check.distance
  all_goals decide
def pairBlock_5_2 : PairBlockRecipe where
  distance := {
    difference := ![13,13,112]
    squares := {
      left := fun i => #[13,13,112][i]?.getD 0
      right := fun i => #[13,13,112][i]?.getD 0
      product := fun i => #[113,113,115][i]?.getD 0
      accumulator := fun i => #[11,113,269,270][i]?.getD 0 }
    root := 271
    inverse := 272 }
  powers := { base := 272, accumulator := fun i => #[2,272,273,274,275,276][i]?.getD 0 }
  three := 24
  scaledFifth := 277
  timesFirst := ![278,278,295]
  numerator := ![![279,279,287],![279,279,287],![296,296,301]]
  delta := ![![2,11,11],![11,2,11],![11,11,2]]
  diagonalTerm := ![![274,11,11],![11,274,11],![11,11,274]]
  negativeDiagonal := ![![280,11,11],![11,280,11],![11,11,280]]
  block := ![![281,279,287],![279,281,287],![296,296,302]]
theorem pairBlock_5_2_check : pairBlock_5_2.Check nodes := by
  constructor <;> decide
#print axioms pairBlock_5_2_check
def difference_5_2 : DifferenceRecipe where
  left := ![11,13,0]
  right := ![5,11,0]
  negative := ![13,11,12]
  output := ![13,13,112]
theorem difference_5_2_check : difference_5_2.Check nodes := by decide
def halfInverse_5_2 : HalfInverseRecipe where
  distance := pairBlock_5_2.distance
  two := 6
  twice := 306
  inverse := 307
  negative := 308
theorem halfInverse_5_2_check : halfInverse_5_2.Check nodes := by
  constructor
  · exact pairBlock_5_2_check.distance
  all_goals decide
def pairBlock_5_3 : PairBlockRecipe where
  distance := {
    difference := ![11,230,112]
    squares := {
      left := fun i => #[11,230,112][i]?.getD 0
      right := fun i => #[11,230,112][i]?.getD 0
      product := fun i => #[11,231,115][i]?.getD 0
      accumulator := fun i => #[11,11,231,232][i]?.getD 0 }
    root := 233
    inverse := 234 }
  powers := { base := 234, accumulator := fun i => #[2,234,235,236,237,238][i]?.getD 0 }
  three := 24
  scaledFifth := 239
  timesFirst := ![11,240,254]
  numerator := ![![11,11,11],![11,241,247],![11,255,259]]
  delta := ![![2,11,11],![11,2,11],![11,11,2]]
  diagonalTerm := ![![236,11,11],![11,236,11],![11,11,236]]
  negativeDiagonal := ![![242,11,11],![11,242,11],![11,11,242]]
  block := ![![242,11,11],![11,243,247],![11,255,260]]
theorem pairBlock_5_3_check : pairBlock_5_3.Check nodes := by
  constructor <;> decide
#print axioms pairBlock_5_3_check
def difference_5_3 : DifferenceRecipe where
  left := ![11,13,0]
  right := ![11,5,0]
  negative := ![11,13,12]
  output := ![11,230,112]
theorem difference_5_3_check : difference_5_3.Check nodes := by decide
def halfInverse_5_3 : HalfInverseRecipe where
  distance := pairBlock_5_3.distance
  two := 6
  twice := 264
  inverse := 265
  negative := 266
theorem halfInverse_5_3_check : halfInverse_5_3.Check nodes := by
  constructor
  · exact pairBlock_5_3_check.distance
  all_goals decide
def pairBlock_5_4 : PairBlockRecipe where
  distance := {
    difference := ![345,13,112]
    squares := {
      left := fun i => #[345,13,112][i]?.getD 0
      right := fun i => #[345,13,112][i]?.getD 0
      product := fun i => #[346,113,115][i]?.getD 0
      accumulator := fun i => #[11,346,347,348][i]?.getD 0 }
    root := 349
    inverse := 350 }
  powers := { base := 350, accumulator := fun i => #[2,350,351,352,353,354][i]?.getD 0 }
  three := 24
  scaledFifth := 355
  timesFirst := ![356,370,383]
  numerator := ![![357,363,366],![371,374,379],![384,388,392]]
  delta := ![![2,11,11],![11,2,11],![11,11,2]]
  diagonalTerm := ![![352,11,11],![11,352,11],![11,11,352]]
  negativeDiagonal := ![![358,11,11],![11,358,11],![11,11,358]]
  block := ![![359,363,366],![371,375,379],![384,388,393]]
theorem pairBlock_5_4_check : pairBlock_5_4.Check nodes := by
  constructor <;> decide
#print axioms pairBlock_5_4_check
def difference_5_4 : DifferenceRecipe where
  left := ![11,13,0]
  right := ![13,11,0]
  negative := ![345,11,12]
  output := ![345,13,112]
theorem difference_5_4_check : difference_5_4.Check nodes := by decide
def halfInverse_5_4 : HalfInverseRecipe where
  distance := pairBlock_5_4.distance
  two := 6
  twice := 397
  inverse := 398
  negative := 399
theorem halfInverse_5_4_check : halfInverse_5_4.Check nodes := by
  constructor
  · exact pairBlock_5_4_check.distance
  all_goals decide
def pairBlock_6_0 : PairBlockRecipe where
  distance := {
    difference := ![10,10,402]
    squares := {
      left := fun i => #[10,10,402][i]?.getD 0
      right := fun i => #[10,10,402][i]?.getD 0
      product := fun i => #[403,403,405][i]?.getD 0
      accumulator := fun i => #[11,403,404,406][i]?.getD 0 }
    root := 407
    inverse := 408 }
  powers := { base := 408, accumulator := fun i => #[2,408,409,410,411,412][i]?.getD 0 }
  three := 24
  scaledFifth := 413
  timesFirst := ![414,414,425]
  numerator := ![![415,415,421],![415,415,421],![426,426,429]]
  delta := ![![2,11,11],![11,2,11],![11,11,2]]
  diagonalTerm := ![![410,11,11],![11,410,11],![11,11,410]]
  negativeDiagonal := ![![416,11,11],![11,416,11],![11,11,416]]
  block := ![![417,415,421],![415,417,421],![426,426,430]]
theorem pairBlock_6_0_check : pairBlock_6_0.Check nodes := by
  constructor <;> decide
#print axioms pairBlock_6_0_check
def difference_6_0 : DifferenceRecipe where
  left := ![10,10,12]
  right := ![11,11,2]
  negative := ![11,11,15]
  output := ![10,10,402]
theorem difference_6_0_check : difference_6_0.Check nodes := by decide
def halfInverse_6_0 : HalfInverseRecipe where
  distance := pairBlock_6_0.distance
  two := 6
  twice := 433
  inverse := 434
  negative := 435
theorem halfInverse_6_0_check : halfInverse_6_0.Check nodes := by
  constructor
  · exact pairBlock_6_0_check.distance
  all_goals decide
def pairBlock_6_1 : PairBlockRecipe where
  distance := {
    difference := ![10,10,437]
    squares := {
      left := fun i => #[10,10,437][i]?.getD 0
      right := fun i => #[10,10,437][i]?.getD 0
      product := fun i => #[403,403,438][i]?.getD 0
      accumulator := fun i => #[11,403,404,439][i]?.getD 0 }
    root := 440
    inverse := 441 }
  powers := { base := 441, accumulator := fun i => #[2,441,442,443,444,445][i]?.getD 0 }
  three := 24
  scaledFifth := 446
  timesFirst := ![447,447,461]
  numerator := ![![448,448,456],![448,448,456],![462,462,466]]
  delta := ![![2,11,11],![11,2,11],![11,11,2]]
  diagonalTerm := ![![443,11,11],![11,443,11],![11,11,443]]
  negativeDiagonal := ![![449,11,11],![11,449,11],![11,11,449]]
  block := ![![450,448,456],![448,450,456],![462,462,467]]
theorem pairBlock_6_1_check : pairBlock_6_1.Check nodes := by
  constructor <;> decide
#print axioms pairBlock_6_1_check
def difference_6_1 : DifferenceRecipe where
  left := ![10,10,12]
  right := ![11,11,15]
  negative := ![11,11,2]
  output := ![10,10,437]
theorem difference_6_1_check : difference_6_1.Check nodes := by decide
def halfInverse_6_1 : HalfInverseRecipe where
  distance := pairBlock_6_1.distance
  two := 6
  twice := 471
  inverse := 472
  negative := 473
theorem halfInverse_6_1_check : halfInverse_6_1.Check nodes := by
  constructor
  · exact pairBlock_6_1_check.distance
  all_goals decide
def pairBlock_6_2 : PairBlockRecipe where
  distance := {
    difference := ![476,10,477]
    squares := {
      left := fun i => #[476,10,477][i]?.getD 0
      right := fun i => #[476,10,477][i]?.getD 0
      product := fun i => #[478,403,480][i]?.getD 0
      accumulator := fun i => #[11,478,479,481][i]?.getD 0 }
    root := 482
    inverse := 483 }
  powers := { base := 483, accumulator := fun i => #[2,483,484,485,486,487][i]?.getD 0 }
  three := 24
  scaledFifth := 488
  timesFirst := ![489,504,518]
  numerator := ![![490,496,500],![505,509,514],![519,523,527]]
  delta := ![![2,11,11],![11,2,11],![11,11,2]]
  diagonalTerm := ![![485,11,11],![11,485,11],![11,11,485]]
  negativeDiagonal := ![![491,11,11],![11,491,11],![11,11,491]]
  block := ![![492,496,500],![505,510,514],![519,523,528]]
theorem pairBlock_6_2_check : pairBlock_6_2.Check nodes := by
  constructor <;> decide
#print axioms pairBlock_6_2_check
def difference_6_2 : DifferenceRecipe where
  left := ![10,10,12]
  right := ![5,11,0]
  negative := ![13,11,12]
  output := ![476,10,477]
theorem difference_6_2_check : difference_6_2.Check nodes := by decide
def halfInverse_6_2 : HalfInverseRecipe where
  distance := pairBlock_6_2.distance
  two := 6
  twice := 532
  inverse := 533
  negative := 534
theorem halfInverse_6_2_check : halfInverse_6_2.Check nodes := by
  constructor
  · exact pairBlock_6_2_check.distance
  all_goals decide
def pairBlock_6_3 : PairBlockRecipe where
  distance := {
    difference := ![10,476,477]
    squares := {
      left := fun i => #[10,476,477][i]?.getD 0
      right := fun i => #[10,476,477][i]?.getD 0
      product := fun i => #[403,478,480][i]?.getD 0
      accumulator := fun i => #[11,403,537,538][i]?.getD 0 }
    root := 539
    inverse := 540 }
  powers := { base := 540, accumulator := fun i => #[2,540,541,542,543,544][i]?.getD 0 }
  three := 24
  scaledFifth := 545
  timesFirst := ![546,561,575]
  numerator := ![![547,553,557],![562,566,571],![576,580,584]]
  delta := ![![2,11,11],![11,2,11],![11,11,2]]
  diagonalTerm := ![![542,11,11],![11,542,11],![11,11,542]]
  negativeDiagonal := ![![548,11,11],![11,548,11],![11,11,548]]
  block := ![![549,553,557],![562,567,571],![576,580,585]]
theorem pairBlock_6_3_check : pairBlock_6_3.Check nodes := by
  constructor <;> decide
#print axioms pairBlock_6_3_check
def difference_6_3 : DifferenceRecipe where
  left := ![10,10,12]
  right := ![11,5,0]
  negative := ![11,13,12]
  output := ![10,476,477]
theorem difference_6_3_check : difference_6_3.Check nodes := by decide
def halfInverse_6_3 : HalfInverseRecipe where
  distance := pairBlock_6_3.distance
  two := 6
  twice := 589
  inverse := 590
  negative := 591
theorem halfInverse_6_3_check : halfInverse_6_3.Check nodes := by
  constructor
  · exact pairBlock_6_3_check.distance
  all_goals decide
def pairBlock_6_4 : PairBlockRecipe where
  distance := {
    difference := ![594,10,477]
    squares := {
      left := fun i => #[594,10,477][i]?.getD 0
      right := fun i => #[594,10,477][i]?.getD 0
      product := fun i => #[595,403,480][i]?.getD 0
      accumulator := fun i => #[11,595,596,597][i]?.getD 0 }
    root := 598
    inverse := 599 }
  powers := { base := 599, accumulator := fun i => #[2,599,600,601,602,603][i]?.getD 0 }
  three := 24
  scaledFifth := 604
  timesFirst := ![605,620,634]
  numerator := ![![606,612,616],![621,625,630],![635,639,643]]
  delta := ![![2,11,11],![11,2,11],![11,11,2]]
  diagonalTerm := ![![601,11,11],![11,601,11],![11,11,601]]
  negativeDiagonal := ![![607,11,11],![11,607,11],![11,11,607]]
  block := ![![608,612,616],![621,626,630],![635,639,644]]
theorem pairBlock_6_4_check : pairBlock_6_4.Check nodes := by
  constructor <;> decide
#print axioms pairBlock_6_4_check
def difference_6_4 : DifferenceRecipe where
  left := ![10,10,12]
  right := ![13,11,0]
  negative := ![345,11,12]
  output := ![594,10,477]
theorem difference_6_4_check : difference_6_4.Check nodes := by decide
def halfInverse_6_4 : HalfInverseRecipe where
  distance := pairBlock_6_4.distance
  two := 6
  twice := 648
  inverse := 649
  negative := 650
theorem halfInverse_6_4_check : halfInverse_6_4.Check nodes := by
  constructor
  · exact pairBlock_6_4_check.distance
  all_goals decide
def pairBlock_6_5 : PairBlockRecipe where
  distance := {
    difference := ![10,594,477]
    squares := {
      left := fun i => #[10,594,477][i]?.getD 0
      right := fun i => #[10,594,477][i]?.getD 0
      product := fun i => #[403,595,480][i]?.getD 0
      accumulator := fun i => #[11,403,653,654][i]?.getD 0 }
    root := 655
    inverse := 656 }
  powers := { base := 656, accumulator := fun i => #[2,656,657,658,659,660][i]?.getD 0 }
  three := 24
  scaledFifth := 661
  timesFirst := ![662,677,691]
  numerator := ![![663,669,673],![678,682,687],![692,696,700]]
  delta := ![![2,11,11],![11,2,11],![11,11,2]]
  diagonalTerm := ![![658,11,11],![11,658,11],![11,11,658]]
  negativeDiagonal := ![![664,11,11],![11,664,11],![11,11,664]]
  block := ![![665,669,673],![678,683,687],![692,696,701]]
theorem pairBlock_6_5_check : pairBlock_6_5.Check nodes := by
  constructor <;> decide
#print axioms pairBlock_6_5_check
def difference_6_5 : DifferenceRecipe where
  left := ![10,10,12]
  right := ![11,13,0]
  negative := ![11,345,12]
  output := ![10,594,477]
theorem difference_6_5_check : difference_6_5.Check nodes := by decide
def halfInverse_6_5 : HalfInverseRecipe where
  distance := pairBlock_6_5.distance
  two := 6
  twice := 705
  inverse := 706
  negative := 707
theorem halfInverse_6_5_check : halfInverse_6_5.Check nodes := by
  constructor
  · exact pairBlock_6_5_check.distance
  all_goals decide
def pairBlock_7_0 : PairBlockRecipe where
  distance := {
    difference := ![14,10,402]
    squares := {
      left := fun i => #[14,10,402][i]?.getD 0
      right := fun i => #[14,10,402][i]?.getD 0
      product := fun i => #[710,403,405][i]?.getD 0
      accumulator := fun i => #[11,710,711,712][i]?.getD 0 }
    root := 713
    inverse := 714 }
  powers := { base := 714, accumulator := fun i => #[2,714,715,716,717,718][i]?.getD 0 }
  three := 24
  scaledFifth := 719
  timesFirst := ![720,732,743]
  numerator := ![![721,726,729],![733,736,740],![744,747,750]]
  delta := ![![2,11,11],![11,2,11],![11,11,2]]
  diagonalTerm := ![![716,11,11],![11,716,11],![11,11,716]]
  negativeDiagonal := ![![722,11,11],![11,722,11],![11,11,722]]
  block := ![![723,726,729],![733,737,740],![744,747,751]]
theorem pairBlock_7_0_check : pairBlock_7_0.Check nodes := by
  constructor <;> decide
#print axioms pairBlock_7_0_check
def difference_7_0 : DifferenceRecipe where
  left := ![14,10,12]
  right := ![11,11,2]
  negative := ![11,11,15]
  output := ![14,10,402]
theorem difference_7_0_check : difference_7_0.Check nodes := by decide
def halfInverse_7_0 : HalfInverseRecipe where
  distance := pairBlock_7_0.distance
  two := 6
  twice := 754
  inverse := 755
  negative := 756
theorem halfInverse_7_0_check : halfInverse_7_0.Check nodes := by
  constructor
  · exact pairBlock_7_0_check.distance
  all_goals decide
def pairBlock_7_1 : PairBlockRecipe where
  distance := {
    difference := ![14,10,437]
    squares := {
      left := fun i => #[14,10,437][i]?.getD 0
      right := fun i => #[14,10,437][i]?.getD 0
      product := fun i => #[710,403,438][i]?.getD 0
      accumulator := fun i => #[11,710,711,758][i]?.getD 0 }
    root := 759
    inverse := 760 }
  powers := { base := 760, accumulator := fun i => #[2,760,761,762,763,764][i]?.getD 0 }
  three := 24
  scaledFifth := 765
  timesFirst := ![766,781,795]
  numerator := ![![767,773,777],![782,786,791],![796,800,804]]
  delta := ![![2,11,11],![11,2,11],![11,11,2]]
  diagonalTerm := ![![762,11,11],![11,762,11],![11,11,762]]
  negativeDiagonal := ![![768,11,11],![11,768,11],![11,11,768]]
  block := ![![769,773,777],![782,787,791],![796,800,805]]
theorem pairBlock_7_1_check : pairBlock_7_1.Check nodes := by
  constructor <;> decide
#print axioms pairBlock_7_1_check
def difference_7_1 : DifferenceRecipe where
  left := ![14,10,12]
  right := ![11,11,15]
  negative := ![11,11,2]
  output := ![14,10,437]
theorem difference_7_1_check : difference_7_1.Check nodes := by decide
def halfInverse_7_1 : HalfInverseRecipe where
  distance := pairBlock_7_1.distance
  two := 6
  twice := 809
  inverse := 810
  negative := 811
theorem halfInverse_7_1_check : halfInverse_7_1.Check nodes := by
  constructor
  · exact pairBlock_7_1_check.distance
  all_goals decide
def pairBlock_7_2 : PairBlockRecipe where
  distance := {
    difference := ![814,10,477]
    squares := {
      left := fun i => #[814,10,477][i]?.getD 0
      right := fun i => #[814,10,477][i]?.getD 0
      product := fun i => #[815,403,480][i]?.getD 0
      accumulator := fun i => #[11,815,816,817][i]?.getD 0 }
    root := 818
    inverse := 819 }
  powers := { base := 819, accumulator := fun i => #[2,819,820,821,822,823][i]?.getD 0 }
  three := 24
  scaledFifth := 824
  timesFirst := ![825,840,854]
  numerator := ![![826,832,836],![841,845,850],![855,859,863]]
  delta := ![![2,11,11],![11,2,11],![11,11,2]]
  diagonalTerm := ![![821,11,11],![11,821,11],![11,11,821]]
  negativeDiagonal := ![![827,11,11],![11,827,11],![11,11,827]]
  block := ![![828,832,836],![841,846,850],![855,859,864]]
theorem pairBlock_7_2_check : pairBlock_7_2.Check nodes := by
  constructor <;> decide
#print axioms pairBlock_7_2_check
def difference_7_2 : DifferenceRecipe where
  left := ![14,10,12]
  right := ![5,11,0]
  negative := ![13,11,12]
  output := ![814,10,477]
theorem difference_7_2_check : difference_7_2.Check nodes := by decide
def halfInverse_7_2 : HalfInverseRecipe where
  distance := pairBlock_7_2.distance
  two := 6
  twice := 868
  inverse := 869
  negative := 870
theorem halfInverse_7_2_check : halfInverse_7_2.Check nodes := by
  constructor
  · exact pairBlock_7_2_check.distance
  all_goals decide
def pairBlock_7_3 : PairBlockRecipe where
  distance := {
    difference := ![14,476,477]
    squares := {
      left := fun i => #[14,476,477][i]?.getD 0
      right := fun i => #[14,476,477][i]?.getD 0
      product := fun i => #[710,478,480][i]?.getD 0
      accumulator := fun i => #[11,710,873,874][i]?.getD 0 }
    root := 875
    inverse := 876 }
  powers := { base := 876, accumulator := fun i => #[2,876,877,878,879,880][i]?.getD 0 }
  three := 24
  scaledFifth := 881
  timesFirst := ![882,897,911]
  numerator := ![![883,889,893],![898,902,907],![912,916,920]]
  delta := ![![2,11,11],![11,2,11],![11,11,2]]
  diagonalTerm := ![![878,11,11],![11,878,11],![11,11,878]]
  negativeDiagonal := ![![884,11,11],![11,884,11],![11,11,884]]
  block := ![![885,889,893],![898,903,907],![912,916,921]]
theorem pairBlock_7_3_check : pairBlock_7_3.Check nodes := by
  constructor <;> decide
#print axioms pairBlock_7_3_check
def difference_7_3 : DifferenceRecipe where
  left := ![14,10,12]
  right := ![11,5,0]
  negative := ![11,13,12]
  output := ![14,476,477]
theorem difference_7_3_check : difference_7_3.Check nodes := by decide
def halfInverse_7_3 : HalfInverseRecipe where
  distance := pairBlock_7_3.distance
  two := 6
  twice := 925
  inverse := 926
  negative := 927
theorem halfInverse_7_3_check : halfInverse_7_3.Check nodes := by
  constructor
  · exact pairBlock_7_3_check.distance
  all_goals decide
def pairBlock_7_4 : PairBlockRecipe where
  distance := {
    difference := ![930,10,477]
    squares := {
      left := fun i => #[930,10,477][i]?.getD 0
      right := fun i => #[930,10,477][i]?.getD 0
      product := fun i => #[931,403,480][i]?.getD 0
      accumulator := fun i => #[11,931,932,933][i]?.getD 0 }
    root := 934
    inverse := 935 }
  powers := { base := 935, accumulator := fun i => #[2,935,936,937,938,939][i]?.getD 0 }
  three := 24
  scaledFifth := 940
  timesFirst := ![941,956,970]
  numerator := ![![942,948,952],![957,961,966],![971,975,979]]
  delta := ![![2,11,11],![11,2,11],![11,11,2]]
  diagonalTerm := ![![937,11,11],![11,937,11],![11,11,937]]
  negativeDiagonal := ![![943,11,11],![11,943,11],![11,11,943]]
  block := ![![944,948,952],![957,962,966],![971,975,980]]
theorem pairBlock_7_4_check : pairBlock_7_4.Check nodes := by
  constructor <;> decide
#print axioms pairBlock_7_4_check
def difference_7_4 : DifferenceRecipe where
  left := ![14,10,12]
  right := ![13,11,0]
  negative := ![345,11,12]
  output := ![930,10,477]
theorem difference_7_4_check : difference_7_4.Check nodes := by decide
def halfInverse_7_4 : HalfInverseRecipe where
  distance := pairBlock_7_4.distance
  two := 6
  twice := 984
  inverse := 985
  negative := 986
theorem halfInverse_7_4_check : halfInverse_7_4.Check nodes := by
  constructor
  · exact pairBlock_7_4_check.distance
  all_goals decide
def pairBlock_7_5 : PairBlockRecipe where
  distance := {
    difference := ![14,594,477]
    squares := {
      left := fun i => #[14,594,477][i]?.getD 0
      right := fun i => #[14,594,477][i]?.getD 0
      product := fun i => #[710,595,480][i]?.getD 0
      accumulator := fun i => #[11,710,989,990][i]?.getD 0 }
    root := 991
    inverse := 992 }
  powers := { base := 992, accumulator := fun i => #[2,992,993,994,995,996][i]?.getD 0 }
  three := 24
  scaledFifth := 997
  timesFirst := ![998,1013,1027]
  numerator := ![![999,1005,1009],![1014,1018,1023],![1028,1032,1036]]
  delta := ![![2,11,11],![11,2,11],![11,11,2]]
  diagonalTerm := ![![994,11,11],![11,994,11],![11,11,994]]
  negativeDiagonal := ![![1000,11,11],![11,1000,11],![11,11,1000]]
  block := ![![1001,1005,1009],![1014,1019,1023],![1028,1032,1037]]
theorem pairBlock_7_5_check : pairBlock_7_5.Check nodes := by
  constructor <;> decide
#print axioms pairBlock_7_5_check
def difference_7_5 : DifferenceRecipe where
  left := ![14,10,12]
  right := ![11,13,0]
  negative := ![11,345,12]
  output := ![14,594,477]
theorem difference_7_5_check : difference_7_5.Check nodes := by decide
def halfInverse_7_5 : HalfInverseRecipe where
  distance := pairBlock_7_5.distance
  two := 6
  twice := 1041
  inverse := 1042
  negative := 1043
theorem halfInverse_7_5_check : halfInverse_7_5.Check nodes := by
  constructor
  · exact pairBlock_7_5_check.distance
  all_goals decide
def pairBlock_7_6 : PairBlockRecipe where
  distance := {
    difference := ![1046,1047,1049]
    squares := {
      left := fun i => #[1046,1047,1049][i]?.getD 0
      right := fun i => #[1046,1047,1049][i]?.getD 0
      product := fun i => #[1050,1051,1053][i]?.getD 0
      accumulator := fun i => #[11,1050,1052,1054][i]?.getD 0 }
    root := 1055
    inverse := 1056 }
  powers := { base := 1056, accumulator := fun i => #[2,1056,1057,1058,1059,1060][i]?.getD 0 }
  three := 24
  scaledFifth := 1061
  timesFirst := ![1062,1077,1091]
  numerator := ![![1063,1069,1073],![1078,1082,1087],![1092,1096,1100]]
  delta := ![![2,11,11],![11,2,11],![11,11,2]]
  diagonalTerm := ![![1058,11,11],![11,1058,11],![11,11,1058]]
  negativeDiagonal := ![![1064,11,11],![11,1064,11],![11,11,1064]]
  block := ![![1065,1069,1073],![1078,1083,1087],![1092,1096,1101]]
theorem pairBlock_7_6_check : pairBlock_7_6.Check nodes := by
  constructor <;> decide
#print axioms pairBlock_7_6_check
def difference_7_6 : DifferenceRecipe where
  left := ![14,10,12]
  right := ![10,10,12]
  negative := ![14,14,1048]
  output := ![1046,1047,1049]
theorem difference_7_6_check : difference_7_6.Check nodes := by decide
def halfInverse_7_6 : HalfInverseRecipe where
  distance := pairBlock_7_6.distance
  two := 6
  twice := 1105
  inverse := 1106
  negative := 1107
theorem halfInverse_7_6_check : halfInverse_7_6.Check nodes := by
  constructor
  · exact pairBlock_7_6_check.distance
  all_goals decide
def pairBlock_8_0 : PairBlockRecipe where
  distance := {
    difference := ![14,14,402]
    squares := {
      left := fun i => #[14,14,402][i]?.getD 0
      right := fun i => #[14,14,402][i]?.getD 0
      product := fun i => #[710,710,405][i]?.getD 0
      accumulator := fun i => #[11,710,1110,1111][i]?.getD 0 }
    root := 1112
    inverse := 1113 }
  powers := { base := 1113, accumulator := fun i => #[2,1113,1114,1115,1116,1117][i]?.getD 0 }
  three := 24
  scaledFifth := 1118
  timesFirst := ![1119,1119,1133]
  numerator := ![![1120,1120,1127],![1120,1120,1127],![1134,1134,1138]]
  delta := ![![2,11,11],![11,2,11],![11,11,2]]
  diagonalTerm := ![![1115,11,11],![11,1115,11],![11,11,1115]]
  negativeDiagonal := ![![1121,11,11],![11,1121,11],![11,11,1121]]
  block := ![![1122,1120,1127],![1120,1122,1127],![1134,1134,1139]]
theorem pairBlock_8_0_check : pairBlock_8_0.Check nodes := by
  constructor <;> decide
#print axioms pairBlock_8_0_check
def difference_8_0 : DifferenceRecipe where
  left := ![14,14,12]
  right := ![11,11,2]
  negative := ![11,11,15]
  output := ![14,14,402]
theorem difference_8_0_check : difference_8_0.Check nodes := by decide
def halfInverse_8_0 : HalfInverseRecipe where
  distance := pairBlock_8_0.distance
  two := 6
  twice := 1142
  inverse := 1143
  negative := 1144
theorem halfInverse_8_0_check : halfInverse_8_0.Check nodes := by
  constructor
  · exact pairBlock_8_0_check.distance
  all_goals decide
def pairBlock_8_1 : PairBlockRecipe where
  distance := {
    difference := ![14,14,437]
    squares := {
      left := fun i => #[14,14,437][i]?.getD 0
      right := fun i => #[14,14,437][i]?.getD 0
      product := fun i => #[710,710,438][i]?.getD 0
      accumulator := fun i => #[11,710,1110,1146][i]?.getD 0 }
    root := 1147
    inverse := 1148 }
  powers := { base := 1148, accumulator := fun i => #[2,1148,1149,1150,1151,1152][i]?.getD 0 }
  three := 24
  scaledFifth := 1153
  timesFirst := ![1154,1154,1171]
  numerator := ![![1155,1155,1164],![1155,1155,1164],![1172,1172,1177]]
  delta := ![![2,11,11],![11,2,11],![11,11,2]]
  diagonalTerm := ![![1150,11,11],![11,1150,11],![11,11,1150]]
  negativeDiagonal := ![![1156,11,11],![11,1156,11],![11,11,1156]]
  block := ![![1157,1155,1164],![1155,1157,1164],![1172,1172,1178]]
theorem pairBlock_8_1_check : pairBlock_8_1.Check nodes := by
  constructor <;> decide
#print axioms pairBlock_8_1_check
def difference_8_1 : DifferenceRecipe where
  left := ![14,14,12]
  right := ![11,11,15]
  negative := ![11,11,2]
  output := ![14,14,437]
theorem difference_8_1_check : difference_8_1.Check nodes := by decide
def halfInverse_8_1 : HalfInverseRecipe where
  distance := pairBlock_8_1.distance
  two := 6
  twice := 1182
  inverse := 1183
  negative := 1184
theorem halfInverse_8_1_check : halfInverse_8_1.Check nodes := by
  constructor
  · exact pairBlock_8_1_check.distance
  all_goals decide
def pairBlock_8_2 : PairBlockRecipe where
  distance := {
    difference := ![814,14,477]
    squares := {
      left := fun i => #[814,14,477][i]?.getD 0
      right := fun i => #[814,14,477][i]?.getD 0
      product := fun i => #[815,710,480][i]?.getD 0
      accumulator := fun i => #[11,815,1187,1188][i]?.getD 0 }
    root := 1189
    inverse := 1190 }
  powers := { base := 1190, accumulator := fun i => #[2,1190,1191,1192,1193,1194][i]?.getD 0 }
  three := 24
  scaledFifth := 1195
  timesFirst := ![1196,1211,1225]
  numerator := ![![1197,1203,1207],![1212,1216,1221],![1226,1230,1234]]
  delta := ![![2,11,11],![11,2,11],![11,11,2]]
  diagonalTerm := ![![1192,11,11],![11,1192,11],![11,11,1192]]
  negativeDiagonal := ![![1198,11,11],![11,1198,11],![11,11,1198]]
  block := ![![1199,1203,1207],![1212,1217,1221],![1226,1230,1235]]
theorem pairBlock_8_2_check : pairBlock_8_2.Check nodes := by
  constructor <;> decide
#print axioms pairBlock_8_2_check
def difference_8_2 : DifferenceRecipe where
  left := ![14,14,12]
  right := ![5,11,0]
  negative := ![13,11,12]
  output := ![814,14,477]
theorem difference_8_2_check : difference_8_2.Check nodes := by decide
def halfInverse_8_2 : HalfInverseRecipe where
  distance := pairBlock_8_2.distance
  two := 6
  twice := 1239
  inverse := 1240
  negative := 1241
theorem halfInverse_8_2_check : halfInverse_8_2.Check nodes := by
  constructor
  · exact pairBlock_8_2_check.distance
  all_goals decide
def pairBlock_8_3 : PairBlockRecipe where
  distance := {
    difference := ![14,814,477]
    squares := {
      left := fun i => #[14,814,477][i]?.getD 0
      right := fun i => #[14,814,477][i]?.getD 0
      product := fun i => #[710,815,480][i]?.getD 0
      accumulator := fun i => #[11,710,1244,1245][i]?.getD 0 }
    root := 1246
    inverse := 1247 }
  powers := { base := 1247, accumulator := fun i => #[2,1247,1248,1249,1250,1251][i]?.getD 0 }
  three := 24
  scaledFifth := 1252
  timesFirst := ![1253,1268,1282]
  numerator := ![![1254,1260,1264],![1269,1273,1278],![1283,1287,1291]]
  delta := ![![2,11,11],![11,2,11],![11,11,2]]
  diagonalTerm := ![![1249,11,11],![11,1249,11],![11,11,1249]]
  negativeDiagonal := ![![1255,11,11],![11,1255,11],![11,11,1255]]
  block := ![![1256,1260,1264],![1269,1274,1278],![1283,1287,1292]]
theorem pairBlock_8_3_check : pairBlock_8_3.Check nodes := by
  constructor <;> decide
#print axioms pairBlock_8_3_check
def difference_8_3 : DifferenceRecipe where
  left := ![14,14,12]
  right := ![11,5,0]
  negative := ![11,13,12]
  output := ![14,814,477]
theorem difference_8_3_check : difference_8_3.Check nodes := by decide
def halfInverse_8_3 : HalfInverseRecipe where
  distance := pairBlock_8_3.distance
  two := 6
  twice := 1296
  inverse := 1297
  negative := 1298
theorem halfInverse_8_3_check : halfInverse_8_3.Check nodes := by
  constructor
  · exact pairBlock_8_3_check.distance
  all_goals decide
def pairBlock_8_4 : PairBlockRecipe where
  distance := {
    difference := ![930,14,477]
    squares := {
      left := fun i => #[930,14,477][i]?.getD 0
      right := fun i => #[930,14,477][i]?.getD 0
      product := fun i => #[931,710,480][i]?.getD 0
      accumulator := fun i => #[11,931,1301,1302][i]?.getD 0 }
    root := 1303
    inverse := 1304 }
  powers := { base := 1304, accumulator := fun i => #[2,1304,1305,1306,1307,1308][i]?.getD 0 }
  three := 24
  scaledFifth := 1309
  timesFirst := ![1310,1325,1339]
  numerator := ![![1311,1317,1321],![1326,1330,1335],![1340,1344,1348]]
  delta := ![![2,11,11],![11,2,11],![11,11,2]]
  diagonalTerm := ![![1306,11,11],![11,1306,11],![11,11,1306]]
  negativeDiagonal := ![![1312,11,11],![11,1312,11],![11,11,1312]]
  block := ![![1313,1317,1321],![1326,1331,1335],![1340,1344,1349]]
theorem pairBlock_8_4_check : pairBlock_8_4.Check nodes := by
  constructor <;> decide
#print axioms pairBlock_8_4_check
def difference_8_4 : DifferenceRecipe where
  left := ![14,14,12]
  right := ![13,11,0]
  negative := ![345,11,12]
  output := ![930,14,477]
theorem difference_8_4_check : difference_8_4.Check nodes := by decide
def halfInverse_8_4 : HalfInverseRecipe where
  distance := pairBlock_8_4.distance
  two := 6
  twice := 1353
  inverse := 1354
  negative := 1355
theorem halfInverse_8_4_check : halfInverse_8_4.Check nodes := by
  constructor
  · exact pairBlock_8_4_check.distance
  all_goals decide
def pairBlock_8_5 : PairBlockRecipe where
  distance := {
    difference := ![14,930,477]
    squares := {
      left := fun i => #[14,930,477][i]?.getD 0
      right := fun i => #[14,930,477][i]?.getD 0
      product := fun i => #[710,931,480][i]?.getD 0
      accumulator := fun i => #[11,710,1358,1359][i]?.getD 0 }
    root := 1360
    inverse := 1361 }
  powers := { base := 1361, accumulator := fun i => #[2,1361,1362,1363,1364,1365][i]?.getD 0 }
  three := 24
  scaledFifth := 1366
  timesFirst := ![1367,1382,1396]
  numerator := ![![1368,1374,1378],![1383,1387,1392],![1397,1401,1405]]
  delta := ![![2,11,11],![11,2,11],![11,11,2]]
  diagonalTerm := ![![1363,11,11],![11,1363,11],![11,11,1363]]
  negativeDiagonal := ![![1369,11,11],![11,1369,11],![11,11,1369]]
  block := ![![1370,1374,1378],![1383,1388,1392],![1397,1401,1406]]
theorem pairBlock_8_5_check : pairBlock_8_5.Check nodes := by
  constructor <;> decide
#print axioms pairBlock_8_5_check
def difference_8_5 : DifferenceRecipe where
  left := ![14,14,12]
  right := ![11,13,0]
  negative := ![11,345,12]
  output := ![14,930,477]
theorem difference_8_5_check : difference_8_5.Check nodes := by decide
def halfInverse_8_5 : HalfInverseRecipe where
  distance := pairBlock_8_5.distance
  two := 6
  twice := 1410
  inverse := 1411
  negative := 1412
theorem halfInverse_8_5_check : halfInverse_8_5.Check nodes := by
  constructor
  · exact pairBlock_8_5_check.distance
  all_goals decide
def pairBlock_8_6 : PairBlockRecipe where
  distance := {
    difference := ![1046,1046,1049]
    squares := {
      left := fun i => #[1046,1046,1049][i]?.getD 0
      right := fun i => #[1046,1046,1049][i]?.getD 0
      product := fun i => #[1050,1050,1053][i]?.getD 0
      accumulator := fun i => #[11,1050,1415,1416][i]?.getD 0 }
    root := 1417
    inverse := 1418 }
  powers := { base := 1418, accumulator := fun i => #[2,1418,1419,1420,1421,1422][i]?.getD 0 }
  three := 24
  scaledFifth := 1423
  timesFirst := ![1424,1424,1444]
  numerator := ![![1425,1425,1434],![1425,1425,1434],![1445,1445,1451]]
  delta := ![![2,11,11],![11,2,11],![11,11,2]]
  diagonalTerm := ![![1420,11,11],![11,1420,11],![11,11,1420]]
  negativeDiagonal := ![![1426,11,11],![11,1426,11],![11,11,1426]]
  block := ![![1427,1425,1434],![1425,1427,1434],![1445,1445,1452]]
theorem pairBlock_8_6_check : pairBlock_8_6.Check nodes := by
  constructor <;> decide
#print axioms pairBlock_8_6_check
def difference_8_6 : DifferenceRecipe where
  left := ![14,14,12]
  right := ![10,10,12]
  negative := ![14,14,1048]
  output := ![1046,1046,1049]
theorem difference_8_6_check : difference_8_6.Check nodes := by decide
def halfInverse_8_6 : HalfInverseRecipe where
  distance := pairBlock_8_6.distance
  two := 6
  twice := 1456
  inverse := 1457
  negative := 1458
theorem halfInverse_8_6_check : halfInverse_8_6.Check nodes := by
  constructor
  · exact pairBlock_8_6_check.distance
  all_goals decide
def pairBlock_8_7 : PairBlockRecipe where
  distance := {
    difference := ![1462,1046,1049]
    squares := {
      left := fun i => #[1462,1046,1049][i]?.getD 0
      right := fun i => #[1462,1046,1049][i]?.getD 0
      product := fun i => #[1463,1050,1053][i]?.getD 0
      accumulator := fun i => #[11,1463,1464,1465][i]?.getD 0 }
    root := 1466
    inverse := 1467 }
  powers := { base := 1467, accumulator := fun i => #[2,1467,1468,1469,1470,1471][i]?.getD 0 }
  three := 24
  scaledFifth := 1472
  timesFirst := ![1473,1488,1502]
  numerator := ![![1474,1480,1484],![1489,1493,1498],![1503,1507,1511]]
  delta := ![![2,11,11],![11,2,11],![11,11,2]]
  diagonalTerm := ![![1469,11,11],![11,1469,11],![11,11,1469]]
  negativeDiagonal := ![![1475,11,11],![11,1475,11],![11,11,1475]]
  block := ![![1476,1480,1484],![1489,1494,1498],![1503,1507,1512]]
theorem pairBlock_8_7_check : pairBlock_8_7.Check nodes := by
  constructor <;> decide
#print axioms pairBlock_8_7_check
def difference_8_7 : DifferenceRecipe where
  left := ![14,14,12]
  right := ![14,10,12]
  negative := ![1461,14,1048]
  output := ![1462,1046,1049]
theorem difference_8_7_check : difference_8_7.Check nodes := by decide
def halfInverse_8_7 : HalfInverseRecipe where
  distance := pairBlock_8_7.distance
  two := 6
  twice := 1516
  inverse := 1517
  negative := 1518
theorem halfInverse_8_7_check : halfInverse_8_7.Check nodes := by
  constructor
  · exact pairBlock_8_7_check.distance
  all_goals decide
def pairBlock_9_0 : PairBlockRecipe where
  distance := {
    difference := ![10,14,402]
    squares := {
      left := fun i => #[10,14,402][i]?.getD 0
      right := fun i => #[10,14,402][i]?.getD 0
      product := fun i => #[403,710,405][i]?.getD 0
      accumulator := fun i => #[11,403,1521,1522][i]?.getD 0 }
    root := 1523
    inverse := 1524 }
  powers := { base := 1524, accumulator := fun i => #[2,1524,1525,1526,1527,1528][i]?.getD 0 }
  three := 24
  scaledFifth := 1529
  timesFirst := ![1530,1542,1553]
  numerator := ![![1531,1536,1539],![1543,1546,1550],![1554,1557,1560]]
  delta := ![![2,11,11],![11,2,11],![11,11,2]]
  diagonalTerm := ![![1526,11,11],![11,1526,11],![11,11,1526]]
  negativeDiagonal := ![![1532,11,11],![11,1532,11],![11,11,1532]]
  block := ![![1533,1536,1539],![1543,1547,1550],![1554,1557,1561]]
theorem pairBlock_9_0_check : pairBlock_9_0.Check nodes := by
  constructor <;> decide
#print axioms pairBlock_9_0_check
def difference_9_0 : DifferenceRecipe where
  left := ![10,14,12]
  right := ![11,11,2]
  negative := ![11,11,15]
  output := ![10,14,402]
theorem difference_9_0_check : difference_9_0.Check nodes := by decide
def halfInverse_9_0 : HalfInverseRecipe where
  distance := pairBlock_9_0.distance
  two := 6
  twice := 1564
  inverse := 1565
  negative := 1566
theorem halfInverse_9_0_check : halfInverse_9_0.Check nodes := by
  constructor
  · exact pairBlock_9_0_check.distance
  all_goals decide
def pairBlock_9_1 : PairBlockRecipe where
  distance := {
    difference := ![10,14,437]
    squares := {
      left := fun i => #[10,14,437][i]?.getD 0
      right := fun i => #[10,14,437][i]?.getD 0
      product := fun i => #[403,710,438][i]?.getD 0
      accumulator := fun i => #[11,403,1521,1568][i]?.getD 0 }
    root := 1569
    inverse := 1570 }
  powers := { base := 1570, accumulator := fun i => #[2,1570,1571,1572,1573,1574][i]?.getD 0 }
  three := 24
  scaledFifth := 1575
  timesFirst := ![1576,1591,1605]
  numerator := ![![1577,1583,1587],![1592,1596,1601],![1606,1610,1614]]
  delta := ![![2,11,11],![11,2,11],![11,11,2]]
  diagonalTerm := ![![1572,11,11],![11,1572,11],![11,11,1572]]
  negativeDiagonal := ![![1578,11,11],![11,1578,11],![11,11,1578]]
  block := ![![1579,1583,1587],![1592,1597,1601],![1606,1610,1615]]
theorem pairBlock_9_1_check : pairBlock_9_1.Check nodes := by
  constructor <;> decide
#print axioms pairBlock_9_1_check
def difference_9_1 : DifferenceRecipe where
  left := ![10,14,12]
  right := ![11,11,15]
  negative := ![11,11,2]
  output := ![10,14,437]
theorem difference_9_1_check : difference_9_1.Check nodes := by decide
def halfInverse_9_1 : HalfInverseRecipe where
  distance := pairBlock_9_1.distance
  two := 6
  twice := 1619
  inverse := 1620
  negative := 1621
theorem halfInverse_9_1_check : halfInverse_9_1.Check nodes := by
  constructor
  · exact pairBlock_9_1_check.distance
  all_goals decide
def pairBlock_9_2 : PairBlockRecipe where
  distance := {
    difference := ![476,14,477]
    squares := {
      left := fun i => #[476,14,477][i]?.getD 0
      right := fun i => #[476,14,477][i]?.getD 0
      product := fun i => #[478,710,480][i]?.getD 0
      accumulator := fun i => #[11,478,1624,1625][i]?.getD 0 }
    root := 1626
    inverse := 1627 }
  powers := { base := 1627, accumulator := fun i => #[2,1627,1628,1629,1630,1631][i]?.getD 0 }
  three := 24
  scaledFifth := 1632
  timesFirst := ![1633,1648,1662]
  numerator := ![![1634,1640,1644],![1649,1653,1658],![1663,1667,1671]]
  delta := ![![2,11,11],![11,2,11],![11,11,2]]
  diagonalTerm := ![![1629,11,11],![11,1629,11],![11,11,1629]]
  negativeDiagonal := ![![1635,11,11],![11,1635,11],![11,11,1635]]
  block := ![![1636,1640,1644],![1649,1654,1658],![1663,1667,1672]]
theorem pairBlock_9_2_check : pairBlock_9_2.Check nodes := by
  constructor <;> decide
#print axioms pairBlock_9_2_check
def difference_9_2 : DifferenceRecipe where
  left := ![10,14,12]
  right := ![5,11,0]
  negative := ![13,11,12]
  output := ![476,14,477]
theorem difference_9_2_check : difference_9_2.Check nodes := by decide
def halfInverse_9_2 : HalfInverseRecipe where
  distance := pairBlock_9_2.distance
  two := 6
  twice := 1676
  inverse := 1677
  negative := 1678
theorem halfInverse_9_2_check : halfInverse_9_2.Check nodes := by
  constructor
  · exact pairBlock_9_2_check.distance
  all_goals decide
def pairBlock_9_3 : PairBlockRecipe where
  distance := {
    difference := ![10,814,477]
    squares := {
      left := fun i => #[10,814,477][i]?.getD 0
      right := fun i => #[10,814,477][i]?.getD 0
      product := fun i => #[403,815,480][i]?.getD 0
      accumulator := fun i => #[11,403,1681,1682][i]?.getD 0 }
    root := 1683
    inverse := 1684 }
  powers := { base := 1684, accumulator := fun i => #[2,1684,1685,1686,1687,1688][i]?.getD 0 }
  three := 24
  scaledFifth := 1689
  timesFirst := ![1690,1705,1719]
  numerator := ![![1691,1697,1701],![1706,1710,1715],![1720,1724,1728]]
  delta := ![![2,11,11],![11,2,11],![11,11,2]]
  diagonalTerm := ![![1686,11,11],![11,1686,11],![11,11,1686]]
  negativeDiagonal := ![![1692,11,11],![11,1692,11],![11,11,1692]]
  block := ![![1693,1697,1701],![1706,1711,1715],![1720,1724,1729]]
theorem pairBlock_9_3_check : pairBlock_9_3.Check nodes := by
  constructor <;> decide
#print axioms pairBlock_9_3_check
def difference_9_3 : DifferenceRecipe where
  left := ![10,14,12]
  right := ![11,5,0]
  negative := ![11,13,12]
  output := ![10,814,477]
theorem difference_9_3_check : difference_9_3.Check nodes := by decide
def halfInverse_9_3 : HalfInverseRecipe where
  distance := pairBlock_9_3.distance
  two := 6
  twice := 1733
  inverse := 1734
  negative := 1735
theorem halfInverse_9_3_check : halfInverse_9_3.Check nodes := by
  constructor
  · exact pairBlock_9_3_check.distance
  all_goals decide
def pairBlock_9_4 : PairBlockRecipe where
  distance := {
    difference := ![594,14,477]
    squares := {
      left := fun i => #[594,14,477][i]?.getD 0
      right := fun i => #[594,14,477][i]?.getD 0
      product := fun i => #[595,710,480][i]?.getD 0
      accumulator := fun i => #[11,595,1738,1739][i]?.getD 0 }
    root := 1740
    inverse := 1741 }
  powers := { base := 1741, accumulator := fun i => #[2,1741,1742,1743,1744,1745][i]?.getD 0 }
  three := 24
  scaledFifth := 1746
  timesFirst := ![1747,1762,1776]
  numerator := ![![1748,1754,1758],![1763,1767,1772],![1777,1781,1785]]
  delta := ![![2,11,11],![11,2,11],![11,11,2]]
  diagonalTerm := ![![1743,11,11],![11,1743,11],![11,11,1743]]
  negativeDiagonal := ![![1749,11,11],![11,1749,11],![11,11,1749]]
  block := ![![1750,1754,1758],![1763,1768,1772],![1777,1781,1786]]
theorem pairBlock_9_4_check : pairBlock_9_4.Check nodes := by
  constructor <;> decide
#print axioms pairBlock_9_4_check
def difference_9_4 : DifferenceRecipe where
  left := ![10,14,12]
  right := ![13,11,0]
  negative := ![345,11,12]
  output := ![594,14,477]
theorem difference_9_4_check : difference_9_4.Check nodes := by decide
def halfInverse_9_4 : HalfInverseRecipe where
  distance := pairBlock_9_4.distance
  two := 6
  twice := 1790
  inverse := 1791
  negative := 1792
theorem halfInverse_9_4_check : halfInverse_9_4.Check nodes := by
  constructor
  · exact pairBlock_9_4_check.distance
  all_goals decide
def pairBlock_9_5 : PairBlockRecipe where
  distance := {
    difference := ![10,930,477]
    squares := {
      left := fun i => #[10,930,477][i]?.getD 0
      right := fun i => #[10,930,477][i]?.getD 0
      product := fun i => #[403,931,480][i]?.getD 0
      accumulator := fun i => #[11,403,1795,1796][i]?.getD 0 }
    root := 1797
    inverse := 1798 }
  powers := { base := 1798, accumulator := fun i => #[2,1798,1799,1800,1801,1802][i]?.getD 0 }
  three := 24
  scaledFifth := 1803
  timesFirst := ![1804,1819,1833]
  numerator := ![![1805,1811,1815],![1820,1824,1829],![1834,1838,1842]]
  delta := ![![2,11,11],![11,2,11],![11,11,2]]
  diagonalTerm := ![![1800,11,11],![11,1800,11],![11,11,1800]]
  negativeDiagonal := ![![1806,11,11],![11,1806,11],![11,11,1806]]
  block := ![![1807,1811,1815],![1820,1825,1829],![1834,1838,1843]]
theorem pairBlock_9_5_check : pairBlock_9_5.Check nodes := by
  constructor <;> decide
#print axioms pairBlock_9_5_check
def difference_9_5 : DifferenceRecipe where
  left := ![10,14,12]
  right := ![11,13,0]
  negative := ![11,345,12]
  output := ![10,930,477]
theorem difference_9_5_check : difference_9_5.Check nodes := by decide
def halfInverse_9_5 : HalfInverseRecipe where
  distance := pairBlock_9_5.distance
  two := 6
  twice := 1847
  inverse := 1848
  negative := 1849
theorem halfInverse_9_5_check : halfInverse_9_5.Check nodes := by
  constructor
  · exact pairBlock_9_5_check.distance
  all_goals decide
def pairBlock_9_6 : PairBlockRecipe where
  distance := {
    difference := ![1047,1046,1049]
    squares := {
      left := fun i => #[1047,1046,1049][i]?.getD 0
      right := fun i => #[1047,1046,1049][i]?.getD 0
      product := fun i => #[1051,1050,1053][i]?.getD 0
      accumulator := fun i => #[11,1051,1852,1853][i]?.getD 0 }
    root := 1854
    inverse := 1855 }
  powers := { base := 1855, accumulator := fun i => #[2,1855,1856,1857,1858,1859][i]?.getD 0 }
  three := 24
  scaledFifth := 1860
  timesFirst := ![1861,1876,1890]
  numerator := ![![1862,1868,1872],![1877,1881,1886],![1891,1895,1899]]
  delta := ![![2,11,11],![11,2,11],![11,11,2]]
  diagonalTerm := ![![1857,11,11],![11,1857,11],![11,11,1857]]
  negativeDiagonal := ![![1863,11,11],![11,1863,11],![11,11,1863]]
  block := ![![1864,1868,1872],![1877,1882,1886],![1891,1895,1900]]
theorem pairBlock_9_6_check : pairBlock_9_6.Check nodes := by
  constructor <;> decide
#print axioms pairBlock_9_6_check
def difference_9_6 : DifferenceRecipe where
  left := ![10,14,12]
  right := ![10,10,12]
  negative := ![14,14,1048]
  output := ![1047,1046,1049]
theorem difference_9_6_check : difference_9_6.Check nodes := by decide
def halfInverse_9_6 : HalfInverseRecipe where
  distance := pairBlock_9_6.distance
  two := 6
  twice := 1904
  inverse := 1905
  negative := 1906
theorem halfInverse_9_6_check : halfInverse_9_6.Check nodes := by
  constructor
  · exact pairBlock_9_6_check.distance
  all_goals decide
def pairBlock_9_7 : PairBlockRecipe where
  distance := {
    difference := ![1909,1046,1049]
    squares := {
      left := fun i => #[1909,1046,1049][i]?.getD 0
      right := fun i => #[1909,1046,1049][i]?.getD 0
      product := fun i => #[1910,1050,1053][i]?.getD 0
      accumulator := fun i => #[11,1910,1911,1912][i]?.getD 0 }
    root := 1913
    inverse := 1914 }
  powers := { base := 1914, accumulator := fun i => #[2,1914,1915,1916,1917,1918][i]?.getD 0 }
  three := 24
  scaledFifth := 1919
  timesFirst := ![1920,1935,1949]
  numerator := ![![1921,1927,1931],![1936,1940,1945],![1950,1954,1958]]
  delta := ![![2,11,11],![11,2,11],![11,11,2]]
  diagonalTerm := ![![1916,11,11],![11,1916,11],![11,11,1916]]
  negativeDiagonal := ![![1922,11,11],![11,1922,11],![11,11,1922]]
  block := ![![1923,1927,1931],![1936,1941,1945],![1950,1954,1959]]
theorem pairBlock_9_7_check : pairBlock_9_7.Check nodes := by
  constructor <;> decide
#print axioms pairBlock_9_7_check
def difference_9_7 : DifferenceRecipe where
  left := ![10,14,12]
  right := ![14,10,12]
  negative := ![1461,14,1048]
  output := ![1909,1046,1049]
theorem difference_9_7_check : difference_9_7.Check nodes := by decide
def halfInverse_9_7 : HalfInverseRecipe where
  distance := pairBlock_9_7.distance
  two := 6
  twice := 1963
  inverse := 1964
  negative := 1965
theorem halfInverse_9_7_check : halfInverse_9_7.Check nodes := by
  constructor
  · exact pairBlock_9_7_check.distance
  all_goals decide
def pairBlock_9_8 : PairBlockRecipe where
  distance := {
    difference := ![1909,1462,1049]
    squares := {
      left := fun i => #[1909,1462,1049][i]?.getD 0
      right := fun i => #[1909,1462,1049][i]?.getD 0
      product := fun i => #[1910,1463,1053][i]?.getD 0
      accumulator := fun i => #[11,1910,1968,1969][i]?.getD 0 }
    root := 1970
    inverse := 1971 }
  powers := { base := 1971, accumulator := fun i => #[2,1971,1972,1973,1974,1975][i]?.getD 0 }
  three := 24
  scaledFifth := 1976
  timesFirst := ![1977,1992,2006]
  numerator := ![![1978,1984,1988],![1993,1997,2002],![2007,2011,2015]]
  delta := ![![2,11,11],![11,2,11],![11,11,2]]
  diagonalTerm := ![![1973,11,11],![11,1973,11],![11,11,1973]]
  negativeDiagonal := ![![1979,11,11],![11,1979,11],![11,11,1979]]
  block := ![![1980,1984,1988],![1993,1998,2002],![2007,2011,2016]]
theorem pairBlock_9_8_check : pairBlock_9_8.Check nodes := by
  constructor <;> decide
#print axioms pairBlock_9_8_check
def difference_9_8 : DifferenceRecipe where
  left := ![10,14,12]
  right := ![14,14,12]
  negative := ![1461,1461,1048]
  output := ![1909,1462,1049]
theorem difference_9_8_check : difference_9_8.Check nodes := by decide
def halfInverse_9_8 : HalfInverseRecipe where
  distance := pairBlock_9_8.distance
  two := 6
  twice := 2020
  inverse := 2021
  negative := 2022
theorem halfInverse_9_8_check : halfInverse_9_8.Check nodes := by
  constructor
  · exact pairBlock_9_8_check.distance
  all_goals decide
def pairRecipes : Fin 45 → PairBlockRecipe := ![pairBlock_1_0, pairBlock_2_0, pairBlock_2_1, pairBlock_3_0, pairBlock_3_1, pairBlock_3_2, pairBlock_4_0, pairBlock_4_1, pairBlock_4_2, pairBlock_4_3, pairBlock_5_0, pairBlock_5_1, pairBlock_5_2, pairBlock_5_3, pairBlock_5_4, pairBlock_6_0, pairBlock_6_1, pairBlock_6_2, pairBlock_6_3, pairBlock_6_4, pairBlock_6_5, pairBlock_7_0, pairBlock_7_1, pairBlock_7_2, pairBlock_7_3, pairBlock_7_4, pairBlock_7_5, pairBlock_7_6, pairBlock_8_0, pairBlock_8_1, pairBlock_8_2, pairBlock_8_3, pairBlock_8_4, pairBlock_8_5, pairBlock_8_6, pairBlock_8_7, pairBlock_9_0, pairBlock_9_1, pairBlock_9_2, pairBlock_9_3, pairBlock_9_4, pairBlock_9_5, pairBlock_9_6, pairBlock_9_7, pairBlock_9_8]
theorem pair_recipes_checked (k : Fin 45) : (pairRecipes k).Check nodes := by
  fin_cases k
  · exact pairBlock_1_0_check
  · exact pairBlock_2_0_check
  · exact pairBlock_2_1_check
  · exact pairBlock_3_0_check
  · exact pairBlock_3_1_check
  · exact pairBlock_3_2_check
  · exact pairBlock_4_0_check
  · exact pairBlock_4_1_check
  · exact pairBlock_4_2_check
  · exact pairBlock_4_3_check
  · exact pairBlock_5_0_check
  · exact pairBlock_5_1_check
  · exact pairBlock_5_2_check
  · exact pairBlock_5_3_check
  · exact pairBlock_5_4_check
  · exact pairBlock_6_0_check
  · exact pairBlock_6_1_check
  · exact pairBlock_6_2_check
  · exact pairBlock_6_3_check
  · exact pairBlock_6_4_check
  · exact pairBlock_6_5_check
  · exact pairBlock_7_0_check
  · exact pairBlock_7_1_check
  · exact pairBlock_7_2_check
  · exact pairBlock_7_3_check
  · exact pairBlock_7_4_check
  · exact pairBlock_7_5_check
  · exact pairBlock_7_6_check
  · exact pairBlock_8_0_check
  · exact pairBlock_8_1_check
  · exact pairBlock_8_2_check
  · exact pairBlock_8_3_check
  · exact pairBlock_8_4_check
  · exact pairBlock_8_5_check
  · exact pairBlock_8_6_check
  · exact pairBlock_8_7_check
  · exact pairBlock_9_0_check
  · exact pairBlock_9_1_check
  · exact pairBlock_9_2_check
  · exact pairBlock_9_3_check
  · exact pairBlock_9_4_check
  · exact pairBlock_9_5_check
  · exact pairBlock_9_6_check
  · exact pairBlock_9_7_check
  · exact pairBlock_9_8_check
theorem pair_blocks_sound (values : ℕ → ℝ) (k : Fin 45) (p q : R3)
    (hdiff : ∀ a : Fin 3, IntervalCircuit.value values nodes
      ((pairRecipes k).distance.difference a) = p a-q a) (a b : Fin 3) :
    IntervalCircuit.value values nodes ((pairRecipes k).block a b) =
      coulombPairBlock (p-q) a b :=
  (pairRecipes k).sound values nodes (pair_recipes_checked k) p q hdiff a b
#print axioms pair_recipes_checked
#print axioms pair_blocks_sound
def pairDifferences : Fin 45 → DifferenceRecipe := ![difference_1_0, difference_2_0, difference_2_1, difference_3_0, difference_3_1, difference_3_2, difference_4_0, difference_4_1, difference_4_2, difference_4_3, difference_5_0, difference_5_1, difference_5_2, difference_5_3, difference_5_4, difference_6_0, difference_6_1, difference_6_2, difference_6_3, difference_6_4, difference_6_5, difference_7_0, difference_7_1, difference_7_2, difference_7_3, difference_7_4, difference_7_5, difference_7_6, difference_8_0, difference_8_1, difference_8_2, difference_8_3, difference_8_4, difference_8_5, difference_8_6, difference_8_7, difference_9_0, difference_9_1, difference_9_2, difference_9_3, difference_9_4, difference_9_5, difference_9_6, difference_9_7, difference_9_8]
def pairFirst : Fin 45 → Fin 10 := ![1,2,2,3,3,3,4,4,4,4,5,5,5,5,5,6,6,6,6,6,6,7,7,7,7,7,7,7,8,8,8,8,8,8,8,8,9,9,9,9,9,9,9,9,9]
def pairSecond : Fin 45 → Fin 10 := ![0,0,1,0,1,2,0,1,2,3,0,1,2,3,4,0,1,2,3,4,5,0,1,2,3,4,5,6,0,1,2,3,4,5,6,7,0,1,2,3,4,5,6,7,8]
theorem difference_recipes_checked (k : Fin 45) : (pairDifferences k).Check nodes := by
  fin_cases k
  · exact difference_1_0_check
  · exact difference_2_0_check
  · exact difference_2_1_check
  · exact difference_3_0_check
  · exact difference_3_1_check
  · exact difference_3_2_check
  · exact difference_4_0_check
  · exact difference_4_1_check
  · exact difference_4_2_check
  · exact difference_4_3_check
  · exact difference_5_0_check
  · exact difference_5_1_check
  · exact difference_5_2_check
  · exact difference_5_3_check
  · exact difference_5_4_check
  · exact difference_6_0_check
  · exact difference_6_1_check
  · exact difference_6_2_check
  · exact difference_6_3_check
  · exact difference_6_4_check
  · exact difference_6_5_check
  · exact difference_7_0_check
  · exact difference_7_1_check
  · exact difference_7_2_check
  · exact difference_7_3_check
  · exact difference_7_4_check
  · exact difference_7_5_check
  · exact difference_7_6_check
  · exact difference_8_0_check
  · exact difference_8_1_check
  · exact difference_8_2_check
  · exact difference_8_3_check
  · exact difference_8_4_check
  · exact difference_8_5_check
  · exact difference_8_6_check
  · exact difference_8_7_check
  · exact difference_9_0_check
  · exact difference_9_1_check
  · exact difference_9_2_check
  · exact difference_9_3_check
  · exact difference_9_4_check
  · exact difference_9_5_check
  · exact difference_9_6_check
  · exact difference_9_7_check
  · exact difference_9_8_check
theorem coordinate_prefix_checked : CoordinateCheck nodes := by decide
theorem difference_left (k : Fin 45) (a : Fin 3) :
    (pairDifferences k).left a = pointIndices (pairFirst k) a := by
  fin_cases k <;> fin_cases a <;> rfl
theorem difference_right (k : Fin 45) (a : Fin 3) :
    (pairDifferences k).right a = pointIndices (pairSecond k) a := by
  fin_cases k <;> fin_cases a <;> rfl
theorem difference_output (k : Fin 45) (a : Fin 3) :
    (pairDifferences k).output a = (pairRecipes k).distance.difference a := by
  fin_cases k <;> fin_cases a <;> rfl
theorem pair_differences_candidate_sound (r : ℝ) (k : Fin 45) (a : Fin 3) :
    IntervalCircuit.value (parameterInputs r) nodes ((pairRecipes k).distance.difference a) =
      candidateAt r (pairFirst k) a-candidateAt r (pairSecond k) a := by
  rw [← difference_output]
  exact (pairDifferences k).candidate_sound r nodes coordinate_prefix_checked
    (difference_recipes_checked k) (pairFirst k) (pairSecond k)
    (difference_left k) (difference_right k) a
theorem pair_blocks_candidate_sound (r : ℝ) (k : Fin 45) (a b : Fin 3) :
    IntervalCircuit.value (parameterInputs r) nodes ((pairRecipes k).block a b) =
      coulombPairBlock (candidateAt r (pairFirst k)-candidateAt r (pairSecond k)) a b :=
  pair_blocks_sound _ k _ _ (pair_differences_candidate_sound r k) a b
#print axioms pair_blocks_candidate_sound
def halfInverseRecipes : Fin 45 → HalfInverseRecipe := ![halfInverse_1_0, halfInverse_2_0, halfInverse_2_1, halfInverse_3_0, halfInverse_3_1, halfInverse_3_2, halfInverse_4_0, halfInverse_4_1, halfInverse_4_2, halfInverse_4_3, halfInverse_5_0, halfInverse_5_1, halfInverse_5_2, halfInverse_5_3, halfInverse_5_4, halfInverse_6_0, halfInverse_6_1, halfInverse_6_2, halfInverse_6_3, halfInverse_6_4, halfInverse_6_5, halfInverse_7_0, halfInverse_7_1, halfInverse_7_2, halfInverse_7_3, halfInverse_7_4, halfInverse_7_5, halfInverse_7_6, halfInverse_8_0, halfInverse_8_1, halfInverse_8_2, halfInverse_8_3, halfInverse_8_4, halfInverse_8_5, halfInverse_8_6, halfInverse_8_7, halfInverse_9_0, halfInverse_9_1, halfInverse_9_2, halfInverse_9_3, halfInverse_9_4, halfInverse_9_5, halfInverse_9_6, halfInverse_9_7, halfInverse_9_8]
theorem half_inverse_recipes_checked (k : Fin 45) : (halfInverseRecipes k).Check nodes := by
  fin_cases k
  · exact halfInverse_1_0_check
  · exact halfInverse_2_0_check
  · exact halfInverse_2_1_check
  · exact halfInverse_3_0_check
  · exact halfInverse_3_1_check
  · exact halfInverse_3_2_check
  · exact halfInverse_4_0_check
  · exact halfInverse_4_1_check
  · exact halfInverse_4_2_check
  · exact halfInverse_4_3_check
  · exact halfInverse_5_0_check
  · exact halfInverse_5_1_check
  · exact halfInverse_5_2_check
  · exact halfInverse_5_3_check
  · exact halfInverse_5_4_check
  · exact halfInverse_6_0_check
  · exact halfInverse_6_1_check
  · exact halfInverse_6_2_check
  · exact halfInverse_6_3_check
  · exact halfInverse_6_4_check
  · exact halfInverse_6_5_check
  · exact halfInverse_7_0_check
  · exact halfInverse_7_1_check
  · exact halfInverse_7_2_check
  · exact halfInverse_7_3_check
  · exact halfInverse_7_4_check
  · exact halfInverse_7_5_check
  · exact halfInverse_7_6_check
  · exact halfInverse_8_0_check
  · exact halfInverse_8_1_check
  · exact halfInverse_8_2_check
  · exact halfInverse_8_3_check
  · exact halfInverse_8_4_check
  · exact halfInverse_8_5_check
  · exact halfInverse_8_6_check
  · exact halfInverse_8_7_check
  · exact halfInverse_9_0_check
  · exact halfInverse_9_1_check
  · exact halfInverse_9_2_check
  · exact halfInverse_9_3_check
  · exact halfInverse_9_4_check
  · exact halfInverse_9_5_check
  · exact halfInverse_9_6_check
  · exact halfInverse_9_7_check
  · exact halfInverse_9_8_check
theorem half_inverse_distance (k : Fin 45) :
    (halfInverseRecipes k).distance = (pairRecipes k).distance := by fin_cases k <;> rfl
theorem half_inverse_candidate_sound (r : ℝ) (k : Fin 45) :
    IntervalCircuit.value (parameterInputs r) nodes (halfInverseRecipes k).negative =
      -(‖candidateAt r (pairFirst k)-candidateAt r (pairSecond k)‖⁻¹/2) := by
  apply (halfInverseRecipes k).sound _ _ (half_inverse_recipes_checked k)
  intro a
  rw [half_inverse_distance]
  exact pair_differences_candidate_sound r k a
def pairIndex : Fin 10 → Fin 10 → Fin 45 := ![![0,0,1,3,6,10,15,21,28,36],![0,0,2,4,7,11,16,22,29,37],![1,2,0,5,8,12,17,23,30,38],![3,4,5,0,9,13,18,24,31,39],![6,7,8,9,0,14,19,25,32,40],![10,11,12,13,14,0,20,26,33,41],![15,16,17,18,19,20,0,27,34,42],![21,22,23,24,25,26,27,0,35,43],![28,29,30,31,32,33,34,35,0,44],![36,37,38,39,40,41,42,43,44,0]]
theorem pair_endpoints (i j : Fin 10) (h : i ≠ j) :
    (pairFirst (pairIndex i j) = i ∧ pairSecond (pairIndex i j) = j) ∨
    (pairFirst (pairIndex i j) = j ∧ pairSecond (pairIndex i j) = i) := by
  revert i j
  decide
theorem unordered_pair_block_sound (r : ℝ) (i j : Fin 10) (h : i ≠ j) (a b : Fin 3) :
    IntervalCircuit.value (parameterInputs r) nodes ((pairRecipes (pairIndex i j)).block a b) =
      coulombPairBlock (candidateAt r i-candidateAt r j) a b := by
  rw [pair_blocks_candidate_sound]
  rcases pair_endpoints i j h with h | h
  · rw [h.1,h.2]
  · rw [h.1,h.2]
    have heq : candidateAt r j-candidateAt r i = -(candidateAt r i-candidateAt r j) := by abel
    rw [heq,coulombPairBlock_neg]
theorem unordered_half_inverse_sound (r : ℝ) (i j : Fin 10) (h : i ≠ j) :
    IntervalCircuit.value (parameterInputs r) nodes (halfInverseRecipes (pairIndex i j)).negative =
      -(‖candidateAt r i-candidateAt r j‖⁻¹/2) := by
  rw [half_inverse_candidate_sound]
  rcases pair_endpoints i j h with h | h
  · rw [h.1,h.2]
  · rw [h.1,h.2,norm_sub_rev]
#print axioms unordered_pair_block_sound
#print axioms unordered_half_inverse_sound
end ThomsonN10.Local.Certificates.AmbientKernel
