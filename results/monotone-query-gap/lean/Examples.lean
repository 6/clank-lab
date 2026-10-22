import KS24

-- Coordinates are numbered from zero, with the least significant bit first.
example : KS24.f1 0 = false := by decide
example : KS24.f1 14 = true := by decide
example : KS24.f1 19 = true := by decide
example : KS24.f1 17 = false := by decide
example : KS24.f1 31 = true := by decide
example : KS24.partition.length = 11 := by decide
example : KS24.codim 3 = 2 := by decide
example : KS24.codim 14 = 3 := by decide
example : 104 * 4 = 13 * 32 := by decide
example : 102 * 16 = 51 * 32 := by decide
example : 102 < 104 := by decide
