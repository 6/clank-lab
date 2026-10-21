import DS243

/-! Axiom checks run as part of the standard Lake build. -/

/-- info: 'DS243.coverage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms DS243.coverage

/-- info: 'DS243.normal_form' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms DS243.normal_form

/-- info: 'DS243.leaf_has_id' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms DS243.leaf_has_id

/-- info: 'DS243.ranges_partition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms DS243.ranges_partition

/-- info: 'DS243.no_difference_set' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms DS243.no_difference_set

/-- info: 'DS243.reduction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms DS243.reduction

/-- info: 'DS243.prune_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms DS243.prune_sound

/-- info: 'DS243.isDiffSet_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms DS243.isDiffSet_of_le

/-- info: 'DS243.pruneA_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms DS243.pruneA_sound

/-- info: 'DS243.leafA_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms DS243.leafA_exact

/-- info: 'DS243.Planted.not_weakPrune' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms DS243.Planted.not_weakPrune

/-- info: 'DS243.Planted.not_weakLeaf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms DS243.Planted.not_weakLeaf

/-- info: 'DS243.Planted.not_dropLastRange' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms DS243.Planted.not_dropLastRange

namespace CheckDefinitions
open DS243

example : G = (ZMod 3 × ZMod 9 × ZMod 9) := rfl
example (D : Finset G) : IsDiffSet D ↔ D.card = 121 ∧ ∀ g : G, g ≠ 0 → diffCount D g = 60 := Iff.rfl
example : MASK = 24909666 := rfl
example : prefixDigit 4251527 11 = 2 := by decide
example : prefixDigit 531441 0 = 0 := by decide
example : (List.range 27).filterMap (fun b => if MASK.testBit b then some (encG (hDec b)) else none) = [3, 33, 54, 60, 81, 84, 108, 162, 165, 168, 189, 192, 216] := by decide +kernel
example : caseRows = [[4, 6, 3, 6, 6, 6, 3, 3, 3, 3, 6, 6, 6, 3, 6, 6, 3, 6, 6, 3, 3, 3, 3, 6, 3, 3, 6], [4, 6, 3, 6, 6, 3, 3, 6, 3, 3, 6, 6, 6, 3, 3, 6, 6, 6, 6, 3, 3, 3, 3, 3, 3, 6, 6], [4, 3, 6, 6, 6, 6, 3, 3, 3, 3, 6, 6, 6, 6, 3, 6, 6, 3, 6, 3, 3, 3, 6, 3, 3, 6, 3], [4, 3, 6, 6, 3, 6, 3, 3, 6, 3, 6, 6, 6, 3, 3, 6, 6, 6, 6, 3, 3, 3, 3, 3, 3, 6, 6], [4, 6, 3, 6, 6, 6, 3, 3, 3, 3, 6, 3, 6, 3, 3, 6, 3, 3, 6, 6, 3, 3, 6, 6, 3, 6, 6], [4, 3, 6, 6, 6, 6, 3, 3, 3, 3, 3, 6, 6, 3, 3, 6, 3, 3, 6, 3, 6, 3, 6, 6, 3, 6, 6], [4, 6, 3, 6, 6, 6, 3, 3, 3, 3, 6, 6, 3, 6, 6, 6, 6, 3, 6, 3, 3, 3, 6, 3, 6, 3, 3], [4, 6, 3, 6, 3, 6, 3, 3, 6, 3, 6, 6, 3, 3, 6, 6, 6, 6, 6, 3, 3, 3, 3, 3, 6, 3, 6]] := by decide +kernel
example : ((optionLeaders 0 0 0).flatMap orbitE) = [28, 34, 31, 55, 61, 58] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([28, 55].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 0 0 1).flatMap orbitE) = [1, 7, 4, 55, 61, 58] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([1, 55].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 0 0 2).flatMap orbitE) = [1, 7, 4, 28, 34, 31] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([1, 28].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 0 1 0).flatMap orbitE) = [12, 66, 39, 15, 69, 42] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([12, 15].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 0 1 1).flatMap orbitE) = [9, 63, 36, 15, 69, 42] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([9, 15].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 0 1 2).flatMap orbitE) = [9, 63, 36, 12, 66, 39] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([9, 12].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 0 2 0).flatMap orbitE) = [13, 64, 43, 16, 67, 37] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([13, 16].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 0 2 1).flatMap orbitE) = [10, 70, 40, 16, 67, 37] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([10, 16].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 0 2 2).flatMap orbitE) = [10, 70, 40, 13, 64, 43] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([10, 13].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 0 3 0).flatMap orbitE) = [14, 71, 38, 17, 65, 41] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([14, 17].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 0 3 1).flatMap orbitE) = [11, 68, 44, 17, 65, 41] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([11, 17].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 0 3 2).flatMap orbitE) = [11, 68, 44, 14, 71, 38] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([11, 14].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 0 4 0).flatMap orbitE) = [109, 115, 112, 136, 142, 139] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([109, 136].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 0 4 1).flatMap orbitE) = [82, 88, 85, 136, 142, 139] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([82, 136].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 0 4 2).flatMap orbitE) = [82, 88, 85, 109, 115, 112] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([82, 109].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 0 5 0).flatMap orbitE) = [110, 113, 116, 137, 140, 143] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([110, 137].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 0 5 1).flatMap orbitE) = [83, 86, 89, 137, 140, 143] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([83, 137].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 0 5 2).flatMap orbitE) = [83, 86, 89, 110, 113, 116] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([83, 110].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 0 6 0).flatMap orbitE) = [93, 147, 120, 96, 150, 123] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([93, 96].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 0 6 1).flatMap orbitE) = [90, 144, 117, 96, 150, 123] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([90, 96].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 0 6 2).flatMap orbitE) = [90, 144, 117, 93, 147, 120] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([90, 93].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 0 7 0).flatMap orbitE) = [95, 152, 119, 98, 146, 122] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([95, 98].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 0 7 1).flatMap orbitE) = [92, 149, 125, 98, 146, 122] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([92, 98].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 0 7 2).flatMap orbitE) = [92, 149, 125, 95, 152, 119] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([92, 95].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 0 8 0).flatMap orbitE) = [102, 129, 156, 105, 132, 159] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([102, 105].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 0 8 1).flatMap orbitE) = [99, 126, 153, 105, 132, 159] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([99, 105].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 0 8 2).flatMap orbitE) = [99, 126, 153, 102, 129, 156] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([99, 102].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 0 9 0).flatMap orbitE) = [104, 134, 155, 107, 128, 158] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([104, 107].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 0 9 1).flatMap orbitE) = [101, 131, 161, 107, 128, 158] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([101, 107].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 0 9 2).flatMap orbitE) = [101, 131, 161, 104, 134, 155] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([101, 104].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 0 10 0).flatMap orbitE) = [176, 233, 200, 179, 227, 203] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([176, 179].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 0 10 1).flatMap orbitE) = [173, 230, 206, 179, 227, 203] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([173, 179].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 0 10 2).flatMap orbitE) = [173, 230, 206, 176, 233, 200] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([173, 176].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 0 11 0).flatMap orbitE) = [185, 215, 236, 188, 209, 239] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([185, 188].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 0 11 1).flatMap orbitE) = [182, 212, 242, 188, 209, 239] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([182, 188].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 0 11 2).flatMap orbitE) = [182, 212, 242, 185, 215, 236] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([182, 185].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 0 12 0).flatMap orbitE) = [2, 5, 8] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([2].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 0 12 1).flatMap orbitE) = [29, 32, 35] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([29].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 0 12 2).flatMap orbitE) = [56, 59, 62] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([56].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 0 13 0).flatMap orbitE) = [18, 45, 72] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([18].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 0 13 1).flatMap orbitE) = [21, 48, 75] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([21].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 0 13 2).flatMap orbitE) = [24, 51, 78] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([24].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 0 14 0).flatMap orbitE) = [19, 52, 76] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([19].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 0 14 1).flatMap orbitE) = [22, 46, 79] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([22].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 0 14 2).flatMap orbitE) = [25, 49, 73] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([25].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 0 15 0).flatMap orbitE) = [20, 50, 80] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([20].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 0 15 1).flatMap orbitE) = [23, 53, 74] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([23].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 0 15 2).flatMap orbitE) = [26, 47, 77] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([26].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 0 16 0).flatMap orbitE) = [91, 151, 121] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([91].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 0 16 1).flatMap orbitE) = [94, 145, 124] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([94].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 0 16 2).flatMap orbitE) = [97, 148, 118] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([97].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 0 17 0).flatMap orbitE) = [100, 133, 157] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([100].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 0 17 1).flatMap orbitE) = [103, 127, 160] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([103].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 0 17 2).flatMap orbitE) = [106, 130, 154] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([106].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 0 18 0).flatMap orbitE) = [163, 169, 166] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([163].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 0 18 1).flatMap orbitE) = [190, 196, 193] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([190].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 0 18 2).flatMap orbitE) = [217, 223, 220] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([217].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 0 19 0).flatMap orbitE) = [164, 167, 170] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([164].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 0 19 1).flatMap orbitE) = [191, 194, 197] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([191].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 0 19 2).flatMap orbitE) = [218, 221, 224] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([218].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 0 20 0).flatMap orbitE) = [171, 225, 198] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([171].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 0 20 1).flatMap orbitE) = [174, 228, 201] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([174].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 0 20 2).flatMap orbitE) = [177, 231, 204] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([177].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 0 21 0).flatMap orbitE) = [172, 232, 202] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([172].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 0 21 1).flatMap orbitE) = [175, 226, 205] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([175].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 0 21 2).flatMap orbitE) = [178, 229, 199] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([178].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 0 22 0).flatMap orbitE) = [180, 207, 234] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([180].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 0 22 1).flatMap orbitE) = [183, 210, 237] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([183].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 0 22 2).flatMap orbitE) = [186, 213, 240] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([186].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 0 23 0).flatMap orbitE) = [181, 214, 238] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([181].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 0 23 1).flatMap orbitE) = [184, 208, 241] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([184].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 0 23 2).flatMap orbitE) = [187, 211, 235] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([187].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 1 0 0).flatMap orbitE) = [28, 34, 31, 55, 61, 58] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([28, 55].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 1 0 1).flatMap orbitE) = [1, 7, 4, 55, 61, 58] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([1, 55].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 1 0 2).flatMap orbitE) = [1, 7, 4, 28, 34, 31] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([1, 28].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 1 1 0).flatMap orbitE) = [12, 66, 39, 15, 69, 42] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([12, 15].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 1 1 1).flatMap orbitE) = [9, 63, 36, 15, 69, 42] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([9, 15].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 1 1 2).flatMap orbitE) = [9, 63, 36, 12, 66, 39] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([9, 12].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 1 2 0).flatMap orbitE) = [13, 64, 43, 16, 67, 37] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([13, 16].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 1 2 1).flatMap orbitE) = [10, 70, 40, 16, 67, 37] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([10, 16].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 1 2 2).flatMap orbitE) = [10, 70, 40, 13, 64, 43] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([10, 13].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 1 3 0).flatMap orbitE) = [22, 46, 79, 25, 49, 73] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([22, 25].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 1 3 1).flatMap orbitE) = [19, 52, 76, 25, 49, 73] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([19, 25].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 1 3 2).flatMap orbitE) = [19, 52, 76, 22, 46, 79] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([19, 22].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 1 4 0).flatMap orbitE) = [109, 115, 112, 136, 142, 139] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([109, 136].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 1 4 1).flatMap orbitE) = [82, 88, 85, 136, 142, 139] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([82, 136].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 1 4 2).flatMap orbitE) = [82, 88, 85, 109, 115, 112] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([82, 109].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 1 5 0).flatMap orbitE) = [110, 113, 116, 137, 140, 143] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([110, 137].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 1 5 1).flatMap orbitE) = [83, 86, 89, 137, 140, 143] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([83, 137].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 1 5 2).flatMap orbitE) = [83, 86, 89, 110, 113, 116] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([83, 110].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 1 6 0).flatMap orbitE) = [93, 147, 120, 96, 150, 123] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([93, 96].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 1 6 1).flatMap orbitE) = [90, 144, 117, 96, 150, 123] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([90, 96].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 1 6 2).flatMap orbitE) = [90, 144, 117, 93, 147, 120] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([90, 93].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 1 7 0).flatMap orbitE) = [102, 129, 156, 105, 132, 159] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([102, 105].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 1 7 1).flatMap orbitE) = [99, 126, 153, 105, 132, 159] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([99, 105].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 1 7 2).flatMap orbitE) = [99, 126, 153, 102, 129, 156] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([99, 102].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 1 8 0).flatMap orbitE) = [103, 127, 160, 106, 130, 154] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([103, 106].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 1 8 1).flatMap orbitE) = [100, 133, 157, 106, 130, 154] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([100, 106].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 1 8 2).flatMap orbitE) = [100, 133, 157, 103, 127, 160] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([100, 103].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 1 9 0).flatMap orbitE) = [104, 134, 155, 107, 128, 158] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([104, 107].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 1 9 1).flatMap orbitE) = [101, 131, 161, 107, 128, 158] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([101, 107].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 1 9 2).flatMap orbitE) = [101, 131, 161, 104, 134, 155] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([101, 104].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 1 10 0).flatMap orbitE) = [184, 208, 241, 187, 211, 235] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([184, 187].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 1 10 1).flatMap orbitE) = [181, 214, 238, 187, 211, 235] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([181, 187].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 1 10 2).flatMap orbitE) = [181, 214, 238, 184, 208, 241] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([181, 184].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 1 11 0).flatMap orbitE) = [185, 215, 236, 188, 209, 239] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([185, 188].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 1 11 1).flatMap orbitE) = [182, 212, 242, 188, 209, 239] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([182, 188].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 1 11 2).flatMap orbitE) = [182, 212, 242, 185, 215, 236] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([182, 185].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 1 12 0).flatMap orbitE) = [2, 5, 8] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([2].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 1 12 1).flatMap orbitE) = [29, 32, 35] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([29].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 1 12 2).flatMap orbitE) = [56, 59, 62] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([56].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 1 13 0).flatMap orbitE) = [11, 68, 44] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([11].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 1 13 1).flatMap orbitE) = [14, 71, 38] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([14].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 1 13 2).flatMap orbitE) = [17, 65, 41] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([17].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 1 14 0).flatMap orbitE) = [18, 45, 72] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([18].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 1 14 1).flatMap orbitE) = [21, 48, 75] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([21].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 1 14 2).flatMap orbitE) = [24, 51, 78] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([24].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 1 15 0).flatMap orbitE) = [20, 50, 80] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([20].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 1 15 1).flatMap orbitE) = [23, 53, 74] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([23].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 1 15 2).flatMap orbitE) = [26, 47, 77] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([26].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 1 16 0).flatMap orbitE) = [91, 151, 121] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([91].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 1 16 1).flatMap orbitE) = [94, 145, 124] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([94].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 1 16 2).flatMap orbitE) = [97, 148, 118] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([97].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 1 17 0).flatMap orbitE) = [92, 149, 125] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([92].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 1 17 1).flatMap orbitE) = [95, 152, 119] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([95].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 1 17 2).flatMap orbitE) = [98, 146, 122] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([98].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 1 18 0).flatMap orbitE) = [163, 169, 166] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([163].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 1 18 1).flatMap orbitE) = [190, 196, 193] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([190].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 1 18 2).flatMap orbitE) = [217, 223, 220] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([217].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 1 19 0).flatMap orbitE) = [164, 167, 170] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([164].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 1 19 1).flatMap orbitE) = [191, 194, 197] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([191].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 1 19 2).flatMap orbitE) = [218, 221, 224] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([218].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 1 20 0).flatMap orbitE) = [171, 225, 198] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([171].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 1 20 1).flatMap orbitE) = [174, 228, 201] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([174].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 1 20 2).flatMap orbitE) = [177, 231, 204] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([177].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 1 21 0).flatMap orbitE) = [172, 232, 202] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([172].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 1 21 1).flatMap orbitE) = [175, 226, 205] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([175].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 1 21 2).flatMap orbitE) = [178, 229, 199] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([178].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 1 22 0).flatMap orbitE) = [173, 230, 206] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([173].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 1 22 1).flatMap orbitE) = [176, 233, 200] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([176].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 1 22 2).flatMap orbitE) = [179, 227, 203] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([179].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 1 23 0).flatMap orbitE) = [180, 207, 234] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([180].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 1 23 1).flatMap orbitE) = [183, 210, 237] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([183].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 1 23 2).flatMap orbitE) = [186, 213, 240] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([186].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 2 0 0).flatMap orbitE) = [29, 32, 35, 56, 59, 62] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([29, 56].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 2 0 1).flatMap orbitE) = [2, 5, 8, 56, 59, 62] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([2, 56].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 2 0 2).flatMap orbitE) = [2, 5, 8, 29, 32, 35] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([2, 29].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 2 1 0).flatMap orbitE) = [12, 66, 39, 15, 69, 42] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([12, 15].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 2 1 1).flatMap orbitE) = [9, 63, 36, 15, 69, 42] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([9, 15].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 2 1 2).flatMap orbitE) = [9, 63, 36, 12, 66, 39] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([9, 12].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 2 2 0).flatMap orbitE) = [13, 64, 43, 16, 67, 37] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([13, 16].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 2 2 1).flatMap orbitE) = [10, 70, 40, 16, 67, 37] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([10, 16].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 2 2 2).flatMap orbitE) = [10, 70, 40, 13, 64, 43] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([10, 13].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 2 3 0).flatMap orbitE) = [14, 71, 38, 17, 65, 41] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([14, 17].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 2 3 1).flatMap orbitE) = [11, 68, 44, 17, 65, 41] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([11, 17].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 2 3 2).flatMap orbitE) = [11, 68, 44, 14, 71, 38] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([11, 14].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 2 4 0).flatMap orbitE) = [109, 115, 112, 136, 142, 139] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([109, 136].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 2 4 1).flatMap orbitE) = [82, 88, 85, 136, 142, 139] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([82, 136].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 2 4 2).flatMap orbitE) = [82, 88, 85, 109, 115, 112] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([82, 109].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 2 5 0).flatMap orbitE) = [110, 113, 116, 137, 140, 143] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([110, 137].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 2 5 1).flatMap orbitE) = [83, 86, 89, 137, 140, 143] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([83, 137].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 2 5 2).flatMap orbitE) = [83, 86, 89, 110, 113, 116] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([83, 110].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 2 6 0).flatMap orbitE) = [93, 147, 120, 96, 150, 123] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([93, 96].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 2 6 1).flatMap orbitE) = [90, 144, 117, 96, 150, 123] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([90, 96].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 2 6 2).flatMap orbitE) = [90, 144, 117, 93, 147, 120] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([90, 93].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 2 7 0).flatMap orbitE) = [94, 145, 124, 97, 148, 118] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([94, 97].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 2 7 1).flatMap orbitE) = [91, 151, 121, 97, 148, 118] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([91, 97].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 2 7 2).flatMap orbitE) = [91, 151, 121, 94, 145, 124] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([91, 94].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 2 8 0).flatMap orbitE) = [102, 129, 156, 105, 132, 159] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([102, 105].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 2 8 1).flatMap orbitE) = [99, 126, 153, 105, 132, 159] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([99, 105].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 2 8 2).flatMap orbitE) = [99, 126, 153, 102, 129, 156] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([99, 102].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 2 9 0).flatMap orbitE) = [103, 127, 160, 106, 130, 154] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([103, 106].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 2 9 1).flatMap orbitE) = [100, 133, 157, 106, 130, 154] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([100, 106].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 2 9 2).flatMap orbitE) = [100, 133, 157, 103, 127, 160] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([100, 103].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 2 10 0).flatMap orbitE) = [175, 226, 205, 178, 229, 199] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([175, 178].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 2 10 1).flatMap orbitE) = [172, 232, 202, 178, 229, 199] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([172, 178].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 2 10 2).flatMap orbitE) = [172, 232, 202, 175, 226, 205] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([172, 175].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 2 11 0).flatMap orbitE) = [184, 208, 241, 187, 211, 235] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([184, 187].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 2 11 1).flatMap orbitE) = [181, 214, 238, 187, 211, 235] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([181, 187].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 2 11 2).flatMap orbitE) = [181, 214, 238, 184, 208, 241] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([181, 184].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 2 12 0).flatMap orbitE) = [1, 7, 4] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([1].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 2 12 1).flatMap orbitE) = [28, 34, 31] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([28].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 2 12 2).flatMap orbitE) = [55, 61, 58] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([55].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 2 13 0).flatMap orbitE) = [18, 45, 72] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([18].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 2 13 1).flatMap orbitE) = [21, 48, 75] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([21].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 2 13 2).flatMap orbitE) = [24, 51, 78] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([24].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 2 14 0).flatMap orbitE) = [19, 52, 76] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([19].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 2 14 1).flatMap orbitE) = [22, 46, 79] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([22].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 2 14 2).flatMap orbitE) = [25, 49, 73] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([25].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 2 15 0).flatMap orbitE) = [20, 50, 80] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([20].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 2 15 1).flatMap orbitE) = [23, 53, 74] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([23].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 2 15 2).flatMap orbitE) = [26, 47, 77] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([26].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 2 16 0).flatMap orbitE) = [92, 149, 125] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([92].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 2 16 1).flatMap orbitE) = [95, 152, 119] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([95].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 2 16 2).flatMap orbitE) = [98, 146, 122] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([98].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 2 17 0).flatMap orbitE) = [101, 131, 161] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([101].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 2 17 1).flatMap orbitE) = [104, 134, 155] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([104].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 2 17 2).flatMap orbitE) = [107, 128, 158] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([107].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 2 18 0).flatMap orbitE) = [163, 169, 166] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([163].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 2 18 1).flatMap orbitE) = [190, 196, 193] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([190].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 2 18 2).flatMap orbitE) = [217, 223, 220] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([217].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 2 19 0).flatMap orbitE) = [164, 167, 170] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([164].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 2 19 1).flatMap orbitE) = [191, 194, 197] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([191].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 2 19 2).flatMap orbitE) = [218, 221, 224] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([218].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 2 20 0).flatMap orbitE) = [171, 225, 198] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([171].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 2 20 1).flatMap orbitE) = [174, 228, 201] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([174].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 2 20 2).flatMap orbitE) = [177, 231, 204] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([177].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 2 21 0).flatMap orbitE) = [173, 230, 206] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([173].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 2 21 1).flatMap orbitE) = [176, 233, 200] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([176].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 2 21 2).flatMap orbitE) = [179, 227, 203] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([179].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 2 22 0).flatMap orbitE) = [180, 207, 234] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([180].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 2 22 1).flatMap orbitE) = [183, 210, 237] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([183].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 2 22 2).flatMap orbitE) = [186, 213, 240] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([186].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 2 23 0).flatMap orbitE) = [182, 212, 242] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([182].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 2 23 1).flatMap orbitE) = [185, 215, 236] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([185].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 2 23 2).flatMap orbitE) = [188, 209, 239] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([188].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 3 0 0).flatMap orbitE) = [29, 32, 35, 56, 59, 62] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([29, 56].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 3 0 1).flatMap orbitE) = [2, 5, 8, 56, 59, 62] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([2, 56].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 3 0 2).flatMap orbitE) = [2, 5, 8, 29, 32, 35] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([2, 29].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 3 1 0).flatMap orbitE) = [12, 66, 39, 15, 69, 42] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([12, 15].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 3 1 1).flatMap orbitE) = [9, 63, 36, 15, 69, 42] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([9, 15].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 3 1 2).flatMap orbitE) = [9, 63, 36, 12, 66, 39] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([9, 12].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 3 2 0).flatMap orbitE) = [14, 71, 38, 17, 65, 41] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([14, 17].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 3 2 1).flatMap orbitE) = [11, 68, 44, 17, 65, 41] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([11, 17].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 3 2 2).flatMap orbitE) = [11, 68, 44, 14, 71, 38] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([11, 14].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 3 3 0).flatMap orbitE) = [23, 53, 74, 26, 47, 77] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([23, 26].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 3 3 1).flatMap orbitE) = [20, 50, 80, 26, 47, 77] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([20, 26].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 3 3 2).flatMap orbitE) = [20, 50, 80, 23, 53, 74] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([20, 23].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 3 4 0).flatMap orbitE) = [109, 115, 112, 136, 142, 139] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([109, 136].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 3 4 1).flatMap orbitE) = [82, 88, 85, 136, 142, 139] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([82, 136].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 3 4 2).flatMap orbitE) = [82, 88, 85, 109, 115, 112] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([82, 109].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 3 5 0).flatMap orbitE) = [110, 113, 116, 137, 140, 143] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([110, 137].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 3 5 1).flatMap orbitE) = [83, 86, 89, 137, 140, 143] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([83, 137].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 3 5 2).flatMap orbitE) = [83, 86, 89, 110, 113, 116] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([83, 110].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 3 6 0).flatMap orbitE) = [93, 147, 120, 96, 150, 123] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([93, 96].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 3 6 1).flatMap orbitE) = [90, 144, 117, 96, 150, 123] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([90, 96].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 3 6 2).flatMap orbitE) = [90, 144, 117, 93, 147, 120] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([90, 93].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 3 7 0).flatMap orbitE) = [102, 129, 156, 105, 132, 159] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([102, 105].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 3 7 1).flatMap orbitE) = [99, 126, 153, 105, 132, 159] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([99, 105].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 3 7 2).flatMap orbitE) = [99, 126, 153, 102, 129, 156] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([99, 102].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 3 8 0).flatMap orbitE) = [103, 127, 160, 106, 130, 154] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([103, 106].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 3 8 1).flatMap orbitE) = [100, 133, 157, 106, 130, 154] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([100, 106].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 3 8 2).flatMap orbitE) = [100, 133, 157, 103, 127, 160] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([100, 103].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 3 9 0).flatMap orbitE) = [104, 134, 155, 107, 128, 158] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([104, 107].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 3 9 1).flatMap orbitE) = [101, 131, 161, 107, 128, 158] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([101, 107].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 3 9 2).flatMap orbitE) = [101, 131, 161, 104, 134, 155] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([101, 104].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 3 10 0).flatMap orbitE) = [184, 208, 241, 187, 211, 235] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([184, 187].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 3 10 1).flatMap orbitE) = [181, 214, 238, 187, 211, 235] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([181, 187].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 3 10 2).flatMap orbitE) = [181, 214, 238, 184, 208, 241] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([181, 184].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 3 11 0).flatMap orbitE) = [185, 215, 236, 188, 209, 239] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([185, 188].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 3 11 1).flatMap orbitE) = [182, 212, 242, 188, 209, 239] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([182, 188].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 3 11 2).flatMap orbitE) = [182, 212, 242, 185, 215, 236] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([182, 185].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 3 12 0).flatMap orbitE) = [1, 7, 4] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([1].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 3 12 1).flatMap orbitE) = [28, 34, 31] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([28].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 3 12 2).flatMap orbitE) = [55, 61, 58] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([55].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 3 13 0).flatMap orbitE) = [10, 70, 40] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([10].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 3 13 1).flatMap orbitE) = [13, 64, 43] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([13].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 3 13 2).flatMap orbitE) = [16, 67, 37] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([16].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 3 14 0).flatMap orbitE) = [18, 45, 72] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([18].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 3 14 1).flatMap orbitE) = [21, 48, 75] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([21].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 3 14 2).flatMap orbitE) = [24, 51, 78] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([24].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 3 15 0).flatMap orbitE) = [19, 52, 76] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([19].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 3 15 1).flatMap orbitE) = [22, 46, 79] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([22].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 3 15 2).flatMap orbitE) = [25, 49, 73] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([25].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 3 16 0).flatMap orbitE) = [91, 151, 121] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([91].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 3 16 1).flatMap orbitE) = [94, 145, 124] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([94].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 3 16 2).flatMap orbitE) = [97, 148, 118] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([97].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 3 17 0).flatMap orbitE) = [92, 149, 125] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([92].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 3 17 1).flatMap orbitE) = [95, 152, 119] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([95].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 3 17 2).flatMap orbitE) = [98, 146, 122] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([98].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 3 18 0).flatMap orbitE) = [163, 169, 166] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([163].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 3 18 1).flatMap orbitE) = [190, 196, 193] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([190].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 3 18 2).flatMap orbitE) = [217, 223, 220] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([217].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 3 19 0).flatMap orbitE) = [164, 167, 170] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([164].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 3 19 1).flatMap orbitE) = [191, 194, 197] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([191].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 3 19 2).flatMap orbitE) = [218, 221, 224] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([218].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 3 20 0).flatMap orbitE) = [171, 225, 198] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([171].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 3 20 1).flatMap orbitE) = [174, 228, 201] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([174].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 3 20 2).flatMap orbitE) = [177, 231, 204] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([177].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 3 21 0).flatMap orbitE) = [172, 232, 202] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([172].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 3 21 1).flatMap orbitE) = [175, 226, 205] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([175].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 3 21 2).flatMap orbitE) = [178, 229, 199] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([178].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 3 22 0).flatMap orbitE) = [173, 230, 206] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([173].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 3 22 1).flatMap orbitE) = [176, 233, 200] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([176].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 3 22 2).flatMap orbitE) = [179, 227, 203] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([179].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 3 23 0).flatMap orbitE) = [180, 207, 234] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([180].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 3 23 1).flatMap orbitE) = [183, 210, 237] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([183].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 3 23 2).flatMap orbitE) = [186, 213, 240] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([186].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 4 0 0).flatMap orbitE) = [28, 34, 31, 55, 61, 58] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([28, 55].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 4 0 1).flatMap orbitE) = [1, 7, 4, 55, 61, 58] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([1, 55].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 4 0 2).flatMap orbitE) = [1, 7, 4, 28, 34, 31] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([1, 28].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 4 1 0).flatMap orbitE) = [12, 66, 39, 15, 69, 42] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([12, 15].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 4 1 1).flatMap orbitE) = [9, 63, 36, 15, 69, 42] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([9, 15].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 4 1 2).flatMap orbitE) = [9, 63, 36, 12, 66, 39] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([9, 12].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 4 2 0).flatMap orbitE) = [13, 64, 43, 16, 67, 37] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([13, 16].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 4 2 1).flatMap orbitE) = [10, 70, 40, 16, 67, 37] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([10, 16].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 4 2 2).flatMap orbitE) = [10, 70, 40, 13, 64, 43] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([10, 13].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 4 3 0).flatMap orbitE) = [14, 71, 38, 17, 65, 41] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([14, 17].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 4 3 1).flatMap orbitE) = [11, 68, 44, 17, 65, 41] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([11, 17].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 4 3 2).flatMap orbitE) = [11, 68, 44, 14, 71, 38] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([11, 14].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 4 4 0).flatMap orbitE) = [109, 115, 112, 136, 142, 139] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([109, 136].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 4 4 1).flatMap orbitE) = [82, 88, 85, 136, 142, 139] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([82, 136].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 4 4 2).flatMap orbitE) = [82, 88, 85, 109, 115, 112] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([82, 109].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 4 5 0).flatMap orbitE) = [93, 147, 120, 96, 150, 123] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([93, 96].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 4 5 1).flatMap orbitE) = [90, 144, 117, 96, 150, 123] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([90, 96].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 4 5 2).flatMap orbitE) = [90, 144, 117, 93, 147, 120] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([90, 93].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 4 6 0).flatMap orbitE) = [102, 129, 156, 105, 132, 159] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([102, 105].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 4 6 1).flatMap orbitE) = [99, 126, 153, 105, 132, 159] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([99, 105].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 4 6 2).flatMap orbitE) = [99, 126, 153, 102, 129, 156] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([99, 102].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 4 7 0).flatMap orbitE) = [190, 196, 193, 217, 223, 220] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([190, 217].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 4 7 1).flatMap orbitE) = [163, 169, 166, 217, 223, 220] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([163, 217].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 4 7 2).flatMap orbitE) = [163, 169, 166, 190, 196, 193] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([163, 190].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 4 8 0).flatMap orbitE) = [175, 226, 205, 178, 229, 199] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([175, 178].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 4 8 1).flatMap orbitE) = [172, 232, 202, 178, 229, 199] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([172, 178].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 4 8 2).flatMap orbitE) = [172, 232, 202, 175, 226, 205] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([172, 175].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 4 9 0).flatMap orbitE) = [176, 233, 200, 179, 227, 203] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([176, 179].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 4 9 1).flatMap orbitE) = [173, 230, 206, 179, 227, 203] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([173, 179].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 4 9 2).flatMap orbitE) = [173, 230, 206, 176, 233, 200] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([173, 176].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 4 10 0).flatMap orbitE) = [184, 208, 241, 187, 211, 235] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([184, 187].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 4 10 1).flatMap orbitE) = [181, 214, 238, 187, 211, 235] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([181, 187].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 4 10 2).flatMap orbitE) = [181, 214, 238, 184, 208, 241] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([181, 184].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 4 11 0).flatMap orbitE) = [185, 215, 236, 188, 209, 239] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([185, 188].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 4 11 1).flatMap orbitE) = [182, 212, 242, 188, 209, 239] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([182, 188].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 4 11 2).flatMap orbitE) = [182, 212, 242, 185, 215, 236] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([182, 185].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 4 12 0).flatMap orbitE) = [2, 5, 8] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([2].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 4 12 1).flatMap orbitE) = [29, 32, 35] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([29].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 4 12 2).flatMap orbitE) = [56, 59, 62] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([56].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 4 13 0).flatMap orbitE) = [18, 45, 72] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([18].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 4 13 1).flatMap orbitE) = [21, 48, 75] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([21].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 4 13 2).flatMap orbitE) = [24, 51, 78] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([24].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 4 14 0).flatMap orbitE) = [19, 52, 76] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([19].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 4 14 1).flatMap orbitE) = [22, 46, 79] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([22].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 4 14 2).flatMap orbitE) = [25, 49, 73] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([25].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 4 15 0).flatMap orbitE) = [20, 50, 80] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([20].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 4 15 1).flatMap orbitE) = [23, 53, 74] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([23].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 4 15 2).flatMap orbitE) = [26, 47, 77] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([26].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 4 16 0).flatMap orbitE) = [83, 86, 89] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([83].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 4 16 1).flatMap orbitE) = [110, 113, 116] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([110].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 4 16 2).flatMap orbitE) = [137, 140, 143] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([137].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 4 17 0).flatMap orbitE) = [91, 151, 121] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([91].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 4 17 1).flatMap orbitE) = [94, 145, 124] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([94].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 4 17 2).flatMap orbitE) = [97, 148, 118] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([97].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 4 18 0).flatMap orbitE) = [92, 149, 125] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([92].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 4 18 1).flatMap orbitE) = [95, 152, 119] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([95].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 4 18 2).flatMap orbitE) = [98, 146, 122] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([98].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 4 19 0).flatMap orbitE) = [100, 133, 157] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([100].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 4 19 1).flatMap orbitE) = [103, 127, 160] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([103].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 4 19 2).flatMap orbitE) = [106, 130, 154] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([106].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 4 20 0).flatMap orbitE) = [101, 131, 161] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([101].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 4 20 1).flatMap orbitE) = [104, 134, 155] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([104].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 4 20 2).flatMap orbitE) = [107, 128, 158] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([107].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 4 21 0).flatMap orbitE) = [164, 167, 170] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([164].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 4 21 1).flatMap orbitE) = [191, 194, 197] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([191].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 4 21 2).flatMap orbitE) = [218, 221, 224] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([218].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 4 22 0).flatMap orbitE) = [171, 225, 198] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([171].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 4 22 1).flatMap orbitE) = [174, 228, 201] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([174].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 4 22 2).flatMap orbitE) = [177, 231, 204] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([177].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 4 23 0).flatMap orbitE) = [180, 207, 234] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([180].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 4 23 1).flatMap orbitE) = [183, 210, 237] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([183].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 4 23 2).flatMap orbitE) = [186, 213, 240] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([186].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 5 0 0).flatMap orbitE) = [29, 32, 35, 56, 59, 62] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([29, 56].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 5 0 1).flatMap orbitE) = [2, 5, 8, 56, 59, 62] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([2, 56].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 5 0 2).flatMap orbitE) = [2, 5, 8, 29, 32, 35] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([2, 29].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 5 1 0).flatMap orbitE) = [12, 66, 39, 15, 69, 42] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([12, 15].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 5 1 1).flatMap orbitE) = [9, 63, 36, 15, 69, 42] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([9, 15].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 5 1 2).flatMap orbitE) = [9, 63, 36, 12, 66, 39] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([9, 12].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 5 2 0).flatMap orbitE) = [13, 64, 43, 16, 67, 37] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([13, 16].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 5 2 1).flatMap orbitE) = [10, 70, 40, 16, 67, 37] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([10, 16].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 5 2 2).flatMap orbitE) = [10, 70, 40, 13, 64, 43] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([10, 13].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 5 3 0).flatMap orbitE) = [14, 71, 38, 17, 65, 41] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([14, 17].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 5 3 1).flatMap orbitE) = [11, 68, 44, 17, 65, 41] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([11, 17].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 5 3 2).flatMap orbitE) = [11, 68, 44, 14, 71, 38] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([11, 14].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 5 4 0).flatMap orbitE) = [110, 113, 116, 137, 140, 143] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([110, 137].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 5 4 1).flatMap orbitE) = [83, 86, 89, 137, 140, 143] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([83, 137].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 5 4 2).flatMap orbitE) = [83, 86, 89, 110, 113, 116] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([83, 110].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 5 5 0).flatMap orbitE) = [93, 147, 120, 96, 150, 123] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([93, 96].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 5 5 1).flatMap orbitE) = [90, 144, 117, 96, 150, 123] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([90, 96].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 5 5 2).flatMap orbitE) = [90, 144, 117, 93, 147, 120] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([90, 93].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 5 6 0).flatMap orbitE) = [102, 129, 156, 105, 132, 159] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([102, 105].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 5 6 1).flatMap orbitE) = [99, 126, 153, 105, 132, 159] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([99, 105].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 5 6 2).flatMap orbitE) = [99, 126, 153, 102, 129, 156] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([99, 102].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 5 7 0).flatMap orbitE) = [191, 194, 197, 218, 221, 224] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([191, 218].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 5 7 1).flatMap orbitE) = [164, 167, 170, 218, 221, 224] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([164, 218].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 5 7 2).flatMap orbitE) = [164, 167, 170, 191, 194, 197] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([164, 191].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 5 8 0).flatMap orbitE) = [175, 226, 205, 178, 229, 199] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([175, 178].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 5 8 1).flatMap orbitE) = [172, 232, 202, 178, 229, 199] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([172, 178].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 5 8 2).flatMap orbitE) = [172, 232, 202, 175, 226, 205] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([172, 175].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 5 9 0).flatMap orbitE) = [176, 233, 200, 179, 227, 203] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([176, 179].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 5 9 1).flatMap orbitE) = [173, 230, 206, 179, 227, 203] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([173, 179].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 5 9 2).flatMap orbitE) = [173, 230, 206, 176, 233, 200] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([173, 176].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 5 10 0).flatMap orbitE) = [184, 208, 241, 187, 211, 235] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([184, 187].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 5 10 1).flatMap orbitE) = [181, 214, 238, 187, 211, 235] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([181, 187].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 5 10 2).flatMap orbitE) = [181, 214, 238, 184, 208, 241] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([181, 184].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 5 11 0).flatMap orbitE) = [185, 215, 236, 188, 209, 239] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([185, 188].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 5 11 1).flatMap orbitE) = [182, 212, 242, 188, 209, 239] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([182, 188].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 5 11 2).flatMap orbitE) = [182, 212, 242, 185, 215, 236] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([182, 185].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 5 12 0).flatMap orbitE) = [1, 7, 4] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([1].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 5 12 1).flatMap orbitE) = [28, 34, 31] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([28].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 5 12 2).flatMap orbitE) = [55, 61, 58] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([55].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 5 13 0).flatMap orbitE) = [18, 45, 72] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([18].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 5 13 1).flatMap orbitE) = [21, 48, 75] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([21].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 5 13 2).flatMap orbitE) = [24, 51, 78] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([24].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 5 14 0).flatMap orbitE) = [19, 52, 76] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([19].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 5 14 1).flatMap orbitE) = [22, 46, 79] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([22].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 5 14 2).flatMap orbitE) = [25, 49, 73] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([25].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 5 15 0).flatMap orbitE) = [20, 50, 80] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([20].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 5 15 1).flatMap orbitE) = [23, 53, 74] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([23].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 5 15 2).flatMap orbitE) = [26, 47, 77] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([26].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 5 16 0).flatMap orbitE) = [82, 88, 85] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([82].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 5 16 1).flatMap orbitE) = [109, 115, 112] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([109].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 5 16 2).flatMap orbitE) = [136, 142, 139] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([136].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 5 17 0).flatMap orbitE) = [91, 151, 121] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([91].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 5 17 1).flatMap orbitE) = [94, 145, 124] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([94].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 5 17 2).flatMap orbitE) = [97, 148, 118] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([97].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 5 18 0).flatMap orbitE) = [92, 149, 125] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([92].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 5 18 1).flatMap orbitE) = [95, 152, 119] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([95].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 5 18 2).flatMap orbitE) = [98, 146, 122] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([98].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 5 19 0).flatMap orbitE) = [100, 133, 157] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([100].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 5 19 1).flatMap orbitE) = [103, 127, 160] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([103].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 5 19 2).flatMap orbitE) = [106, 130, 154] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([106].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 5 20 0).flatMap orbitE) = [101, 131, 161] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([101].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 5 20 1).flatMap orbitE) = [104, 134, 155] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([104].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 5 20 2).flatMap orbitE) = [107, 128, 158] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([107].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 5 21 0).flatMap orbitE) = [163, 169, 166] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([163].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 5 21 1).flatMap orbitE) = [190, 196, 193] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([190].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 5 21 2).flatMap orbitE) = [217, 223, 220] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([217].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 5 22 0).flatMap orbitE) = [171, 225, 198] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([171].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 5 22 1).flatMap orbitE) = [174, 228, 201] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([174].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 5 22 2).flatMap orbitE) = [177, 231, 204] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([177].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 5 23 0).flatMap orbitE) = [180, 207, 234] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([180].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 5 23 1).flatMap orbitE) = [183, 210, 237] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([183].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 5 23 2).flatMap orbitE) = [186, 213, 240] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([186].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 6 0 0).flatMap orbitE) = [28, 34, 31, 55, 61, 58] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([28, 55].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 6 0 1).flatMap orbitE) = [1, 7, 4, 55, 61, 58] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([1, 55].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 6 0 2).flatMap orbitE) = [1, 7, 4, 28, 34, 31] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([1, 28].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 6 1 0).flatMap orbitE) = [12, 66, 39, 15, 69, 42] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([12, 15].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 6 1 1).flatMap orbitE) = [9, 63, 36, 15, 69, 42] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([9, 15].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 6 1 2).flatMap orbitE) = [9, 63, 36, 12, 66, 39] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([9, 12].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 6 2 0).flatMap orbitE) = [13, 64, 43, 16, 67, 37] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([13, 16].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 6 2 1).flatMap orbitE) = [10, 70, 40, 16, 67, 37] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([10, 16].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 6 2 2).flatMap orbitE) = [10, 70, 40, 13, 64, 43] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([10, 13].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 6 3 0).flatMap orbitE) = [14, 71, 38, 17, 65, 41] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([14, 17].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 6 3 1).flatMap orbitE) = [11, 68, 44, 17, 65, 41] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([11, 17].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 6 3 2).flatMap orbitE) = [11, 68, 44, 14, 71, 38] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([11, 14].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 6 4 0).flatMap orbitE) = [109, 115, 112, 136, 142, 139] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([109, 136].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 6 4 1).flatMap orbitE) = [82, 88, 85, 136, 142, 139] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([82, 136].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 6 4 2).flatMap orbitE) = [82, 88, 85, 109, 115, 112] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([82, 109].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 6 5 0).flatMap orbitE) = [110, 113, 116, 137, 140, 143] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([110, 137].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 6 5 1).flatMap orbitE) = [83, 86, 89, 137, 140, 143] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([83, 137].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 6 5 2).flatMap orbitE) = [83, 86, 89, 110, 113, 116] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([83, 110].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 6 6 0).flatMap orbitE) = [94, 145, 124, 97, 148, 118] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([94, 97].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 6 6 1).flatMap orbitE) = [91, 151, 121, 97, 148, 118] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([91, 97].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 6 6 2).flatMap orbitE) = [91, 151, 121, 94, 145, 124] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([91, 94].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 6 7 0).flatMap orbitE) = [95, 152, 119, 98, 146, 122] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([95, 98].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 6 7 1).flatMap orbitE) = [92, 149, 125, 98, 146, 122] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([92, 98].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 6 7 2).flatMap orbitE) = [92, 149, 125, 95, 152, 119] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([92, 95].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 6 8 0).flatMap orbitE) = [102, 129, 156, 105, 132, 159] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([102, 105].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 6 8 1).flatMap orbitE) = [99, 126, 153, 105, 132, 159] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([99, 105].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 6 8 2).flatMap orbitE) = [99, 126, 153, 102, 129, 156] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([99, 102].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 6 9 0).flatMap orbitE) = [103, 127, 160, 106, 130, 154] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([103, 106].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 6 9 1).flatMap orbitE) = [100, 133, 157, 106, 130, 154] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([100, 106].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 6 9 2).flatMap orbitE) = [100, 133, 157, 103, 127, 160] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([100, 103].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 6 10 0).flatMap orbitE) = [175, 226, 205, 178, 229, 199] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([175, 178].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 6 10 1).flatMap orbitE) = [172, 232, 202, 178, 229, 199] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([172, 178].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 6 10 2).flatMap orbitE) = [172, 232, 202, 175, 226, 205] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([172, 175].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 6 11 0).flatMap orbitE) = [183, 210, 237, 186, 213, 240] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([183, 186].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 6 11 1).flatMap orbitE) = [180, 207, 234, 186, 213, 240] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([180, 186].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 6 11 2).flatMap orbitE) = [180, 207, 234, 183, 210, 237] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([180, 183].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 6 12 0).flatMap orbitE) = [2, 5, 8] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([2].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 6 12 1).flatMap orbitE) = [29, 32, 35] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([29].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 6 12 2).flatMap orbitE) = [56, 59, 62] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([56].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 6 13 0).flatMap orbitE) = [18, 45, 72] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([18].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 6 13 1).flatMap orbitE) = [21, 48, 75] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([21].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 6 13 2).flatMap orbitE) = [24, 51, 78] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([24].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 6 14 0).flatMap orbitE) = [19, 52, 76] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([19].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 6 14 1).flatMap orbitE) = [22, 46, 79] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([22].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 6 14 2).flatMap orbitE) = [25, 49, 73] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([25].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 6 15 0).flatMap orbitE) = [20, 50, 80] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([20].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 6 15 1).flatMap orbitE) = [23, 53, 74] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([23].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 6 15 2).flatMap orbitE) = [26, 47, 77] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([26].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 6 16 0).flatMap orbitE) = [90, 144, 117] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([90].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 6 16 1).flatMap orbitE) = [93, 147, 120] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([93].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 6 16 2).flatMap orbitE) = [96, 150, 123] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([96].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 6 17 0).flatMap orbitE) = [101, 131, 161] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([101].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 6 17 1).flatMap orbitE) = [104, 134, 155] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([104].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 6 17 2).flatMap orbitE) = [107, 128, 158] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([107].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 6 18 0).flatMap orbitE) = [163, 169, 166] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([163].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 6 18 1).flatMap orbitE) = [190, 196, 193] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([190].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 6 18 2).flatMap orbitE) = [217, 223, 220] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([217].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 6 19 0).flatMap orbitE) = [164, 167, 170] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([164].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 6 19 1).flatMap orbitE) = [191, 194, 197] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([191].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 6 19 2).flatMap orbitE) = [218, 221, 224] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([218].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 6 20 0).flatMap orbitE) = [171, 225, 198] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([171].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 6 20 1).flatMap orbitE) = [174, 228, 201] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([174].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 6 20 2).flatMap orbitE) = [177, 231, 204] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([177].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 6 21 0).flatMap orbitE) = [173, 230, 206] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([173].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 6 21 1).flatMap orbitE) = [176, 233, 200] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([176].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 6 21 2).flatMap orbitE) = [179, 227, 203] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([179].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 6 22 0).flatMap orbitE) = [181, 214, 238] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([181].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 6 22 1).flatMap orbitE) = [184, 208, 241] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([184].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 6 22 2).flatMap orbitE) = [187, 211, 235] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([187].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 6 23 0).flatMap orbitE) = [182, 212, 242] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([182].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 6 23 1).flatMap orbitE) = [185, 215, 236] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([185].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 6 23 2).flatMap orbitE) = [188, 209, 239] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([188].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 7 0 0).flatMap orbitE) = [28, 34, 31, 55, 61, 58] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([28, 55].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 7 0 1).flatMap orbitE) = [1, 7, 4, 55, 61, 58] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([1, 55].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 7 0 2).flatMap orbitE) = [1, 7, 4, 28, 34, 31] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([1, 28].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 7 1 0).flatMap orbitE) = [12, 66, 39, 15, 69, 42] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([12, 15].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 7 1 1).flatMap orbitE) = [9, 63, 36, 15, 69, 42] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([9, 15].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 7 1 2).flatMap orbitE) = [9, 63, 36, 12, 66, 39] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([9, 12].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 7 2 0).flatMap orbitE) = [14, 71, 38, 17, 65, 41] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([14, 17].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 7 2 1).flatMap orbitE) = [11, 68, 44, 17, 65, 41] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([11, 17].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 7 2 2).flatMap orbitE) = [11, 68, 44, 14, 71, 38] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([11, 14].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 7 3 0).flatMap orbitE) = [23, 53, 74, 26, 47, 77] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([23, 26].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 7 3 1).flatMap orbitE) = [20, 50, 80, 26, 47, 77] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([20, 26].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 7 3 2).flatMap orbitE) = [20, 50, 80, 23, 53, 74] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([20, 23].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 7 4 0).flatMap orbitE) = [109, 115, 112, 136, 142, 139] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([109, 136].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 7 4 1).flatMap orbitE) = [82, 88, 85, 136, 142, 139] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([82, 136].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 7 4 2).flatMap orbitE) = [82, 88, 85, 109, 115, 112] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([82, 109].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 7 5 0).flatMap orbitE) = [110, 113, 116, 137, 140, 143] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([110, 137].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 7 5 1).flatMap orbitE) = [83, 86, 89, 137, 140, 143] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([83, 137].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 7 5 2).flatMap orbitE) = [83, 86, 89, 110, 113, 116] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([83, 110].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 7 6 0).flatMap orbitE) = [95, 152, 119, 98, 146, 122] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([95, 98].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 7 6 1).flatMap orbitE) = [92, 149, 125, 98, 146, 122] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([92, 98].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 7 6 2).flatMap orbitE) = [92, 149, 125, 95, 152, 119] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([92, 95].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 7 7 0).flatMap orbitE) = [102, 129, 156, 105, 132, 159] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([102, 105].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 7 7 1).flatMap orbitE) = [99, 126, 153, 105, 132, 159] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([99, 105].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 7 7 2).flatMap orbitE) = [99, 126, 153, 102, 129, 156] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([99, 102].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 7 8 0).flatMap orbitE) = [103, 127, 160, 106, 130, 154] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([103, 106].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 7 8 1).flatMap orbitE) = [100, 133, 157, 106, 130, 154] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([100, 106].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 7 8 2).flatMap orbitE) = [100, 133, 157, 103, 127, 160] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([100, 103].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 7 9 0).flatMap orbitE) = [104, 134, 155, 107, 128, 158] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([104, 107].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 7 9 1).flatMap orbitE) = [101, 131, 161, 107, 128, 158] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([101, 107].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 7 9 2).flatMap orbitE) = [101, 131, 161, 104, 134, 155] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([101, 104].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 7 10 0).flatMap orbitE) = [183, 210, 237, 186, 213, 240] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([183, 186].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 7 10 1).flatMap orbitE) = [180, 207, 234, 186, 213, 240] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([180, 186].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 7 10 2).flatMap orbitE) = [180, 207, 234, 183, 210, 237] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([180, 183].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 7 11 0).flatMap orbitE) = [185, 215, 236, 188, 209, 239] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([185, 188].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 7 11 1).flatMap orbitE) = [182, 212, 242, 188, 209, 239] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([182, 188].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 7 11 2).flatMap orbitE) = [182, 212, 242, 185, 215, 236] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([182, 185].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 7 12 0).flatMap orbitE) = [2, 5, 8] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([2].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 7 12 1).flatMap orbitE) = [29, 32, 35] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([29].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 7 12 2).flatMap orbitE) = [56, 59, 62] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([56].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 7 13 0).flatMap orbitE) = [10, 70, 40] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([10].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 7 13 1).flatMap orbitE) = [13, 64, 43] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([13].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 7 13 2).flatMap orbitE) = [16, 67, 37] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([16].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 7 14 0).flatMap orbitE) = [18, 45, 72] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([18].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 7 14 1).flatMap orbitE) = [21, 48, 75] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([21].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 7 14 2).flatMap orbitE) = [24, 51, 78] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([24].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 7 15 0).flatMap orbitE) = [19, 52, 76] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([19].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 7 15 1).flatMap orbitE) = [22, 46, 79] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([22].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 7 15 2).flatMap orbitE) = [25, 49, 73] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([25].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 7 16 0).flatMap orbitE) = [90, 144, 117] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([90].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 7 16 1).flatMap orbitE) = [93, 147, 120] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([93].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 7 16 2).flatMap orbitE) = [96, 150, 123] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([96].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 7 17 0).flatMap orbitE) = [91, 151, 121] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([91].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 7 17 1).flatMap orbitE) = [94, 145, 124] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([94].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 7 17 2).flatMap orbitE) = [97, 148, 118] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([97].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 7 18 0).flatMap orbitE) = [163, 169, 166] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([163].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 7 18 1).flatMap orbitE) = [190, 196, 193] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([190].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 7 18 2).flatMap orbitE) = [217, 223, 220] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([217].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 7 19 0).flatMap orbitE) = [164, 167, 170] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([164].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 7 19 1).flatMap orbitE) = [191, 194, 197] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([191].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 7 19 2).flatMap orbitE) = [218, 221, 224] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([218].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 7 20 0).flatMap orbitE) = [171, 225, 198] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([171].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 7 20 1).flatMap orbitE) = [174, 228, 201] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([174].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 7 20 2).flatMap orbitE) = [177, 231, 204] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([177].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 7 21 0).flatMap orbitE) = [172, 232, 202] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([172].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 7 21 1).flatMap orbitE) = [175, 226, 205] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([175].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 7 21 2).flatMap orbitE) = [178, 229, 199] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([178].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 7 22 0).flatMap orbitE) = [173, 230, 206] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([173].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 7 22 1).flatMap orbitE) = [176, 233, 200] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([176].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 7 22 2).flatMap orbitE) = [179, 227, 203] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([179].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 7 23 0).flatMap orbitE) = [181, 214, 238] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([181].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 7 23 1).flatMap orbitE) = [184, 208, 241] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([184].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel
example : ((optionLeaders 7 23 2).flatMap orbitE) = [187, 211, 235] := by
  simp only [optionLeaders]
  rw [bucket_eq _ (by decide)]
  change ([187].flatMap orbitE) = _
  simp only [List.flatMap_cons, List.flatMap_nil, orbitE, smul61, smul3721]
  decide +kernel

-- Exact public statement types, including the conditional range-clear boundary.
example : (∀ r, r < 1038 → Receipt r (receiptDigest.getD r "")) → ¬ ∃ D : Finset G, IsDiffSet D := no_difference_set
example : (∀ r, r < 1038 → RangeClear r) → ¬ ∃ D : Finset G, IsDiffSet D := by
  intro h
  exact no_difference_set (fun r hr => ⟨h r hr⟩)
example (r : ℕ) (s : String) : Receipt r s ↔ RangeClear r := ⟨fun h => h.clear, fun h => ⟨h⟩⟩
example : ∀ {D : Finset G}, IsDiffSet D → ∃ u : G, ∃ w : Word, ∃ r, r < 1038 ∧ ∃ id, 4096 * r ≤ id ∧ id < min (4096 * (r + 1)) 4251528 ∧ ∃ tail : Fin 12 → Fin 3, (D.image (· - u)).image w.legal.toFun = leaf (id / 531441) (idDigits id tail) := @coverage
-- An actual admissible K3 survivor cannot be dropped from the witness table.
example : condMask 92847627 = true := by decide +kernel
example : 92847627 ∈ survivors.map Prod.fst := by decide +kernel
example : 92847627 ∉ (survivors.map Prod.fst).erase 92847627 := by decide +kernel
end CheckDefinitions
