import CatalogCertificate

namespace LockedTromino.Witnesses
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def pattern_0 : Pattern := ([(0,0),(0,1),(0,2)],[(0,3),(0,4),(0,5)])
theorem pattern_0_check : SubsetPairCheck pattern_0.1 pattern_0.2 := by decide +kernel
theorem pattern_0_rigid : Rigid (Cells pattern_0.1) (Cells pattern_0.2) :=
  subsetPairCheck_sound pattern_0_check

def pattern_1 : Pattern := ([(0,0),(0,1),(0,2)],[(0,3),(0,4),(1,3)])
theorem pattern_1_check : SubsetPairCheck pattern_1.1 pattern_1.2 := by decide +kernel
theorem pattern_1_rigid : Rigid (Cells pattern_1.1) (Cells pattern_1.2) :=
  subsetPairCheck_sound pattern_1_check

def pattern_2 : Pattern := ([(0,0),(0,1),(0,2)],[(0,3),(0,4),(1,4)])
theorem pattern_2_check : SubsetPairCheck pattern_2.1 pattern_2.2 := by decide +kernel
theorem pattern_2_rigid : Rigid (Cells pattern_2.1) (Cells pattern_2.2) :=
  subsetPairCheck_sound pattern_2_check

def pattern_3 : Pattern := ([(0,0),(0,1),(0,2)],[(0,3),(1,2),(1,3)])
theorem pattern_3_check : SubsetPairCheck pattern_3.1 pattern_3.2 := by decide +kernel
theorem pattern_3_rigid : Rigid (Cells pattern_3.1) (Cells pattern_3.2) :=
  subsetPairCheck_sound pattern_3_check

def pattern_4 : Pattern := ([(0,0),(0,1),(0,2)],[(0,3),(1,3),(1,4)])
theorem pattern_4_check : SubsetPairCheck pattern_4.1 pattern_4.2 := by decide +kernel
theorem pattern_4_rigid : Rigid (Cells pattern_4.1) (Cells pattern_4.2) :=
  subsetPairCheck_sound pattern_4_check

def pattern_5 : Pattern := ([(0,0),(0,1),(0,2)],[(0,3),(1,3),(2,3)])
theorem pattern_5_check : SubsetPairCheck pattern_5.1 pattern_5.2 := by decide +kernel
theorem pattern_5_rigid : Rigid (Cells pattern_5.1) (Cells pattern_5.2) :=
  subsetPairCheck_sound pattern_5_check

def pattern_6 : Pattern := ([(0,0),(0,1),(0,2)],[(1,0),(1,1),(2,1)])
theorem pattern_6_check : SubsetPairCheck pattern_6.1 pattern_6.2 := by decide +kernel
theorem pattern_6_rigid : Rigid (Cells pattern_6.1) (Cells pattern_6.2) :=
  subsetPairCheck_sound pattern_6_check

def pattern_7 : Pattern := ([(0,0),(0,1),(0,2)],[(1,0),(2,0),(3,0)])
theorem pattern_7_check : SubsetPairCheck pattern_7.1 pattern_7.2 := by decide +kernel
theorem pattern_7_rigid : Rigid (Cells pattern_7.1) (Cells pattern_7.2) :=
  subsetPairCheck_sound pattern_7_check

def pattern_8 : Pattern := ([(0,0),(0,1),(0,2)],[(1,1),(1,2),(2,1)])
theorem pattern_8_check : SubsetPairCheck pattern_8.1 pattern_8.2 := by decide +kernel
theorem pattern_8_rigid : Rigid (Cells pattern_8.1) (Cells pattern_8.2) :=
  subsetPairCheck_sound pattern_8_check

def pattern_9 : Pattern := ([(0,0),(0,1),(0,2)],[(1,1),(2,0),(2,1)])
theorem pattern_9_check : SubsetPairCheck pattern_9.1 pattern_9.2 := by decide +kernel
theorem pattern_9_rigid : Rigid (Cells pattern_9.1) (Cells pattern_9.2) :=
  subsetPairCheck_sound pattern_9_check

def pattern_10 : Pattern := ([(0,0),(0,1),(0,2)],[(1,1),(2,1),(2,2)])
theorem pattern_10_check : SubsetPairCheck pattern_10.1 pattern_10.2 := by decide +kernel
theorem pattern_10_rigid : Rigid (Cells pattern_10.1) (Cells pattern_10.2) :=
  subsetPairCheck_sound pattern_10_check

def pattern_11 : Pattern := ([(0,0),(0,1),(0,2)],[(1,1),(2,1),(3,1)])
theorem pattern_11_check : SubsetPairCheck pattern_11.1 pattern_11.2 := by decide +kernel
theorem pattern_11_rigid : Rigid (Cells pattern_11.1) (Cells pattern_11.2) :=
  subsetPairCheck_sound pattern_11_check

def pattern_12 : Pattern := ([(0,0),(0,1),(0,2)],[(1,2),(1,3),(1,4)])
theorem pattern_12_check : SubsetPairCheck pattern_12.1 pattern_12.2 := by decide +kernel
theorem pattern_12_rigid : Rigid (Cells pattern_12.1) (Cells pattern_12.2) :=
  subsetPairCheck_sound pattern_12_check

def pattern_13 : Pattern := ([(0,0),(0,1),(0,2)],[(1,2),(1,3),(2,2)])
theorem pattern_13_check : SubsetPairCheck pattern_13.1 pattern_13.2 := by decide +kernel
theorem pattern_13_rigid : Rigid (Cells pattern_13.1) (Cells pattern_13.2) :=
  subsetPairCheck_sound pattern_13_check

def pattern_14 : Pattern := ([(0,0),(0,1),(0,2)],[(1,2),(1,3),(2,3)])
theorem pattern_14_check : SubsetPairCheck pattern_14.1 pattern_14.2 := by decide +kernel
theorem pattern_14_rigid : Rigid (Cells pattern_14.1) (Cells pattern_14.2) :=
  subsetPairCheck_sound pattern_14_check

def pattern_15 : Pattern := ([(0,0),(0,1),(0,2)],[(1,2),(2,2),(2,3)])
theorem pattern_15_check : SubsetPairCheck pattern_15.1 pattern_15.2 := by decide +kernel
theorem pattern_15_rigid : Rigid (Cells pattern_15.1) (Cells pattern_15.2) :=
  subsetPairCheck_sound pattern_15_check

def pattern_16 : Pattern := ([(0,0),(0,1),(0,2)],[(1,2),(2,2),(3,2)])
theorem pattern_16_check : SubsetPairCheck pattern_16.1 pattern_16.2 := by decide +kernel
theorem pattern_16_rigid : Rigid (Cells pattern_16.1) (Cells pattern_16.2) :=
  subsetPairCheck_sound pattern_16_check

def pattern_17 : Pattern := ([(0,0),(0,1),(1,0)],[(0,2),(0,3),(0,4)])
theorem pattern_17_check : SubsetPairCheck pattern_17.1 pattern_17.2 := by decide +kernel
theorem pattern_17_rigid : Rigid (Cells pattern_17.1) (Cells pattern_17.2) :=
  subsetPairCheck_sound pattern_17_check

def pattern_18 : Pattern := ([(0,0),(0,1),(1,0)],[(0,2),(0,3),(1,2)])
theorem pattern_18_check : SubsetPairCheck pattern_18.1 pattern_18.2 := by decide +kernel
theorem pattern_18_rigid : Rigid (Cells pattern_18.1) (Cells pattern_18.2) :=
  subsetPairCheck_sound pattern_18_check

def pattern_19 : Pattern := ([(0,0),(0,1),(1,0)],[(0,2),(0,3),(1,3)])
theorem pattern_19_check : SubsetPairCheck pattern_19.1 pattern_19.2 := by decide +kernel
theorem pattern_19_rigid : Rigid (Cells pattern_19.1) (Cells pattern_19.2) :=
  subsetPairCheck_sound pattern_19_check

def pattern_20 : Pattern := ([(0,0),(0,1),(1,0)],[(0,2),(1,2),(1,3)])
theorem pattern_20_check : SubsetPairCheck pattern_20.1 pattern_20.2 := by decide +kernel
theorem pattern_20_rigid : Rigid (Cells pattern_20.1) (Cells pattern_20.2) :=
  subsetPairCheck_sound pattern_20_check

def pattern_21 : Pattern := ([(0,0),(0,1),(1,0)],[(1,1),(1,2),(1,3)])
theorem pattern_21_check : SubsetPairCheck pattern_21.1 pattern_21.2 := by decide +kernel
theorem pattern_21_rigid : Rigid (Cells pattern_21.1) (Cells pattern_21.2) :=
  subsetPairCheck_sound pattern_21_check

def pattern_22 : Pattern := ([(0,0),(0,1),(1,0)],[(1,1),(1,2),(2,1)])
theorem pattern_22_check : SubsetPairCheck pattern_22.1 pattern_22.2 := by decide +kernel
theorem pattern_22_rigid : Rigid (Cells pattern_22.1) (Cells pattern_22.2) :=
  subsetPairCheck_sound pattern_22_check

def pattern_23 : Pattern := ([(0,0),(0,1),(1,0)],[(1,1),(1,2),(2,2)])
theorem pattern_23_check : SubsetPairCheck pattern_23.1 pattern_23.2 := by decide +kernel
theorem pattern_23_rigid : Rigid (Cells pattern_23.1) (Cells pattern_23.2) :=
  subsetPairCheck_sound pattern_23_check

def pattern_24 : Pattern := ([(0,0),(0,1),(1,0)],[(1,1),(2,1),(2,2)])
theorem pattern_24_check : SubsetPairCheck pattern_24.1 pattern_24.2 := by decide +kernel
theorem pattern_24_rigid : Rigid (Cells pattern_24.1) (Cells pattern_24.2) :=
  subsetPairCheck_sound pattern_24_check

def pattern_25 : Pattern := ([(0,0),(0,1),(1,0)],[(1,1),(2,1),(3,1)])
theorem pattern_25_check : SubsetPairCheck pattern_25.1 pattern_25.2 := by decide +kernel
theorem pattern_25_rigid : Rigid (Cells pattern_25.1) (Cells pattern_25.2) :=
  subsetPairCheck_sound pattern_25_check

def pattern_26 : Pattern := ([(0,0),(0,1),(1,0)],[(2,0),(2,1),(3,0)])
theorem pattern_26_check : SubsetPairCheck pattern_26.1 pattern_26.2 := by decide +kernel
theorem pattern_26_rigid : Rigid (Cells pattern_26.1) (Cells pattern_26.2) :=
  subsetPairCheck_sound pattern_26_check

def pattern_27 : Pattern := ([(0,0),(0,1),(1,0)],[(2,0),(2,1),(3,1)])
theorem pattern_27_check : SubsetPairCheck pattern_27.1 pattern_27.2 := by decide +kernel
theorem pattern_27_rigid : Rigid (Cells pattern_27.1) (Cells pattern_27.2) :=
  subsetPairCheck_sound pattern_27_check

def pattern_28 : Pattern := ([(0,0),(0,1),(1,0)],[(2,0),(3,0),(3,1)])
theorem pattern_28_check : SubsetPairCheck pattern_28.1 pattern_28.2 := by decide +kernel
theorem pattern_28_rigid : Rigid (Cells pattern_28.1) (Cells pattern_28.2) :=
  subsetPairCheck_sound pattern_28_check

def pattern_29 : Pattern := ([(0,0),(0,1),(1,0)],[(2,0),(3,0),(4,0)])
theorem pattern_29_check : SubsetPairCheck pattern_29.1 pattern_29.2 := by decide +kernel
theorem pattern_29_rigid : Rigid (Cells pattern_29.1) (Cells pattern_29.2) :=
  subsetPairCheck_sound pattern_29_check

def pattern_30 : Pattern := ([(0,0),(0,1),(1,1)],[(0,2),(0,3),(0,4)])
theorem pattern_30_check : SubsetPairCheck pattern_30.1 pattern_30.2 := by decide +kernel
theorem pattern_30_rigid : Rigid (Cells pattern_30.1) (Cells pattern_30.2) :=
  subsetPairCheck_sound pattern_30_check

def pattern_31 : Pattern := ([(0,0),(0,1),(1,1)],[(0,2),(0,3),(1,2)])
theorem pattern_31_check : SubsetPairCheck pattern_31.1 pattern_31.2 := by decide +kernel
theorem pattern_31_rigid : Rigid (Cells pattern_31.1) (Cells pattern_31.2) :=
  subsetPairCheck_sound pattern_31_check

def pattern_32 : Pattern := ([(0,0),(0,1),(1,1)],[(0,2),(0,3),(1,3)])
theorem pattern_32_check : SubsetPairCheck pattern_32.1 pattern_32.2 := by decide +kernel
theorem pattern_32_rigid : Rigid (Cells pattern_32.1) (Cells pattern_32.2) :=
  subsetPairCheck_sound pattern_32_check

def pattern_33 : Pattern := ([(0,0),(0,1),(1,1)],[(0,3),(1,2),(1,3)])
theorem pattern_33_check : SubsetPairCheck pattern_33.1 pattern_33.2 := by decide +kernel
theorem pattern_33_rigid : Rigid (Cells pattern_33.1) (Cells pattern_33.2) :=
  subsetPairCheck_sound pattern_33_check

def pattern_34 : Pattern := ([(0,0),(0,1),(1,1)],[(1,0),(2,0),(3,0)])
theorem pattern_34_check : SubsetPairCheck pattern_34.1 pattern_34.2 := by decide +kernel
theorem pattern_34_rigid : Rigid (Cells pattern_34.1) (Cells pattern_34.2) :=
  subsetPairCheck_sound pattern_34_check

def pattern_35 : Pattern := ([(0,0),(0,1),(1,1)],[(1,2),(1,3),(1,4)])
theorem pattern_35_check : SubsetPairCheck pattern_35.1 pattern_35.2 := by decide +kernel
theorem pattern_35_rigid : Rigid (Cells pattern_35.1) (Cells pattern_35.2) :=
  subsetPairCheck_sound pattern_35_check

def pattern_36 : Pattern := ([(0,0),(0,1),(1,1)],[(1,2),(1,3),(2,2)])
theorem pattern_36_check : SubsetPairCheck pattern_36.1 pattern_36.2 := by decide +kernel
theorem pattern_36_rigid : Rigid (Cells pattern_36.1) (Cells pattern_36.2) :=
  subsetPairCheck_sound pattern_36_check

def pattern_37 : Pattern := ([(0,0),(0,1),(1,1)],[(1,2),(1,3),(2,3)])
theorem pattern_37_check : SubsetPairCheck pattern_37.1 pattern_37.2 := by decide +kernel
theorem pattern_37_rigid : Rigid (Cells pattern_37.1) (Cells pattern_37.2) :=
  subsetPairCheck_sound pattern_37_check

def pattern_38 : Pattern := ([(0,0),(0,1),(1,1)],[(1,2),(2,1),(2,2)])
theorem pattern_38_check : SubsetPairCheck pattern_38.1 pattern_38.2 := by decide +kernel
theorem pattern_38_rigid : Rigid (Cells pattern_38.1) (Cells pattern_38.2) :=
  subsetPairCheck_sound pattern_38_check

def pattern_39 : Pattern := ([(0,0),(0,1),(1,1)],[(1,2),(2,2),(2,3)])
theorem pattern_39_check : SubsetPairCheck pattern_39.1 pattern_39.2 := by decide +kernel
theorem pattern_39_rigid : Rigid (Cells pattern_39.1) (Cells pattern_39.2) :=
  subsetPairCheck_sound pattern_39_check

def pattern_40 : Pattern := ([(0,0),(0,1),(1,1)],[(1,2),(2,2),(3,2)])
theorem pattern_40_check : SubsetPairCheck pattern_40.1 pattern_40.2 := by decide +kernel
theorem pattern_40_rigid : Rigid (Cells pattern_40.1) (Cells pattern_40.2) :=
  subsetPairCheck_sound pattern_40_check

def pattern_41 : Pattern := ([(0,0),(0,1),(1,1)],[(2,0),(2,1),(2,2)])
theorem pattern_41_check : SubsetPairCheck pattern_41.1 pattern_41.2 := by decide +kernel
theorem pattern_41_rigid : Rigid (Cells pattern_41.1) (Cells pattern_41.2) :=
  subsetPairCheck_sound pattern_41_check

def pattern_42 : Pattern := ([(0,0),(0,1),(1,1)],[(2,0),(2,1),(3,0)])
theorem pattern_42_check : SubsetPairCheck pattern_42.1 pattern_42.2 := by decide +kernel
theorem pattern_42_rigid : Rigid (Cells pattern_42.1) (Cells pattern_42.2) :=
  subsetPairCheck_sound pattern_42_check

def pattern_43 : Pattern := ([(0,0),(0,1),(1,1)],[(2,0),(2,1),(3,1)])
theorem pattern_43_check : SubsetPairCheck pattern_43.1 pattern_43.2 := by decide +kernel
theorem pattern_43_rigid : Rigid (Cells pattern_43.1) (Cells pattern_43.2) :=
  subsetPairCheck_sound pattern_43_check

def pattern_44 : Pattern := ([(0,0),(0,1),(1,1)],[(2,1),(2,2),(2,3)])
theorem pattern_44_check : SubsetPairCheck pattern_44.1 pattern_44.2 := by decide +kernel
theorem pattern_44_rigid : Rigid (Cells pattern_44.1) (Cells pattern_44.2) :=
  subsetPairCheck_sound pattern_44_check

def pattern_45 : Pattern := ([(0,0),(0,1),(1,1)],[(2,1),(2,2),(3,1)])
theorem pattern_45_check : SubsetPairCheck pattern_45.1 pattern_45.2 := by decide +kernel
theorem pattern_45_rigid : Rigid (Cells pattern_45.1) (Cells pattern_45.2) :=
  subsetPairCheck_sound pattern_45_check

def pattern_46 : Pattern := ([(0,0),(0,1),(1,1)],[(2,1),(2,2),(3,2)])
theorem pattern_46_check : SubsetPairCheck pattern_46.1 pattern_46.2 := by decide +kernel
theorem pattern_46_rigid : Rigid (Cells pattern_46.1) (Cells pattern_46.2) :=
  subsetPairCheck_sound pattern_46_check

def pattern_47 : Pattern := ([(0,0),(0,1),(1,1)],[(2,1),(3,0),(3,1)])
theorem pattern_47_check : SubsetPairCheck pattern_47.1 pattern_47.2 := by decide +kernel
theorem pattern_47_rigid : Rigid (Cells pattern_47.1) (Cells pattern_47.2) :=
  subsetPairCheck_sound pattern_47_check

def pattern_48 : Pattern := ([(0,0),(0,1),(1,1)],[(2,1),(3,1),(3,2)])
theorem pattern_48_check : SubsetPairCheck pattern_48.1 pattern_48.2 := by decide +kernel
theorem pattern_48_rigid : Rigid (Cells pattern_48.1) (Cells pattern_48.2) :=
  subsetPairCheck_sound pattern_48_check

def pattern_49 : Pattern := ([(0,0),(0,1),(1,1)],[(2,1),(3,1),(4,1)])
theorem pattern_49_check : SubsetPairCheck pattern_49.1 pattern_49.2 := by decide +kernel
theorem pattern_49_rigid : Rigid (Cells pattern_49.1) (Cells pattern_49.2) :=
  subsetPairCheck_sound pattern_49_check

def pattern_50 : Pattern := ([(0,0),(1,0),(1,1)],[(0,1),(0,2),(0,3)])
theorem pattern_50_check : SubsetPairCheck pattern_50.1 pattern_50.2 := by decide +kernel
theorem pattern_50_rigid : Rigid (Cells pattern_50.1) (Cells pattern_50.2) :=
  subsetPairCheck_sound pattern_50_check

def pattern_51 : Pattern := ([(0,0),(1,0),(1,1)],[(0,2),(0,3),(1,2)])
theorem pattern_51_check : SubsetPairCheck pattern_51.1 pattern_51.2 := by decide +kernel
theorem pattern_51_rigid : Rigid (Cells pattern_51.1) (Cells pattern_51.2) :=
  subsetPairCheck_sound pattern_51_check

def pattern_52 : Pattern := ([(0,0),(1,0),(1,1)],[(0,2),(1,2),(1,3)])
theorem pattern_52_check : SubsetPairCheck pattern_52.1 pattern_52.2 := by decide +kernel
theorem pattern_52_rigid : Rigid (Cells pattern_52.1) (Cells pattern_52.2) :=
  subsetPairCheck_sound pattern_52_check

def pattern_53 : Pattern := ([(0,0),(1,0),(1,1)],[(0,2),(1,2),(2,2)])
theorem pattern_53_check : SubsetPairCheck pattern_53.1 pattern_53.2 := by decide +kernel
theorem pattern_53_rigid : Rigid (Cells pattern_53.1) (Cells pattern_53.2) :=
  subsetPairCheck_sound pattern_53_check

def pattern_54 : Pattern := ([(0,0),(1,0),(1,1)],[(0,3),(1,2),(1,3)])
theorem pattern_54_check : SubsetPairCheck pattern_54.1 pattern_54.2 := by decide +kernel
theorem pattern_54_rigid : Rigid (Cells pattern_54.1) (Cells pattern_54.2) :=
  subsetPairCheck_sound pattern_54_check

def pattern_55 : Pattern := ([(0,0),(1,0),(1,1)],[(1,2),(1,3),(1,4)])
theorem pattern_55_check : SubsetPairCheck pattern_55.1 pattern_55.2 := by decide +kernel
theorem pattern_55_rigid : Rigid (Cells pattern_55.1) (Cells pattern_55.2) :=
  subsetPairCheck_sound pattern_55_check

def pattern_56 : Pattern := ([(0,0),(1,0),(1,1)],[(1,2),(1,3),(2,2)])
theorem pattern_56_check : SubsetPairCheck pattern_56.1 pattern_56.2 := by decide +kernel
theorem pattern_56_rigid : Rigid (Cells pattern_56.1) (Cells pattern_56.2) :=
  subsetPairCheck_sound pattern_56_check

def pattern_57 : Pattern := ([(0,0),(1,0),(1,1)],[(1,2),(1,3),(2,3)])
theorem pattern_57_check : SubsetPairCheck pattern_57.1 pattern_57.2 := by decide +kernel
theorem pattern_57_rigid : Rigid (Cells pattern_57.1) (Cells pattern_57.2) :=
  subsetPairCheck_sound pattern_57_check

def pattern_58 : Pattern := ([(0,0),(1,0),(1,1)],[(1,2),(2,1),(2,2)])
theorem pattern_58_check : SubsetPairCheck pattern_58.1 pattern_58.2 := by decide +kernel
theorem pattern_58_rigid : Rigid (Cells pattern_58.1) (Cells pattern_58.2) :=
  subsetPairCheck_sound pattern_58_check

def pattern_59 : Pattern := ([(0,0),(1,0),(1,1)],[(1,2),(2,2),(2,3)])
theorem pattern_59_check : SubsetPairCheck pattern_59.1 pattern_59.2 := by decide +kernel
theorem pattern_59_rigid : Rigid (Cells pattern_59.1) (Cells pattern_59.2) :=
  subsetPairCheck_sound pattern_59_check

def pattern_60 : Pattern := ([(0,0),(1,0),(1,1)],[(1,2),(2,2),(3,2)])
theorem pattern_60_check : SubsetPairCheck pattern_60.1 pattern_60.2 := by decide +kernel
theorem pattern_60_rigid : Rigid (Cells pattern_60.1) (Cells pattern_60.2) :=
  subsetPairCheck_sound pattern_60_check

def pattern_61 : Pattern := ([(0,0),(1,0),(1,1)],[(2,0),(2,1),(3,0)])
theorem pattern_61_check : SubsetPairCheck pattern_61.1 pattern_61.2 := by decide +kernel
theorem pattern_61_rigid : Rigid (Cells pattern_61.1) (Cells pattern_61.2) :=
  subsetPairCheck_sound pattern_61_check

def pattern_62 : Pattern := ([(0,0),(1,0),(1,1)],[(2,0),(3,0),(3,1)])
theorem pattern_62_check : SubsetPairCheck pattern_62.1 pattern_62.2 := by decide +kernel
theorem pattern_62_rigid : Rigid (Cells pattern_62.1) (Cells pattern_62.2) :=
  subsetPairCheck_sound pattern_62_check

def pattern_63 : Pattern := ([(0,0),(1,0),(1,1)],[(2,0),(3,0),(4,0)])
theorem pattern_63_check : SubsetPairCheck pattern_63.1 pattern_63.2 := by decide +kernel
theorem pattern_63_rigid : Rigid (Cells pattern_63.1) (Cells pattern_63.2) :=
  subsetPairCheck_sound pattern_63_check

def pattern_64 : Pattern := ([(0,0),(1,0),(1,1)],[(2,1),(2,2),(2,3)])
theorem pattern_64_check : SubsetPairCheck pattern_64.1 pattern_64.2 := by decide +kernel
theorem pattern_64_rigid : Rigid (Cells pattern_64.1) (Cells pattern_64.2) :=
  subsetPairCheck_sound pattern_64_check

def pattern_65 : Pattern := ([(0,0),(1,0),(1,1)],[(2,1),(2,2),(3,1)])
theorem pattern_65_check : SubsetPairCheck pattern_65.1 pattern_65.2 := by decide +kernel
theorem pattern_65_rigid : Rigid (Cells pattern_65.1) (Cells pattern_65.2) :=
  subsetPairCheck_sound pattern_65_check

def pattern_66 : Pattern := ([(0,0),(1,0),(1,1)],[(2,1),(2,2),(3,2)])
theorem pattern_66_check : SubsetPairCheck pattern_66.1 pattern_66.2 := by decide +kernel
theorem pattern_66_rigid : Rigid (Cells pattern_66.1) (Cells pattern_66.2) :=
  subsetPairCheck_sound pattern_66_check

def pattern_67 : Pattern := ([(0,0),(1,0),(1,1)],[(2,1),(3,0),(3,1)])
theorem pattern_67_check : SubsetPairCheck pattern_67.1 pattern_67.2 := by decide +kernel
theorem pattern_67_rigid : Rigid (Cells pattern_67.1) (Cells pattern_67.2) :=
  subsetPairCheck_sound pattern_67_check

def pattern_68 : Pattern := ([(0,0),(1,0),(1,1)],[(2,1),(3,1),(3,2)])
theorem pattern_68_check : SubsetPairCheck pattern_68.1 pattern_68.2 := by decide +kernel
theorem pattern_68_rigid : Rigid (Cells pattern_68.1) (Cells pattern_68.2) :=
  subsetPairCheck_sound pattern_68_check

def pattern_69 : Pattern := ([(0,0),(1,0),(1,1)],[(2,1),(3,1),(4,1)])
theorem pattern_69_check : SubsetPairCheck pattern_69.1 pattern_69.2 := by decide +kernel
theorem pattern_69_rigid : Rigid (Cells pattern_69.1) (Cells pattern_69.2) :=
  subsetPairCheck_sound pattern_69_check

def pattern_70 : Pattern := ([(0,0),(1,0),(2,0)],[(0,1),(0,2),(0,3)])
theorem pattern_70_check : SubsetPairCheck pattern_70.1 pattern_70.2 := by decide +kernel
theorem pattern_70_rigid : Rigid (Cells pattern_70.1) (Cells pattern_70.2) :=
  subsetPairCheck_sound pattern_70_check

def pattern_71 : Pattern := ([(0,0),(1,0),(2,0)],[(0,1),(1,1),(1,2)])
theorem pattern_71_check : SubsetPairCheck pattern_71.1 pattern_71.2 := by decide +kernel
theorem pattern_71_rigid : Rigid (Cells pattern_71.1) (Cells pattern_71.2) :=
  subsetPairCheck_sound pattern_71_check

def pattern_72 : Pattern := ([(0,0),(1,0),(2,0)],[(0,2),(1,1),(1,2)])
theorem pattern_72_check : SubsetPairCheck pattern_72.1 pattern_72.2 := by decide +kernel
theorem pattern_72_rigid : Rigid (Cells pattern_72.1) (Cells pattern_72.2) :=
  subsetPairCheck_sound pattern_72_check

def pattern_73 : Pattern := ([(0,0),(1,0),(2,0)],[(1,1),(1,2),(1,3)])
theorem pattern_73_check : SubsetPairCheck pattern_73.1 pattern_73.2 := by decide +kernel
theorem pattern_73_rigid : Rigid (Cells pattern_73.1) (Cells pattern_73.2) :=
  subsetPairCheck_sound pattern_73_check

def pattern_74 : Pattern := ([(0,0),(1,0),(2,0)],[(1,1),(1,2),(2,1)])
theorem pattern_74_check : SubsetPairCheck pattern_74.1 pattern_74.2 := by decide +kernel
theorem pattern_74_rigid : Rigid (Cells pattern_74.1) (Cells pattern_74.2) :=
  subsetPairCheck_sound pattern_74_check

def pattern_75 : Pattern := ([(0,0),(1,0),(2,0)],[(1,1),(1,2),(2,2)])
theorem pattern_75_check : SubsetPairCheck pattern_75.1 pattern_75.2 := by decide +kernel
theorem pattern_75_rigid : Rigid (Cells pattern_75.1) (Cells pattern_75.2) :=
  subsetPairCheck_sound pattern_75_check

def pattern_76 : Pattern := ([(0,0),(1,0),(2,0)],[(2,1),(2,2),(2,3)])
theorem pattern_76_check : SubsetPairCheck pattern_76.1 pattern_76.2 := by decide +kernel
theorem pattern_76_rigid : Rigid (Cells pattern_76.1) (Cells pattern_76.2) :=
  subsetPairCheck_sound pattern_76_check

def pattern_77 : Pattern := ([(0,0),(1,0),(2,0)],[(2,1),(2,2),(3,1)])
theorem pattern_77_check : SubsetPairCheck pattern_77.1 pattern_77.2 := by decide +kernel
theorem pattern_77_rigid : Rigid (Cells pattern_77.1) (Cells pattern_77.2) :=
  subsetPairCheck_sound pattern_77_check

def pattern_78 : Pattern := ([(0,0),(1,0),(2,0)],[(2,1),(2,2),(3,2)])
theorem pattern_78_check : SubsetPairCheck pattern_78.1 pattern_78.2 := by decide +kernel
theorem pattern_78_rigid : Rigid (Cells pattern_78.1) (Cells pattern_78.2) :=
  subsetPairCheck_sound pattern_78_check

def pattern_79 : Pattern := ([(0,0),(1,0),(2,0)],[(2,1),(3,0),(3,1)])
theorem pattern_79_check : SubsetPairCheck pattern_79.1 pattern_79.2 := by decide +kernel
theorem pattern_79_rigid : Rigid (Cells pattern_79.1) (Cells pattern_79.2) :=
  subsetPairCheck_sound pattern_79_check

def pattern_80 : Pattern := ([(0,0),(1,0),(2,0)],[(2,1),(3,1),(3,2)])
theorem pattern_80_check : SubsetPairCheck pattern_80.1 pattern_80.2 := by decide +kernel
theorem pattern_80_rigid : Rigid (Cells pattern_80.1) (Cells pattern_80.2) :=
  subsetPairCheck_sound pattern_80_check

def pattern_81 : Pattern := ([(0,0),(1,0),(2,0)],[(2,1),(3,1),(4,1)])
theorem pattern_81_check : SubsetPairCheck pattern_81.1 pattern_81.2 := by decide +kernel
theorem pattern_81_rigid : Rigid (Cells pattern_81.1) (Cells pattern_81.2) :=
  subsetPairCheck_sound pattern_81_check

def pattern_82 : Pattern := ([(0,0),(1,0),(2,0)],[(3,0),(3,1),(3,2)])
theorem pattern_82_check : SubsetPairCheck pattern_82.1 pattern_82.2 := by decide +kernel
theorem pattern_82_rigid : Rigid (Cells pattern_82.1) (Cells pattern_82.2) :=
  subsetPairCheck_sound pattern_82_check

def pattern_83 : Pattern := ([(0,0),(1,0),(2,0)],[(3,0),(3,1),(4,0)])
theorem pattern_83_check : SubsetPairCheck pattern_83.1 pattern_83.2 := by decide +kernel
theorem pattern_83_rigid : Rigid (Cells pattern_83.1) (Cells pattern_83.2) :=
  subsetPairCheck_sound pattern_83_check

def pattern_84 : Pattern := ([(0,0),(1,0),(2,0)],[(3,0),(3,1),(4,1)])
theorem pattern_84_check : SubsetPairCheck pattern_84.1 pattern_84.2 := by decide +kernel
theorem pattern_84_rigid : Rigid (Cells pattern_84.1) (Cells pattern_84.2) :=
  subsetPairCheck_sound pattern_84_check

def pattern_85 : Pattern := ([(0,0),(1,0),(2,0)],[(3,0),(4,0),(4,1)])
theorem pattern_85_check : SubsetPairCheck pattern_85.1 pattern_85.2 := by decide +kernel
theorem pattern_85_rigid : Rigid (Cells pattern_85.1) (Cells pattern_85.2) :=
  subsetPairCheck_sound pattern_85_check

def pattern_86 : Pattern := ([(0,0),(1,0),(2,0)],[(3,0),(4,0),(5,0)])
theorem pattern_86_check : SubsetPairCheck pattern_86.1 pattern_86.2 := by decide +kernel
theorem pattern_86_rigid : Rigid (Cells pattern_86.1) (Cells pattern_86.2) :=
  subsetPairCheck_sound pattern_86_check

def pattern_87 : Pattern := ([(0,1),(0,2),(0,3)],[(1,0),(1,1),(2,0)])
theorem pattern_87_check : SubsetPairCheck pattern_87.1 pattern_87.2 := by decide +kernel
theorem pattern_87_rigid : Rigid (Cells pattern_87.1) (Cells pattern_87.2) :=
  subsetPairCheck_sound pattern_87_check

def pattern_88 : Pattern := ([(0,1),(0,2),(0,3)],[(1,0),(1,1),(2,1)])
theorem pattern_88_check : SubsetPairCheck pattern_88.1 pattern_88.2 := by decide +kernel
theorem pattern_88_rigid : Rigid (Cells pattern_88.1) (Cells pattern_88.2) :=
  subsetPairCheck_sound pattern_88_check

def pattern_89 : Pattern := ([(0,1),(0,2),(0,3)],[(1,1),(2,0),(2,1)])
theorem pattern_89_check : SubsetPairCheck pattern_89.1 pattern_89.2 := by decide +kernel
theorem pattern_89_rigid : Rigid (Cells pattern_89.1) (Cells pattern_89.2) :=
  subsetPairCheck_sound pattern_89_check

def pattern_90 : Pattern := ([(0,1),(0,2),(1,1)],[(1,0),(2,0),(2,1)])
theorem pattern_90_check : SubsetPairCheck pattern_90.1 pattern_90.2 := by decide +kernel
theorem pattern_90_rigid : Rigid (Cells pattern_90.1) (Cells pattern_90.2) :=
  subsetPairCheck_sound pattern_90_check

def pattern_91 : Pattern := ([(0,1),(0,2),(1,1)],[(1,0),(2,0),(3,0)])
theorem pattern_91_check : SubsetPairCheck pattern_91.1 pattern_91.2 := by decide +kernel
theorem pattern_91_rigid : Rigid (Cells pattern_91.1) (Cells pattern_91.2) :=
  subsetPairCheck_sound pattern_91_check

def pattern_92 : Pattern := ([(0,1),(0,2),(1,1)],[(2,0),(2,1),(2,2)])
theorem pattern_92_check : SubsetPairCheck pattern_92.1 pattern_92.2 := by decide +kernel
theorem pattern_92_rigid : Rigid (Cells pattern_92.1) (Cells pattern_92.2) :=
  subsetPairCheck_sound pattern_92_check

def pattern_93 : Pattern := ([(0,1),(0,2),(1,1)],[(2,0),(2,1),(3,0)])
theorem pattern_93_check : SubsetPairCheck pattern_93.1 pattern_93.2 := by decide +kernel
theorem pattern_93_rigid : Rigid (Cells pattern_93.1) (Cells pattern_93.2) :=
  subsetPairCheck_sound pattern_93_check

def pattern_94 : Pattern := ([(0,1),(0,2),(1,1)],[(2,0),(2,1),(3,1)])
theorem pattern_94_check : SubsetPairCheck pattern_94.1 pattern_94.2 := by decide +kernel
theorem pattern_94_rigid : Rigid (Cells pattern_94.1) (Cells pattern_94.2) :=
  subsetPairCheck_sound pattern_94_check

def pattern_95 : Pattern := ([(0,1),(0,2),(1,1)],[(2,1),(3,0),(3,1)])
theorem pattern_95_check : SubsetPairCheck pattern_95.1 pattern_95.2 := by decide +kernel
theorem pattern_95_rigid : Rigid (Cells pattern_95.1) (Cells pattern_95.2) :=
  subsetPairCheck_sound pattern_95_check

def pattern_96 : Pattern := ([(0,1),(0,2),(1,2)],[(1,0),(1,1),(2,0)])
theorem pattern_96_check : SubsetPairCheck pattern_96.1 pattern_96.2 := by decide +kernel
theorem pattern_96_rigid : Rigid (Cells pattern_96.1) (Cells pattern_96.2) :=
  subsetPairCheck_sound pattern_96_check

def pattern_97 : Pattern := ([(0,1),(0,2),(1,2)],[(1,0),(1,1),(2,1)])
theorem pattern_97_check : SubsetPairCheck pattern_97.1 pattern_97.2 := by decide +kernel
theorem pattern_97_rigid : Rigid (Cells pattern_97.1) (Cells pattern_97.2) :=
  subsetPairCheck_sound pattern_97_check

def pattern_98 : Pattern := ([(0,1),(0,2),(1,2)],[(1,1),(2,0),(2,1)])
theorem pattern_98_check : SubsetPairCheck pattern_98.1 pattern_98.2 := by decide +kernel
theorem pattern_98_rigid : Rigid (Cells pattern_98.1) (Cells pattern_98.2) :=
  subsetPairCheck_sound pattern_98_check

def pattern_99 : Pattern := ([(0,1),(1,0),(1,1)],[(0,2),(0,3),(0,4)])
theorem pattern_99_check : SubsetPairCheck pattern_99.1 pattern_99.2 := by decide +kernel
theorem pattern_99_rigid : Rigid (Cells pattern_99.1) (Cells pattern_99.2) :=
  subsetPairCheck_sound pattern_99_check

def pattern_100 : Pattern := ([(0,1),(1,0),(1,1)],[(0,2),(0,3),(1,3)])
theorem pattern_100_check : SubsetPairCheck pattern_100.1 pattern_100.2 := by decide +kernel
theorem pattern_100_rigid : Rigid (Cells pattern_100.1) (Cells pattern_100.2) :=
  subsetPairCheck_sound pattern_100_check

def pattern_101 : Pattern := ([(0,1),(1,0),(1,1)],[(0,2),(1,2),(1,3)])
theorem pattern_101_check : SubsetPairCheck pattern_101.1 pattern_101.2 := by decide +kernel
theorem pattern_101_rigid : Rigid (Cells pattern_101.1) (Cells pattern_101.2) :=
  subsetPairCheck_sound pattern_101_check

def pattern_102 : Pattern := ([(0,1),(1,0),(1,1)],[(0,2),(1,2),(2,2)])
theorem pattern_102_check : SubsetPairCheck pattern_102.1 pattern_102.2 := by decide +kernel
theorem pattern_102_rigid : Rigid (Cells pattern_102.1) (Cells pattern_102.2) :=
  subsetPairCheck_sound pattern_102_check

def pattern_103 : Pattern := ([(0,1),(1,0),(1,1)],[(0,3),(1,2),(1,3)])
theorem pattern_103_check : SubsetPairCheck pattern_103.1 pattern_103.2 := by decide +kernel
theorem pattern_103_rigid : Rigid (Cells pattern_103.1) (Cells pattern_103.2) :=
  subsetPairCheck_sound pattern_103_check

def pattern_104 : Pattern := ([(0,1),(1,0),(1,1)],[(1,2),(1,3),(1,4)])
theorem pattern_104_check : SubsetPairCheck pattern_104.1 pattern_104.2 := by decide +kernel
theorem pattern_104_rigid : Rigid (Cells pattern_104.1) (Cells pattern_104.2) :=
  subsetPairCheck_sound pattern_104_check

def pattern_105 : Pattern := ([(0,1),(1,0),(1,1)],[(1,2),(1,3),(2,2)])
theorem pattern_105_check : SubsetPairCheck pattern_105.1 pattern_105.2 := by decide +kernel
theorem pattern_105_rigid : Rigid (Cells pattern_105.1) (Cells pattern_105.2) :=
  subsetPairCheck_sound pattern_105_check

def pattern_106 : Pattern := ([(0,1),(1,0),(1,1)],[(1,2),(1,3),(2,3)])
theorem pattern_106_check : SubsetPairCheck pattern_106.1 pattern_106.2 := by decide +kernel
theorem pattern_106_rigid : Rigid (Cells pattern_106.1) (Cells pattern_106.2) :=
  subsetPairCheck_sound pattern_106_check

def pattern_107 : Pattern := ([(0,1),(1,0),(1,1)],[(1,2),(2,1),(2,2)])
theorem pattern_107_check : SubsetPairCheck pattern_107.1 pattern_107.2 := by decide +kernel
theorem pattern_107_rigid : Rigid (Cells pattern_107.1) (Cells pattern_107.2) :=
  subsetPairCheck_sound pattern_107_check

def pattern_108 : Pattern := ([(0,1),(1,0),(1,1)],[(1,2),(2,2),(2,3)])
theorem pattern_108_check : SubsetPairCheck pattern_108.1 pattern_108.2 := by decide +kernel
theorem pattern_108_rigid : Rigid (Cells pattern_108.1) (Cells pattern_108.2) :=
  subsetPairCheck_sound pattern_108_check

def pattern_109 : Pattern := ([(0,1),(1,0),(1,1)],[(1,2),(2,2),(3,2)])
theorem pattern_109_check : SubsetPairCheck pattern_109.1 pattern_109.2 := by decide +kernel
theorem pattern_109_rigid : Rigid (Cells pattern_109.1) (Cells pattern_109.2) :=
  subsetPairCheck_sound pattern_109_check

def pattern_110 : Pattern := ([(0,1),(1,0),(1,1)],[(2,0),(2,1),(2,2)])
theorem pattern_110_check : SubsetPairCheck pattern_110.1 pattern_110.2 := by decide +kernel
theorem pattern_110_rigid : Rigid (Cells pattern_110.1) (Cells pattern_110.2) :=
  subsetPairCheck_sound pattern_110_check

def pattern_111 : Pattern := ([(0,1),(1,0),(1,1)],[(2,0),(2,1),(3,1)])
theorem pattern_111_check : SubsetPairCheck pattern_111.1 pattern_111.2 := by decide +kernel
theorem pattern_111_rigid : Rigid (Cells pattern_111.1) (Cells pattern_111.2) :=
  subsetPairCheck_sound pattern_111_check

def pattern_112 : Pattern := ([(0,1),(1,0),(1,1)],[(2,0),(3,0),(3,1)])
theorem pattern_112_check : SubsetPairCheck pattern_112.1 pattern_112.2 := by decide +kernel
theorem pattern_112_rigid : Rigid (Cells pattern_112.1) (Cells pattern_112.2) :=
  subsetPairCheck_sound pattern_112_check

def pattern_113 : Pattern := ([(0,1),(1,0),(1,1)],[(2,0),(3,0),(4,0)])
theorem pattern_113_check : SubsetPairCheck pattern_113.1 pattern_113.2 := by decide +kernel
theorem pattern_113_rigid : Rigid (Cells pattern_113.1) (Cells pattern_113.2) :=
  subsetPairCheck_sound pattern_113_check

def pattern_114 : Pattern := ([(0,1),(1,0),(1,1)],[(2,1),(2,2),(2,3)])
theorem pattern_114_check : SubsetPairCheck pattern_114.1 pattern_114.2 := by decide +kernel
theorem pattern_114_rigid : Rigid (Cells pattern_114.1) (Cells pattern_114.2) :=
  subsetPairCheck_sound pattern_114_check

def pattern_115 : Pattern := ([(0,1),(1,0),(1,1)],[(2,1),(2,2),(3,1)])
theorem pattern_115_check : SubsetPairCheck pattern_115.1 pattern_115.2 := by decide +kernel
theorem pattern_115_rigid : Rigid (Cells pattern_115.1) (Cells pattern_115.2) :=
  subsetPairCheck_sound pattern_115_check

def pattern_116 : Pattern := ([(0,1),(1,0),(1,1)],[(2,1),(2,2),(3,2)])
theorem pattern_116_check : SubsetPairCheck pattern_116.1 pattern_116.2 := by decide +kernel
theorem pattern_116_rigid : Rigid (Cells pattern_116.1) (Cells pattern_116.2) :=
  subsetPairCheck_sound pattern_116_check

def pattern_117 : Pattern := ([(0,1),(1,0),(1,1)],[(2,1),(3,0),(3,1)])
theorem pattern_117_check : SubsetPairCheck pattern_117.1 pattern_117.2 := by decide +kernel
theorem pattern_117_rigid : Rigid (Cells pattern_117.1) (Cells pattern_117.2) :=
  subsetPairCheck_sound pattern_117_check

def pattern_118 : Pattern := ([(0,1),(1,0),(1,1)],[(2,1),(3,1),(3,2)])
theorem pattern_118_check : SubsetPairCheck pattern_118.1 pattern_118.2 := by decide +kernel
theorem pattern_118_rigid : Rigid (Cells pattern_118.1) (Cells pattern_118.2) :=
  subsetPairCheck_sound pattern_118_check

def pattern_119 : Pattern := ([(0,1),(1,0),(1,1)],[(2,1),(3,1),(4,1)])
theorem pattern_119_check : SubsetPairCheck pattern_119.1 pattern_119.2 := by decide +kernel
theorem pattern_119_rigid : Rigid (Cells pattern_119.1) (Cells pattern_119.2) :=
  subsetPairCheck_sound pattern_119_check

def pattern_120 : Pattern := ([(0,1),(1,1),(1,2)],[(1,0),(2,0),(2,1)])
theorem pattern_120_check : SubsetPairCheck pattern_120.1 pattern_120.2 := by decide +kernel
theorem pattern_120_rigid : Rigid (Cells pattern_120.1) (Cells pattern_120.2) :=
  subsetPairCheck_sound pattern_120_check

def pattern_121 : Pattern := ([(0,1),(1,1),(1,2)],[(1,0),(2,0),(3,0)])
theorem pattern_121_check : SubsetPairCheck pattern_121.1 pattern_121.2 := by decide +kernel
theorem pattern_121_rigid : Rigid (Cells pattern_121.1) (Cells pattern_121.2) :=
  subsetPairCheck_sound pattern_121_check

def pattern_122 : Pattern := ([(0,1),(1,1),(1,2)],[(2,0),(2,1),(2,2)])
theorem pattern_122_check : SubsetPairCheck pattern_122.1 pattern_122.2 := by decide +kernel
theorem pattern_122_rigid : Rigid (Cells pattern_122.1) (Cells pattern_122.2) :=
  subsetPairCheck_sound pattern_122_check

def pattern_123 : Pattern := ([(0,1),(1,1),(1,2)],[(2,0),(2,1),(3,0)])
theorem pattern_123_check : SubsetPairCheck pattern_123.1 pattern_123.2 := by decide +kernel
theorem pattern_123_rigid : Rigid (Cells pattern_123.1) (Cells pattern_123.2) :=
  subsetPairCheck_sound pattern_123_check

def pattern_124 : Pattern := ([(0,1),(1,1),(1,2)],[(2,0),(2,1),(3,1)])
theorem pattern_124_check : SubsetPairCheck pattern_124.1 pattern_124.2 := by decide +kernel
theorem pattern_124_rigid : Rigid (Cells pattern_124.1) (Cells pattern_124.2) :=
  subsetPairCheck_sound pattern_124_check

def pattern_125 : Pattern := ([(0,1),(1,1),(1,2)],[(2,1),(3,0),(3,1)])
theorem pattern_125_check : SubsetPairCheck pattern_125.1 pattern_125.2 := by decide +kernel
theorem pattern_125_rigid : Rigid (Cells pattern_125.1) (Cells pattern_125.2) :=
  subsetPairCheck_sound pattern_125_check

def pattern_126 : Pattern := ([(0,1),(1,1),(2,1)],[(2,0),(3,0),(3,1)])
theorem pattern_126_check : SubsetPairCheck pattern_126.1 pattern_126.2 := by decide +kernel
theorem pattern_126_rigid : Rigid (Cells pattern_126.1) (Cells pattern_126.2) :=
  subsetPairCheck_sound pattern_126_check

def pattern_127 : Pattern := ([(0,1),(1,1),(2,1)],[(2,0),(3,0),(4,0)])
theorem pattern_127_check : SubsetPairCheck pattern_127.1 pattern_127.2 := by decide +kernel
theorem pattern_127_rigid : Rigid (Cells pattern_127.1) (Cells pattern_127.2) :=
  subsetPairCheck_sound pattern_127_check

def pattern_128 : Pattern := ([(0,1),(1,1),(2,1)],[(3,0),(3,1),(3,2)])
theorem pattern_128_check : SubsetPairCheck pattern_128.1 pattern_128.2 := by decide +kernel
theorem pattern_128_rigid : Rigid (Cells pattern_128.1) (Cells pattern_128.2) :=
  subsetPairCheck_sound pattern_128_check

def pattern_129 : Pattern := ([(0,1),(1,1),(2,1)],[(3,0),(3,1),(4,0)])
theorem pattern_129_check : SubsetPairCheck pattern_129.1 pattern_129.2 := by decide +kernel
theorem pattern_129_rigid : Rigid (Cells pattern_129.1) (Cells pattern_129.2) :=
  subsetPairCheck_sound pattern_129_check

def pattern_130 : Pattern := ([(0,1),(1,1),(2,1)],[(3,0),(3,1),(4,1)])
theorem pattern_130_check : SubsetPairCheck pattern_130.1 pattern_130.2 := by decide +kernel
theorem pattern_130_rigid : Rigid (Cells pattern_130.1) (Cells pattern_130.2) :=
  subsetPairCheck_sound pattern_130_check

def pattern_131 : Pattern := ([(0,1),(1,1),(2,1)],[(3,1),(4,0),(4,1)])
theorem pattern_131_check : SubsetPairCheck pattern_131.1 pattern_131.2 := by decide +kernel
theorem pattern_131_rigid : Rigid (Cells pattern_131.1) (Cells pattern_131.2) :=
  subsetPairCheck_sound pattern_131_check

def pattern_132 : Pattern := ([(0,2),(0,3),(0,4)],[(1,0),(1,1),(1,2)])
theorem pattern_132_check : SubsetPairCheck pattern_132.1 pattern_132.2 := by decide +kernel
theorem pattern_132_rigid : Rigid (Cells pattern_132.1) (Cells pattern_132.2) :=
  subsetPairCheck_sound pattern_132_check

def pattern_133 : Pattern := ([(0,2),(0,3),(1,2)],[(1,0),(1,1),(2,0)])
theorem pattern_133_check : SubsetPairCheck pattern_133.1 pattern_133.2 := by decide +kernel
theorem pattern_133_rigid : Rigid (Cells pattern_133.1) (Cells pattern_133.2) :=
  subsetPairCheck_sound pattern_133_check

def pattern_134 : Pattern := ([(0,2),(0,3),(1,2)],[(1,0),(1,1),(2,1)])
theorem pattern_134_check : SubsetPairCheck pattern_134.1 pattern_134.2 := by decide +kernel
theorem pattern_134_rigid : Rigid (Cells pattern_134.1) (Cells pattern_134.2) :=
  subsetPairCheck_sound pattern_134_check

def pattern_135 : Pattern := ([(0,2),(0,3),(1,2)],[(1,1),(2,0),(2,1)])
theorem pattern_135_check : SubsetPairCheck pattern_135.1 pattern_135.2 := by decide +kernel
theorem pattern_135_rigid : Rigid (Cells pattern_135.1) (Cells pattern_135.2) :=
  subsetPairCheck_sound pattern_135_check

def pattern_136 : Pattern := ([(0,2),(0,3),(1,2)],[(2,0),(2,1),(2,2)])
theorem pattern_136_check : SubsetPairCheck pattern_136.1 pattern_136.2 := by decide +kernel
theorem pattern_136_rigid : Rigid (Cells pattern_136.1) (Cells pattern_136.2) :=
  subsetPairCheck_sound pattern_136_check

def pattern_137 : Pattern := ([(0,2),(0,3),(1,3)],[(1,0),(1,1),(1,2)])
theorem pattern_137_check : SubsetPairCheck pattern_137.1 pattern_137.2 := by decide +kernel
theorem pattern_137_rigid : Rigid (Cells pattern_137.1) (Cells pattern_137.2) :=
  subsetPairCheck_sound pattern_137_check

def pattern_138 : Pattern := ([(0,2),(1,1),(1,2)],[(1,0),(2,0),(2,1)])
theorem pattern_138_check : SubsetPairCheck pattern_138.1 pattern_138.2 := by decide +kernel
theorem pattern_138_rigid : Rigid (Cells pattern_138.1) (Cells pattern_138.2) :=
  subsetPairCheck_sound pattern_138_check

def pattern_139 : Pattern := ([(0,2),(1,1),(1,2)],[(1,0),(2,0),(3,0)])
theorem pattern_139_check : SubsetPairCheck pattern_139.1 pattern_139.2 := by decide +kernel
theorem pattern_139_rigid : Rigid (Cells pattern_139.1) (Cells pattern_139.2) :=
  subsetPairCheck_sound pattern_139_check

def pattern_140 : Pattern := ([(0,2),(1,1),(1,2)],[(2,0),(2,1),(3,0)])
theorem pattern_140_check : SubsetPairCheck pattern_140.1 pattern_140.2 := by decide +kernel
theorem pattern_140_rigid : Rigid (Cells pattern_140.1) (Cells pattern_140.2) :=
  subsetPairCheck_sound pattern_140_check

def pattern_141 : Pattern := ([(0,2),(1,1),(1,2)],[(2,0),(2,1),(3,1)])
theorem pattern_141_check : SubsetPairCheck pattern_141.1 pattern_141.2 := by decide +kernel
theorem pattern_141_rigid : Rigid (Cells pattern_141.1) (Cells pattern_141.2) :=
  subsetPairCheck_sound pattern_141_check

def pattern_142 : Pattern := ([(0,2),(1,1),(1,2)],[(2,1),(3,0),(3,1)])
theorem pattern_142_check : SubsetPairCheck pattern_142.1 pattern_142.2 := by decide +kernel
theorem pattern_142_rigid : Rigid (Cells pattern_142.1) (Cells pattern_142.2) :=
  subsetPairCheck_sound pattern_142_check

def pattern_143 : Pattern := ([(0,2),(1,2),(1,3)],[(1,0),(1,1),(2,0)])
theorem pattern_143_check : SubsetPairCheck pattern_143.1 pattern_143.2 := by decide +kernel
theorem pattern_143_rigid : Rigid (Cells pattern_143.1) (Cells pattern_143.2) :=
  subsetPairCheck_sound pattern_143_check

def pattern_144 : Pattern := ([(0,2),(1,2),(1,3)],[(1,0),(1,1),(2,1)])
theorem pattern_144_check : SubsetPairCheck pattern_144.1 pattern_144.2 := by decide +kernel
theorem pattern_144_rigid : Rigid (Cells pattern_144.1) (Cells pattern_144.2) :=
  subsetPairCheck_sound pattern_144_check

def pattern_145 : Pattern := ([(0,2),(1,2),(1,3)],[(1,1),(2,0),(2,1)])
theorem pattern_145_check : SubsetPairCheck pattern_145.1 pattern_145.2 := by decide +kernel
theorem pattern_145_rigid : Rigid (Cells pattern_145.1) (Cells pattern_145.2) :=
  subsetPairCheck_sound pattern_145_check

def pattern_146 : Pattern := ([(0,2),(1,2),(1,3)],[(2,0),(2,1),(2,2)])
theorem pattern_146_check : SubsetPairCheck pattern_146.1 pattern_146.2 := by decide +kernel
theorem pattern_146_rigid : Rigid (Cells pattern_146.1) (Cells pattern_146.2) :=
  subsetPairCheck_sound pattern_146_check

def pattern_147 : Pattern := ([(0,2),(1,2),(2,2)],[(1,0),(1,1),(2,0)])
theorem pattern_147_check : SubsetPairCheck pattern_147.1 pattern_147.2 := by decide +kernel
theorem pattern_147_rigid : Rigid (Cells pattern_147.1) (Cells pattern_147.2) :=
  subsetPairCheck_sound pattern_147_check

def pattern_148 : Pattern := ([(0,2),(1,2),(2,2)],[(1,0),(1,1),(2,1)])
theorem pattern_148_check : SubsetPairCheck pattern_148.1 pattern_148.2 := by decide +kernel
theorem pattern_148_rigid : Rigid (Cells pattern_148.1) (Cells pattern_148.2) :=
  subsetPairCheck_sound pattern_148_check

def pattern_149 : Pattern := ([(0,2),(1,2),(2,2)],[(2,0),(2,1),(3,0)])
theorem pattern_149_check : SubsetPairCheck pattern_149.1 pattern_149.2 := by decide +kernel
theorem pattern_149_rigid : Rigid (Cells pattern_149.1) (Cells pattern_149.2) :=
  subsetPairCheck_sound pattern_149_check

def pattern_150 : Pattern := ([(0,2),(1,2),(2,2)],[(2,0),(2,1),(3,1)])
theorem pattern_150_check : SubsetPairCheck pattern_150.1 pattern_150.2 := by decide +kernel
theorem pattern_150_rigid : Rigid (Cells pattern_150.1) (Cells pattern_150.2) :=
  subsetPairCheck_sound pattern_150_check

def pattern_151 : Pattern := ([(0,2),(1,2),(2,2)],[(2,1),(3,0),(3,1)])
theorem pattern_151_check : SubsetPairCheck pattern_151.1 pattern_151.2 := by decide +kernel
theorem pattern_151_rigid : Rigid (Cells pattern_151.1) (Cells pattern_151.2) :=
  subsetPairCheck_sound pattern_151_check

def pattern_152 : Pattern := ([(0,2),(1,2),(2,2)],[(3,0),(3,1),(3,2)])
theorem pattern_152_check : SubsetPairCheck pattern_152.1 pattern_152.2 := by decide +kernel
theorem pattern_152_rigid : Rigid (Cells pattern_152.1) (Cells pattern_152.2) :=
  subsetPairCheck_sound pattern_152_check

def pattern_153 : Pattern := ([(0,3),(0,4),(1,3)],[(1,0),(1,1),(1,2)])
theorem pattern_153_check : SubsetPairCheck pattern_153.1 pattern_153.2 := by decide +kernel
theorem pattern_153_rigid : Rigid (Cells pattern_153.1) (Cells pattern_153.2) :=
  subsetPairCheck_sound pattern_153_check

def pattern_154 : Pattern := ([(0,3),(1,2),(1,3)],[(1,0),(1,1),(2,0)])
theorem pattern_154_check : SubsetPairCheck pattern_154.1 pattern_154.2 := by decide +kernel
theorem pattern_154_rigid : Rigid (Cells pattern_154.1) (Cells pattern_154.2) :=
  subsetPairCheck_sound pattern_154_check

def pattern_155 : Pattern := ([(0,3),(1,2),(1,3)],[(1,0),(1,1),(2,1)])
theorem pattern_155_check : SubsetPairCheck pattern_155.1 pattern_155.2 := by decide +kernel
theorem pattern_155_rigid : Rigid (Cells pattern_155.1) (Cells pattern_155.2) :=
  subsetPairCheck_sound pattern_155_check

def pattern_156 : Pattern := ([(0,3),(1,2),(1,3)],[(1,1),(2,0),(2,1)])
theorem pattern_156_check : SubsetPairCheck pattern_156.1 pattern_156.2 := by decide +kernel
theorem pattern_156_rigid : Rigid (Cells pattern_156.1) (Cells pattern_156.2) :=
  subsetPairCheck_sound pattern_156_check

def pattern_157 : Pattern := ([(0,3),(1,2),(1,3)],[(2,0),(2,1),(2,2)])
theorem pattern_157_check : SubsetPairCheck pattern_157.1 pattern_157.2 := by decide +kernel
theorem pattern_157_rigid : Rigid (Cells pattern_157.1) (Cells pattern_157.2) :=
  subsetPairCheck_sound pattern_157_check

def pattern_158 : Pattern := ([(0,3),(1,3),(1,4)],[(1,0),(1,1),(1,2)])
theorem pattern_158_check : SubsetPairCheck pattern_158.1 pattern_158.2 := by decide +kernel
theorem pattern_158_rigid : Rigid (Cells pattern_158.1) (Cells pattern_158.2) :=
  subsetPairCheck_sound pattern_158_check

def pattern_159 : Pattern := ([(0,3),(1,3),(2,3)],[(1,0),(1,1),(1,2)])
theorem pattern_159_check : SubsetPairCheck pattern_159.1 pattern_159.2 := by decide +kernel
theorem pattern_159_rigid : Rigid (Cells pattern_159.1) (Cells pattern_159.2) :=
  subsetPairCheck_sound pattern_159_check

def pattern_160 : Pattern := ([(0,3),(1,3),(2,3)],[(2,0),(2,1),(2,2)])
theorem pattern_160_check : SubsetPairCheck pattern_160.1 pattern_160.2 := by decide +kernel
theorem pattern_160_rigid : Rigid (Cells pattern_160.1) (Cells pattern_160.2) :=
  subsetPairCheck_sound pattern_160_check

def pattern_161 : Pattern := ([(0,4),(1,3),(1,4)],[(1,0),(1,1),(1,2)])
theorem pattern_161_check : SubsetPairCheck pattern_161.1 pattern_161.2 := by decide +kernel
theorem pattern_161_rigid : Rigid (Cells pattern_161.1) (Cells pattern_161.2) :=
  subsetPairCheck_sound pattern_161_check

def patterns : List Pattern := [pattern_0,pattern_1,pattern_2,pattern_3,pattern_4,pattern_5,pattern_6,pattern_7,pattern_8,pattern_9,pattern_10,pattern_11,pattern_12,pattern_13,pattern_14,pattern_15,pattern_16,pattern_17,pattern_18,pattern_19,pattern_20,pattern_21,pattern_22,pattern_23,pattern_24,pattern_25,pattern_26,pattern_27,pattern_28,pattern_29,pattern_30,pattern_31,pattern_32,pattern_33,pattern_34,pattern_35,pattern_36,pattern_37,pattern_38,pattern_39,pattern_40,pattern_41,pattern_42,pattern_43,pattern_44,pattern_45,pattern_46,pattern_47,pattern_48,pattern_49,pattern_50,pattern_51,pattern_52,pattern_53,pattern_54,pattern_55,pattern_56,pattern_57,pattern_58,pattern_59,pattern_60,pattern_61,pattern_62,pattern_63,pattern_64,pattern_65,pattern_66,pattern_67,pattern_68,pattern_69,pattern_70,pattern_71,pattern_72,pattern_73,pattern_74,pattern_75,pattern_76,pattern_77,pattern_78,pattern_79,pattern_80,pattern_81,pattern_82,pattern_83,pattern_84,pattern_85,pattern_86,pattern_87,pattern_88,pattern_89,pattern_90,pattern_91,pattern_92,pattern_93,pattern_94,pattern_95,pattern_96,pattern_97,pattern_98,pattern_99,pattern_100,pattern_101,pattern_102,pattern_103,pattern_104,pattern_105,pattern_106,pattern_107,pattern_108,pattern_109,pattern_110,pattern_111,pattern_112,pattern_113,pattern_114,pattern_115,pattern_116,pattern_117,pattern_118,pattern_119,pattern_120,pattern_121,pattern_122,pattern_123,pattern_124,pattern_125,pattern_126,pattern_127,pattern_128,pattern_129,pattern_130,pattern_131,pattern_132,pattern_133,pattern_134,pattern_135,pattern_136,pattern_137,pattern_138,pattern_139,pattern_140,pattern_141,pattern_142,pattern_143,pattern_144,pattern_145,pattern_146,pattern_147,pattern_148,pattern_149,pattern_150,pattern_151,pattern_152,pattern_153,pattern_154,pattern_155,pattern_156,pattern_157,pattern_158,pattern_159,pattern_160,pattern_161]
def catalog (k : Nat) : Pattern := patterns[k]?.getD pattern_0
theorem patterns_sound : ∀ p ∈ patterns, Rigid (Cells p.1) (Cells p.2) := by
  intro p hp
  simp only [patterns, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39 | h40 | h41 | h42 | h43 | h44 | h45 | h46 | h47 | h48 | h49 | h50 | h51 | h52 | h53 | h54 | h55 | h56 | h57 | h58 | h59 | h60 | h61 | h62 | h63 | h64 | h65 | h66 | h67 | h68 | h69 | h70 | h71 | h72 | h73 | h74 | h75 | h76 | h77 | h78 | h79 | h80 | h81 | h82 | h83 | h84 | h85 | h86 | h87 | h88 | h89 | h90 | h91 | h92 | h93 | h94 | h95 | h96 | h97 | h98 | h99 | h100 | h101 | h102 | h103 | h104 | h105 | h106 | h107 | h108 | h109 | h110 | h111 | h112 | h113 | h114 | h115 | h116 | h117 | h118 | h119 | h120 | h121 | h122 | h123 | h124 | h125 | h126 | h127 | h128 | h129 | h130 | h131 | h132 | h133 | h134 | h135 | h136 | h137 | h138 | h139 | h140 | h141 | h142 | h143 | h144 | h145 | h146 | h147 | h148 | h149 | h150 | h151 | h152 | h153 | h154 | h155 | h156 | h157 | h158 | h159 | h160 | h161
  · subst p; exact pattern_0_rigid
  · subst p; exact pattern_1_rigid
  · subst p; exact pattern_2_rigid
  · subst p; exact pattern_3_rigid
  · subst p; exact pattern_4_rigid
  · subst p; exact pattern_5_rigid
  · subst p; exact pattern_6_rigid
  · subst p; exact pattern_7_rigid
  · subst p; exact pattern_8_rigid
  · subst p; exact pattern_9_rigid
  · subst p; exact pattern_10_rigid
  · subst p; exact pattern_11_rigid
  · subst p; exact pattern_12_rigid
  · subst p; exact pattern_13_rigid
  · subst p; exact pattern_14_rigid
  · subst p; exact pattern_15_rigid
  · subst p; exact pattern_16_rigid
  · subst p; exact pattern_17_rigid
  · subst p; exact pattern_18_rigid
  · subst p; exact pattern_19_rigid
  · subst p; exact pattern_20_rigid
  · subst p; exact pattern_21_rigid
  · subst p; exact pattern_22_rigid
  · subst p; exact pattern_23_rigid
  · subst p; exact pattern_24_rigid
  · subst p; exact pattern_25_rigid
  · subst p; exact pattern_26_rigid
  · subst p; exact pattern_27_rigid
  · subst p; exact pattern_28_rigid
  · subst p; exact pattern_29_rigid
  · subst p; exact pattern_30_rigid
  · subst p; exact pattern_31_rigid
  · subst p; exact pattern_32_rigid
  · subst p; exact pattern_33_rigid
  · subst p; exact pattern_34_rigid
  · subst p; exact pattern_35_rigid
  · subst p; exact pattern_36_rigid
  · subst p; exact pattern_37_rigid
  · subst p; exact pattern_38_rigid
  · subst p; exact pattern_39_rigid
  · subst p; exact pattern_40_rigid
  · subst p; exact pattern_41_rigid
  · subst p; exact pattern_42_rigid
  · subst p; exact pattern_43_rigid
  · subst p; exact pattern_44_rigid
  · subst p; exact pattern_45_rigid
  · subst p; exact pattern_46_rigid
  · subst p; exact pattern_47_rigid
  · subst p; exact pattern_48_rigid
  · subst p; exact pattern_49_rigid
  · subst p; exact pattern_50_rigid
  · subst p; exact pattern_51_rigid
  · subst p; exact pattern_52_rigid
  · subst p; exact pattern_53_rigid
  · subst p; exact pattern_54_rigid
  · subst p; exact pattern_55_rigid
  · subst p; exact pattern_56_rigid
  · subst p; exact pattern_57_rigid
  · subst p; exact pattern_58_rigid
  · subst p; exact pattern_59_rigid
  · subst p; exact pattern_60_rigid
  · subst p; exact pattern_61_rigid
  · subst p; exact pattern_62_rigid
  · subst p; exact pattern_63_rigid
  · subst p; exact pattern_64_rigid
  · subst p; exact pattern_65_rigid
  · subst p; exact pattern_66_rigid
  · subst p; exact pattern_67_rigid
  · subst p; exact pattern_68_rigid
  · subst p; exact pattern_69_rigid
  · subst p; exact pattern_70_rigid
  · subst p; exact pattern_71_rigid
  · subst p; exact pattern_72_rigid
  · subst p; exact pattern_73_rigid
  · subst p; exact pattern_74_rigid
  · subst p; exact pattern_75_rigid
  · subst p; exact pattern_76_rigid
  · subst p; exact pattern_77_rigid
  · subst p; exact pattern_78_rigid
  · subst p; exact pattern_79_rigid
  · subst p; exact pattern_80_rigid
  · subst p; exact pattern_81_rigid
  · subst p; exact pattern_82_rigid
  · subst p; exact pattern_83_rigid
  · subst p; exact pattern_84_rigid
  · subst p; exact pattern_85_rigid
  · subst p; exact pattern_86_rigid
  · subst p; exact pattern_87_rigid
  · subst p; exact pattern_88_rigid
  · subst p; exact pattern_89_rigid
  · subst p; exact pattern_90_rigid
  · subst p; exact pattern_91_rigid
  · subst p; exact pattern_92_rigid
  · subst p; exact pattern_93_rigid
  · subst p; exact pattern_94_rigid
  · subst p; exact pattern_95_rigid
  · subst p; exact pattern_96_rigid
  · subst p; exact pattern_97_rigid
  · subst p; exact pattern_98_rigid
  · subst p; exact pattern_99_rigid
  · subst p; exact pattern_100_rigid
  · subst p; exact pattern_101_rigid
  · subst p; exact pattern_102_rigid
  · subst p; exact pattern_103_rigid
  · subst p; exact pattern_104_rigid
  · subst p; exact pattern_105_rigid
  · subst p; exact pattern_106_rigid
  · subst p; exact pattern_107_rigid
  · subst p; exact pattern_108_rigid
  · subst p; exact pattern_109_rigid
  · subst p; exact pattern_110_rigid
  · subst p; exact pattern_111_rigid
  · subst p; exact pattern_112_rigid
  · subst p; exact pattern_113_rigid
  · subst p; exact pattern_114_rigid
  · subst p; exact pattern_115_rigid
  · subst p; exact pattern_116_rigid
  · subst p; exact pattern_117_rigid
  · subst p; exact pattern_118_rigid
  · subst p; exact pattern_119_rigid
  · subst p; exact pattern_120_rigid
  · subst p; exact pattern_121_rigid
  · subst p; exact pattern_122_rigid
  · subst p; exact pattern_123_rigid
  · subst p; exact pattern_124_rigid
  · subst p; exact pattern_125_rigid
  · subst p; exact pattern_126_rigid
  · subst p; exact pattern_127_rigid
  · subst p; exact pattern_128_rigid
  · subst p; exact pattern_129_rigid
  · subst p; exact pattern_130_rigid
  · subst p; exact pattern_131_rigid
  · subst p; exact pattern_132_rigid
  · subst p; exact pattern_133_rigid
  · subst p; exact pattern_134_rigid
  · subst p; exact pattern_135_rigid
  · subst p; exact pattern_136_rigid
  · subst p; exact pattern_137_rigid
  · subst p; exact pattern_138_rigid
  · subst p; exact pattern_139_rigid
  · subst p; exact pattern_140_rigid
  · subst p; exact pattern_141_rigid
  · subst p; exact pattern_142_rigid
  · subst p; exact pattern_143_rigid
  · subst p; exact pattern_144_rigid
  · subst p; exact pattern_145_rigid
  · subst p; exact pattern_146_rigid
  · subst p; exact pattern_147_rigid
  · subst p; exact pattern_148_rigid
  · subst p; exact pattern_149_rigid
  · subst p; exact pattern_150_rigid
  · subst p; exact pattern_151_rigid
  · subst p; exact pattern_152_rigid
  · subst p; exact pattern_153_rigid
  · subst p; exact pattern_154_rigid
  · subst p; exact pattern_155_rigid
  · subst p; exact pattern_156_rigid
  · subst p; exact pattern_157_rigid
  · subst p; exact pattern_158_rigid
  · subst p; exact pattern_159_rigid
  · subst p; exact pattern_160_rigid
  · subst p; exact pattern_161_rigid
theorem catalog_sound : ∀ k, Rigid (Cells (catalog k).1) (Cells (catalog k).2) :=
  catalog_getD_sound patterns_sound pattern_0_rigid

end LockedTromino.Witnesses
