import Steinberg.DrawingCertificate

namespace Steinberg.Drawing

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem points_distinct : distinctCheck points 82 = true := by decide +kernel

theorem row_0 : edgeRow points 82 drawingEdges (0, 1) = true := by
  decide +kernel

theorem row_1 : edgeRow points 82 drawingEdges (0, 2) = true := by
  decide +kernel

theorem row_2 : edgeRow points 82 drawingEdges (0, 3) = true := by
  decide +kernel

theorem row_3 : edgeRow points 82 drawingEdges (0, 4) = true := by
  decide +kernel

theorem row_4 : edgeRow points 82 drawingEdges (0, 5) = true := by
  decide +kernel

theorem row_5 : edgeRow points 82 drawingEdges (0, 6) = true := by
  decide +kernel

theorem row_6 : edgeRow points 82 drawingEdges (1, 6) = true := by
  decide +kernel

theorem row_7 : edgeRow points 82 drawingEdges (1, 18) = true := by
  decide +kernel

theorem row_8 : edgeRow points 82 drawingEdges (1, 19) = true := by
  decide +kernel

theorem row_9 : edgeRow points 82 drawingEdges (1, 20) = true := by
  decide +kernel

theorem row_10 : edgeRow points 82 drawingEdges (1, 21) = true := by
  decide +kernel

theorem row_11 : edgeRow points 82 drawingEdges (2, 23) = true := by
  decide +kernel

theorem row_12 : edgeRow points 82 drawingEdges (2, 32) = true := by
  decide +kernel

theorem row_13 : edgeRow points 82 drawingEdges (3, 24) = true := by
  decide +kernel

theorem row_14 : edgeRow points 82 drawingEdges (3, 33) = true := by
  decide +kernel

theorem row_15 : edgeRow points 82 drawingEdges (4, 28) = true := by
  decide +kernel

theorem row_16 : edgeRow points 82 drawingEdges (4, 34) = true := by
  decide +kernel

theorem row_17 : edgeRow points 82 drawingEdges (5, 29) = true := by
  decide +kernel

theorem row_18 : edgeRow points 82 drawingEdges (5, 35) = true := by
  decide +kernel

theorem row_19 : edgeRow points 82 drawingEdges (6, 60) = true := by
  decide +kernel

theorem row_20 : edgeRow points 82 drawingEdges (6, 61) = true := by
  decide +kernel

theorem row_21 : edgeRow points 82 drawingEdges (7, 8) = true := by
  decide +kernel

theorem row_22 : edgeRow points 82 drawingEdges (7, 9) = true := by
  decide +kernel

theorem row_23 : edgeRow points 82 drawingEdges (7, 10) = true := by
  decide +kernel

theorem row_24 : edgeRow points 82 drawingEdges (7, 11) = true := by
  decide +kernel

theorem row_25 : edgeRow points 82 drawingEdges (7, 12) = true := by
  decide +kernel

theorem row_26 : edgeRow points 82 drawingEdges (7, 13) = true := by
  decide +kernel

theorem row_27 : edgeRow points 82 drawingEdges (7, 14) = true := by
  decide +kernel

theorem row_28 : edgeRow points 82 drawingEdges (7, 15) = true := by
  decide +kernel

theorem row_29 : edgeRow points 82 drawingEdges (7, 16) = true := by
  decide +kernel

theorem row_30 : edgeRow points 82 drawingEdges (7, 17) = true := by
  decide +kernel

theorem row_31 : edgeRow points 82 drawingEdges (8, 36) = true := by
  decide +kernel

theorem row_32 : edgeRow points 82 drawingEdges (8, 40) = true := by
  decide +kernel

theorem row_33 : edgeRow points 82 drawingEdges (9, 37) = true := by
  decide +kernel

theorem row_34 : edgeRow points 82 drawingEdges (9, 41) = true := by
  decide +kernel

theorem row_35 : edgeRow points 82 drawingEdges (10, 42) = true := by
  decide +kernel

theorem row_36 : edgeRow points 82 drawingEdges (10, 44) = true := by
  decide +kernel

theorem row_37 : edgeRow points 82 drawingEdges (11, 43) = true := by
  decide +kernel

theorem row_38 : edgeRow points 82 drawingEdges (11, 45) = true := by
  decide +kernel

theorem row_39 : edgeRow points 82 drawingEdges (12, 60) = true := by
  decide +kernel

theorem row_40 : edgeRow points 82 drawingEdges (12, 62) = true := by
  decide +kernel

theorem row_41 : edgeRow points 82 drawingEdges (13, 61) = true := by
  decide +kernel

theorem row_42 : edgeRow points 82 drawingEdges (13, 63) = true := by
  decide +kernel

theorem row_43 : edgeRow points 82 drawingEdges (14, 68) = true := by
  decide +kernel

theorem row_44 : edgeRow points 82 drawingEdges (14, 72) = true := by
  decide +kernel

theorem row_45 : edgeRow points 82 drawingEdges (15, 69) = true := by
  decide +kernel

theorem row_46 : edgeRow points 82 drawingEdges (15, 73) = true := by
  decide +kernel

theorem row_47 : edgeRow points 82 drawingEdges (16, 74) = true := by
  decide +kernel

theorem row_48 : edgeRow points 82 drawingEdges (16, 76) = true := by
  decide +kernel

theorem row_49 : edgeRow points 82 drawingEdges (17, 75) = true := by
  decide +kernel

theorem row_50 : edgeRow points 82 drawingEdges (17, 77) = true := by
  decide +kernel

theorem row_51 : edgeRow points 82 drawingEdges (18, 51) = true := by
  decide +kernel

theorem row_52 : edgeRow points 82 drawingEdges (18, 64) = true := by
  decide +kernel

theorem row_53 : edgeRow points 82 drawingEdges (19, 52) = true := by
  decide +kernel

theorem row_54 : edgeRow points 82 drawingEdges (19, 65) = true := by
  decide +kernel

theorem row_55 : edgeRow points 82 drawingEdges (20, 56) = true := by
  decide +kernel

theorem row_56 : edgeRow points 82 drawingEdges (20, 66) = true := by
  decide +kernel

theorem row_57 : edgeRow points 82 drawingEdges (21, 57) = true := by
  decide +kernel

theorem row_58 : edgeRow points 82 drawingEdges (21, 67) = true := by
  decide +kernel

theorem row_59 : edgeRow points 82 drawingEdges (22, 23) = true := by
  decide +kernel

theorem row_60 : edgeRow points 82 drawingEdges (22, 24) = true := by
  decide +kernel

theorem row_61 : edgeRow points 82 drawingEdges (22, 25) = true := by
  decide +kernel

theorem row_62 : edgeRow points 82 drawingEdges (22, 26) = true := by
  decide +kernel

theorem row_63 : edgeRow points 82 drawingEdges (23, 32) = true := by
  decide +kernel

theorem row_64 : edgeRow points 82 drawingEdges (24, 33) = true := by
  decide +kernel

theorem row_65 : edgeRow points 82 drawingEdges (25, 26) = true := by
  decide +kernel

theorem row_66 : edgeRow points 82 drawingEdges (25, 38) = true := by
  decide +kernel

theorem row_67 : edgeRow points 82 drawingEdges (25, 39) = true := by
  decide +kernel

theorem row_68 : edgeRow points 82 drawingEdges (26, 42) = true := by
  decide +kernel

theorem row_69 : edgeRow points 82 drawingEdges (26, 43) = true := by
  decide +kernel

theorem row_70 : edgeRow points 82 drawingEdges (27, 28) = true := by
  decide +kernel

theorem row_71 : edgeRow points 82 drawingEdges (27, 29) = true := by
  decide +kernel

theorem row_72 : edgeRow points 82 drawingEdges (27, 30) = true := by
  decide +kernel

theorem row_73 : edgeRow points 82 drawingEdges (27, 31) = true := by
  decide +kernel

theorem row_74 : edgeRow points 82 drawingEdges (28, 34) = true := by
  decide +kernel

theorem row_75 : edgeRow points 82 drawingEdges (29, 35) = true := by
  decide +kernel

theorem row_76 : edgeRow points 82 drawingEdges (30, 31) = true := by
  decide +kernel

theorem row_77 : edgeRow points 82 drawingEdges (30, 36) = true := by
  decide +kernel

theorem row_78 : edgeRow points 82 drawingEdges (30, 37) = true := by
  decide +kernel

theorem row_79 : edgeRow points 82 drawingEdges (31, 46) = true := by
  decide +kernel

theorem row_80 : edgeRow points 82 drawingEdges (31, 47) = true := by
  decide +kernel

theorem row_81 : edgeRow points 82 drawingEdges (32, 33) = true := by
  decide +kernel

theorem row_82 : edgeRow points 82 drawingEdges (34, 35) = true := by
  decide +kernel

theorem row_83 : edgeRow points 82 drawingEdges (36, 40) = true := by
  decide +kernel

theorem row_84 : edgeRow points 82 drawingEdges (37, 41) = true := by
  decide +kernel

theorem row_85 : edgeRow points 82 drawingEdges (38, 46) = true := by
  decide +kernel

theorem row_86 : edgeRow points 82 drawingEdges (38, 48) = true := by
  decide +kernel

theorem row_87 : edgeRow points 82 drawingEdges (39, 47) = true := by
  decide +kernel

theorem row_88 : edgeRow points 82 drawingEdges (39, 49) = true := by
  decide +kernel

theorem row_89 : edgeRow points 82 drawingEdges (40, 41) = true := by
  decide +kernel

theorem row_90 : edgeRow points 82 drawingEdges (42, 44) = true := by
  decide +kernel

theorem row_91 : edgeRow points 82 drawingEdges (43, 45) = true := by
  decide +kernel

theorem row_92 : edgeRow points 82 drawingEdges (44, 45) = true := by
  decide +kernel

theorem row_93 : edgeRow points 82 drawingEdges (46, 48) = true := by
  decide +kernel

theorem row_94 : edgeRow points 82 drawingEdges (47, 49) = true := by
  decide +kernel

theorem row_95 : edgeRow points 82 drawingEdges (48, 49) = true := by
  decide +kernel

theorem row_96 : edgeRow points 82 drawingEdges (50, 51) = true := by
  decide +kernel

theorem row_97 : edgeRow points 82 drawingEdges (50, 52) = true := by
  decide +kernel

theorem row_98 : edgeRow points 82 drawingEdges (50, 53) = true := by
  decide +kernel

theorem row_99 : edgeRow points 82 drawingEdges (50, 54) = true := by
  decide +kernel

theorem row_100 : edgeRow points 82 drawingEdges (51, 64) = true := by
  decide +kernel

theorem row_101 : edgeRow points 82 drawingEdges (52, 65) = true := by
  decide +kernel

theorem row_102 : edgeRow points 82 drawingEdges (53, 54) = true := by
  decide +kernel

theorem row_103 : edgeRow points 82 drawingEdges (53, 70) = true := by
  decide +kernel

theorem row_104 : edgeRow points 82 drawingEdges (53, 71) = true := by
  decide +kernel

theorem row_105 : edgeRow points 82 drawingEdges (54, 74) = true := by
  decide +kernel

theorem row_106 : edgeRow points 82 drawingEdges (54, 75) = true := by
  decide +kernel

theorem row_107 : edgeRow points 82 drawingEdges (55, 56) = true := by
  decide +kernel

theorem row_108 : edgeRow points 82 drawingEdges (55, 57) = true := by
  decide +kernel

theorem row_109 : edgeRow points 82 drawingEdges (55, 58) = true := by
  decide +kernel

theorem row_110 : edgeRow points 82 drawingEdges (55, 59) = true := by
  decide +kernel

theorem row_111 : edgeRow points 82 drawingEdges (56, 66) = true := by
  decide +kernel

theorem row_112 : edgeRow points 82 drawingEdges (57, 67) = true := by
  decide +kernel

theorem row_113 : edgeRow points 82 drawingEdges (58, 59) = true := by
  decide +kernel

theorem row_114 : edgeRow points 82 drawingEdges (58, 68) = true := by
  decide +kernel

theorem row_115 : edgeRow points 82 drawingEdges (58, 69) = true := by
  decide +kernel

theorem row_116 : edgeRow points 82 drawingEdges (59, 78) = true := by
  decide +kernel

theorem row_117 : edgeRow points 82 drawingEdges (59, 79) = true := by
  decide +kernel

theorem row_118 : edgeRow points 82 drawingEdges (60, 62) = true := by
  decide +kernel

theorem row_119 : edgeRow points 82 drawingEdges (61, 63) = true := by
  decide +kernel

theorem row_120 : edgeRow points 82 drawingEdges (62, 63) = true := by
  decide +kernel

theorem row_121 : edgeRow points 82 drawingEdges (64, 65) = true := by
  decide +kernel

theorem row_122 : edgeRow points 82 drawingEdges (66, 67) = true := by
  decide +kernel

theorem row_123 : edgeRow points 82 drawingEdges (68, 72) = true := by
  decide +kernel

theorem row_124 : edgeRow points 82 drawingEdges (69, 73) = true := by
  decide +kernel

theorem row_125 : edgeRow points 82 drawingEdges (70, 78) = true := by
  decide +kernel

theorem row_126 : edgeRow points 82 drawingEdges (70, 80) = true := by
  decide +kernel

theorem row_127 : edgeRow points 82 drawingEdges (71, 79) = true := by
  decide +kernel

theorem row_128 : edgeRow points 82 drawingEdges (71, 81) = true := by
  decide +kernel

theorem row_129 : edgeRow points 82 drawingEdges (72, 73) = true := by
  decide +kernel

theorem row_130 : edgeRow points 82 drawingEdges (74, 76) = true := by
  decide +kernel

theorem row_131 : edgeRow points 82 drawingEdges (75, 77) = true := by
  decide +kernel

theorem row_132 : edgeRow points 82 drawingEdges (76, 77) = true := by
  decide +kernel

theorem row_133 : edgeRow points 82 drawingEdges (78, 80) = true := by
  decide +kernel

theorem row_134 : edgeRow points 82 drawingEdges (79, 81) = true := by
  decide +kernel

theorem row_135 : edgeRow points 82 drawingEdges (80, 81) = true := by
  decide +kernel

theorem rows_checked : drawingEdges.all (edgeRow points 82 drawingEdges) = true := by
  unfold drawingEdges
  simp only [List.all_cons, List.all_nil, Bool.and_eq_true, and_true]
  exact ⟨row_0, row_1, row_2, row_3, row_4, row_5, row_6, row_7, row_8, row_9, row_10, row_11, row_12, row_13, row_14, row_15, row_16, row_17, row_18, row_19, row_20, row_21, row_22, row_23, row_24, row_25, row_26, row_27, row_28, row_29, row_30, row_31, row_32, row_33, row_34, row_35, row_36, row_37, row_38, row_39, row_40, row_41, row_42, row_43, row_44, row_45, row_46, row_47, row_48, row_49, row_50, row_51, row_52, row_53, row_54, row_55, row_56, row_57, row_58, row_59, row_60, row_61, row_62, row_63, row_64, row_65, row_66, row_67, row_68, row_69, row_70, row_71, row_72, row_73, row_74, row_75, row_76, row_77, row_78, row_79, row_80, row_81, row_82, row_83, row_84, row_85, row_86, row_87, row_88, row_89, row_90, row_91, row_92, row_93, row_94, row_95, row_96, row_97, row_98, row_99, row_100, row_101, row_102, row_103, row_104, row_105, row_106, row_107, row_108, row_109, row_110, row_111, row_112, row_113, row_114, row_115, row_116, row_117, row_118, row_119, row_120, row_121, row_122, row_123, row_124, row_125, row_126, row_127, row_128, row_129, row_130, row_131, row_132, row_133, row_134, row_135⟩

end Steinberg.Drawing
