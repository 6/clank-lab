import BaseREhrhart.CertificateCore

/-! Kernel-checked finite certificate chunks. -/
set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace BaseREhrhart

theorem packedBlock_010 :
    packedBlock 163840 14 = 25354476022217651479080818704384 := by decide

theorem packedBlock_011 :
    packedBlock 180224 14 = 1270102313135160362123640438784 := by decide

theorem packedBlock_012 :
    packedBlock 196608 14 = 87472104531995588193498283638784 := by decide

theorem packedBlock_013 :
    packedBlock 212992 14 = 1505123256916074911088246784 := by decide

theorem packedBlock_014 :
    packedBlock 229376 14 = 88740908449020242240552628649984 := by decide

theorem packedBlock_015 :
    packedBlock 245760 14 = 70990618151295768817041050435584 := by decide

theorem packedBlock_016 :
    packedBlock 262144 14 = 19018518774381941137843850051584 := by decide

theorem packedBlock_017 :
    packedBlock 278528 14 = 247197458336096924472575298371584 := by decide

theorem packedBlock_018 :
    packedBlock 294912 14 = 1270109566707371849378047197184 := by decide

theorem packedBlock_019 :
    packedBlock 311296 14 = 202830972417255879706259576848384 := by decide

end BaseREhrhart
