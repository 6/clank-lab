import BaseREhrhart.CertificateCore

/-! Kernel-checked finite certificate chunks. -/
set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace BaseREhrhart

theorem packedBlock_000 :
    packedBlock 0 14 = 84629862944683820772753409 := by decide

theorem packedBlock_001 :
    packedBlock 16384 14 = 1125519813994043219544899584 := by decide

theorem packedBlock_002 :
    packedBlock 32768 14 = 1269334642151030865345022787584 := by decide

theorem packedBlock_003 :
    packedBlock 49152 14 = 580292780927708037312937984 := by decide

theorem packedBlock_004 :
    packedBlock 65536 14 = 1270273980855188006541573750784 := by decide

theorem packedBlock_005 :
    packedBlock 81920 14 = 5071322927482901751138048016384 := by decide

theorem packedBlock_006 :
    packedBlock 98304 14 = 1663492833280194576655581184 := by decide

theorem packedBlock_007 :
    packedBlock 114688 14 = 19017569765084036447891183632384 := by decide

theorem packedBlock_008 :
    packedBlock 131072 14 = 991328960394979644600745984 := by decide

theorem packedBlock_009 :
    packedBlock 147456 14 = 19018532072556733523429382160384 := by decide

end BaseREhrhart
