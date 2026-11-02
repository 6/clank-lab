import BaseREhrhart.CertificateCore

/-! Kernel-checked finite certificate chunks. -/
set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace BaseREhrhart

theorem packedBlock_020 :
    packedBlock 327680 14 = 214236273576821514351828228112384 := by decide

theorem packedBlock_021 :
    packedBlock 344064 14 = 69726087790461858293343698550784 := by decide

theorem packedBlock_022 :
    packedBlock 360448 14 = 557773254118582290224895920963584 := by decide

theorem packedBlock_023 :
    packedBlock 376832 14 = 19018535699366474135361037533184 := by decide

theorem packedBlock_024 :
    packedBlock 393216 14 = 411994497738896888681249042857984 := by decide

theorem packedBlock_025 :
    packedBlock 409600 14 = 476641611305877496509309710761984 := by decide

theorem packedBlock_026 :
    packedBlock 425984 14 = 163533396402436659784786414403584 := by decide

theorem packedBlock_027 :
    packedBlock 442368 14 = 1104132519725795215956567742480384 := by decide

theorem packedBlock_028 :
    packedBlock 458752 14 = 49443297375384535298061903069184 := by decide

theorem packedBlock_029 :
    packedBlock 475136 14 = 858209029846502383945134987280384 := by decide

end BaseREhrhart
