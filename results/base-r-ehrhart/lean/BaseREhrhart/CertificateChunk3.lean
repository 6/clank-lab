import BaseREhrhart.CertificateCore

/-! Kernel-checked finite certificate chunks. -/
set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace BaseREhrhart

theorem packedBlock_030 :
    packedBlock 491520 14 = 830317630254999490388688171433984 := by decide

theorem packedBlock_031 :
    packedBlock 507904 14 = 410726748006771050618306097577984 := by decide

theorem packedBlock_032 :
    packedBlock 524288 13 = 850599243170144235751445670920192 := by decide

theorem packedBlock_033 :
    packedBlock 532480 12 = 567910587932088086099093509636096 := by decide

theorem packedBlock_034 :
    packedBlock 536576 10 = 339731190184358439742052786765824 := by decide

theorem packedBlock_035 :
    packedBlock 537600 7 = 43100230420012843346656627785728 := by decide

theorem packedBlock_036 :
    packedBlock 537728 6 = 53241351805953666384703378161664 := by decide

theorem packedBlock_037 :
    packedBlock 537792 5 = 34226572250791291913556860076032 := by decide

end BaseREhrhart
