import ABC.Hand
import ABC.S4.Final

/-! The KAM input (K″), `ABC.KAMInput`, from stage 4's `HAND_KAM_curves_proof`. -/

namespace ABC.S4

theorem kam_input : KAMInput := fun p hp δ hδ => HAND_KAM_curves_proof p hp δ hδ

end ABC.S4
