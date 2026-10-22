import Certificate

/-! Dependency audit. Standard logical axioms may occur; `sorryAx` must not.
The conditional interface theorem is included here; the closed theorem is
audited separately in Generated/Universal.lean. -/
#print axioms LockedTromino.noEdges_rigid
#print axioms LockedTromino.edge_boxes
#print axioms LockedTromino.rectangular_assembly
#print axioms LockedTromino.locked_of_rigid
#print axioms LockedTromino.pairCheck_sound
#print axioms LockedTromino.blockCheck_tiling
#print axioms LockedTromino.blockCheck_rigid
#print axioms LockedTromino.seamCheck_sound
#print axioms LockedTromino.universal_of_proposed_certificate
