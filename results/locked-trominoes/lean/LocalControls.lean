import CatalogCertificate

namespace LockedTromino

/-! Corruption controls exercise the shortcut obligations, not just the fallback. -/
private def line : List Cell := [(0,0),(1,0),(2,0)]
private def beside : List Cell := [(0,1),(1,1),(2,1)]
private def oneEntry : List EntryData := [⟨line,[]⟩]
private def oneTiles := EntryTiles (localEntries oneEntry)

example : OwnerPartitionCheck 3 1 oneTiles (tableOwner 1 oneTiles [0,0,0]) := by decide +kernel
example : EdgeCoverCheck (localEntries oneEntry) (tableOwner 1 oneTiles [0,0,0]) 0 0 3 1 := by decide +kernel

/-- Both legal triples have been assigned to the same owner: rejected. -/
example : ¬ OwnerPartitionCheck 3 2 [line,beside] (tableOwner 2 [line,beside] [0,0,0,0,0,0]) := by decide +kernel

/-- An interacting neighbor was omitted from the links: the cover rejects it. -/
example : ¬ EdgeCoverCheck [⟨line,[]⟩] (tableOwner 2 [line,beside] [0,1,0,1,0,1]) 0 0 3 2 := by decide +kernel

/-- The proposed translation does not match the actual pair: rejected. -/
example : ¬ MatchLink (fun _ => (line,beside)) line ⟨beside,0,(1,0),false⟩ := by decide +kernel

/-- The interacting 3-by-2 rectangle has an alternative two-tile split. -/
example : ¬ SubsetPairCheck line beside := by decide +kernel

#print axioms localCheckedBlock
#print axioms localSeam_rigid
#print axioms catalogLinks_sound
#print axioms subsetPairCheck_sound

end LockedTromino
