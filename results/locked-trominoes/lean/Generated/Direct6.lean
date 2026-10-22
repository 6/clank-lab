import Generated.Catalog

namespace LockedTromino.Witnesses
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def Direct6_b0_entries : List EntryData := [
  ⟨[(0,0),(0,1),(1,0)],[⟨[(0,2),(0,3),(0,4)],17,(0,0),false⟩,⟨[(1,1),(1,2),(2,2)],23,(0,0),false⟩,⟨[(2,0),(2,1),(3,1)],27,(0,0),false⟩]⟩,
  ⟨[(0,2),(0,3),(0,4)],[⟨[(0,0),(0,1),(1,0)],17,(0,0),true⟩,⟨[(1,1),(1,2),(2,2)],88,(0,1),false⟩,⟨[(1,3),(1,4),(2,3)],8,(0,2),false⟩]⟩,
  ⟨[(1,1),(1,2),(2,2)],[⟨[(0,0),(0,1),(1,0)],23,(0,0),true⟩,⟨[(0,2),(0,3),(0,4)],88,(0,1),true⟩,⟨[(1,3),(1,4),(2,3)],31,(1,1),false⟩,⟨[(2,0),(2,1),(3,1)],97,(1,0),false⟩,⟨[(3,2),(3,3),(4,3)],46,(1,1),false⟩]⟩,
  ⟨[(1,3),(1,4),(2,3)],[⟨[(0,2),(0,3),(0,4)],8,(0,2),true⟩,⟨[(1,1),(1,2),(2,2)],31,(1,1),true⟩,⟨[(2,4),(3,4),(4,4)],25,(1,3),false⟩,⟨[(3,2),(3,3),(4,3)],94,(1,2),false⟩]⟩,
  ⟨[(2,0),(2,1),(3,1)],[⟨[(0,0),(0,1),(1,0)],27,(0,0),true⟩,⟨[(1,1),(1,2),(2,2)],97,(1,0),true⟩,⟨[(3,0),(4,0),(5,0)],34,(2,0),false⟩,⟨[(3,2),(3,3),(4,3)],37,(2,0),false⟩,⟨[(4,1),(4,2),(5,1)],45,(2,0),false⟩]⟩,
  ⟨[(2,4),(3,4),(4,4)],[⟨[(1,3),(1,4),(2,3)],25,(1,3),true⟩,⟨[(3,2),(3,3),(4,3)],148,(2,2),false⟩,⟨[(5,2),(5,3),(5,4)],152,(2,2),false⟩]⟩,
  ⟨[(3,0),(4,0),(5,0)],[⟨[(2,0),(2,1),(3,1)],34,(2,0),true⟩,⟨[(4,1),(4,2),(5,1)],74,(3,0),false⟩]⟩,
  ⟨[(3,2),(3,3),(4,3)],[⟨[(1,1),(1,2),(2,2)],46,(1,1),true⟩,⟨[(1,3),(1,4),(2,3)],94,(1,2),true⟩,⟨[(2,0),(2,1),(3,1)],37,(2,0),true⟩,⟨[(2,4),(3,4),(4,4)],148,(2,2),true⟩,⟨[(4,1),(4,2),(5,1)],96,(3,1),false⟩,⟨[(5,2),(5,3),(5,4)],41,(3,2),false⟩]⟩,
  ⟨[(4,1),(4,2),(5,1)],[⟨[(2,0),(2,1),(3,1)],45,(2,0),true⟩,⟨[(3,0),(4,0),(5,0)],74,(3,0),true⟩,⟨[(3,2),(3,3),(4,3)],96,(3,1),true⟩,⟨[(5,2),(5,3),(5,4)],21,(4,1),false⟩]⟩,
  ⟨[(5,2),(5,3),(5,4)],[⟨[(2,4),(3,4),(4,4)],152,(2,2),true⟩,⟨[(3,2),(3,3),(4,3)],41,(3,2),true⟩,⟨[(4,1),(4,2),(5,1)],21,(4,1),true⟩]⟩,
]
theorem Direct6_b0_entries_match : CatalogLinksCheck catalog Direct6_b0_entries := by decide +kernel
theorem Direct6_b0_entries_links : CertifiedLinks (localEntries Direct6_b0_entries) :=
  catalogLinks_sound catalog_sound Direct6_b0_entries_match

def Direct6_b0_tiles := EntryTiles (localEntries Direct6_b0_entries)
def Direct6_b0_owner : Cell → List Cell := tableOwner 5 Direct6_b0_tiles [0,0,1,1,1,0,2,2,3,3,4,4,2,3,5,6,4,7,7,5,6,8,8,7,5,6,8,9,9,9]
theorem Direct6_b0_partition : OwnerPartitionCheck 6 5 Direct6_b0_tiles Direct6_b0_owner := by decide +kernel
theorem Direct6_b0_cover : EdgeCoverCheck (localEntries Direct6_b0_entries) Direct6_b0_owner 0 0 6 5 := by decide +kernel
def Direct6_b0 : RigidBlock 6 5 :=
  localCheckedBlock Direct6_b0_partition Direct6_b0_entries_links Direct6_b0_cover


end LockedTromino.Witnesses
