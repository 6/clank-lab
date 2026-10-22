import Generated.Catalog

namespace LockedTromino.Witnesses
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def Width5_b0_entries : List EntryData := [
  ⟨[(0,0),(0,1),(0,2)],[⟨[(0,3),(1,2),(1,3)],3,(0,0),false⟩,⟨[(1,0),(2,0),(3,0)],7,(0,0),false⟩,⟨[(1,1),(2,1),(2,2)],10,(0,0),false⟩]⟩,
  ⟨[(0,3),(1,2),(1,3)],[⟨[(0,0),(0,1),(0,2)],3,(0,0),true⟩,⟨[(0,4),(1,4),(2,4)],102,(0,2),false⟩,⟨[(1,1),(2,1),(2,2)],138,(0,1),false⟩,⟨[(2,3),(3,3),(3,4)],118,(0,2),false⟩]⟩,
  ⟨[(0,4),(1,4),(2,4)],[⟨[(0,3),(1,2),(1,3)],102,(0,2),true⟩,⟨[(2,3),(3,3),(3,4)],126,(0,3),false⟩]⟩,
  ⟨[(1,0),(2,0),(3,0)],[⟨[(0,0),(0,1),(0,2)],7,(0,0),true⟩,⟨[(1,1),(2,1),(2,2)],71,(1,0),false⟩,⟨[(3,1),(4,0),(4,1)],79,(1,0),false⟩]⟩,
  ⟨[(1,1),(2,1),(2,2)],[⟨[(0,0),(0,1),(0,2)],10,(0,0),true⟩,⟨[(0,3),(1,2),(1,3)],138,(0,1),true⟩,⟨[(1,0),(2,0),(3,0)],71,(1,0),true⟩,⟨[(2,3),(3,3),(3,4)],59,(1,1),false⟩,⟨[(3,1),(4,0),(4,1)],125,(1,0),false⟩,⟨[(3,2),(4,2),(5,2)],69,(1,1),false⟩]⟩,
  ⟨[(2,3),(3,3),(3,4)],[⟨[(0,3),(1,2),(1,3)],118,(0,2),true⟩,⟨[(0,4),(1,4),(2,4)],126,(0,3),true⟩,⟨[(1,1),(2,1),(2,2)],59,(1,1),true⟩,⟨[(3,2),(4,2),(5,2)],121,(2,2),false⟩,⟨[(4,3),(4,4),(5,3)],61,(2,3),false⟩]⟩,
  ⟨[(3,1),(4,0),(4,1)],[⟨[(1,0),(2,0),(3,0)],79,(1,0),true⟩,⟨[(1,1),(2,1),(2,2)],125,(1,0),true⟩,⟨[(3,2),(4,2),(5,2)],102,(3,0),false⟩,⟨[(5,0),(5,1),(6,1)],111,(3,0),false⟩]⟩,
  ⟨[(3,2),(4,2),(5,2)],[⟨[(1,1),(2,1),(2,2)],69,(1,1),true⟩,⟨[(2,3),(3,3),(3,4)],121,(2,2),true⟩,⟨[(3,1),(4,0),(4,1)],102,(3,0),true⟩,⟨[(4,3),(4,4),(5,3)],74,(3,2),false⟩,⟨[(5,0),(5,1),(6,1)],150,(3,0),false⟩,⟨[(6,2),(6,3),(7,3)],84,(3,2),false⟩]⟩,
  ⟨[(4,3),(4,4),(5,3)],[⟨[(2,3),(3,3),(3,4)],61,(2,3),true⟩,⟨[(3,2),(4,2),(5,2)],74,(3,2),true⟩,⟨[(5,4),(6,4),(7,4)],25,(4,3),false⟩,⟨[(6,2),(6,3),(7,3)],94,(4,2),false⟩]⟩,
  ⟨[(5,0),(5,1),(6,1)],[⟨[(3,1),(4,0),(4,1)],111,(3,0),true⟩,⟨[(3,2),(4,2),(5,2)],150,(3,0),true⟩,⟨[(6,0),(7,0),(8,0)],34,(5,0),false⟩,⟨[(6,2),(6,3),(7,3)],37,(5,0),false⟩,⟨[(7,1),(7,2),(8,1)],45,(5,0),false⟩]⟩,
  ⟨[(5,4),(6,4),(7,4)],[⟨[(4,3),(4,4),(5,3)],25,(4,3),true⟩,⟨[(6,2),(6,3),(7,3)],148,(5,2),false⟩,⟨[(8,2),(8,3),(8,4)],152,(5,2),false⟩]⟩,
  ⟨[(6,0),(7,0),(8,0)],[⟨[(5,0),(5,1),(6,1)],34,(5,0),true⟩,⟨[(7,1),(7,2),(8,1)],74,(6,0),false⟩]⟩,
  ⟨[(6,2),(6,3),(7,3)],[⟨[(3,2),(4,2),(5,2)],84,(3,2),true⟩,⟨[(4,3),(4,4),(5,3)],94,(4,2),true⟩,⟨[(5,0),(5,1),(6,1)],37,(5,0),true⟩,⟨[(5,4),(6,4),(7,4)],148,(5,2),true⟩,⟨[(7,1),(7,2),(8,1)],96,(6,1),false⟩,⟨[(8,2),(8,3),(8,4)],41,(6,2),false⟩]⟩,
  ⟨[(7,1),(7,2),(8,1)],[⟨[(5,0),(5,1),(6,1)],45,(5,0),true⟩,⟨[(6,0),(7,0),(8,0)],74,(6,0),true⟩,⟨[(6,2),(6,3),(7,3)],96,(6,1),true⟩,⟨[(8,2),(8,3),(8,4)],21,(7,1),false⟩]⟩,
  ⟨[(8,2),(8,3),(8,4)],[⟨[(5,4),(6,4),(7,4)],152,(5,2),true⟩,⟨[(6,2),(6,3),(7,3)],41,(6,2),true⟩,⟨[(7,1),(7,2),(8,1)],21,(7,1),true⟩]⟩,
]
theorem Width5_b0_entries_match : CatalogLinksCheck catalog Width5_b0_entries := by decide +kernel
theorem Width5_b0_entries_links : CertifiedLinks (localEntries Width5_b0_entries) :=
  catalogLinks_sound catalog_sound Width5_b0_entries_match

def Width5_b0_tiles := EntryTiles (localEntries Width5_b0_entries)
def Width5_b0_owner : Cell → List Cell := tableOwner 5 Width5_b0_tiles [0,0,0,1,2,3,4,1,1,2,3,4,4,5,2,3,6,7,5,5,6,6,7,8,8,9,9,7,8,10,11,9,12,12,10,11,13,13,12,10,11,13,14,14,14]
theorem Width5_b0_partition : OwnerPartitionCheck 9 5 Width5_b0_tiles Width5_b0_owner := by decide +kernel
theorem Width5_b0_cover : EdgeCoverCheck (localEntries Width5_b0_entries) Width5_b0_owner 0 0 9 5 := by decide +kernel
def Width5_b0 : RigidBlock 9 5 :=
  localCheckedBlock Width5_b0_partition Width5_b0_entries_links Width5_b0_cover

def Width5_b1_entries : List EntryData := [
  ⟨[(0,0),(0,1),(0,2)],[⟨[(0,3),(1,2),(1,3)],3,(0,0),false⟩,⟨[(1,0),(2,0),(3,0)],7,(0,0),false⟩,⟨[(1,1),(2,1),(2,2)],10,(0,0),false⟩]⟩,
  ⟨[(0,3),(1,2),(1,3)],[⟨[(0,0),(0,1),(0,2)],3,(0,0),true⟩,⟨[(0,4),(1,4),(2,4)],102,(0,2),false⟩,⟨[(1,1),(2,1),(2,2)],138,(0,1),false⟩,⟨[(2,3),(3,2),(3,3)],117,(0,2),false⟩]⟩,
  ⟨[(0,4),(1,4),(2,4)],[⟨[(0,3),(1,2),(1,3)],102,(0,2),true⟩,⟨[(2,3),(3,2),(3,3)],151,(0,2),false⟩,⟨[(3,4),(4,3),(4,4)],131,(0,3),false⟩]⟩,
  ⟨[(1,0),(2,0),(3,0)],[⟨[(0,0),(0,1),(0,2)],7,(0,0),true⟩,⟨[(1,1),(2,1),(2,2)],71,(1,0),false⟩,⟨[(3,1),(4,0),(4,1)],79,(1,0),false⟩]⟩,
  ⟨[(1,1),(2,1),(2,2)],[⟨[(0,0),(0,1),(0,2)],10,(0,0),true⟩,⟨[(0,3),(1,2),(1,3)],138,(0,1),true⟩,⟨[(1,0),(2,0),(3,0)],71,(1,0),true⟩,⟨[(2,3),(3,2),(3,3)],58,(1,1),false⟩,⟨[(3,1),(4,0),(4,1)],125,(1,0),false⟩]⟩,
  ⟨[(2,3),(3,2),(3,3)],[⟨[(0,3),(1,2),(1,3)],117,(0,2),true⟩,⟨[(0,4),(1,4),(2,4)],151,(0,2),true⟩,⟨[(1,1),(2,1),(2,2)],58,(1,1),true⟩,⟨[(3,1),(4,0),(4,1)],156,(2,0),false⟩,⟨[(3,4),(4,3),(4,4)],107,(2,2),false⟩,⟨[(4,2),(5,1),(5,2)],142,(2,1),false⟩]⟩,
  ⟨[(3,1),(4,0),(4,1)],[⟨[(1,0),(2,0),(3,0)],79,(1,0),true⟩,⟨[(1,1),(2,1),(2,2)],125,(1,0),true⟩,⟨[(2,3),(3,2),(3,3)],156,(2,0),true⟩,⟨[(4,2),(5,1),(5,2)],107,(3,0),false⟩,⟨[(5,0),(6,0),(7,0)],113,(3,0),false⟩]⟩,
  ⟨[(3,4),(4,3),(4,4)],[⟨[(0,4),(1,4),(2,4)],131,(0,3),true⟩,⟨[(2,3),(3,2),(3,3)],107,(2,2),true⟩,⟨[(4,2),(5,1),(5,2)],156,(3,1),false⟩,⟨[(5,3),(5,4),(6,4)],111,(3,3),false⟩]⟩,
  ⟨[(4,2),(5,1),(5,2)],[⟨[(2,3),(3,2),(3,3)],142,(2,1),true⟩,⟨[(3,1),(4,0),(4,1)],107,(3,0),true⟩,⟨[(3,4),(4,3),(4,4)],156,(3,1),true⟩,⟨[(5,0),(6,0),(7,0)],139,(4,0),false⟩,⟨[(5,3),(5,4),(6,4)],106,(4,1),false⟩,⟨[(6,1),(6,2),(6,3)],110,(4,1),false⟩]⟩,
  ⟨[(5,0),(6,0),(7,0)],[⟨[(3,1),(4,0),(4,1)],113,(3,0),true⟩,⟨[(4,2),(5,1),(5,2)],139,(4,0),true⟩,⟨[(6,1),(6,2),(6,3)],73,(5,0),false⟩,⟨[(7,1),(7,2),(8,2)],78,(5,0),false⟩,⟨[(8,0),(8,1),(9,1)],84,(5,0),false⟩]⟩,
  ⟨[(5,3),(5,4),(6,4)],[⟨[(3,4),(4,3),(4,4)],111,(3,3),true⟩,⟨[(4,2),(5,1),(5,2)],106,(4,1),true⟩,⟨[(6,1),(6,2),(6,3)],137,(5,1),false⟩,⟨[(7,3),(7,4),(8,3)],42,(5,3),false⟩]⟩,
  ⟨[(6,1),(6,2),(6,3)],[⟨[(4,2),(5,1),(5,2)],110,(4,1),true⟩,⟨[(5,0),(6,0),(7,0)],73,(5,0),true⟩,⟨[(5,3),(5,4),(6,4)],137,(5,1),true⟩,⟨[(7,1),(7,2),(8,2)],6,(6,1),false⟩,⟨[(7,3),(7,4),(8,3)],13,(6,1),false⟩]⟩,
  ⟨[(7,1),(7,2),(8,2)],[⟨[(5,0),(6,0),(7,0)],78,(5,0),true⟩,⟨[(6,1),(6,2),(6,3)],6,(6,1),true⟩,⟨[(7,3),(7,4),(8,3)],31,(7,1),false⟩,⟨[(8,0),(8,1),(9,1)],97,(7,0),false⟩,⟨[(9,2),(9,3),(10,3)],46,(7,1),false⟩]⟩,
  ⟨[(7,3),(7,4),(8,3)],[⟨[(5,3),(5,4),(6,4)],42,(5,3),true⟩,⟨[(6,1),(6,2),(6,3)],13,(6,1),true⟩,⟨[(7,1),(7,2),(8,2)],31,(7,1),true⟩,⟨[(8,4),(9,4),(10,4)],25,(7,3),false⟩,⟨[(9,2),(9,3),(10,3)],94,(7,2),false⟩]⟩,
  ⟨[(8,0),(8,1),(9,1)],[⟨[(5,0),(6,0),(7,0)],84,(5,0),true⟩,⟨[(7,1),(7,2),(8,2)],97,(7,0),true⟩,⟨[(9,0),(10,0),(11,0)],34,(8,0),false⟩,⟨[(9,2),(9,3),(10,3)],37,(8,0),false⟩,⟨[(10,1),(10,2),(11,1)],45,(8,0),false⟩]⟩,
  ⟨[(8,4),(9,4),(10,4)],[⟨[(7,3),(7,4),(8,3)],25,(7,3),true⟩,⟨[(9,2),(9,3),(10,3)],148,(8,2),false⟩,⟨[(11,2),(11,3),(11,4)],152,(8,2),false⟩]⟩,
  ⟨[(9,0),(10,0),(11,0)],[⟨[(8,0),(8,1),(9,1)],34,(8,0),true⟩,⟨[(10,1),(10,2),(11,1)],74,(9,0),false⟩]⟩,
  ⟨[(9,2),(9,3),(10,3)],[⟨[(7,1),(7,2),(8,2)],46,(7,1),true⟩,⟨[(7,3),(7,4),(8,3)],94,(7,2),true⟩,⟨[(8,0),(8,1),(9,1)],37,(8,0),true⟩,⟨[(8,4),(9,4),(10,4)],148,(8,2),true⟩,⟨[(10,1),(10,2),(11,1)],96,(9,1),false⟩,⟨[(11,2),(11,3),(11,4)],41,(9,2),false⟩]⟩,
  ⟨[(10,1),(10,2),(11,1)],[⟨[(8,0),(8,1),(9,1)],45,(8,0),true⟩,⟨[(9,0),(10,0),(11,0)],74,(9,0),true⟩,⟨[(9,2),(9,3),(10,3)],96,(9,1),true⟩,⟨[(11,2),(11,3),(11,4)],21,(10,1),false⟩]⟩,
  ⟨[(11,2),(11,3),(11,4)],[⟨[(8,4),(9,4),(10,4)],152,(8,2),true⟩,⟨[(9,2),(9,3),(10,3)],41,(9,2),true⟩,⟨[(10,1),(10,2),(11,1)],21,(10,1),true⟩]⟩,
]
theorem Width5_b1_entries_match : CatalogLinksCheck catalog Width5_b1_entries := by decide +kernel
theorem Width5_b1_entries_links : CertifiedLinks (localEntries Width5_b1_entries) :=
  catalogLinks_sound catalog_sound Width5_b1_entries_match

def Width5_b1_tiles := EntryTiles (localEntries Width5_b1_entries)
def Width5_b1_owner : Cell → List Cell := tableOwner 5 Width5_b1_tiles [0,0,0,1,2,3,4,1,1,2,3,4,4,5,2,3,6,5,5,7,6,6,8,7,7,9,8,8,10,10,9,11,11,11,10,9,12,12,13,13,14,14,12,13,15,16,14,17,17,15,16,18,18,17,15,16,18,19,19,19]
theorem Width5_b1_partition : OwnerPartitionCheck 12 5 Width5_b1_tiles Width5_b1_owner := by decide +kernel
theorem Width5_b1_cover : EdgeCoverCheck (localEntries Width5_b1_entries) Width5_b1_owner 0 0 12 5 := by decide +kernel
def Width5_b1 : RigidBlock 12 5 :=
  localCheckedBlock Width5_b1_partition Width5_b1_entries_links Width5_b1_cover

def Width5_vertical_0_entries : List EntryData := [
  ⟨[(0,0),(0,1),(0,2)],[]⟩,
  ⟨[(0,3),(1,2),(1,3)],[]⟩,
  ⟨[(0,4),(1,4),(2,4)],[]⟩,
  ⟨[(1,0),(2,0),(3,0)],[]⟩,
  ⟨[(1,1),(2,1),(2,2)],[]⟩,
  ⟨[(2,3),(3,3),(3,4)],[]⟩,
  ⟨[(3,1),(4,0),(4,1)],[]⟩,
  ⟨[(3,2),(4,2),(5,2)],[]⟩,
  ⟨[(4,3),(4,4),(5,3)],[]⟩,
  ⟨[(5,0),(5,1),(6,1)],[]⟩,
  ⟨[(5,4),(6,4),(7,4)],[]⟩,
  ⟨[(6,0),(7,0),(8,0)],[⟨[(9,0),(9,1),(9,2)],82,(6,0),false⟩]⟩,
  ⟨[(6,2),(6,3),(7,3)],[]⟩,
  ⟨[(7,1),(7,2),(8,1)],[⟨[(9,0),(9,1),(9,2)],92,(7,0),false⟩]⟩,
  ⟨[(8,2),(8,3),(8,4)],[⟨[(9,0),(9,1),(9,2)],132,(8,0),false⟩,⟨[(9,3),(10,2),(10,3)],9,(8,2),false⟩,⟨[(9,4),(10,4),(11,4)],16,(8,2),false⟩]⟩,
]
theorem Width5_vertical_0_entries_match : CatalogLinksCheck catalog Width5_vertical_0_entries := by decide +kernel
theorem Width5_vertical_0_entries_links : CertifiedLinks (localEntries Width5_vertical_0_entries) :=
  catalogLinks_sound catalog_sound Width5_vertical_0_entries_match

theorem Width5_vertical_0_same : EntryTiles (localEntries Width5_vertical_0_entries) = Width5_b0_tiles := by rfl
theorem Width5_vertical_0_cover : EdgeCoverCheck (localEntries Width5_vertical_0_entries)
    (shiftOwner (9,0) Width5_b0_owner) 9 0 9 5 := by decide +kernel
theorem Width5_vertical_0 : ∀ A B, Width5_b0.tiles A → Width5_b0.tiles B → Rigid A (Shift (9,0) B) := by
  have hp := localSeam_rigid (h := 9) (w := 5)
    (Width5_vertical_0_same.symm ▸ Width5_b0.partition) Width5_b0_partition
    Width5_vertical_0_entries_links Width5_vertical_0_cover
    (side_disjoint 9 5 9 5).1
  rw [Width5_vertical_0_same] at hp
  exact hp

def Width5_vertical_1_entries : List EntryData := [
  ⟨[(0,0),(0,1),(0,2)],[]⟩,
  ⟨[(0,3),(1,2),(1,3)],[]⟩,
  ⟨[(0,4),(1,4),(2,4)],[]⟩,
  ⟨[(1,0),(2,0),(3,0)],[]⟩,
  ⟨[(1,1),(2,1),(2,2)],[]⟩,
  ⟨[(2,3),(3,3),(3,4)],[]⟩,
  ⟨[(3,1),(4,0),(4,1)],[]⟩,
  ⟨[(3,2),(4,2),(5,2)],[]⟩,
  ⟨[(4,3),(4,4),(5,3)],[]⟩,
  ⟨[(5,0),(5,1),(6,1)],[]⟩,
  ⟨[(5,4),(6,4),(7,4)],[]⟩,
  ⟨[(6,0),(7,0),(8,0)],[⟨[(9,0),(9,1),(9,2)],82,(6,0),false⟩]⟩,
  ⟨[(6,2),(6,3),(7,3)],[]⟩,
  ⟨[(7,1),(7,2),(8,1)],[⟨[(9,0),(9,1),(9,2)],92,(7,0),false⟩]⟩,
  ⟨[(8,2),(8,3),(8,4)],[⟨[(9,0),(9,1),(9,2)],132,(8,0),false⟩,⟨[(9,3),(10,2),(10,3)],9,(8,2),false⟩,⟨[(9,4),(10,4),(11,4)],16,(8,2),false⟩]⟩,
]
theorem Width5_vertical_1_entries_match : CatalogLinksCheck catalog Width5_vertical_1_entries := by decide +kernel
theorem Width5_vertical_1_entries_links : CertifiedLinks (localEntries Width5_vertical_1_entries) :=
  catalogLinks_sound catalog_sound Width5_vertical_1_entries_match

theorem Width5_vertical_1_same : EntryTiles (localEntries Width5_vertical_1_entries) = Width5_b0_tiles := by rfl
theorem Width5_vertical_1_cover : EdgeCoverCheck (localEntries Width5_vertical_1_entries)
    (shiftOwner (9,0) Width5_b1_owner) 9 0 12 5 := by decide +kernel
theorem Width5_vertical_1 : ∀ A B, Width5_b0.tiles A → Width5_b1.tiles B → Rigid A (Shift (9,0) B) := by
  have hp := localSeam_rigid (h := 9) (w := 5)
    (Width5_vertical_1_same.symm ▸ Width5_b0.partition) Width5_b1_partition
    Width5_vertical_1_entries_links Width5_vertical_1_cover
    (side_disjoint 9 5 12 5).1
  rw [Width5_vertical_1_same] at hp
  exact hp

def Width5_vertical_2_entries : List EntryData := [
  ⟨[(0,0),(0,1),(0,2)],[]⟩,
  ⟨[(0,3),(1,2),(1,3)],[]⟩,
  ⟨[(0,4),(1,4),(2,4)],[]⟩,
  ⟨[(1,0),(2,0),(3,0)],[]⟩,
  ⟨[(1,1),(2,1),(2,2)],[]⟩,
  ⟨[(2,3),(3,2),(3,3)],[]⟩,
  ⟨[(3,1),(4,0),(4,1)],[]⟩,
  ⟨[(3,4),(4,3),(4,4)],[]⟩,
  ⟨[(4,2),(5,1),(5,2)],[]⟩,
  ⟨[(5,0),(6,0),(7,0)],[]⟩,
  ⟨[(5,3),(5,4),(6,4)],[]⟩,
  ⟨[(6,1),(6,2),(6,3)],[]⟩,
  ⟨[(7,1),(7,2),(8,2)],[]⟩,
  ⟨[(7,3),(7,4),(8,3)],[]⟩,
  ⟨[(8,0),(8,1),(9,1)],[]⟩,
  ⟨[(8,4),(9,4),(10,4)],[]⟩,
  ⟨[(9,0),(10,0),(11,0)],[⟨[(12,0),(12,1),(12,2)],82,(9,0),false⟩]⟩,
  ⟨[(9,2),(9,3),(10,3)],[]⟩,
  ⟨[(10,1),(10,2),(11,1)],[⟨[(12,0),(12,1),(12,2)],92,(10,0),false⟩]⟩,
  ⟨[(11,2),(11,3),(11,4)],[⟨[(12,0),(12,1),(12,2)],132,(11,0),false⟩,⟨[(12,3),(13,2),(13,3)],9,(11,2),false⟩,⟨[(12,4),(13,4),(14,4)],16,(11,2),false⟩]⟩,
]
theorem Width5_vertical_2_entries_match : CatalogLinksCheck catalog Width5_vertical_2_entries := by decide +kernel
theorem Width5_vertical_2_entries_links : CertifiedLinks (localEntries Width5_vertical_2_entries) :=
  catalogLinks_sound catalog_sound Width5_vertical_2_entries_match

theorem Width5_vertical_2_same : EntryTiles (localEntries Width5_vertical_2_entries) = Width5_b1_tiles := by rfl
theorem Width5_vertical_2_cover : EdgeCoverCheck (localEntries Width5_vertical_2_entries)
    (shiftOwner (12,0) Width5_b0_owner) 12 0 9 5 := by decide +kernel
theorem Width5_vertical_2 : ∀ A B, Width5_b1.tiles A → Width5_b0.tiles B → Rigid A (Shift (12,0) B) := by
  have hp := localSeam_rigid (h := 12) (w := 5)
    (Width5_vertical_2_same.symm ▸ Width5_b1.partition) Width5_b0_partition
    Width5_vertical_2_entries_links Width5_vertical_2_cover
    (side_disjoint 12 5 9 5).1
  rw [Width5_vertical_2_same] at hp
  exact hp

def Width5_vertical_3_entries : List EntryData := [
  ⟨[(0,0),(0,1),(0,2)],[]⟩,
  ⟨[(0,3),(1,2),(1,3)],[]⟩,
  ⟨[(0,4),(1,4),(2,4)],[]⟩,
  ⟨[(1,0),(2,0),(3,0)],[]⟩,
  ⟨[(1,1),(2,1),(2,2)],[]⟩,
  ⟨[(2,3),(3,2),(3,3)],[]⟩,
  ⟨[(3,1),(4,0),(4,1)],[]⟩,
  ⟨[(3,4),(4,3),(4,4)],[]⟩,
  ⟨[(4,2),(5,1),(5,2)],[]⟩,
  ⟨[(5,0),(6,0),(7,0)],[]⟩,
  ⟨[(5,3),(5,4),(6,4)],[]⟩,
  ⟨[(6,1),(6,2),(6,3)],[]⟩,
  ⟨[(7,1),(7,2),(8,2)],[]⟩,
  ⟨[(7,3),(7,4),(8,3)],[]⟩,
  ⟨[(8,0),(8,1),(9,1)],[]⟩,
  ⟨[(8,4),(9,4),(10,4)],[]⟩,
  ⟨[(9,0),(10,0),(11,0)],[⟨[(12,0),(12,1),(12,2)],82,(9,0),false⟩]⟩,
  ⟨[(9,2),(9,3),(10,3)],[]⟩,
  ⟨[(10,1),(10,2),(11,1)],[⟨[(12,0),(12,1),(12,2)],92,(10,0),false⟩]⟩,
  ⟨[(11,2),(11,3),(11,4)],[⟨[(12,0),(12,1),(12,2)],132,(11,0),false⟩,⟨[(12,3),(13,2),(13,3)],9,(11,2),false⟩,⟨[(12,4),(13,4),(14,4)],16,(11,2),false⟩]⟩,
]
theorem Width5_vertical_3_entries_match : CatalogLinksCheck catalog Width5_vertical_3_entries := by decide +kernel
theorem Width5_vertical_3_entries_links : CertifiedLinks (localEntries Width5_vertical_3_entries) :=
  catalogLinks_sound catalog_sound Width5_vertical_3_entries_match

theorem Width5_vertical_3_same : EntryTiles (localEntries Width5_vertical_3_entries) = Width5_b1_tiles := by rfl
theorem Width5_vertical_3_cover : EdgeCoverCheck (localEntries Width5_vertical_3_entries)
    (shiftOwner (12,0) Width5_b1_owner) 12 0 12 5 := by decide +kernel
theorem Width5_vertical_3 : ∀ A B, Width5_b1.tiles A → Width5_b1.tiles B → Rigid A (Shift (12,0) B) := by
  have hp := localSeam_rigid (h := 12) (w := 5)
    (Width5_vertical_3_same.symm ▸ Width5_b1.partition) Width5_b1_partition
    Width5_vertical_3_entries_links Width5_vertical_3_cover
    (side_disjoint 12 5 12 5).1
  rw [Width5_vertical_3_same] at hp
  exact hp

def Width5_palette : VerticalPalette (fun h => h = 9 ∨ h = 12) 5 where
  tiles h := if h = 9 then Width5_b0.tiles else Width5_b1.tiles
  partition := by
    intro h hh
    rcases hh with rfl | rfl
    · exact Width5_b0.partition
    · exact Width5_b1.partition
  internal := by
    intro h hh
    rcases hh with rfl | rfl
    · exact Width5_b0.internal
    · exact Width5_b1.internal
  vertical := by
    intro h k hh hk
    rcases hh with rfl | rfl <;> rcases hk with rfl | rfl
    · exact Width5_vertical_0
    · exact Width5_vertical_1
    · exact Width5_vertical_2
    · exact Width5_vertical_3

end LockedTromino.Witnesses
