import Generated.Catalog

namespace LockedTromino.Witnesses
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def Width6_b0_entries : List EntryData := [
  ⟨[(0,0),(1,0),(1,1)],[⟨[(0,1),(0,2),(0,3)],50,(0,0),false⟩,⟨[(1,2),(1,3),(2,2)],56,(0,0),false⟩,⟨[(2,0),(2,1),(3,0)],61,(0,0),false⟩]⟩,
  ⟨[(0,1),(0,2),(0,3)],[⟨[(0,0),(1,0),(1,1)],50,(0,0),true⟩,⟨[(0,4),(0,5),(1,4)],1,(0,1),false⟩,⟨[(1,2),(1,3),(2,2)],8,(0,1),false⟩]⟩,
  ⟨[(0,4),(0,5),(1,4)],[⟨[(0,1),(0,2),(0,3)],1,(0,1),true⟩,⟨[(1,2),(1,3),(2,2)],133,(0,2),false⟩,⟨[(1,5),(2,5),(3,5)],25,(0,4),false⟩,⟨[(2,3),(2,4),(3,3)],93,(0,3),false⟩]⟩,
  ⟨[(1,2),(1,3),(2,2)],[⟨[(0,0),(1,0),(1,1)],56,(0,0),true⟩,⟨[(0,1),(0,2),(0,3)],8,(0,1),true⟩,⟨[(0,4),(0,5),(1,4)],133,(0,2),true⟩,⟨[(2,0),(2,1),(3,0)],133,(1,0),false⟩,⟨[(2,3),(2,4),(3,3)],22,(1,2),false⟩,⟨[(3,1),(3,2),(4,1)],93,(1,1),false⟩]⟩,
  ⟨[(1,5),(2,5),(3,5)],[⟨[(0,4),(0,5),(1,4)],25,(0,4),true⟩,⟨[(2,3),(2,4),(3,3)],147,(1,3),false⟩,⟨[(3,4),(4,4),(4,5)],126,(1,4),false⟩]⟩,
  ⟨[(2,0),(2,1),(3,0)],[⟨[(0,0),(1,0),(1,1)],61,(0,0),true⟩,⟨[(1,2),(1,3),(2,2)],133,(1,0),true⟩,⟨[(3,1),(3,2),(4,1)],22,(2,0),false⟩,⟨[(4,0),(5,0),(5,1)],28,(2,0),false⟩]⟩,
  ⟨[(2,3),(2,4),(3,3)],[⟨[(0,4),(0,5),(1,4)],93,(0,3),true⟩,⟨[(1,2),(1,3),(2,2)],22,(1,2),true⟩,⟨[(1,5),(2,5),(3,5)],147,(1,3),true⟩,⟨[(3,1),(3,2),(4,1)],133,(2,1),false⟩,⟨[(3,4),(4,4),(4,5)],24,(2,3),false⟩,⟨[(4,2),(4,3),(5,2)],93,(2,2),false⟩]⟩,
  ⟨[(3,1),(3,2),(4,1)],[⟨[(1,2),(1,3),(2,2)],93,(1,1),true⟩,⟨[(2,0),(2,1),(3,0)],22,(2,0),true⟩,⟨[(2,3),(2,4),(3,3)],133,(2,1),true⟩,⟨[(4,0),(5,0),(5,1)],90,(3,0),false⟩,⟨[(4,2),(4,3),(5,2)],22,(3,1),false⟩]⟩,
  ⟨[(3,4),(4,4),(4,5)],[⟨[(1,5),(2,5),(3,5)],126,(1,4),true⟩,⟨[(2,3),(2,4),(3,3)],24,(2,3),true⟩,⟨[(4,2),(4,3),(5,2)],143,(3,2),false⟩,⟨[(5,3),(5,4),(5,5)],122,(3,3),false⟩]⟩,
  ⟨[(4,0),(5,0),(5,1)],[⟨[(2,0),(2,1),(3,0)],28,(2,0),true⟩,⟨[(3,1),(3,2),(4,1)],90,(3,0),true⟩,⟨[(4,2),(4,3),(5,2)],51,(4,0),false⟩]⟩,
  ⟨[(4,2),(4,3),(5,2)],[⟨[(2,3),(2,4),(3,3)],93,(2,2),true⟩,⟨[(3,1),(3,2),(4,1)],22,(3,1),true⟩,⟨[(3,4),(4,4),(4,5)],143,(3,2),true⟩,⟨[(4,0),(5,0),(5,1)],51,(4,0),true⟩,⟨[(5,3),(5,4),(5,5)],21,(4,2),false⟩]⟩,
  ⟨[(5,3),(5,4),(5,5)],[⟨[(3,4),(4,4),(4,5)],122,(3,3),true⟩,⟨[(4,2),(4,3),(5,2)],21,(4,2),true⟩]⟩,
]
theorem Width6_b0_entries_match : CatalogLinksCheck catalog Width6_b0_entries := by decide +kernel
theorem Width6_b0_entries_links : CertifiedLinks (localEntries Width6_b0_entries) :=
  catalogLinks_sound catalog_sound Width6_b0_entries_match

def Width6_b0_tiles := EntryTiles (localEntries Width6_b0_entries)
def Width6_b0_owner : Cell → List Cell := tableOwner 6 Width6_b0_tiles [0,1,1,1,2,2,0,0,3,3,2,4,5,5,3,6,6,4,5,7,7,6,8,4,9,7,10,10,8,8,9,9,10,11,11,11]
theorem Width6_b0_partition : OwnerPartitionCheck 6 6 Width6_b0_tiles Width6_b0_owner := by decide +kernel
theorem Width6_b0_cover : EdgeCoverCheck (localEntries Width6_b0_entries) Width6_b0_owner 0 0 6 6 := by decide +kernel
def Width6_b0 : RigidBlock 6 6 :=
  localCheckedBlock Width6_b0_partition Width6_b0_entries_links Width6_b0_cover

def Width6_b1_entries : List EntryData := [
  ⟨[(0,0),(1,0),(2,0)],[⟨[(0,1),(0,2),(0,3)],70,(0,0),false⟩,⟨[(1,1),(1,2),(2,2)],75,(0,0),false⟩,⟨[(2,1),(3,0),(3,1)],79,(0,0),false⟩]⟩,
  ⟨[(0,1),(0,2),(0,3)],[⟨[(0,0),(1,0),(2,0)],70,(0,0),true⟩,⟨[(0,4),(1,3),(1,4)],3,(0,1),false⟩,⟨[(1,1),(1,2),(2,2)],6,(0,1),false⟩]⟩,
  ⟨[(0,4),(1,3),(1,4)],[⟨[(0,1),(0,2),(0,3)],3,(0,1),true⟩,⟨[(0,5),(1,5),(2,5)],102,(0,3),false⟩,⟨[(1,1),(1,2),(2,2)],155,(0,1),false⟩,⟨[(2,3),(2,4),(3,4)],111,(0,3),false⟩]⟩,
  ⟨[(0,5),(1,5),(2,5)],[⟨[(0,4),(1,3),(1,4)],102,(0,3),true⟩,⟨[(2,3),(2,4),(3,4)],150,(0,3),false⟩,⟨[(3,5),(4,4),(4,5)],131,(0,4),false⟩]⟩,
  ⟨[(1,1),(1,2),(2,2)],[⟨[(0,0),(1,0),(2,0)],75,(0,0),true⟩,⟨[(0,1),(0,2),(0,3)],6,(0,1),true⟩,⟨[(0,4),(1,3),(1,4)],155,(0,1),true⟩,⟨[(2,1),(3,0),(3,1)],98,(1,0),false⟩,⟨[(2,3),(2,4),(3,4)],37,(1,1),false⟩,⟨[(3,2),(3,3),(4,3)],46,(1,1),false⟩]⟩,
  ⟨[(2,1),(3,0),(3,1)],[⟨[(0,0),(1,0),(2,0)],79,(0,0),true⟩,⟨[(1,1),(1,2),(2,2)],98,(1,0),true⟩,⟨[(3,2),(3,3),(4,3)],106,(2,0),false⟩,⟨[(4,0),(4,1),(4,2)],110,(2,0),false⟩]⟩,
  ⟨[(2,3),(2,4),(3,4)],[⟨[(0,4),(1,3),(1,4)],111,(0,3),true⟩,⟨[(0,5),(1,5),(2,5)],150,(0,3),true⟩,⟨[(1,1),(1,2),(2,2)],37,(1,1),true⟩,⟨[(3,2),(3,3),(4,3)],97,(2,2),false⟩,⟨[(3,5),(4,4),(4,5)],38,(2,3),false⟩]⟩,
  ⟨[(3,2),(3,3),(4,3)],[⟨[(1,1),(1,2),(2,2)],46,(1,1),true⟩,⟨[(2,1),(3,0),(3,1)],106,(2,0),true⟩,⟨[(2,3),(2,4),(3,4)],97,(2,2),true⟩,⟨[(3,5),(4,4),(4,5)],33,(3,2),false⟩,⟨[(4,0),(4,1),(4,2)],137,(3,0),false⟩,⟨[(5,2),(5,3),(5,4)],41,(3,2),false⟩]⟩,
  ⟨[(3,5),(4,4),(4,5)],[⟨[(0,5),(1,5),(2,5)],131,(0,4),true⟩,⟨[(2,3),(2,4),(3,4)],38,(2,3),true⟩,⟨[(3,2),(3,3),(4,3)],33,(3,2),true⟩,⟨[(5,2),(5,3),(5,4)],157,(3,2),false⟩,⟨[(5,5),(6,5),(7,5)],119,(3,4),false⟩]⟩,
  ⟨[(4,0),(4,1),(4,2)],[⟨[(2,1),(3,0),(3,1)],110,(2,0),true⟩,⟨[(3,2),(3,3),(4,3)],137,(3,0),true⟩,⟨[(5,0),(6,0),(7,0)],7,(4,0),false⟩,⟨[(5,1),(6,1),(6,2)],10,(4,0),false⟩,⟨[(5,2),(5,3),(5,4)],12,(4,0),false⟩]⟩,
  ⟨[(5,0),(6,0),(7,0)],[⟨[(4,0),(4,1),(4,2)],7,(4,0),true⟩,⟨[(5,1),(6,1),(6,2)],71,(5,0),false⟩,⟨[(7,1),(8,0),(8,1)],79,(5,0),false⟩]⟩,
  ⟨[(5,1),(6,1),(6,2)],[⟨[(4,0),(4,1),(4,2)],10,(4,0),true⟩,⟨[(5,0),(6,0),(7,0)],71,(5,0),true⟩,⟨[(5,2),(5,3),(5,4)],50,(5,1),false⟩,⟨[(6,3),(6,4),(7,3)],56,(5,1),false⟩,⟨[(7,1),(8,0),(8,1)],125,(5,0),false⟩,⟨[(7,2),(8,2),(8,3)],68,(5,1),false⟩]⟩,
  ⟨[(5,2),(5,3),(5,4)],[⟨[(3,2),(3,3),(4,3)],41,(3,2),true⟩,⟨[(3,5),(4,4),(4,5)],157,(3,2),true⟩,⟨[(4,0),(4,1),(4,2)],12,(4,0),true⟩,⟨[(5,1),(6,1),(6,2)],50,(5,1),true⟩,⟨[(5,5),(6,5),(7,5)],5,(5,2),false⟩,⟨[(6,3),(6,4),(7,3)],8,(5,2),false⟩]⟩,
  ⟨[(5,5),(6,5),(7,5)],[⟨[(3,5),(4,4),(4,5)],119,(3,4),true⟩,⟨[(5,2),(5,3),(5,4)],5,(5,2),true⟩,⟨[(6,3),(6,4),(7,3)],147,(5,3),false⟩,⟨[(7,4),(8,4),(8,5)],126,(5,4),false⟩]⟩,
  ⟨[(6,3),(6,4),(7,3)],[⟨[(5,1),(6,1),(6,2)],56,(5,1),true⟩,⟨[(5,2),(5,3),(5,4)],8,(5,2),true⟩,⟨[(5,5),(6,5),(7,5)],147,(5,3),true⟩,⟨[(7,2),(8,2),(8,3)],90,(6,2),false⟩,⟨[(7,4),(8,4),(8,5)],24,(6,3),false⟩]⟩,
  ⟨[(7,1),(8,0),(8,1)],[⟨[(5,0),(6,0),(7,0)],79,(5,0),true⟩,⟨[(5,1),(6,1),(6,2)],125,(5,0),true⟩,⟨[(7,2),(8,2),(8,3)],101,(7,0),false⟩]⟩,
  ⟨[(7,2),(8,2),(8,3)],[⟨[(5,1),(6,1),(6,2)],68,(5,1),true⟩,⟨[(6,3),(6,4),(7,3)],90,(6,2),true⟩,⟨[(7,1),(8,0),(8,1)],101,(7,0),true⟩,⟨[(7,4),(8,4),(8,5)],52,(7,2),false⟩]⟩,
  ⟨[(7,4),(8,4),(8,5)],[⟨[(5,5),(6,5),(7,5)],126,(5,4),true⟩,⟨[(6,3),(6,4),(7,3)],24,(6,3),true⟩,⟨[(7,2),(8,2),(8,3)],52,(7,2),true⟩]⟩,
]
theorem Width6_b1_entries_match : CatalogLinksCheck catalog Width6_b1_entries := by decide +kernel
theorem Width6_b1_entries_links : CertifiedLinks (localEntries Width6_b1_entries) :=
  catalogLinks_sound catalog_sound Width6_b1_entries_match

def Width6_b1_tiles := EntryTiles (localEntries Width6_b1_entries)
def Width6_b1_owner : Cell → List Cell := tableOwner 6 Width6_b1_tiles [0,1,1,1,2,3,0,4,4,2,2,3,0,5,4,6,6,3,5,5,7,7,6,8,9,9,9,7,8,8,10,11,12,12,12,13,10,11,11,14,14,13,10,15,16,14,17,13,15,15,16,16,17,17]
theorem Width6_b1_partition : OwnerPartitionCheck 9 6 Width6_b1_tiles Width6_b1_owner := by decide +kernel
theorem Width6_b1_cover : EdgeCoverCheck (localEntries Width6_b1_entries) Width6_b1_owner 0 0 9 6 := by decide +kernel
def Width6_b1 : RigidBlock 9 6 :=
  localCheckedBlock Width6_b1_partition Width6_b1_entries_links Width6_b1_cover

def Width6_vertical_0_entries : List EntryData := [
  ⟨[(0,0),(1,0),(1,1)],[]⟩,
  ⟨[(0,1),(0,2),(0,3)],[]⟩,
  ⟨[(0,4),(0,5),(1,4)],[]⟩,
  ⟨[(1,2),(1,3),(2,2)],[]⟩,
  ⟨[(1,5),(2,5),(3,5)],[]⟩,
  ⟨[(2,0),(2,1),(3,0)],[]⟩,
  ⟨[(2,3),(2,4),(3,3)],[]⟩,
  ⟨[(3,1),(3,2),(4,1)],[]⟩,
  ⟨[(3,4),(4,4),(4,5)],[]⟩,
  ⟨[(4,0),(5,0),(5,1)],[⟨[(6,0),(7,0),(7,1)],62,(4,0),false⟩,⟨[(6,1),(6,2),(6,3)],64,(4,0),false⟩]⟩,
  ⟨[(4,2),(4,3),(5,2)],[⟨[(6,1),(6,2),(6,3)],92,(4,1),false⟩]⟩,
  ⟨[(5,3),(5,4),(5,5)],[⟨[(6,1),(6,2),(6,3)],132,(5,1),false⟩,⟨[(6,4),(6,5),(7,4)],8,(5,3),false⟩]⟩,
]
theorem Width6_vertical_0_entries_match : CatalogLinksCheck catalog Width6_vertical_0_entries := by decide +kernel
theorem Width6_vertical_0_entries_links : CertifiedLinks (localEntries Width6_vertical_0_entries) :=
  catalogLinks_sound catalog_sound Width6_vertical_0_entries_match

theorem Width6_vertical_0_same : EntryTiles (localEntries Width6_vertical_0_entries) = Width6_b0_tiles := by rfl
theorem Width6_vertical_0_cover : EdgeCoverCheck (localEntries Width6_vertical_0_entries)
    (shiftOwner (6,0) Width6_b0_owner) 6 0 6 6 := by decide +kernel
theorem Width6_vertical_0 : ∀ A B, Width6_b0.tiles A → Width6_b0.tiles B → Rigid A (Shift (6,0) B) := by
  have hp := localSeam_rigid (h := 6) (w := 6)
    (Width6_vertical_0_same.symm ▸ Width6_b0.partition) Width6_b0_partition
    Width6_vertical_0_entries_links Width6_vertical_0_cover
    (side_disjoint 6 6 6 6).1
  rw [Width6_vertical_0_same] at hp
  exact hp

def Width6_vertical_1_entries : List EntryData := [
  ⟨[(0,0),(1,0),(1,1)],[]⟩,
  ⟨[(0,1),(0,2),(0,3)],[]⟩,
  ⟨[(0,4),(0,5),(1,4)],[]⟩,
  ⟨[(1,2),(1,3),(2,2)],[]⟩,
  ⟨[(1,5),(2,5),(3,5)],[]⟩,
  ⟨[(2,0),(2,1),(3,0)],[]⟩,
  ⟨[(2,3),(2,4),(3,3)],[]⟩,
  ⟨[(3,1),(3,2),(4,1)],[]⟩,
  ⟨[(3,4),(4,4),(4,5)],[]⟩,
  ⟨[(4,0),(5,0),(5,1)],[⟨[(6,0),(7,0),(8,0)],63,(4,0),false⟩,⟨[(6,1),(6,2),(6,3)],64,(4,0),false⟩]⟩,
  ⟨[(4,2),(4,3),(5,2)],[⟨[(6,1),(6,2),(6,3)],92,(4,1),false⟩]⟩,
  ⟨[(5,3),(5,4),(5,5)],[⟨[(6,1),(6,2),(6,3)],132,(5,1),false⟩,⟨[(6,4),(7,3),(7,4)],9,(5,3),false⟩,⟨[(6,5),(7,5),(8,5)],16,(5,3),false⟩]⟩,
]
theorem Width6_vertical_1_entries_match : CatalogLinksCheck catalog Width6_vertical_1_entries := by decide +kernel
theorem Width6_vertical_1_entries_links : CertifiedLinks (localEntries Width6_vertical_1_entries) :=
  catalogLinks_sound catalog_sound Width6_vertical_1_entries_match

theorem Width6_vertical_1_same : EntryTiles (localEntries Width6_vertical_1_entries) = Width6_b0_tiles := by rfl
theorem Width6_vertical_1_cover : EdgeCoverCheck (localEntries Width6_vertical_1_entries)
    (shiftOwner (6,0) Width6_b1_owner) 6 0 9 6 := by decide +kernel
theorem Width6_vertical_1 : ∀ A B, Width6_b0.tiles A → Width6_b1.tiles B → Rigid A (Shift (6,0) B) := by
  have hp := localSeam_rigid (h := 6) (w := 6)
    (Width6_vertical_1_same.symm ▸ Width6_b0.partition) Width6_b1_partition
    Width6_vertical_1_entries_links Width6_vertical_1_cover
    (side_disjoint 6 6 9 6).1
  rw [Width6_vertical_1_same] at hp
  exact hp

def Width6_vertical_2_entries : List EntryData := [
  ⟨[(0,0),(1,0),(2,0)],[]⟩,
  ⟨[(0,1),(0,2),(0,3)],[]⟩,
  ⟨[(0,4),(1,3),(1,4)],[]⟩,
  ⟨[(0,5),(1,5),(2,5)],[]⟩,
  ⟨[(1,1),(1,2),(2,2)],[]⟩,
  ⟨[(2,1),(3,0),(3,1)],[]⟩,
  ⟨[(2,3),(2,4),(3,4)],[]⟩,
  ⟨[(3,2),(3,3),(4,3)],[]⟩,
  ⟨[(3,5),(4,4),(4,5)],[]⟩,
  ⟨[(4,0),(4,1),(4,2)],[]⟩,
  ⟨[(5,0),(6,0),(7,0)],[]⟩,
  ⟨[(5,1),(6,1),(6,2)],[]⟩,
  ⟨[(5,2),(5,3),(5,4)],[]⟩,
  ⟨[(5,5),(6,5),(7,5)],[]⟩,
  ⟨[(6,3),(6,4),(7,3)],[]⟩,
  ⟨[(7,1),(8,0),(8,1)],[⟨[(9,0),(10,0),(10,1)],112,(7,0),false⟩,⟨[(9,1),(9,2),(9,3)],114,(7,0),false⟩]⟩,
  ⟨[(7,2),(8,2),(8,3)],[⟨[(9,1),(9,2),(9,3)],122,(7,1),false⟩]⟩,
  ⟨[(7,4),(8,4),(8,5)],[⟨[(9,4),(9,5),(10,4)],61,(7,4),false⟩]⟩,
]
theorem Width6_vertical_2_entries_match : CatalogLinksCheck catalog Width6_vertical_2_entries := by decide +kernel
theorem Width6_vertical_2_entries_links : CertifiedLinks (localEntries Width6_vertical_2_entries) :=
  catalogLinks_sound catalog_sound Width6_vertical_2_entries_match

theorem Width6_vertical_2_same : EntryTiles (localEntries Width6_vertical_2_entries) = Width6_b1_tiles := by rfl
theorem Width6_vertical_2_cover : EdgeCoverCheck (localEntries Width6_vertical_2_entries)
    (shiftOwner (9,0) Width6_b0_owner) 9 0 6 6 := by decide +kernel
theorem Width6_vertical_2 : ∀ A B, Width6_b1.tiles A → Width6_b0.tiles B → Rigid A (Shift (9,0) B) := by
  have hp := localSeam_rigid (h := 9) (w := 6)
    (Width6_vertical_2_same.symm ▸ Width6_b1.partition) Width6_b0_partition
    Width6_vertical_2_entries_links Width6_vertical_2_cover
    (side_disjoint 9 6 6 6).1
  rw [Width6_vertical_2_same] at hp
  exact hp

def Width6_vertical_3_entries : List EntryData := [
  ⟨[(0,0),(1,0),(2,0)],[]⟩,
  ⟨[(0,1),(0,2),(0,3)],[]⟩,
  ⟨[(0,4),(1,3),(1,4)],[]⟩,
  ⟨[(0,5),(1,5),(2,5)],[]⟩,
  ⟨[(1,1),(1,2),(2,2)],[]⟩,
  ⟨[(2,1),(3,0),(3,1)],[]⟩,
  ⟨[(2,3),(2,4),(3,4)],[]⟩,
  ⟨[(3,2),(3,3),(4,3)],[]⟩,
  ⟨[(3,5),(4,4),(4,5)],[]⟩,
  ⟨[(4,0),(4,1),(4,2)],[]⟩,
  ⟨[(5,0),(6,0),(7,0)],[]⟩,
  ⟨[(5,1),(6,1),(6,2)],[]⟩,
  ⟨[(5,2),(5,3),(5,4)],[]⟩,
  ⟨[(5,5),(6,5),(7,5)],[]⟩,
  ⟨[(6,3),(6,4),(7,3)],[]⟩,
  ⟨[(7,1),(8,0),(8,1)],[⟨[(9,0),(10,0),(11,0)],113,(7,0),false⟩,⟨[(9,1),(9,2),(9,3)],114,(7,0),false⟩]⟩,
  ⟨[(7,2),(8,2),(8,3)],[⟨[(9,1),(9,2),(9,3)],122,(7,1),false⟩]⟩,
  ⟨[(7,4),(8,4),(8,5)],[⟨[(9,4),(10,3),(10,4)],125,(7,3),false⟩,⟨[(9,5),(10,5),(11,5)],69,(7,4),false⟩]⟩,
]
theorem Width6_vertical_3_entries_match : CatalogLinksCheck catalog Width6_vertical_3_entries := by decide +kernel
theorem Width6_vertical_3_entries_links : CertifiedLinks (localEntries Width6_vertical_3_entries) :=
  catalogLinks_sound catalog_sound Width6_vertical_3_entries_match

theorem Width6_vertical_3_same : EntryTiles (localEntries Width6_vertical_3_entries) = Width6_b1_tiles := by rfl
theorem Width6_vertical_3_cover : EdgeCoverCheck (localEntries Width6_vertical_3_entries)
    (shiftOwner (9,0) Width6_b1_owner) 9 0 9 6 := by decide +kernel
theorem Width6_vertical_3 : ∀ A B, Width6_b1.tiles A → Width6_b1.tiles B → Rigid A (Shift (9,0) B) := by
  have hp := localSeam_rigid (h := 9) (w := 6)
    (Width6_vertical_3_same.symm ▸ Width6_b1.partition) Width6_b1_partition
    Width6_vertical_3_entries_links Width6_vertical_3_cover
    (side_disjoint 9 6 9 6).1
  rw [Width6_vertical_3_same] at hp
  exact hp

def Width6_palette : VerticalPalette (fun h => h = 6 ∨ h = 9) 6 where
  tiles h := if h = 6 then Width6_b0.tiles else Width6_b1.tiles
  partition := by
    intro h hh
    rcases hh with rfl | rfl
    · exact Width6_b0.partition
    · exact Width6_b1.partition
  internal := by
    intro h hh
    rcases hh with rfl | rfl
    · exact Width6_b0.internal
    · exact Width6_b1.internal
  vertical := by
    intro h k hh hk
    rcases hh with rfl | rfl <;> rcases hk with rfl | rfl
    · exact Width6_vertical_0
    · exact Width6_vertical_1
    · exact Width6_vertical_2
    · exact Width6_vertical_3

end LockedTromino.Witnesses
