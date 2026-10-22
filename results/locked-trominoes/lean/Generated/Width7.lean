import Generated.Catalog

namespace LockedTromino.Witnesses
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def Width7_b0_entries : List EntryData := [
  ⟨[(0,0),(1,0),(1,1)],[⟨[(0,1),(0,2),(0,3)],50,(0,0),false⟩,⟨[(1,2),(2,2),(2,3)],59,(0,0),false⟩,⟨[(2,0),(2,1),(3,0)],61,(0,0),false⟩]⟩,
  ⟨[(0,1),(0,2),(0,3)],[⟨[(0,0),(1,0),(1,1)],50,(0,0),true⟩,⟨[(0,4),(1,3),(1,4)],3,(0,1),false⟩,⟨[(1,2),(2,2),(2,3)],10,(0,1),false⟩]⟩,
  ⟨[(0,4),(1,3),(1,4)],[⟨[(0,1),(0,2),(0,3)],3,(0,1),true⟩,⟨[(0,5),(0,6),(1,6)],100,(0,3),false⟩,⟨[(1,2),(2,2),(2,3)],138,(0,2),false⟩,⟨[(1,5),(2,4),(2,5)],107,(0,3),false⟩]⟩,
  ⟨[(0,5),(0,6),(1,6)],[⟨[(0,4),(1,3),(1,4)],100,(0,3),true⟩,⟨[(1,5),(2,4),(2,5)],98,(0,4),false⟩,⟨[(2,6),(3,5),(3,6)],47,(0,5),false⟩]⟩,
  ⟨[(1,2),(2,2),(2,3)],[⟨[(0,0),(1,0),(1,1)],59,(0,0),true⟩,⟨[(0,1),(0,2),(0,3)],10,(0,1),true⟩,⟨[(0,4),(1,3),(1,4)],138,(0,2),true⟩,⟨[(1,5),(2,4),(2,5)],54,(1,2),false⟩,⟨[(2,0),(2,1),(3,0)],143,(1,0),false⟩,⟨[(3,1),(3,2),(4,1)],123,(1,1),false⟩,⟨[(3,3),(3,4),(4,4)],66,(1,2),false⟩]⟩,
  ⟨[(1,5),(2,4),(2,5)],[⟨[(0,4),(1,3),(1,4)],107,(0,3),true⟩,⟨[(0,5),(0,6),(1,6)],98,(0,4),true⟩,⟨[(1,2),(2,2),(2,3)],54,(1,2),true⟩,⟨[(2,6),(3,5),(3,6)],107,(1,4),false⟩,⟨[(3,3),(3,4),(4,4)],141,(1,3),false⟩]⟩,
  ⟨[(2,0),(2,1),(3,0)],[⟨[(0,0),(1,0),(1,1)],61,(0,0),true⟩,⟨[(1,2),(2,2),(2,3)],143,(1,0),true⟩,⟨[(3,1),(3,2),(4,1)],22,(2,0),false⟩,⟨[(4,0),(5,0),(5,1)],28,(2,0),false⟩]⟩,
  ⟨[(2,6),(3,5),(3,6)],[⟨[(0,5),(0,6),(1,6)],47,(0,5),true⟩,⟨[(1,5),(2,4),(2,5)],107,(1,4),true⟩,⟨[(3,3),(3,4),(4,4)],155,(2,3),false⟩,⟨[(4,5),(4,6),(5,6)],111,(2,5),false⟩]⟩,
  ⟨[(3,1),(3,2),(4,1)],[⟨[(1,2),(2,2),(2,3)],123,(1,1),true⟩,⟨[(2,0),(2,1),(3,0)],22,(2,0),true⟩,⟨[(3,3),(3,4),(4,4)],19,(3,1),false⟩,⟨[(4,0),(5,0),(5,1)],90,(3,0),false⟩,⟨[(4,2),(4,3),(5,2)],22,(3,1),false⟩]⟩,
  ⟨[(3,3),(3,4),(4,4)],[⟨[(1,2),(2,2),(2,3)],66,(1,2),true⟩,⟨[(1,5),(2,4),(2,5)],141,(1,3),true⟩,⟨[(2,6),(3,5),(3,6)],155,(2,3),true⟩,⟨[(3,1),(3,2),(4,1)],19,(3,1),true⟩,⟨[(4,2),(4,3),(5,2)],96,(3,2),false⟩,⟨[(4,5),(4,6),(5,6)],37,(3,3),false⟩,⟨[(5,3),(5,4),(5,5)],41,(3,3),false⟩]⟩,
  ⟨[(4,0),(5,0),(5,1)],[⟨[(2,0),(2,1),(3,0)],28,(2,0),true⟩,⟨[(3,1),(3,2),(4,1)],90,(3,0),true⟩,⟨[(4,2),(4,3),(5,2)],51,(4,0),false⟩]⟩,
  ⟨[(4,2),(4,3),(5,2)],[⟨[(3,1),(3,2),(4,1)],22,(3,1),true⟩,⟨[(3,3),(3,4),(4,4)],96,(3,2),true⟩,⟨[(4,0),(5,0),(5,1)],51,(4,0),true⟩,⟨[(5,3),(5,4),(5,5)],21,(4,2),false⟩]⟩,
  ⟨[(4,5),(4,6),(5,6)],[⟨[(2,6),(3,5),(3,6)],111,(2,5),true⟩,⟨[(3,3),(3,4),(4,4)],37,(3,3),true⟩,⟨[(5,3),(5,4),(5,5)],137,(4,3),false⟩]⟩,
  ⟨[(5,3),(5,4),(5,5)],[⟨[(3,3),(3,4),(4,4)],41,(3,3),true⟩,⟨[(4,2),(4,3),(5,2)],21,(4,2),true⟩,⟨[(4,5),(4,6),(5,6)],137,(4,3),true⟩]⟩,
]
theorem Width7_b0_entries_match : CatalogLinksCheck catalog Width7_b0_entries := by decide +kernel
theorem Width7_b0_entries_links : CertifiedLinks (localEntries Width7_b0_entries) :=
  catalogLinks_sound catalog_sound Width7_b0_entries_match

def Width7_b0_tiles := EntryTiles (localEntries Width7_b0_entries)
def Width7_b0_owner : Cell → List Cell := tableOwner 7 Width7_b0_tiles [0,1,1,1,2,3,3,0,0,4,2,2,5,3,6,6,4,4,5,5,7,6,8,8,9,9,7,7,10,8,11,11,9,12,12,10,10,11,13,13,13,12]
theorem Width7_b0_partition : OwnerPartitionCheck 6 7 Width7_b0_tiles Width7_b0_owner := by decide +kernel
theorem Width7_b0_cover : EdgeCoverCheck (localEntries Width7_b0_entries) Width7_b0_owner 0 0 6 7 := by decide +kernel
def Width7_b0 : RigidBlock 6 7 :=
  localCheckedBlock Width7_b0_partition Width7_b0_entries_links Width7_b0_cover

def Width7_b1_entries : List EntryData := [
  ⟨[(0,0),(1,0),(1,1)],[⟨[(0,1),(0,2),(0,3)],50,(0,0),false⟩,⟨[(1,2),(2,1),(2,2)],58,(0,0),false⟩,⟨[(2,0),(3,0),(3,1)],62,(0,0),false⟩]⟩,
  ⟨[(0,1),(0,2),(0,3)],[⟨[(0,0),(1,0),(1,1)],50,(0,0),true⟩,⟨[(0,4),(1,3),(1,4)],3,(0,1),false⟩,⟨[(1,2),(2,1),(2,2)],9,(0,1),false⟩]⟩,
  ⟨[(0,4),(1,3),(1,4)],[⟨[(0,1),(0,2),(0,3)],3,(0,1),true⟩,⟨[(0,5),(0,6),(1,6)],100,(0,3),false⟩,⟨[(1,2),(2,1),(2,2)],156,(0,1),false⟩,⟨[(1,5),(2,4),(2,5)],107,(0,3),false⟩,⟨[(2,3),(3,2),(3,3)],142,(0,2),false⟩]⟩,
  ⟨[(0,5),(0,6),(1,6)],[⟨[(0,4),(1,3),(1,4)],100,(0,3),true⟩,⟨[(1,5),(2,4),(2,5)],98,(0,4),false⟩,⟨[(2,6),(3,6),(4,6)],49,(0,5),false⟩]⟩,
  ⟨[(1,2),(2,1),(2,2)],[⟨[(0,0),(1,0),(1,1)],58,(0,0),true⟩,⟨[(0,1),(0,2),(0,3)],9,(0,1),true⟩,⟨[(0,4),(1,3),(1,4)],156,(0,1),true⟩,⟨[(2,0),(3,0),(3,1)],138,(1,0),false⟩,⟨[(2,3),(3,2),(3,3)],107,(1,1),false⟩]⟩,
  ⟨[(1,5),(2,4),(2,5)],[⟨[(0,4),(1,3),(1,4)],107,(0,3),true⟩,⟨[(0,5),(0,6),(1,6)],98,(0,4),true⟩,⟨[(2,3),(3,2),(3,3)],156,(1,2),false⟩,⟨[(2,6),(3,6),(4,6)],109,(1,4),false⟩,⟨[(3,4),(3,5),(4,5)],111,(1,4),false⟩]⟩,
  ⟨[(2,0),(3,0),(3,1)],[⟨[(0,0),(1,0),(1,1)],62,(0,0),true⟩,⟨[(1,2),(2,1),(2,2)],138,(1,0),true⟩,⟨[(2,3),(3,2),(3,3)],54,(2,0),false⟩,⟨[(4,0),(5,0),(6,0)],63,(2,0),false⟩,⟨[(4,1),(5,1),(5,2)],68,(2,0),false⟩]⟩,
  ⟨[(2,3),(3,2),(3,3)],[⟨[(0,4),(1,3),(1,4)],142,(0,2),true⟩,⟨[(1,2),(2,1),(2,2)],107,(1,1),true⟩,⟨[(1,5),(2,4),(2,5)],156,(1,2),true⟩,⟨[(2,0),(3,0),(3,1)],54,(2,0),true⟩,⟨[(3,4),(3,5),(4,5)],106,(2,2),false⟩,⟨[(4,2),(4,3),(4,4)],110,(2,2),false⟩]⟩,
  ⟨[(2,6),(3,6),(4,6)],[⟨[(0,5),(0,6),(1,6)],49,(0,5),true⟩,⟨[(1,5),(2,4),(2,5)],109,(1,4),true⟩,⟨[(3,4),(3,5),(4,5)],148,(2,4),false⟩,⟨[(5,5),(5,6),(6,6)],130,(2,5),false⟩]⟩,
  ⟨[(3,4),(3,5),(4,5)],[⟨[(1,5),(2,4),(2,5)],111,(1,4),true⟩,⟨[(2,3),(3,2),(3,3)],106,(2,2),true⟩,⟨[(2,6),(3,6),(4,6)],148,(2,4),true⟩,⟨[(4,2),(4,3),(4,4)],137,(3,2),false⟩,⟨[(5,5),(5,6),(6,6)],46,(3,4),false⟩]⟩,
  ⟨[(4,0),(5,0),(6,0)],[⟨[(2,0),(3,0),(3,1)],63,(2,0),true⟩,⟨[(4,1),(5,1),(5,2)],71,(4,0),false⟩,⟨[(6,1),(6,2),(7,1)],77,(4,0),false⟩,⟨[(7,0),(8,0),(8,1)],85,(4,0),false⟩]⟩,
  ⟨[(4,1),(5,1),(5,2)],[⟨[(2,0),(3,0),(3,1)],68,(2,0),true⟩,⟨[(4,0),(5,0),(6,0)],71,(4,0),true⟩,⟨[(4,2),(4,3),(4,4)],50,(4,1),false⟩,⟨[(5,3),(5,4),(6,3)],56,(4,1),false⟩,⟨[(6,1),(6,2),(7,1)],61,(4,1),false⟩]⟩,
  ⟨[(4,2),(4,3),(4,4)],[⟨[(2,3),(3,2),(3,3)],110,(2,2),true⟩,⟨[(3,4),(3,5),(4,5)],137,(3,2),true⟩,⟨[(4,1),(5,1),(5,2)],50,(4,1),true⟩,⟨[(5,3),(5,4),(6,3)],8,(4,2),false⟩]⟩,
  ⟨[(5,3),(5,4),(6,3)],[⟨[(4,1),(5,1),(5,2)],56,(4,1),true⟩,⟨[(4,2),(4,3),(4,4)],8,(4,2),true⟩,⟨[(5,5),(5,6),(6,6)],19,(5,3),false⟩,⟨[(6,1),(6,2),(7,1)],133,(5,1),false⟩,⟨[(6,4),(6,5),(7,4)],22,(5,3),false⟩,⟨[(7,2),(7,3),(8,2)],93,(5,2),false⟩]⟩,
  ⟨[(5,5),(5,6),(6,6)],[⟨[(2,6),(3,6),(4,6)],130,(2,5),true⟩,⟨[(3,4),(3,5),(4,5)],46,(3,4),true⟩,⟨[(5,3),(5,4),(6,3)],19,(5,3),true⟩,⟨[(6,4),(6,5),(7,4)],96,(5,4),false⟩,⟨[(7,5),(7,6),(8,6)],43,(5,5),false⟩]⟩,
  ⟨[(6,1),(6,2),(7,1)],[⟨[(4,0),(5,0),(6,0)],77,(4,0),true⟩,⟨[(4,1),(5,1),(5,2)],61,(4,1),true⟩,⟨[(5,3),(5,4),(6,3)],133,(5,1),true⟩,⟨[(7,0),(8,0),(8,1)],90,(6,0),false⟩,⟨[(7,2),(7,3),(8,2)],22,(6,1),false⟩]⟩,
  ⟨[(6,4),(6,5),(7,4)],[⟨[(5,3),(5,4),(6,3)],22,(5,3),true⟩,⟨[(5,5),(5,6),(6,6)],96,(5,4),true⟩,⟨[(7,2),(7,3),(8,2)],133,(6,2),false⟩,⟨[(7,5),(7,6),(8,6)],23,(6,4),false⟩,⟨[(8,3),(8,4),(8,5)],92,(6,3),false⟩]⟩,
  ⟨[(7,0),(8,0),(8,1)],[⟨[(4,0),(5,0),(6,0)],85,(4,0),true⟩,⟨[(6,1),(6,2),(7,1)],90,(6,0),true⟩,⟨[(7,2),(7,3),(8,2)],51,(7,0),false⟩]⟩,
  ⟨[(7,2),(7,3),(8,2)],[⟨[(5,3),(5,4),(6,3)],93,(5,2),true⟩,⟨[(6,1),(6,2),(7,1)],22,(6,1),true⟩,⟨[(6,4),(6,5),(7,4)],133,(6,2),true⟩,⟨[(7,0),(8,0),(8,1)],51,(7,0),true⟩,⟨[(8,3),(8,4),(8,5)],21,(7,2),false⟩]⟩,
  ⟨[(7,5),(7,6),(8,6)],[⟨[(5,5),(5,6),(6,6)],43,(5,5),true⟩,⟨[(6,4),(6,5),(7,4)],23,(6,4),true⟩,⟨[(8,3),(8,4),(8,5)],137,(7,3),false⟩]⟩,
  ⟨[(8,3),(8,4),(8,5)],[⟨[(6,4),(6,5),(7,4)],92,(6,3),true⟩,⟨[(7,2),(7,3),(8,2)],21,(7,2),true⟩,⟨[(7,5),(7,6),(8,6)],137,(7,3),true⟩]⟩,
]
theorem Width7_b1_entries_match : CatalogLinksCheck catalog Width7_b1_entries := by decide +kernel
theorem Width7_b1_entries_links : CertifiedLinks (localEntries Width7_b1_entries) :=
  catalogLinks_sound catalog_sound Width7_b1_entries_match

def Width7_b1_tiles := EntryTiles (localEntries Width7_b1_entries)
def Width7_b1_owner : Cell → List Cell := tableOwner 7 Width7_b1_tiles [0,1,1,1,2,3,3,0,0,4,2,2,5,3,6,4,4,7,5,5,8,6,6,7,7,9,9,8,10,11,12,12,12,9,8,10,11,11,13,13,14,14,10,15,15,13,16,16,14,17,15,18,18,16,19,19,17,17,18,20,20,20,19]
theorem Width7_b1_partition : OwnerPartitionCheck 9 7 Width7_b1_tiles Width7_b1_owner := by decide +kernel
theorem Width7_b1_cover : EdgeCoverCheck (localEntries Width7_b1_entries) Width7_b1_owner 0 0 9 7 := by decide +kernel
def Width7_b1 : RigidBlock 9 7 :=
  localCheckedBlock Width7_b1_partition Width7_b1_entries_links Width7_b1_cover

def Width7_vertical_0_entries : List EntryData := [
  ⟨[(0,0),(1,0),(1,1)],[]⟩,
  ⟨[(0,1),(0,2),(0,3)],[]⟩,
  ⟨[(0,4),(1,3),(1,4)],[]⟩,
  ⟨[(0,5),(0,6),(1,6)],[]⟩,
  ⟨[(1,2),(2,2),(2,3)],[]⟩,
  ⟨[(1,5),(2,4),(2,5)],[]⟩,
  ⟨[(2,0),(2,1),(3,0)],[]⟩,
  ⟨[(2,6),(3,5),(3,6)],[]⟩,
  ⟨[(3,1),(3,2),(4,1)],[]⟩,
  ⟨[(3,3),(3,4),(4,4)],[]⟩,
  ⟨[(4,0),(5,0),(5,1)],[⟨[(6,0),(7,0),(7,1)],62,(4,0),false⟩,⟨[(6,1),(6,2),(6,3)],64,(4,0),false⟩]⟩,
  ⟨[(4,2),(4,3),(5,2)],[⟨[(6,1),(6,2),(6,3)],92,(4,1),false⟩]⟩,
  ⟨[(4,5),(4,6),(5,6)],[⟨[(6,5),(6,6),(7,6)],43,(4,5),false⟩]⟩,
  ⟨[(5,3),(5,4),(5,5)],[⟨[(6,1),(6,2),(6,3)],132,(5,1),false⟩,⟨[(6,4),(7,3),(7,4)],9,(5,3),false⟩,⟨[(6,5),(6,6),(7,6)],14,(5,3),false⟩]⟩,
]
theorem Width7_vertical_0_entries_match : CatalogLinksCheck catalog Width7_vertical_0_entries := by decide +kernel
theorem Width7_vertical_0_entries_links : CertifiedLinks (localEntries Width7_vertical_0_entries) :=
  catalogLinks_sound catalog_sound Width7_vertical_0_entries_match

theorem Width7_vertical_0_same : EntryTiles (localEntries Width7_vertical_0_entries) = Width7_b0_tiles := by rfl
theorem Width7_vertical_0_cover : EdgeCoverCheck (localEntries Width7_vertical_0_entries)
    (shiftOwner (6,0) Width7_b0_owner) 6 0 6 7 := by decide +kernel
theorem Width7_vertical_0 : ∀ A B, Width7_b0.tiles A → Width7_b0.tiles B → Rigid A (Shift (6,0) B) := by
  have hp := localSeam_rigid (h := 6) (w := 7)
    (Width7_vertical_0_same.symm ▸ Width7_b0.partition) Width7_b0_partition
    Width7_vertical_0_entries_links Width7_vertical_0_cover
    (side_disjoint 6 7 6 7).1
  rw [Width7_vertical_0_same] at hp
  exact hp

def Width7_vertical_1_entries : List EntryData := [
  ⟨[(0,0),(1,0),(1,1)],[]⟩,
  ⟨[(0,1),(0,2),(0,3)],[]⟩,
  ⟨[(0,4),(1,3),(1,4)],[]⟩,
  ⟨[(0,5),(0,6),(1,6)],[]⟩,
  ⟨[(1,2),(2,2),(2,3)],[]⟩,
  ⟨[(1,5),(2,4),(2,5)],[]⟩,
  ⟨[(2,0),(2,1),(3,0)],[]⟩,
  ⟨[(2,6),(3,5),(3,6)],[]⟩,
  ⟨[(3,1),(3,2),(4,1)],[]⟩,
  ⟨[(3,3),(3,4),(4,4)],[]⟩,
  ⟨[(4,0),(5,0),(5,1)],[⟨[(6,0),(7,0),(7,1)],62,(4,0),false⟩,⟨[(6,1),(6,2),(6,3)],64,(4,0),false⟩]⟩,
  ⟨[(4,2),(4,3),(5,2)],[⟨[(6,1),(6,2),(6,3)],92,(4,1),false⟩]⟩,
  ⟨[(4,5),(4,6),(5,6)],[⟨[(6,5),(6,6),(7,6)],43,(4,5),false⟩]⟩,
  ⟨[(5,3),(5,4),(5,5)],[⟨[(6,1),(6,2),(6,3)],132,(5,1),false⟩,⟨[(6,4),(7,3),(7,4)],9,(5,3),false⟩,⟨[(6,5),(6,6),(7,6)],14,(5,3),false⟩]⟩,
]
theorem Width7_vertical_1_entries_match : CatalogLinksCheck catalog Width7_vertical_1_entries := by decide +kernel
theorem Width7_vertical_1_entries_links : CertifiedLinks (localEntries Width7_vertical_1_entries) :=
  catalogLinks_sound catalog_sound Width7_vertical_1_entries_match

theorem Width7_vertical_1_same : EntryTiles (localEntries Width7_vertical_1_entries) = Width7_b0_tiles := by rfl
theorem Width7_vertical_1_cover : EdgeCoverCheck (localEntries Width7_vertical_1_entries)
    (shiftOwner (6,0) Width7_b1_owner) 6 0 9 7 := by decide +kernel
theorem Width7_vertical_1 : ∀ A B, Width7_b0.tiles A → Width7_b1.tiles B → Rigid A (Shift (6,0) B) := by
  have hp := localSeam_rigid (h := 6) (w := 7)
    (Width7_vertical_1_same.symm ▸ Width7_b0.partition) Width7_b1_partition
    Width7_vertical_1_entries_links Width7_vertical_1_cover
    (side_disjoint 6 7 9 7).1
  rw [Width7_vertical_1_same] at hp
  exact hp

def Width7_vertical_2_entries : List EntryData := [
  ⟨[(0,0),(1,0),(1,1)],[]⟩,
  ⟨[(0,1),(0,2),(0,3)],[]⟩,
  ⟨[(0,4),(1,3),(1,4)],[]⟩,
  ⟨[(0,5),(0,6),(1,6)],[]⟩,
  ⟨[(1,2),(2,1),(2,2)],[]⟩,
  ⟨[(1,5),(2,4),(2,5)],[]⟩,
  ⟨[(2,0),(3,0),(3,1)],[]⟩,
  ⟨[(2,3),(3,2),(3,3)],[]⟩,
  ⟨[(2,6),(3,6),(4,6)],[]⟩,
  ⟨[(3,4),(3,5),(4,5)],[]⟩,
  ⟨[(4,0),(5,0),(6,0)],[]⟩,
  ⟨[(4,1),(5,1),(5,2)],[]⟩,
  ⟨[(4,2),(4,3),(4,4)],[]⟩,
  ⟨[(5,3),(5,4),(6,3)],[]⟩,
  ⟨[(5,5),(5,6),(6,6)],[]⟩,
  ⟨[(6,1),(6,2),(7,1)],[]⟩,
  ⟨[(6,4),(6,5),(7,4)],[]⟩,
  ⟨[(7,0),(8,0),(8,1)],[⟨[(9,0),(10,0),(10,1)],62,(7,0),false⟩,⟨[(9,1),(9,2),(9,3)],64,(7,0),false⟩]⟩,
  ⟨[(7,2),(7,3),(8,2)],[⟨[(9,1),(9,2),(9,3)],92,(7,1),false⟩]⟩,
  ⟨[(7,5),(7,6),(8,6)],[⟨[(9,5),(9,6),(10,6)],43,(7,5),false⟩]⟩,
  ⟨[(8,3),(8,4),(8,5)],[⟨[(9,1),(9,2),(9,3)],132,(8,1),false⟩,⟨[(9,4),(10,3),(10,4)],9,(8,3),false⟩,⟨[(9,5),(9,6),(10,6)],14,(8,3),false⟩]⟩,
]
theorem Width7_vertical_2_entries_match : CatalogLinksCheck catalog Width7_vertical_2_entries := by decide +kernel
theorem Width7_vertical_2_entries_links : CertifiedLinks (localEntries Width7_vertical_2_entries) :=
  catalogLinks_sound catalog_sound Width7_vertical_2_entries_match

theorem Width7_vertical_2_same : EntryTiles (localEntries Width7_vertical_2_entries) = Width7_b1_tiles := by rfl
theorem Width7_vertical_2_cover : EdgeCoverCheck (localEntries Width7_vertical_2_entries)
    (shiftOwner (9,0) Width7_b0_owner) 9 0 6 7 := by decide +kernel
theorem Width7_vertical_2 : ∀ A B, Width7_b1.tiles A → Width7_b0.tiles B → Rigid A (Shift (9,0) B) := by
  have hp := localSeam_rigid (h := 9) (w := 7)
    (Width7_vertical_2_same.symm ▸ Width7_b1.partition) Width7_b0_partition
    Width7_vertical_2_entries_links Width7_vertical_2_cover
    (side_disjoint 9 7 6 7).1
  rw [Width7_vertical_2_same] at hp
  exact hp

def Width7_vertical_3_entries : List EntryData := [
  ⟨[(0,0),(1,0),(1,1)],[]⟩,
  ⟨[(0,1),(0,2),(0,3)],[]⟩,
  ⟨[(0,4),(1,3),(1,4)],[]⟩,
  ⟨[(0,5),(0,6),(1,6)],[]⟩,
  ⟨[(1,2),(2,1),(2,2)],[]⟩,
  ⟨[(1,5),(2,4),(2,5)],[]⟩,
  ⟨[(2,0),(3,0),(3,1)],[]⟩,
  ⟨[(2,3),(3,2),(3,3)],[]⟩,
  ⟨[(2,6),(3,6),(4,6)],[]⟩,
  ⟨[(3,4),(3,5),(4,5)],[]⟩,
  ⟨[(4,0),(5,0),(6,0)],[]⟩,
  ⟨[(4,1),(5,1),(5,2)],[]⟩,
  ⟨[(4,2),(4,3),(4,4)],[]⟩,
  ⟨[(5,3),(5,4),(6,3)],[]⟩,
  ⟨[(5,5),(5,6),(6,6)],[]⟩,
  ⟨[(6,1),(6,2),(7,1)],[]⟩,
  ⟨[(6,4),(6,5),(7,4)],[]⟩,
  ⟨[(7,0),(8,0),(8,1)],[⟨[(9,0),(10,0),(10,1)],62,(7,0),false⟩,⟨[(9,1),(9,2),(9,3)],64,(7,0),false⟩]⟩,
  ⟨[(7,2),(7,3),(8,2)],[⟨[(9,1),(9,2),(9,3)],92,(7,1),false⟩]⟩,
  ⟨[(7,5),(7,6),(8,6)],[⟨[(9,5),(9,6),(10,6)],43,(7,5),false⟩]⟩,
  ⟨[(8,3),(8,4),(8,5)],[⟨[(9,1),(9,2),(9,3)],132,(8,1),false⟩,⟨[(9,4),(10,3),(10,4)],9,(8,3),false⟩,⟨[(9,5),(9,6),(10,6)],14,(8,3),false⟩]⟩,
]
theorem Width7_vertical_3_entries_match : CatalogLinksCheck catalog Width7_vertical_3_entries := by decide +kernel
theorem Width7_vertical_3_entries_links : CertifiedLinks (localEntries Width7_vertical_3_entries) :=
  catalogLinks_sound catalog_sound Width7_vertical_3_entries_match

theorem Width7_vertical_3_same : EntryTiles (localEntries Width7_vertical_3_entries) = Width7_b1_tiles := by rfl
theorem Width7_vertical_3_cover : EdgeCoverCheck (localEntries Width7_vertical_3_entries)
    (shiftOwner (9,0) Width7_b1_owner) 9 0 9 7 := by decide +kernel
theorem Width7_vertical_3 : ∀ A B, Width7_b1.tiles A → Width7_b1.tiles B → Rigid A (Shift (9,0) B) := by
  have hp := localSeam_rigid (h := 9) (w := 7)
    (Width7_vertical_3_same.symm ▸ Width7_b1.partition) Width7_b1_partition
    Width7_vertical_3_entries_links Width7_vertical_3_cover
    (side_disjoint 9 7 9 7).1
  rw [Width7_vertical_3_same] at hp
  exact hp

def Width7_palette : VerticalPalette (fun h => h = 6 ∨ h = 9) 7 where
  tiles h := if h = 6 then Width7_b0.tiles else Width7_b1.tiles
  partition := by
    intro h hh
    rcases hh with rfl | rfl
    · exact Width7_b0.partition
    · exact Width7_b1.partition
  internal := by
    intro h hh
    rcases hh with rfl | rfl
    · exact Width7_b0.internal
    · exact Width7_b1.internal
  vertical := by
    intro h k hh hk
    rcases hh with rfl | rfl <;> rcases hk with rfl | rfl
    · exact Width7_vertical_0
    · exact Width7_vertical_1
    · exact Width7_vertical_2
    · exact Width7_vertical_3

end LockedTromino.Witnesses
