import Generated.Catalog

namespace LockedTromino.Witnesses
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def Width8_b0_entries : List EntryData := [
  ⟨[(0,0),(0,1),(1,0)],[⟨[(0,2),(1,2),(1,3)],20,(0,0),false⟩,⟨[(1,1),(2,1),(2,2)],24,(0,0),false⟩,⟨[(2,0),(3,0),(3,1)],28,(0,0),false⟩]⟩,
  ⟨[(0,2),(1,2),(1,3)],[⟨[(0,0),(0,1),(1,0)],20,(0,0),true⟩,⟨[(0,3),(0,4),(0,5)],50,(0,2),false⟩,⟨[(1,1),(2,1),(2,2)],120,(0,1),false⟩,⟨[(1,4),(2,4),(2,5)],59,(0,2),false⟩,⟨[(2,3),(3,3),(3,4)],68,(0,2),false⟩]⟩,
  ⟨[(0,3),(0,4),(0,5)],[⟨[(0,2),(1,2),(1,3)],50,(0,2),true⟩,⟨[(0,6),(1,5),(1,6)],3,(0,3),false⟩,⟨[(1,4),(2,4),(2,5)],10,(0,3),false⟩]⟩,
  ⟨[(0,6),(1,5),(1,6)],[⟨[(0,3),(0,4),(0,5)],3,(0,3),true⟩,⟨[(0,7),(1,7),(2,7)],102,(0,5),false⟩,⟨[(1,4),(2,4),(2,5)],138,(0,4),false⟩,⟨[(2,6),(3,6),(3,7)],118,(0,5),false⟩]⟩,
  ⟨[(0,7),(1,7),(2,7)],[⟨[(0,6),(1,5),(1,6)],102,(0,5),true⟩,⟨[(2,6),(3,6),(3,7)],126,(0,6),false⟩]⟩,
  ⟨[(1,1),(2,1),(2,2)],[⟨[(0,0),(0,1),(1,0)],24,(0,0),true⟩,⟨[(0,2),(1,2),(1,3)],120,(0,1),true⟩,⟨[(2,0),(3,0),(3,1)],120,(1,0),false⟩,⟨[(2,3),(3,3),(3,4)],59,(1,1),false⟩,⟨[(3,2),(4,1),(4,2)],67,(1,1),false⟩]⟩,
  ⟨[(1,4),(2,4),(2,5)],[⟨[(0,2),(1,2),(1,3)],59,(0,2),true⟩,⟨[(0,3),(0,4),(0,5)],10,(0,3),true⟩,⟨[(0,6),(1,5),(1,6)],138,(0,4),true⟩,⟨[(2,3),(3,3),(3,4)],120,(1,3),false⟩,⟨[(2,6),(3,6),(3,7)],59,(1,4),false⟩,⟨[(3,5),(4,5),(4,6)],68,(1,4),false⟩]⟩,
  ⟨[(2,0),(3,0),(3,1)],[⟨[(0,0),(0,1),(1,0)],28,(0,0),true⟩,⟨[(1,1),(2,1),(2,2)],120,(1,0),true⟩,⟨[(3,2),(4,1),(4,2)],58,(2,0),false⟩,⟨[(4,0),(5,0),(5,1)],62,(2,0),false⟩]⟩,
  ⟨[(2,3),(3,3),(3,4)],[⟨[(0,2),(1,2),(1,3)],68,(0,2),true⟩,⟨[(1,1),(2,1),(2,2)],59,(1,1),true⟩,⟨[(1,4),(2,4),(2,5)],120,(1,3),true⟩,⟨[(3,2),(4,1),(4,2)],145,(2,1),false⟩,⟨[(3,5),(4,5),(4,6)],59,(2,3),false⟩,⟨[(4,3),(5,2),(5,3)],125,(2,2),false⟩,⟨[(4,4),(5,4),(5,5)],68,(2,3),false⟩]⟩,
  ⟨[(2,6),(3,6),(3,7)],[⟨[(0,6),(1,5),(1,6)],118,(0,5),true⟩,⟨[(0,7),(1,7),(2,7)],126,(0,6),true⟩,⟨[(1,4),(2,4),(2,5)],59,(1,4),true⟩,⟨[(3,5),(4,5),(4,6)],120,(2,5),false⟩,⟨[(4,7),(5,6),(5,7)],67,(2,6),false⟩]⟩,
  ⟨[(3,2),(4,1),(4,2)],[⟨[(1,1),(2,1),(2,2)],67,(1,1),true⟩,⟨[(2,0),(3,0),(3,1)],58,(2,0),true⟩,⟨[(2,3),(3,3),(3,4)],145,(2,1),true⟩,⟨[(4,0),(5,0),(5,1)],138,(3,0),false⟩,⟨[(4,3),(5,2),(5,3)],107,(3,1),false⟩]⟩,
  ⟨[(3,5),(4,5),(4,6)],[⟨[(1,4),(2,4),(2,5)],68,(1,4),true⟩,⟨[(2,3),(3,3),(3,4)],59,(2,3),true⟩,⟨[(2,6),(3,6),(3,7)],120,(2,5),true⟩,⟨[(4,4),(5,4),(5,5)],120,(3,4),false⟩,⟨[(4,7),(5,6),(5,7)],58,(3,5),false⟩]⟩,
  ⟨[(4,0),(5,0),(5,1)],[⟨[(2,0),(3,0),(3,1)],62,(2,0),true⟩,⟨[(3,2),(4,1),(4,2)],138,(3,0),true⟩,⟨[(4,3),(5,2),(5,3)],54,(4,0),false⟩]⟩,
  ⟨[(4,3),(5,2),(5,3)],[⟨[(2,3),(3,3),(3,4)],125,(2,2),true⟩,⟨[(3,2),(4,1),(4,2)],107,(3,1),true⟩,⟨[(4,0),(5,0),(5,1)],54,(4,0),true⟩,⟨[(4,4),(5,4),(5,5)],101,(4,2),false⟩]⟩,
  ⟨[(4,4),(5,4),(5,5)],[⟨[(2,3),(3,3),(3,4)],68,(2,3),true⟩,⟨[(3,5),(4,5),(4,6)],120,(3,4),true⟩,⟨[(4,3),(5,2),(5,3)],101,(4,2),true⟩,⟨[(4,7),(5,6),(5,7)],54,(4,4),false⟩]⟩,
  ⟨[(4,7),(5,6),(5,7)],[⟨[(2,6),(3,6),(3,7)],67,(2,6),true⟩,⟨[(3,5),(4,5),(4,6)],58,(3,5),true⟩,⟨[(4,4),(5,4),(5,5)],54,(4,4),true⟩]⟩,
]
theorem Width8_b0_entries_match : CatalogLinksCheck catalog Width8_b0_entries := by decide +kernel
theorem Width8_b0_entries_links : CertifiedLinks (localEntries Width8_b0_entries) :=
  catalogLinks_sound catalog_sound Width8_b0_entries_match

def Width8_b0_tiles := EntryTiles (localEntries Width8_b0_entries)
def Width8_b0_owner : Cell → List Cell := tableOwner 8 Width8_b0_tiles [0,0,1,2,2,2,3,4,0,5,1,1,6,3,3,4,7,5,5,8,6,6,9,4,7,7,10,8,8,11,9,9,12,10,10,13,14,11,11,15,12,12,13,13,14,14,15,15]
theorem Width8_b0_partition : OwnerPartitionCheck 6 8 Width8_b0_tiles Width8_b0_owner := by decide +kernel
theorem Width8_b0_cover : EdgeCoverCheck (localEntries Width8_b0_entries) Width8_b0_owner 0 0 6 8 := by decide +kernel
def Width8_b0 : RigidBlock 6 8 :=
  localCheckedBlock Width8_b0_partition Width8_b0_entries_links Width8_b0_cover

def Width8_b1_entries : List EntryData := [
  ⟨[(0,0),(0,1),(1,0)],[⟨[(0,2),(1,2),(1,3)],20,(0,0),false⟩,⟨[(1,1),(2,1),(2,2)],24,(0,0),false⟩,⟨[(2,0),(3,0),(4,0)],29,(0,0),false⟩]⟩,
  ⟨[(0,2),(1,2),(1,3)],[⟨[(0,0),(0,1),(1,0)],20,(0,0),true⟩,⟨[(0,3),(0,4),(0,5)],50,(0,2),false⟩,⟨[(1,1),(2,1),(2,2)],120,(0,1),false⟩,⟨[(1,4),(2,4),(2,5)],59,(0,2),false⟩,⟨[(2,3),(3,3),(3,4)],68,(0,2),false⟩]⟩,
  ⟨[(0,3),(0,4),(0,5)],[⟨[(0,2),(1,2),(1,3)],50,(0,2),true⟩,⟨[(0,6),(1,5),(1,6)],3,(0,3),false⟩,⟨[(1,4),(2,4),(2,5)],10,(0,3),false⟩]⟩,
  ⟨[(0,6),(1,5),(1,6)],[⟨[(0,3),(0,4),(0,5)],3,(0,3),true⟩,⟨[(0,7),(1,7),(2,7)],102,(0,5),false⟩,⟨[(1,4),(2,4),(2,5)],138,(0,4),false⟩,⟨[(2,6),(3,6),(3,7)],118,(0,5),false⟩]⟩,
  ⟨[(0,7),(1,7),(2,7)],[⟨[(0,6),(1,5),(1,6)],102,(0,5),true⟩,⟨[(2,6),(3,6),(3,7)],126,(0,6),false⟩]⟩,
  ⟨[(1,1),(2,1),(2,2)],[⟨[(0,0),(0,1),(1,0)],24,(0,0),true⟩,⟨[(0,2),(1,2),(1,3)],120,(0,1),true⟩,⟨[(2,0),(3,0),(4,0)],121,(1,0),false⟩,⟨[(2,3),(3,3),(3,4)],59,(1,1),false⟩,⟨[(3,1),(3,2),(4,1)],61,(1,1),false⟩]⟩,
  ⟨[(1,4),(2,4),(2,5)],[⟨[(0,2),(1,2),(1,3)],59,(0,2),true⟩,⟨[(0,3),(0,4),(0,5)],10,(0,3),true⟩,⟨[(0,6),(1,5),(1,6)],138,(0,4),true⟩,⟨[(2,3),(3,3),(3,4)],120,(1,3),false⟩,⟨[(2,6),(3,6),(3,7)],59,(1,4),false⟩,⟨[(3,5),(4,4),(4,5)],67,(1,4),false⟩]⟩,
  ⟨[(2,0),(3,0),(4,0)],[⟨[(0,0),(0,1),(1,0)],29,(0,0),true⟩,⟨[(1,1),(2,1),(2,2)],121,(1,0),true⟩,⟨[(3,1),(3,2),(4,1)],74,(2,0),false⟩,⟨[(5,0),(5,1),(6,0)],83,(2,0),false⟩]⟩,
  ⟨[(2,3),(3,3),(3,4)],[⟨[(0,2),(1,2),(1,3)],68,(0,2),true⟩,⟨[(1,1),(2,1),(2,2)],59,(1,1),true⟩,⟨[(1,4),(2,4),(2,5)],120,(1,3),true⟩,⟨[(3,1),(3,2),(4,1)],143,(2,1),false⟩,⟨[(3,5),(4,4),(4,5)],58,(2,3),false⟩,⟨[(4,2),(4,3),(5,2)],123,(2,2),false⟩]⟩,
  ⟨[(2,6),(3,6),(3,7)],[⟨[(0,6),(1,5),(1,6)],118,(0,5),true⟩,⟨[(0,7),(1,7),(2,7)],126,(0,6),true⟩,⟨[(1,4),(2,4),(2,5)],59,(1,4),true⟩,⟨[(3,5),(4,4),(4,5)],145,(2,4),false⟩,⟨[(4,6),(5,5),(5,6)],125,(2,5),false⟩,⟨[(4,7),(5,7),(6,7)],69,(2,6),false⟩]⟩,
  ⟨[(3,1),(3,2),(4,1)],[⟨[(1,1),(2,1),(2,2)],61,(1,1),true⟩,⟨[(2,0),(3,0),(4,0)],74,(2,0),true⟩,⟨[(2,3),(3,3),(3,4)],143,(2,1),true⟩,⟨[(4,2),(4,3),(5,2)],22,(3,1),false⟩,⟨[(5,0),(5,1),(6,0)],93,(3,0),false⟩]⟩,
  ⟨[(3,5),(4,4),(4,5)],[⟨[(1,4),(2,4),(2,5)],67,(1,4),true⟩,⟨[(2,3),(3,3),(3,4)],58,(2,3),true⟩,⟨[(2,6),(3,6),(3,7)],145,(2,4),true⟩,⟨[(4,2),(4,3),(5,2)],154,(3,2),false⟩,⟨[(4,6),(5,5),(5,6)],107,(3,4),false⟩,⟨[(5,4),(6,4),(6,5)],112,(3,4),false⟩]⟩,
  ⟨[(4,2),(4,3),(5,2)],[⟨[(2,3),(3,3),(3,4)],123,(2,2),true⟩,⟨[(3,1),(3,2),(4,1)],22,(3,1),true⟩,⟨[(3,5),(4,4),(4,5)],154,(3,2),true⟩,⟨[(5,0),(5,1),(6,0)],133,(4,0),false⟩,⟨[(5,3),(6,3),(7,3)],25,(4,2),false⟩,⟨[(6,1),(6,2),(7,1)],93,(4,1),false⟩]⟩,
  ⟨[(4,6),(5,5),(5,6)],[⟨[(2,6),(3,6),(3,7)],125,(2,5),true⟩,⟨[(3,5),(4,4),(4,5)],107,(3,4),true⟩,⟨[(4,7),(5,7),(6,7)],102,(4,5),false⟩,⟨[(5,4),(6,4),(6,5)],138,(4,4),false⟩,⟨[(6,6),(7,6),(7,7)],118,(4,5),false⟩]⟩,
  ⟨[(4,7),(5,7),(6,7)],[⟨[(2,6),(3,6),(3,7)],69,(2,6),true⟩,⟨[(4,6),(5,5),(5,6)],102,(4,5),true⟩,⟨[(6,6),(7,6),(7,7)],126,(4,6),false⟩]⟩,
  ⟨[(5,0),(5,1),(6,0)],[⟨[(2,0),(3,0),(4,0)],83,(2,0),true⟩,⟨[(3,1),(3,2),(4,1)],93,(3,0),true⟩,⟨[(4,2),(4,3),(5,2)],133,(4,0),true⟩,⟨[(6,1),(6,2),(7,1)],22,(5,0),false⟩,⟨[(7,0),(8,0),(8,1)],28,(5,0),false⟩]⟩,
  ⟨[(5,3),(6,3),(7,3)],[⟨[(4,2),(4,3),(5,2)],25,(4,2),true⟩,⟨[(5,4),(6,4),(6,5)],71,(5,3),false⟩,⟨[(6,1),(6,2),(7,1)],147,(5,1),false⟩,⟨[(7,2),(8,2),(8,3)],126,(5,2),false⟩,⟨[(7,4),(7,5),(8,4)],77,(5,3),false⟩]⟩,
  ⟨[(5,4),(6,4),(6,5)],[⟨[(3,5),(4,4),(4,5)],112,(3,4),true⟩,⟨[(4,6),(5,5),(5,6)],138,(4,4),true⟩,⟨[(5,3),(6,3),(7,3)],71,(5,3),true⟩,⟨[(6,6),(7,6),(7,7)],59,(5,4),false⟩,⟨[(7,4),(7,5),(8,4)],61,(5,4),false⟩]⟩,
  ⟨[(6,1),(6,2),(7,1)],[⟨[(4,2),(4,3),(5,2)],93,(4,1),true⟩,⟨[(5,0),(5,1),(6,0)],22,(5,0),true⟩,⟨[(5,3),(6,3),(7,3)],147,(5,1),true⟩,⟨[(7,0),(8,0),(8,1)],90,(6,0),false⟩,⟨[(7,2),(8,2),(8,3)],24,(6,1),false⟩]⟩,
  ⟨[(6,6),(7,6),(7,7)],[⟨[(4,6),(5,5),(5,6)],118,(4,5),true⟩,⟨[(4,7),(5,7),(6,7)],126,(4,6),true⟩,⟨[(5,4),(6,4),(6,5)],59,(5,4),true⟩,⟨[(7,4),(7,5),(8,4)],143,(6,4),false⟩,⟨[(8,5),(8,6),(8,7)],122,(6,5),false⟩]⟩,
  ⟨[(7,0),(8,0),(8,1)],[⟨[(5,0),(5,1),(6,0)],28,(5,0),true⟩,⟨[(6,1),(6,2),(7,1)],90,(6,0),true⟩,⟨[(7,2),(8,2),(8,3)],52,(7,0),false⟩]⟩,
  ⟨[(7,2),(8,2),(8,3)],[⟨[(5,3),(6,3),(7,3)],126,(5,2),true⟩,⟨[(6,1),(6,2),(7,1)],24,(6,1),true⟩,⟨[(7,0),(8,0),(8,1)],52,(7,0),true⟩,⟨[(7,4),(7,5),(8,4)],51,(7,2),false⟩]⟩,
  ⟨[(7,4),(7,5),(8,4)],[⟨[(5,3),(6,3),(7,3)],77,(5,3),true⟩,⟨[(5,4),(6,4),(6,5)],61,(5,4),true⟩,⟨[(6,6),(7,6),(7,7)],143,(6,4),true⟩,⟨[(7,2),(8,2),(8,3)],51,(7,2),true⟩,⟨[(8,5),(8,6),(8,7)],21,(7,4),false⟩]⟩,
  ⟨[(8,5),(8,6),(8,7)],[⟨[(6,6),(7,6),(7,7)],122,(6,5),true⟩,⟨[(7,4),(7,5),(8,4)],21,(7,4),true⟩]⟩,
]
theorem Width8_b1_entries_match : CatalogLinksCheck catalog Width8_b1_entries := by decide +kernel
theorem Width8_b1_entries_links : CertifiedLinks (localEntries Width8_b1_entries) :=
  catalogLinks_sound catalog_sound Width8_b1_entries_match

def Width8_b1_tiles := EntryTiles (localEntries Width8_b1_entries)
def Width8_b1_owner : Cell → List Cell := tableOwner 8 Width8_b1_tiles [0,0,1,2,2,2,3,4,0,5,1,1,6,3,3,4,7,5,5,8,6,6,9,4,7,10,10,8,8,11,9,9,7,10,12,12,11,11,13,14,15,15,12,16,17,13,13,14,15,18,18,16,17,17,19,14,20,18,21,16,22,22,19,19,20,20,21,21,22,23,23,23]
theorem Width8_b1_partition : OwnerPartitionCheck 9 8 Width8_b1_tiles Width8_b1_owner := by decide +kernel
theorem Width8_b1_cover : EdgeCoverCheck (localEntries Width8_b1_entries) Width8_b1_owner 0 0 9 8 := by decide +kernel
def Width8_b1 : RigidBlock 9 8 :=
  localCheckedBlock Width8_b1_partition Width8_b1_entries_links Width8_b1_cover

def Width8_vertical_0_entries : List EntryData := [
  ⟨[(0,0),(0,1),(1,0)],[]⟩,
  ⟨[(0,2),(1,2),(1,3)],[]⟩,
  ⟨[(0,3),(0,4),(0,5)],[]⟩,
  ⟨[(0,6),(1,5),(1,6)],[]⟩,
  ⟨[(0,7),(1,7),(2,7)],[]⟩,
  ⟨[(1,1),(2,1),(2,2)],[]⟩,
  ⟨[(1,4),(2,4),(2,5)],[]⟩,
  ⟨[(2,0),(3,0),(3,1)],[]⟩,
  ⟨[(2,3),(3,3),(3,4)],[]⟩,
  ⟨[(2,6),(3,6),(3,7)],[]⟩,
  ⟨[(3,2),(4,1),(4,2)],[]⟩,
  ⟨[(3,5),(4,5),(4,6)],[]⟩,
  ⟨[(4,0),(5,0),(5,1)],[⟨[(6,0),(6,1),(7,0)],61,(4,0),false⟩]⟩,
  ⟨[(4,3),(5,2),(5,3)],[⟨[(6,2),(7,2),(7,3)],112,(4,2),false⟩,⟨[(6,3),(6,4),(6,5)],114,(4,2),false⟩]⟩,
  ⟨[(4,4),(5,4),(5,5)],[⟨[(6,3),(6,4),(6,5)],122,(4,3),false⟩]⟩,
  ⟨[(4,7),(5,6),(5,7)],[⟨[(6,6),(7,5),(7,6)],142,(4,5),false⟩,⟨[(6,7),(7,7),(8,7)],119,(4,6),false⟩]⟩,
]
theorem Width8_vertical_0_entries_match : CatalogLinksCheck catalog Width8_vertical_0_entries := by decide +kernel
theorem Width8_vertical_0_entries_links : CertifiedLinks (localEntries Width8_vertical_0_entries) :=
  catalogLinks_sound catalog_sound Width8_vertical_0_entries_match

theorem Width8_vertical_0_same : EntryTiles (localEntries Width8_vertical_0_entries) = Width8_b0_tiles := by rfl
theorem Width8_vertical_0_cover : EdgeCoverCheck (localEntries Width8_vertical_0_entries)
    (shiftOwner (6,0) Width8_b0_owner) 6 0 6 8 := by decide +kernel
theorem Width8_vertical_0 : ∀ A B, Width8_b0.tiles A → Width8_b0.tiles B → Rigid A (Shift (6,0) B) := by
  have hp := localSeam_rigid (h := 6) (w := 8)
    (Width8_vertical_0_same.symm ▸ Width8_b0.partition) Width8_b0_partition
    Width8_vertical_0_entries_links Width8_vertical_0_cover
    (side_disjoint 6 8 6 8).1
  rw [Width8_vertical_0_same] at hp
  exact hp

def Width8_vertical_1_entries : List EntryData := [
  ⟨[(0,0),(0,1),(1,0)],[]⟩,
  ⟨[(0,2),(1,2),(1,3)],[]⟩,
  ⟨[(0,3),(0,4),(0,5)],[]⟩,
  ⟨[(0,6),(1,5),(1,6)],[]⟩,
  ⟨[(0,7),(1,7),(2,7)],[]⟩,
  ⟨[(1,1),(2,1),(2,2)],[]⟩,
  ⟨[(1,4),(2,4),(2,5)],[]⟩,
  ⟨[(2,0),(3,0),(3,1)],[]⟩,
  ⟨[(2,3),(3,3),(3,4)],[]⟩,
  ⟨[(2,6),(3,6),(3,7)],[]⟩,
  ⟨[(3,2),(4,1),(4,2)],[]⟩,
  ⟨[(3,5),(4,5),(4,6)],[]⟩,
  ⟨[(4,0),(5,0),(5,1)],[⟨[(6,0),(6,1),(7,0)],61,(4,0),false⟩]⟩,
  ⟨[(4,3),(5,2),(5,3)],[⟨[(6,2),(7,2),(7,3)],112,(4,2),false⟩,⟨[(6,3),(6,4),(6,5)],114,(4,2),false⟩]⟩,
  ⟨[(4,4),(5,4),(5,5)],[⟨[(6,3),(6,4),(6,5)],122,(4,3),false⟩]⟩,
  ⟨[(4,7),(5,6),(5,7)],[⟨[(6,6),(7,5),(7,6)],142,(4,5),false⟩,⟨[(6,7),(7,7),(8,7)],119,(4,6),false⟩]⟩,
]
theorem Width8_vertical_1_entries_match : CatalogLinksCheck catalog Width8_vertical_1_entries := by decide +kernel
theorem Width8_vertical_1_entries_links : CertifiedLinks (localEntries Width8_vertical_1_entries) :=
  catalogLinks_sound catalog_sound Width8_vertical_1_entries_match

theorem Width8_vertical_1_same : EntryTiles (localEntries Width8_vertical_1_entries) = Width8_b0_tiles := by rfl
theorem Width8_vertical_1_cover : EdgeCoverCheck (localEntries Width8_vertical_1_entries)
    (shiftOwner (6,0) Width8_b1_owner) 6 0 9 8 := by decide +kernel
theorem Width8_vertical_1 : ∀ A B, Width8_b0.tiles A → Width8_b1.tiles B → Rigid A (Shift (6,0) B) := by
  have hp := localSeam_rigid (h := 6) (w := 8)
    (Width8_vertical_1_same.symm ▸ Width8_b0.partition) Width8_b1_partition
    Width8_vertical_1_entries_links Width8_vertical_1_cover
    (side_disjoint 6 8 9 8).1
  rw [Width8_vertical_1_same] at hp
  exact hp

def Width8_vertical_2_entries : List EntryData := [
  ⟨[(0,0),(0,1),(1,0)],[]⟩,
  ⟨[(0,2),(1,2),(1,3)],[]⟩,
  ⟨[(0,3),(0,4),(0,5)],[]⟩,
  ⟨[(0,6),(1,5),(1,6)],[]⟩,
  ⟨[(0,7),(1,7),(2,7)],[]⟩,
  ⟨[(1,1),(2,1),(2,2)],[]⟩,
  ⟨[(1,4),(2,4),(2,5)],[]⟩,
  ⟨[(2,0),(3,0),(4,0)],[]⟩,
  ⟨[(2,3),(3,3),(3,4)],[]⟩,
  ⟨[(2,6),(3,6),(3,7)],[]⟩,
  ⟨[(3,1),(3,2),(4,1)],[]⟩,
  ⟨[(3,5),(4,4),(4,5)],[]⟩,
  ⟨[(4,2),(4,3),(5,2)],[]⟩,
  ⟨[(4,6),(5,5),(5,6)],[]⟩,
  ⟨[(4,7),(5,7),(6,7)],[]⟩,
  ⟨[(5,0),(5,1),(6,0)],[]⟩,
  ⟨[(5,3),(6,3),(7,3)],[]⟩,
  ⟨[(5,4),(6,4),(6,5)],[]⟩,
  ⟨[(6,1),(6,2),(7,1)],[]⟩,
  ⟨[(6,6),(7,6),(7,7)],[]⟩,
  ⟨[(7,0),(8,0),(8,1)],[⟨[(9,0),(9,1),(10,0)],61,(7,0),false⟩]⟩,
  ⟨[(7,2),(8,2),(8,3)],[⟨[(9,2),(10,2),(10,3)],62,(7,2),false⟩,⟨[(9,3),(9,4),(9,5)],64,(7,2),false⟩]⟩,
  ⟨[(7,4),(7,5),(8,4)],[⟨[(9,3),(9,4),(9,5)],92,(7,3),false⟩]⟩,
  ⟨[(8,5),(8,6),(8,7)],[⟨[(9,3),(9,4),(9,5)],132,(8,3),false⟩,⟨[(9,6),(10,5),(10,6)],9,(8,5),false⟩,⟨[(9,7),(10,7),(11,7)],16,(8,5),false⟩]⟩,
]
theorem Width8_vertical_2_entries_match : CatalogLinksCheck catalog Width8_vertical_2_entries := by decide +kernel
theorem Width8_vertical_2_entries_links : CertifiedLinks (localEntries Width8_vertical_2_entries) :=
  catalogLinks_sound catalog_sound Width8_vertical_2_entries_match

theorem Width8_vertical_2_same : EntryTiles (localEntries Width8_vertical_2_entries) = Width8_b1_tiles := by rfl
theorem Width8_vertical_2_cover : EdgeCoverCheck (localEntries Width8_vertical_2_entries)
    (shiftOwner (9,0) Width8_b0_owner) 9 0 6 8 := by decide +kernel
theorem Width8_vertical_2 : ∀ A B, Width8_b1.tiles A → Width8_b0.tiles B → Rigid A (Shift (9,0) B) := by
  have hp := localSeam_rigid (h := 9) (w := 8)
    (Width8_vertical_2_same.symm ▸ Width8_b1.partition) Width8_b0_partition
    Width8_vertical_2_entries_links Width8_vertical_2_cover
    (side_disjoint 9 8 6 8).1
  rw [Width8_vertical_2_same] at hp
  exact hp

def Width8_vertical_3_entries : List EntryData := [
  ⟨[(0,0),(0,1),(1,0)],[]⟩,
  ⟨[(0,2),(1,2),(1,3)],[]⟩,
  ⟨[(0,3),(0,4),(0,5)],[]⟩,
  ⟨[(0,6),(1,5),(1,6)],[]⟩,
  ⟨[(0,7),(1,7),(2,7)],[]⟩,
  ⟨[(1,1),(2,1),(2,2)],[]⟩,
  ⟨[(1,4),(2,4),(2,5)],[]⟩,
  ⟨[(2,0),(3,0),(4,0)],[]⟩,
  ⟨[(2,3),(3,3),(3,4)],[]⟩,
  ⟨[(2,6),(3,6),(3,7)],[]⟩,
  ⟨[(3,1),(3,2),(4,1)],[]⟩,
  ⟨[(3,5),(4,4),(4,5)],[]⟩,
  ⟨[(4,2),(4,3),(5,2)],[]⟩,
  ⟨[(4,6),(5,5),(5,6)],[]⟩,
  ⟨[(4,7),(5,7),(6,7)],[]⟩,
  ⟨[(5,0),(5,1),(6,0)],[]⟩,
  ⟨[(5,3),(6,3),(7,3)],[]⟩,
  ⟨[(5,4),(6,4),(6,5)],[]⟩,
  ⟨[(6,1),(6,2),(7,1)],[]⟩,
  ⟨[(6,6),(7,6),(7,7)],[]⟩,
  ⟨[(7,0),(8,0),(8,1)],[⟨[(9,0),(9,1),(10,0)],61,(7,0),false⟩]⟩,
  ⟨[(7,2),(8,2),(8,3)],[⟨[(9,2),(10,2),(10,3)],62,(7,2),false⟩,⟨[(9,3),(9,4),(9,5)],64,(7,2),false⟩]⟩,
  ⟨[(7,4),(7,5),(8,4)],[⟨[(9,3),(9,4),(9,5)],92,(7,3),false⟩]⟩,
  ⟨[(8,5),(8,6),(8,7)],[⟨[(9,3),(9,4),(9,5)],132,(8,3),false⟩,⟨[(9,6),(10,5),(10,6)],9,(8,5),false⟩,⟨[(9,7),(10,7),(11,7)],16,(8,5),false⟩]⟩,
]
theorem Width8_vertical_3_entries_match : CatalogLinksCheck catalog Width8_vertical_3_entries := by decide +kernel
theorem Width8_vertical_3_entries_links : CertifiedLinks (localEntries Width8_vertical_3_entries) :=
  catalogLinks_sound catalog_sound Width8_vertical_3_entries_match

theorem Width8_vertical_3_same : EntryTiles (localEntries Width8_vertical_3_entries) = Width8_b1_tiles := by rfl
theorem Width8_vertical_3_cover : EdgeCoverCheck (localEntries Width8_vertical_3_entries)
    (shiftOwner (9,0) Width8_b1_owner) 9 0 9 8 := by decide +kernel
theorem Width8_vertical_3 : ∀ A B, Width8_b1.tiles A → Width8_b1.tiles B → Rigid A (Shift (9,0) B) := by
  have hp := localSeam_rigid (h := 9) (w := 8)
    (Width8_vertical_3_same.symm ▸ Width8_b1.partition) Width8_b1_partition
    Width8_vertical_3_entries_links Width8_vertical_3_cover
    (side_disjoint 9 8 9 8).1
  rw [Width8_vertical_3_same] at hp
  exact hp

def Width8_palette : VerticalPalette (fun h => h = 6 ∨ h = 9) 8 where
  tiles h := if h = 6 then Width8_b0.tiles else Width8_b1.tiles
  partition := by
    intro h hh
    rcases hh with rfl | rfl
    · exact Width8_b0.partition
    · exact Width8_b1.partition
  internal := by
    intro h hh
    rcases hh with rfl | rfl
    · exact Width8_b0.internal
    · exact Width8_b1.internal
  vertical := by
    intro h k hh hk
    rcases hh with rfl | rfl <;> rcases hk with rfl | rfl
    · exact Width8_vertical_0
    · exact Width8_vertical_1
    · exact Width8_vertical_2
    · exact Width8_vertical_3

end LockedTromino.Witnesses
