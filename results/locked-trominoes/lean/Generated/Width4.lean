import Generated.Catalog

namespace LockedTromino.Witnesses
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def Width4_b0_entries : List EntryData := [
  ⟨[(0,0),(0,1),(0,2)],[⟨[(0,3),(1,2),(1,3)],3,(0,0),false⟩,⟨[(1,0),(1,1),(2,1)],6,(0,0),false⟩]⟩,
  ⟨[(0,3),(1,2),(1,3)],[⟨[(0,0),(0,1),(0,2)],3,(0,0),true⟩,⟨[(1,0),(1,1),(2,1)],155,(0,0),false⟩,⟨[(2,2),(2,3),(3,3)],111,(0,2),false⟩]⟩,
  ⟨[(1,0),(1,1),(2,1)],[⟨[(0,0),(0,1),(0,2)],6,(0,0),true⟩,⟨[(0,3),(1,2),(1,3)],155,(0,0),true⟩,⟨[(2,0),(3,0),(4,0)],34,(1,0),false⟩,⟨[(2,2),(2,3),(3,3)],37,(1,0),false⟩,⟨[(3,1),(3,2),(4,2)],46,(1,0),false⟩]⟩,
  ⟨[(2,0),(3,0),(4,0)],[⟨[(1,0),(1,1),(2,1)],34,(1,0),true⟩,⟨[(3,1),(3,2),(4,2)],75,(2,0),false⟩,⟨[(4,1),(5,0),(5,1)],79,(2,0),false⟩]⟩,
  ⟨[(2,2),(2,3),(3,3)],[⟨[(0,3),(1,2),(1,3)],111,(0,2),true⟩,⟨[(1,0),(1,1),(2,1)],37,(1,0),true⟩,⟨[(3,1),(3,2),(4,2)],97,(2,1),false⟩,⟨[(4,3),(5,2),(5,3)],47,(2,2),false⟩]⟩,
  ⟨[(3,1),(3,2),(4,2)],[⟨[(1,0),(1,1),(2,1)],46,(1,0),true⟩,⟨[(2,0),(3,0),(4,0)],75,(2,0),true⟩,⟨[(2,2),(2,3),(3,3)],97,(2,1),true⟩,⟨[(4,1),(5,0),(5,1)],98,(3,0),false⟩,⟨[(4,3),(5,2),(5,3)],38,(3,1),false⟩]⟩,
  ⟨[(4,1),(5,0),(5,1)],[⟨[(2,0),(3,0),(4,0)],79,(2,0),true⟩,⟨[(3,1),(3,2),(4,2)],98,(3,0),true⟩,⟨[(4,3),(5,2),(5,3)],103,(4,0),false⟩]⟩,
  ⟨[(4,3),(5,2),(5,3)],[⟨[(2,2),(2,3),(3,3)],47,(2,2),true⟩,⟨[(3,1),(3,2),(4,2)],38,(3,1),true⟩,⟨[(4,1),(5,0),(5,1)],103,(4,0),true⟩]⟩,
]
theorem Width4_b0_entries_match : CatalogLinksCheck catalog Width4_b0_entries := by decide +kernel
theorem Width4_b0_entries_links : CertifiedLinks (localEntries Width4_b0_entries) :=
  catalogLinks_sound catalog_sound Width4_b0_entries_match

def Width4_b0_tiles := EntryTiles (localEntries Width4_b0_entries)
def Width4_b0_owner : Cell → List Cell := tableOwner 4 Width4_b0_tiles [0,0,0,1,2,2,1,1,3,2,4,4,3,5,5,4,3,6,5,7,6,6,7,7]
theorem Width4_b0_partition : OwnerPartitionCheck 6 4 Width4_b0_tiles Width4_b0_owner := by decide +kernel
theorem Width4_b0_cover : EdgeCoverCheck (localEntries Width4_b0_entries) Width4_b0_owner 0 0 6 4 := by decide +kernel
def Width4_b0 : RigidBlock 6 4 :=
  localCheckedBlock Width4_b0_partition Width4_b0_entries_links Width4_b0_cover

def Width4_b1_entries : List EntryData := [
  ⟨[(0,0),(0,1),(0,2)],[⟨[(0,3),(1,2),(1,3)],3,(0,0),false⟩,⟨[(1,0),(1,1),(2,1)],6,(0,0),false⟩]⟩,
  ⟨[(0,3),(1,2),(1,3)],[⟨[(0,0),(0,1),(0,2)],3,(0,0),true⟩,⟨[(1,0),(1,1),(2,1)],155,(0,0),false⟩,⟨[(2,2),(2,3),(3,3)],111,(0,2),false⟩]⟩,
  ⟨[(1,0),(1,1),(2,1)],[⟨[(0,0),(0,1),(0,2)],6,(0,0),true⟩,⟨[(0,3),(1,2),(1,3)],155,(0,0),true⟩,⟨[(2,0),(3,0),(4,0)],34,(1,0),false⟩,⟨[(2,2),(2,3),(3,3)],37,(1,0),false⟩,⟨[(3,1),(3,2),(4,1)],45,(1,0),false⟩]⟩,
  ⟨[(2,0),(3,0),(4,0)],[⟨[(1,0),(1,1),(2,1)],34,(1,0),true⟩,⟨[(3,1),(3,2),(4,1)],74,(2,0),false⟩,⟨[(5,0),(6,0),(7,0)],86,(2,0),false⟩]⟩,
  ⟨[(2,2),(2,3),(3,3)],[⟨[(0,3),(1,2),(1,3)],111,(0,2),true⟩,⟨[(1,0),(1,1),(2,1)],37,(1,0),true⟩,⟨[(3,1),(3,2),(4,1)],96,(2,1),false⟩,⟨[(4,2),(4,3),(5,2)],42,(2,2),false⟩]⟩,
  ⟨[(3,1),(3,2),(4,1)],[⟨[(1,0),(1,1),(2,1)],45,(1,0),true⟩,⟨[(2,0),(3,0),(4,0)],74,(2,0),true⟩,⟨[(2,2),(2,3),(3,3)],96,(2,1),true⟩,⟨[(4,2),(4,3),(5,2)],22,(3,1),false⟩,⟨[(5,1),(6,1),(6,2)],28,(3,1),false⟩]⟩,
  ⟨[(4,2),(4,3),(5,2)],[⟨[(2,2),(2,3),(3,3)],42,(2,2),true⟩,⟨[(3,1),(3,2),(4,1)],22,(3,1),true⟩,⟨[(5,1),(6,1),(6,2)],90,(4,1),false⟩,⟨[(5,3),(6,3),(7,3)],25,(4,2),false⟩]⟩,
  ⟨[(5,0),(6,0),(7,0)],[⟨[(2,0),(3,0),(4,0)],86,(2,0),true⟩,⟨[(5,1),(6,1),(6,2)],71,(5,0),false⟩,⟨[(7,1),(8,0),(8,1)],79,(5,0),false⟩]⟩,
  ⟨[(5,1),(6,1),(6,2)],[⟨[(3,1),(3,2),(4,1)],28,(3,1),true⟩,⟨[(4,2),(4,3),(5,2)],90,(4,1),true⟩,⟨[(5,0),(6,0),(7,0)],71,(5,0),true⟩,⟨[(5,3),(6,3),(7,3)],53,(5,1),false⟩,⟨[(7,1),(8,0),(8,1)],125,(5,0),false⟩,⟨[(7,2),(8,2),(8,3)],68,(5,1),false⟩]⟩,
  ⟨[(5,3),(6,3),(7,3)],[⟨[(4,2),(4,3),(5,2)],25,(4,2),true⟩,⟨[(5,1),(6,1),(6,2)],53,(5,1),true⟩,⟨[(7,2),(8,2),(8,3)],126,(5,2),false⟩]⟩,
  ⟨[(7,1),(8,0),(8,1)],[⟨[(5,0),(6,0),(7,0)],79,(5,0),true⟩,⟨[(5,1),(6,1),(6,2)],125,(5,0),true⟩,⟨[(7,2),(8,2),(8,3)],101,(7,0),false⟩]⟩,
  ⟨[(7,2),(8,2),(8,3)],[⟨[(5,1),(6,1),(6,2)],68,(5,1),true⟩,⟨[(5,3),(6,3),(7,3)],126,(5,2),true⟩,⟨[(7,1),(8,0),(8,1)],101,(7,0),true⟩]⟩,
]
theorem Width4_b1_entries_match : CatalogLinksCheck catalog Width4_b1_entries := by decide +kernel
theorem Width4_b1_entries_links : CertifiedLinks (localEntries Width4_b1_entries) :=
  catalogLinks_sound catalog_sound Width4_b1_entries_match

def Width4_b1_tiles := EntryTiles (localEntries Width4_b1_entries)
def Width4_b1_owner : Cell → List Cell := tableOwner 4 Width4_b1_tiles [0,0,0,1,2,2,1,1,3,2,4,4,3,5,5,4,3,5,6,6,7,8,6,9,7,8,8,9,7,10,11,9,10,10,11,11]
theorem Width4_b1_partition : OwnerPartitionCheck 9 4 Width4_b1_tiles Width4_b1_owner := by decide +kernel
theorem Width4_b1_cover : EdgeCoverCheck (localEntries Width4_b1_entries) Width4_b1_owner 0 0 9 4 := by decide +kernel
def Width4_b1 : RigidBlock 9 4 :=
  localCheckedBlock Width4_b1_partition Width4_b1_entries_links Width4_b1_cover

def Width4_vertical_0_entries : List EntryData := [
  ⟨[(0,0),(0,1),(0,2)],[]⟩,
  ⟨[(0,3),(1,2),(1,3)],[]⟩,
  ⟨[(1,0),(1,1),(2,1)],[]⟩,
  ⟨[(2,0),(3,0),(4,0)],[]⟩,
  ⟨[(2,2),(2,3),(3,3)],[]⟩,
  ⟨[(3,1),(3,2),(4,2)],[]⟩,
  ⟨[(4,1),(5,0),(5,1)],[⟨[(6,0),(6,1),(6,2)],110,(4,0),false⟩]⟩,
  ⟨[(4,3),(5,2),(5,3)],[⟨[(6,0),(6,1),(6,2)],157,(4,0),false⟩,⟨[(6,3),(7,2),(7,3)],117,(4,2),false⟩]⟩,
]
theorem Width4_vertical_0_entries_match : CatalogLinksCheck catalog Width4_vertical_0_entries := by decide +kernel
theorem Width4_vertical_0_entries_links : CertifiedLinks (localEntries Width4_vertical_0_entries) :=
  catalogLinks_sound catalog_sound Width4_vertical_0_entries_match

theorem Width4_vertical_0_same : EntryTiles (localEntries Width4_vertical_0_entries) = Width4_b0_tiles := by rfl
theorem Width4_vertical_0_cover : EdgeCoverCheck (localEntries Width4_vertical_0_entries)
    (shiftOwner (6,0) Width4_b0_owner) 6 0 6 4 := by decide +kernel
theorem Width4_vertical_0 : ∀ A B, Width4_b0.tiles A → Width4_b0.tiles B → Rigid A (Shift (6,0) B) := by
  have hp := localSeam_rigid (h := 6) (w := 4)
    (Width4_vertical_0_same.symm ▸ Width4_b0.partition) Width4_b0_partition
    Width4_vertical_0_entries_links Width4_vertical_0_cover
    (side_disjoint 6 4 6 4).1
  rw [Width4_vertical_0_same] at hp
  exact hp

def Width4_vertical_1_entries : List EntryData := [
  ⟨[(0,0),(0,1),(0,2)],[]⟩,
  ⟨[(0,3),(1,2),(1,3)],[]⟩,
  ⟨[(1,0),(1,1),(2,1)],[]⟩,
  ⟨[(2,0),(3,0),(4,0)],[]⟩,
  ⟨[(2,2),(2,3),(3,3)],[]⟩,
  ⟨[(3,1),(3,2),(4,2)],[]⟩,
  ⟨[(4,1),(5,0),(5,1)],[⟨[(6,0),(6,1),(6,2)],110,(4,0),false⟩]⟩,
  ⟨[(4,3),(5,2),(5,3)],[⟨[(6,0),(6,1),(6,2)],157,(4,0),false⟩,⟨[(6,3),(7,2),(7,3)],117,(4,2),false⟩]⟩,
]
theorem Width4_vertical_1_entries_match : CatalogLinksCheck catalog Width4_vertical_1_entries := by decide +kernel
theorem Width4_vertical_1_entries_links : CertifiedLinks (localEntries Width4_vertical_1_entries) :=
  catalogLinks_sound catalog_sound Width4_vertical_1_entries_match

theorem Width4_vertical_1_same : EntryTiles (localEntries Width4_vertical_1_entries) = Width4_b0_tiles := by rfl
theorem Width4_vertical_1_cover : EdgeCoverCheck (localEntries Width4_vertical_1_entries)
    (shiftOwner (6,0) Width4_b1_owner) 6 0 9 4 := by decide +kernel
theorem Width4_vertical_1 : ∀ A B, Width4_b0.tiles A → Width4_b1.tiles B → Rigid A (Shift (6,0) B) := by
  have hp := localSeam_rigid (h := 6) (w := 4)
    (Width4_vertical_1_same.symm ▸ Width4_b0.partition) Width4_b1_partition
    Width4_vertical_1_entries_links Width4_vertical_1_cover
    (side_disjoint 6 4 9 4).1
  rw [Width4_vertical_1_same] at hp
  exact hp

def Width4_vertical_2_entries : List EntryData := [
  ⟨[(0,0),(0,1),(0,2)],[]⟩,
  ⟨[(0,3),(1,2),(1,3)],[]⟩,
  ⟨[(1,0),(1,1),(2,1)],[]⟩,
  ⟨[(2,0),(3,0),(4,0)],[]⟩,
  ⟨[(2,2),(2,3),(3,3)],[]⟩,
  ⟨[(3,1),(3,2),(4,1)],[]⟩,
  ⟨[(4,2),(4,3),(5,2)],[]⟩,
  ⟨[(5,0),(6,0),(7,0)],[]⟩,
  ⟨[(5,1),(6,1),(6,2)],[]⟩,
  ⟨[(5,3),(6,3),(7,3)],[]⟩,
  ⟨[(7,1),(8,0),(8,1)],[⟨[(9,0),(9,1),(9,2)],110,(7,0),false⟩]⟩,
  ⟨[(7,2),(8,2),(8,3)],[⟨[(9,0),(9,1),(9,2)],146,(7,0),false⟩,⟨[(9,3),(10,2),(10,3)],67,(7,2),false⟩]⟩,
]
theorem Width4_vertical_2_entries_match : CatalogLinksCheck catalog Width4_vertical_2_entries := by decide +kernel
theorem Width4_vertical_2_entries_links : CertifiedLinks (localEntries Width4_vertical_2_entries) :=
  catalogLinks_sound catalog_sound Width4_vertical_2_entries_match

theorem Width4_vertical_2_same : EntryTiles (localEntries Width4_vertical_2_entries) = Width4_b1_tiles := by rfl
theorem Width4_vertical_2_cover : EdgeCoverCheck (localEntries Width4_vertical_2_entries)
    (shiftOwner (9,0) Width4_b0_owner) 9 0 6 4 := by decide +kernel
theorem Width4_vertical_2 : ∀ A B, Width4_b1.tiles A → Width4_b0.tiles B → Rigid A (Shift (9,0) B) := by
  have hp := localSeam_rigid (h := 9) (w := 4)
    (Width4_vertical_2_same.symm ▸ Width4_b1.partition) Width4_b0_partition
    Width4_vertical_2_entries_links Width4_vertical_2_cover
    (side_disjoint 9 4 6 4).1
  rw [Width4_vertical_2_same] at hp
  exact hp

def Width4_vertical_3_entries : List EntryData := [
  ⟨[(0,0),(0,1),(0,2)],[]⟩,
  ⟨[(0,3),(1,2),(1,3)],[]⟩,
  ⟨[(1,0),(1,1),(2,1)],[]⟩,
  ⟨[(2,0),(3,0),(4,0)],[]⟩,
  ⟨[(2,2),(2,3),(3,3)],[]⟩,
  ⟨[(3,1),(3,2),(4,1)],[]⟩,
  ⟨[(4,2),(4,3),(5,2)],[]⟩,
  ⟨[(5,0),(6,0),(7,0)],[]⟩,
  ⟨[(5,1),(6,1),(6,2)],[]⟩,
  ⟨[(5,3),(6,3),(7,3)],[]⟩,
  ⟨[(7,1),(8,0),(8,1)],[⟨[(9,0),(9,1),(9,2)],110,(7,0),false⟩]⟩,
  ⟨[(7,2),(8,2),(8,3)],[⟨[(9,0),(9,1),(9,2)],146,(7,0),false⟩,⟨[(9,3),(10,2),(10,3)],67,(7,2),false⟩]⟩,
]
theorem Width4_vertical_3_entries_match : CatalogLinksCheck catalog Width4_vertical_3_entries := by decide +kernel
theorem Width4_vertical_3_entries_links : CertifiedLinks (localEntries Width4_vertical_3_entries) :=
  catalogLinks_sound catalog_sound Width4_vertical_3_entries_match

theorem Width4_vertical_3_same : EntryTiles (localEntries Width4_vertical_3_entries) = Width4_b1_tiles := by rfl
theorem Width4_vertical_3_cover : EdgeCoverCheck (localEntries Width4_vertical_3_entries)
    (shiftOwner (9,0) Width4_b1_owner) 9 0 9 4 := by decide +kernel
theorem Width4_vertical_3 : ∀ A B, Width4_b1.tiles A → Width4_b1.tiles B → Rigid A (Shift (9,0) B) := by
  have hp := localSeam_rigid (h := 9) (w := 4)
    (Width4_vertical_3_same.symm ▸ Width4_b1.partition) Width4_b1_partition
    Width4_vertical_3_entries_links Width4_vertical_3_cover
    (side_disjoint 9 4 9 4).1
  rw [Width4_vertical_3_same] at hp
  exact hp

def Width4_palette : VerticalPalette (fun h => h = 6 ∨ h = 9) 4 where
  tiles h := if h = 6 then Width4_b0.tiles else Width4_b1.tiles
  partition := by
    intro h hh
    rcases hh with rfl | rfl
    · exact Width4_b0.partition
    · exact Width4_b1.partition
  internal := by
    intro h hh
    rcases hh with rfl | rfl
    · exact Width4_b0.internal
    · exact Width4_b1.internal
  vertical := by
    intro h k hh hk
    rcases hh with rfl | rfl <;> rcases hk with rfl | rfl
    · exact Width4_vertical_0
    · exact Width4_vertical_1
    · exact Width4_vertical_2
    · exact Width4_vertical_3

end LockedTromino.Witnesses
