import Generated.Catalog

namespace LockedTromino.Witnesses
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def Width9_b0_entries : List EntryData := [
  ⟨[(0,0),(0,1),(0,2)],[⟨[(0,3),(1,2),(1,3)],3,(0,0),false⟩,⟨[(1,0),(1,1),(2,1)],6,(0,0),false⟩]⟩,
  ⟨[(0,3),(1,2),(1,3)],[⟨[(0,0),(0,1),(0,2)],3,(0,0),true⟩,⟨[(0,4),(1,4),(1,5)],101,(0,2),false⟩,⟨[(1,0),(1,1),(2,1)],155,(0,0),false⟩,⟨[(2,2),(3,1),(3,2)],142,(0,1),false⟩,⟨[(2,3),(2,4),(2,5)],114,(0,2),false⟩]⟩,
  ⟨[(0,4),(1,4),(1,5)],[⟨[(0,3),(1,2),(1,3)],101,(0,2),true⟩,⟨[(0,5),(0,6),(0,7)],50,(0,4),false⟩,⟨[(1,6),(2,6),(2,7)],59,(0,4),false⟩,⟨[(2,3),(2,4),(2,5)],122,(0,3),false⟩]⟩,
  ⟨[(0,5),(0,6),(0,7)],[⟨[(0,4),(1,4),(1,5)],50,(0,4),true⟩,⟨[(0,8),(1,7),(1,8)],3,(0,5),false⟩,⟨[(1,6),(2,6),(2,7)],10,(0,5),false⟩]⟩,
  ⟨[(0,8),(1,7),(1,8)],[⟨[(0,5),(0,6),(0,7)],3,(0,5),true⟩,⟨[(1,6),(2,6),(2,7)],138,(0,6),false⟩,⟨[(2,8),(3,8),(4,8)],119,(0,7),false⟩]⟩,
  ⟨[(1,0),(1,1),(2,1)],[⟨[(0,0),(0,1),(0,2)],6,(0,0),true⟩,⟨[(0,3),(1,2),(1,3)],155,(0,0),true⟩,⟨[(2,0),(3,0),(4,0)],34,(1,0),false⟩,⟨[(2,2),(3,1),(3,2)],38,(1,0),false⟩]⟩,
  ⟨[(1,6),(2,6),(2,7)],[⟨[(0,4),(1,4),(1,5)],59,(0,4),true⟩,⟨[(0,5),(0,6),(0,7)],10,(0,5),true⟩,⟨[(0,8),(1,7),(1,8)],138,(0,6),true⟩,⟨[(2,3),(2,4),(2,5)],158,(1,3),false⟩,⟨[(2,8),(3,8),(4,8)],60,(1,6),false⟩,⟨[(3,5),(3,6),(3,7)],122,(1,5),false⟩]⟩,
  ⟨[(2,0),(3,0),(4,0)],[⟨[(1,0),(1,1),(2,1)],34,(1,0),true⟩,⟨[(2,2),(3,1),(3,2)],72,(2,0),false⟩,⟨[(4,1),(5,0),(5,1)],79,(2,0),false⟩]⟩,
  ⟨[(2,2),(3,1),(3,2)],[⟨[(0,3),(1,2),(1,3)],142,(0,1),true⟩,⟨[(1,0),(1,1),(2,1)],38,(1,0),true⟩,⟨[(2,0),(3,0),(4,0)],72,(2,0),true⟩,⟨[(2,3),(2,4),(2,5)],99,(2,1),false⟩,⟨[(3,3),(4,2),(4,3)],107,(2,1),false⟩,⟨[(4,1),(5,0),(5,1)],142,(2,0),false⟩]⟩,
  ⟨[(2,3),(2,4),(2,5)],[⟨[(0,3),(1,2),(1,3)],114,(0,2),true⟩,⟨[(0,4),(1,4),(1,5)],122,(0,3),true⟩,⟨[(1,6),(2,6),(2,7)],158,(1,3),true⟩,⟨[(2,2),(3,1),(3,2)],99,(2,1),true⟩,⟨[(3,3),(4,2),(4,3)],89,(2,2),false⟩,⟨[(3,4),(4,4),(4,5)],10,(2,3),false⟩,⟨[(3,5),(3,6),(3,7)],12,(2,3),false⟩]⟩,
  ⟨[(2,8),(3,8),(4,8)],[⟨[(0,8),(1,7),(1,8)],119,(0,7),true⟩,⟨[(1,6),(2,6),(2,7)],60,(1,6),true⟩,⟨[(3,5),(3,6),(3,7)],159,(2,5),false⟩,⟨[(4,7),(5,7),(5,8)],126,(2,7),false⟩]⟩,
  ⟨[(3,3),(4,2),(4,3)],[⟨[(2,2),(3,1),(3,2)],107,(2,1),true⟩,⟨[(2,3),(2,4),(2,5)],89,(2,2),true⟩,⟨[(3,4),(4,4),(4,5)],101,(3,2),false⟩,⟨[(4,1),(5,0),(5,1)],156,(3,0),false⟩,⟨[(5,2),(5,3),(5,4)],110,(3,2),false⟩]⟩,
  ⟨[(3,4),(4,4),(4,5)],[⟨[(2,3),(2,4),(2,5)],10,(2,3),true⟩,⟨[(3,3),(4,2),(4,3)],101,(3,2),true⟩,⟨[(3,5),(3,6),(3,7)],50,(3,4),false⟩,⟨[(4,6),(5,5),(5,6)],58,(3,4),false⟩,⟨[(5,2),(5,3),(5,4)],146,(3,2),false⟩]⟩,
  ⟨[(3,5),(3,6),(3,7)],[⟨[(1,6),(2,6),(2,7)],122,(1,5),true⟩,⟨[(2,3),(2,4),(2,5)],12,(2,3),true⟩,⟨[(2,8),(3,8),(4,8)],159,(2,5),true⟩,⟨[(3,4),(4,4),(4,5)],50,(3,4),true⟩,⟨[(4,6),(5,5),(5,6)],9,(3,5),false⟩,⟨[(4,7),(5,7),(5,8)],15,(3,5),false⟩]⟩,
  ⟨[(4,1),(5,0),(5,1)],[⟨[(2,0),(3,0),(4,0)],79,(2,0),true⟩,⟨[(2,2),(3,1),(3,2)],142,(2,0),true⟩,⟨[(3,3),(4,2),(4,3)],156,(3,0),true⟩,⟨[(5,2),(5,3),(5,4)],104,(4,0),false⟩]⟩,
  ⟨[(4,6),(5,5),(5,6)],[⟨[(3,4),(4,4),(4,5)],58,(3,4),true⟩,⟨[(3,5),(3,6),(3,7)],9,(3,5),true⟩,⟨[(4,7),(5,7),(5,8)],101,(4,5),false⟩,⟨[(5,2),(5,3),(5,4)],161,(4,2),false⟩]⟩,
  ⟨[(4,7),(5,7),(5,8)],[⟨[(2,8),(3,8),(4,8)],126,(2,7),true⟩,⟨[(3,5),(3,6),(3,7)],15,(3,5),true⟩,⟨[(4,6),(5,5),(5,6)],101,(4,5),true⟩]⟩,
  ⟨[(5,2),(5,3),(5,4)],[⟨[(3,3),(4,2),(4,3)],110,(3,2),true⟩,⟨[(3,4),(4,4),(4,5)],146,(3,2),true⟩,⟨[(4,1),(5,0),(5,1)],104,(4,0),true⟩,⟨[(4,6),(5,5),(5,6)],161,(4,2),true⟩]⟩,
]
theorem Width9_b0_entries_match : CatalogLinksCheck catalog Width9_b0_entries := by decide +kernel
theorem Width9_b0_entries_links : CertifiedLinks (localEntries Width9_b0_entries) :=
  catalogLinks_sound catalog_sound Width9_b0_entries_match

def Width9_b0_tiles := EntryTiles (localEntries Width9_b0_entries)
def Width9_b0_owner : Cell → List Cell := tableOwner 9 Width9_b0_tiles [0,0,0,1,2,3,3,3,4,5,5,1,1,2,2,6,4,4,7,5,8,9,9,9,6,6,10,7,8,8,11,12,13,13,13,10,7,14,11,11,12,12,15,16,10,14,14,17,17,17,15,15,16,16]
theorem Width9_b0_partition : OwnerPartitionCheck 6 9 Width9_b0_tiles Width9_b0_owner := by decide +kernel
theorem Width9_b0_cover : EdgeCoverCheck (localEntries Width9_b0_entries) Width9_b0_owner 0 0 6 9 := by decide +kernel
def Width9_b0 : RigidBlock 6 9 :=
  localCheckedBlock Width9_b0_partition Width9_b0_entries_links Width9_b0_cover

def Width9_b1_entries : List EntryData := [
  ⟨[(0,0),(0,1),(0,2)],[⟨[(0,3),(1,2),(1,3)],3,(0,0),false⟩,⟨[(1,0),(1,1),(2,1)],6,(0,0),false⟩]⟩,
  ⟨[(0,3),(1,2),(1,3)],[⟨[(0,0),(0,1),(0,2)],3,(0,0),true⟩,⟨[(0,4),(1,4),(1,5)],101,(0,2),false⟩,⟨[(1,0),(1,1),(2,1)],155,(0,0),false⟩,⟨[(2,2),(2,3),(2,4)],110,(0,2),false⟩]⟩,
  ⟨[(0,4),(1,4),(1,5)],[⟨[(0,3),(1,2),(1,3)],101,(0,2),true⟩,⟨[(0,5),(0,6),(0,7)],50,(0,4),false⟩,⟨[(1,6),(1,7),(2,6)],56,(0,4),false⟩,⟨[(2,2),(2,3),(2,4)],146,(0,2),false⟩,⟨[(2,5),(3,5),(3,6)],68,(0,4),false⟩]⟩,
  ⟨[(0,5),(0,6),(0,7)],[⟨[(0,4),(1,4),(1,5)],50,(0,4),true⟩,⟨[(0,8),(1,8),(2,8)],5,(0,5),false⟩,⟨[(1,6),(1,7),(2,6)],8,(0,5),false⟩]⟩,
  ⟨[(0,8),(1,8),(2,8)],[⟨[(0,5),(0,6),(0,7)],5,(0,5),true⟩,⟨[(1,6),(1,7),(2,6)],147,(0,6),false⟩,⟨[(2,7),(3,7),(3,8)],126,(0,7),false⟩]⟩,
  ⟨[(1,0),(1,1),(2,1)],[⟨[(0,0),(0,1),(0,2)],6,(0,0),true⟩,⟨[(0,3),(1,2),(1,3)],155,(0,0),true⟩,⟨[(2,0),(3,0),(4,0)],34,(1,0),false⟩,⟨[(2,2),(2,3),(2,4)],35,(1,0),false⟩,⟨[(3,1),(3,2),(4,1)],45,(1,0),false⟩]⟩,
  ⟨[(1,6),(1,7),(2,6)],[⟨[(0,4),(1,4),(1,5)],56,(0,4),true⟩,⟨[(0,5),(0,6),(0,7)],8,(0,5),true⟩,⟨[(0,8),(1,8),(2,8)],147,(0,6),true⟩,⟨[(2,5),(3,5),(3,6)],90,(1,5),false⟩,⟨[(2,7),(3,7),(3,8)],24,(1,6),false⟩]⟩,
  ⟨[(2,0),(3,0),(4,0)],[⟨[(1,0),(1,1),(2,1)],34,(1,0),true⟩,⟨[(3,1),(3,2),(4,1)],74,(2,0),false⟩,⟨[(5,0),(6,0),(7,0)],86,(2,0),false⟩]⟩,
  ⟨[(2,2),(2,3),(2,4)],[⟨[(0,3),(1,2),(1,3)],110,(0,2),true⟩,⟨[(0,4),(1,4),(1,5)],146,(0,2),true⟩,⟨[(1,0),(1,1),(2,1)],35,(1,0),true⟩,⟨[(2,5),(3,5),(3,6)],4,(2,2),false⟩,⟨[(3,1),(3,2),(4,1)],87,(2,1),false⟩,⟨[(3,3),(3,4),(4,3)],8,(2,2),false⟩]⟩,
  ⟨[(2,5),(3,5),(3,6)],[⟨[(0,4),(1,4),(1,5)],68,(0,4),true⟩,⟨[(1,6),(1,7),(2,6)],90,(1,5),true⟩,⟨[(2,2),(2,3),(2,4)],4,(2,2),true⟩,⟨[(2,7),(3,7),(3,8)],52,(2,5),false⟩,⟨[(3,3),(3,4),(4,3)],143,(2,3),false⟩,⟨[(4,5),(5,5),(5,6)],62,(2,5),false⟩,⟨[(4,6),(4,7),(4,8)],64,(2,5),false⟩]⟩,
  ⟨[(2,7),(3,7),(3,8)],[⟨[(0,8),(1,8),(2,8)],126,(0,7),true⟩,⟨[(1,6),(1,7),(2,6)],24,(1,6),true⟩,⟨[(2,5),(3,5),(3,6)],52,(2,5),true⟩,⟨[(4,6),(4,7),(4,8)],122,(2,6),false⟩]⟩,
  ⟨[(3,1),(3,2),(4,1)],[⟨[(1,0),(1,1),(2,1)],45,(1,0),true⟩,⟨[(2,0),(3,0),(4,0)],74,(2,0),true⟩,⟨[(2,2),(2,3),(2,4)],87,(2,1),true⟩,⟨[(3,3),(3,4),(4,3)],18,(3,1),false⟩,⟨[(4,2),(5,2),(5,3)],24,(3,1),false⟩,⟨[(5,1),(6,1),(6,2)],28,(3,1),false⟩]⟩,
  ⟨[(3,3),(3,4),(4,3)],[⟨[(2,2),(2,3),(2,4)],8,(2,2),true⟩,⟨[(2,5),(3,5),(3,6)],143,(2,3),true⟩,⟨[(3,1),(3,2),(4,1)],18,(3,1),true⟩,⟨[(4,2),(5,2),(5,3)],90,(3,2),false⟩,⟨[(4,4),(5,4),(6,4)],25,(3,3),false⟩]⟩,
  ⟨[(4,2),(5,2),(5,3)],[⟨[(3,1),(3,2),(4,1)],24,(3,1),true⟩,⟨[(3,3),(3,4),(4,3)],90,(3,2),true⟩,⟨[(4,4),(5,4),(6,4)],53,(4,2),false⟩,⟨[(5,1),(6,1),(6,2)],120,(4,1),false⟩,⟨[(6,3),(7,2),(7,3)],67,(4,2),false⟩]⟩,
  ⟨[(4,4),(5,4),(6,4)],[⟨[(3,3),(3,4),(4,3)],25,(3,3),true⟩,⟨[(4,2),(5,2),(5,3)],53,(4,2),true⟩,⟨[(4,5),(5,5),(5,6)],71,(4,4),false⟩,⟨[(6,3),(7,2),(7,3)],151,(4,2),false⟩,⟨[(6,5),(7,4),(7,5)],79,(4,4),false⟩]⟩,
  ⟨[(4,5),(5,5),(5,6)],[⟨[(2,5),(3,5),(3,6)],62,(2,5),true⟩,⟨[(4,4),(5,4),(6,4)],71,(4,4),true⟩,⟨[(4,6),(4,7),(4,8)],50,(4,5),false⟩,⟨[(5,7),(6,6),(6,7)],58,(4,5),false⟩,⟨[(6,5),(7,4),(7,5)],125,(4,4),false⟩]⟩,
  ⟨[(4,6),(4,7),(4,8)],[⟨[(2,5),(3,5),(3,6)],64,(2,5),true⟩,⟨[(2,7),(3,7),(3,8)],122,(2,6),true⟩,⟨[(4,5),(5,5),(5,6)],50,(4,5),true⟩,⟨[(5,7),(6,6),(6,7)],9,(4,6),false⟩,⟨[(5,8),(6,8),(7,8)],16,(4,6),false⟩]⟩,
  ⟨[(5,0),(6,0),(7,0)],[⟨[(2,0),(3,0),(4,0)],86,(2,0),true⟩,⟨[(5,1),(6,1),(6,2)],71,(5,0),false⟩,⟨[(7,1),(8,0),(8,1)],79,(5,0),false⟩]⟩,
  ⟨[(5,1),(6,1),(6,2)],[⟨[(3,1),(3,2),(4,1)],28,(3,1),true⟩,⟨[(4,2),(5,2),(5,3)],120,(4,1),true⟩,⟨[(5,0),(6,0),(7,0)],71,(5,0),true⟩,⟨[(6,3),(7,2),(7,3)],58,(5,1),false⟩,⟨[(7,1),(8,0),(8,1)],125,(5,0),false⟩]⟩,
  ⟨[(5,7),(6,6),(6,7)],[⟨[(4,5),(5,5),(5,6)],58,(4,5),true⟩,⟨[(4,6),(4,7),(4,8)],9,(4,6),true⟩,⟨[(5,8),(6,8),(7,8)],102,(5,6),false⟩,⟨[(6,5),(7,4),(7,5)],156,(5,4),false⟩,⟨[(7,6),(8,5),(8,6)],142,(5,5),false⟩,⟨[(7,7),(8,7),(8,8)],118,(5,6),false⟩]⟩,
  ⟨[(5,8),(6,8),(7,8)],[⟨[(4,6),(4,7),(4,8)],16,(4,6),true⟩,⟨[(5,7),(6,6),(6,7)],102,(5,6),true⟩,⟨[(7,7),(8,7),(8,8)],126,(5,7),false⟩]⟩,
  ⟨[(6,3),(7,2),(7,3)],[⟨[(4,2),(5,2),(5,3)],67,(4,2),true⟩,⟨[(4,4),(5,4),(6,4)],151,(4,2),true⟩,⟨[(5,1),(6,1),(6,2)],58,(5,1),true⟩,⟨[(6,5),(7,4),(7,5)],103,(6,2),false⟩,⟨[(7,1),(8,0),(8,1)],156,(6,0),false⟩,⟨[(8,2),(8,3),(8,4)],110,(6,2),false⟩]⟩,
  ⟨[(6,5),(7,4),(7,5)],[⟨[(4,4),(5,4),(6,4)],79,(4,4),true⟩,⟨[(4,5),(5,5),(5,6)],125,(4,4),true⟩,⟨[(5,7),(6,6),(6,7)],156,(5,4),true⟩,⟨[(6,3),(7,2),(7,3)],103,(6,2),true⟩,⟨[(7,6),(8,5),(8,6)],107,(6,4),false⟩,⟨[(8,2),(8,3),(8,4)],157,(6,2),false⟩]⟩,
  ⟨[(7,1),(8,0),(8,1)],[⟨[(5,0),(6,0),(7,0)],79,(5,0),true⟩,⟨[(5,1),(6,1),(6,2)],125,(5,0),true⟩,⟨[(6,3),(7,2),(7,3)],156,(6,0),true⟩,⟨[(8,2),(8,3),(8,4)],104,(7,0),false⟩]⟩,
  ⟨[(7,6),(8,5),(8,6)],[⟨[(5,7),(6,6),(6,7)],142,(5,5),true⟩,⟨[(6,5),(7,4),(7,5)],107,(6,4),true⟩,⟨[(7,7),(8,7),(8,8)],101,(7,5),false⟩,⟨[(8,2),(8,3),(8,4)],161,(7,2),false⟩]⟩,
  ⟨[(7,7),(8,7),(8,8)],[⟨[(5,7),(6,6),(6,7)],118,(5,6),true⟩,⟨[(5,8),(6,8),(7,8)],126,(5,7),true⟩,⟨[(7,6),(8,5),(8,6)],101,(7,5),true⟩]⟩,
  ⟨[(8,2),(8,3),(8,4)],[⟨[(6,3),(7,2),(7,3)],110,(6,2),true⟩,⟨[(6,5),(7,4),(7,5)],157,(6,2),true⟩,⟨[(7,1),(8,0),(8,1)],104,(7,0),true⟩,⟨[(7,6),(8,5),(8,6)],161,(7,2),true⟩]⟩,
]
theorem Width9_b1_entries_match : CatalogLinksCheck catalog Width9_b1_entries := by decide +kernel
theorem Width9_b1_entries_links : CertifiedLinks (localEntries Width9_b1_entries) :=
  catalogLinks_sound catalog_sound Width9_b1_entries_match

def Width9_b1_tiles := EntryTiles (localEntries Width9_b1_entries)
def Width9_b1_owner : Cell → List Cell := tableOwner 9 Width9_b1_tiles [0,0,0,1,2,3,3,3,4,5,5,1,1,2,2,6,6,4,7,5,8,8,8,9,6,10,4,7,11,11,12,12,9,9,10,10,7,11,13,12,14,15,16,16,16,17,18,13,13,14,15,15,19,20,17,18,18,21,14,22,19,19,20,17,23,21,21,22,22,24,25,20,23,23,26,26,26,24,24,25,25]
theorem Width9_b1_partition : OwnerPartitionCheck 9 9 Width9_b1_tiles Width9_b1_owner := by decide +kernel
theorem Width9_b1_cover : EdgeCoverCheck (localEntries Width9_b1_entries) Width9_b1_owner 0 0 9 9 := by decide +kernel
def Width9_b1 : RigidBlock 9 9 :=
  localCheckedBlock Width9_b1_partition Width9_b1_entries_links Width9_b1_cover

def Width9_vertical_0_entries : List EntryData := [
  ⟨[(0,0),(0,1),(0,2)],[]⟩,
  ⟨[(0,3),(1,2),(1,3)],[]⟩,
  ⟨[(0,4),(1,4),(1,5)],[]⟩,
  ⟨[(0,5),(0,6),(0,7)],[]⟩,
  ⟨[(0,8),(1,7),(1,8)],[]⟩,
  ⟨[(1,0),(1,1),(2,1)],[]⟩,
  ⟨[(1,6),(2,6),(2,7)],[]⟩,
  ⟨[(2,0),(3,0),(4,0)],[]⟩,
  ⟨[(2,2),(3,1),(3,2)],[]⟩,
  ⟨[(2,3),(2,4),(2,5)],[]⟩,
  ⟨[(2,8),(3,8),(4,8)],[]⟩,
  ⟨[(3,3),(4,2),(4,3)],[]⟩,
  ⟨[(3,4),(4,4),(4,5)],[]⟩,
  ⟨[(3,5),(3,6),(3,7)],[]⟩,
  ⟨[(4,1),(5,0),(5,1)],[⟨[(6,0),(6,1),(6,2)],110,(4,0),false⟩]⟩,
  ⟨[(4,6),(5,5),(5,6)],[⟨[(6,5),(6,6),(6,7)],110,(4,5),false⟩]⟩,
  ⟨[(4,7),(5,7),(5,8)],[⟨[(6,5),(6,6),(6,7)],146,(4,5),false⟩,⟨[(6,8),(7,7),(7,8)],67,(4,7),false⟩]⟩,
  ⟨[(5,2),(5,3),(5,4)],[⟨[(6,0),(6,1),(6,2)],132,(5,0),false⟩,⟨[(6,3),(7,2),(7,3)],9,(5,2),false⟩,⟨[(6,4),(7,4),(7,5)],15,(5,2),false⟩]⟩,
]
theorem Width9_vertical_0_entries_match : CatalogLinksCheck catalog Width9_vertical_0_entries := by decide +kernel
theorem Width9_vertical_0_entries_links : CertifiedLinks (localEntries Width9_vertical_0_entries) :=
  catalogLinks_sound catalog_sound Width9_vertical_0_entries_match

theorem Width9_vertical_0_same : EntryTiles (localEntries Width9_vertical_0_entries) = Width9_b0_tiles := by rfl
theorem Width9_vertical_0_cover : EdgeCoverCheck (localEntries Width9_vertical_0_entries)
    (shiftOwner (6,0) Width9_b0_owner) 6 0 6 9 := by decide +kernel
theorem Width9_vertical_0 : ∀ A B, Width9_b0.tiles A → Width9_b0.tiles B → Rigid A (Shift (6,0) B) := by
  have hp := localSeam_rigid (h := 6) (w := 9)
    (Width9_vertical_0_same.symm ▸ Width9_b0.partition) Width9_b0_partition
    Width9_vertical_0_entries_links Width9_vertical_0_cover
    (side_disjoint 6 9 6 9).1
  rw [Width9_vertical_0_same] at hp
  exact hp

def Width9_vertical_1_entries : List EntryData := [
  ⟨[(0,0),(0,1),(0,2)],[]⟩,
  ⟨[(0,3),(1,2),(1,3)],[]⟩,
  ⟨[(0,4),(1,4),(1,5)],[]⟩,
  ⟨[(0,5),(0,6),(0,7)],[]⟩,
  ⟨[(0,8),(1,7),(1,8)],[]⟩,
  ⟨[(1,0),(1,1),(2,1)],[]⟩,
  ⟨[(1,6),(2,6),(2,7)],[]⟩,
  ⟨[(2,0),(3,0),(4,0)],[]⟩,
  ⟨[(2,2),(3,1),(3,2)],[]⟩,
  ⟨[(2,3),(2,4),(2,5)],[]⟩,
  ⟨[(2,8),(3,8),(4,8)],[]⟩,
  ⟨[(3,3),(4,2),(4,3)],[]⟩,
  ⟨[(3,4),(4,4),(4,5)],[]⟩,
  ⟨[(3,5),(3,6),(3,7)],[]⟩,
  ⟨[(4,1),(5,0),(5,1)],[⟨[(6,0),(6,1),(6,2)],110,(4,0),false⟩]⟩,
  ⟨[(4,6),(5,5),(5,6)],[⟨[(6,5),(6,6),(6,7)],110,(4,5),false⟩]⟩,
  ⟨[(4,7),(5,7),(5,8)],[⟨[(6,5),(6,6),(6,7)],146,(4,5),false⟩,⟨[(6,8),(7,8),(8,8)],69,(4,7),false⟩]⟩,
  ⟨[(5,2),(5,3),(5,4)],[⟨[(6,0),(6,1),(6,2)],132,(5,0),false⟩,⟨[(6,3),(7,2),(7,3)],9,(5,2),false⟩,⟨[(6,4),(7,4),(7,5)],15,(5,2),false⟩]⟩,
]
theorem Width9_vertical_1_entries_match : CatalogLinksCheck catalog Width9_vertical_1_entries := by decide +kernel
theorem Width9_vertical_1_entries_links : CertifiedLinks (localEntries Width9_vertical_1_entries) :=
  catalogLinks_sound catalog_sound Width9_vertical_1_entries_match

theorem Width9_vertical_1_same : EntryTiles (localEntries Width9_vertical_1_entries) = Width9_b0_tiles := by rfl
theorem Width9_vertical_1_cover : EdgeCoverCheck (localEntries Width9_vertical_1_entries)
    (shiftOwner (6,0) Width9_b1_owner) 6 0 9 9 := by decide +kernel
theorem Width9_vertical_1 : ∀ A B, Width9_b0.tiles A → Width9_b1.tiles B → Rigid A (Shift (6,0) B) := by
  have hp := localSeam_rigid (h := 6) (w := 9)
    (Width9_vertical_1_same.symm ▸ Width9_b0.partition) Width9_b1_partition
    Width9_vertical_1_entries_links Width9_vertical_1_cover
    (side_disjoint 6 9 9 9).1
  rw [Width9_vertical_1_same] at hp
  exact hp

def Width9_vertical_2_entries : List EntryData := [
  ⟨[(0,0),(0,1),(0,2)],[]⟩,
  ⟨[(0,3),(1,2),(1,3)],[]⟩,
  ⟨[(0,4),(1,4),(1,5)],[]⟩,
  ⟨[(0,5),(0,6),(0,7)],[]⟩,
  ⟨[(0,8),(1,8),(2,8)],[]⟩,
  ⟨[(1,0),(1,1),(2,1)],[]⟩,
  ⟨[(1,6),(1,7),(2,6)],[]⟩,
  ⟨[(2,0),(3,0),(4,0)],[]⟩,
  ⟨[(2,2),(2,3),(2,4)],[]⟩,
  ⟨[(2,5),(3,5),(3,6)],[]⟩,
  ⟨[(2,7),(3,7),(3,8)],[]⟩,
  ⟨[(3,1),(3,2),(4,1)],[]⟩,
  ⟨[(3,3),(3,4),(4,3)],[]⟩,
  ⟨[(4,2),(5,2),(5,3)],[]⟩,
  ⟨[(4,4),(5,4),(6,4)],[]⟩,
  ⟨[(4,5),(5,5),(5,6)],[]⟩,
  ⟨[(4,6),(4,7),(4,8)],[]⟩,
  ⟨[(5,0),(6,0),(7,0)],[]⟩,
  ⟨[(5,1),(6,1),(6,2)],[]⟩,
  ⟨[(5,7),(6,6),(6,7)],[]⟩,
  ⟨[(5,8),(6,8),(7,8)],[]⟩,
  ⟨[(6,3),(7,2),(7,3)],[]⟩,
  ⟨[(6,5),(7,4),(7,5)],[]⟩,
  ⟨[(7,1),(8,0),(8,1)],[⟨[(9,0),(9,1),(9,2)],110,(7,0),false⟩]⟩,
  ⟨[(7,6),(8,5),(8,6)],[⟨[(9,5),(9,6),(9,7)],110,(7,5),false⟩]⟩,
  ⟨[(7,7),(8,7),(8,8)],[⟨[(9,5),(9,6),(9,7)],146,(7,5),false⟩,⟨[(9,8),(10,7),(10,8)],67,(7,7),false⟩]⟩,
  ⟨[(8,2),(8,3),(8,4)],[⟨[(9,0),(9,1),(9,2)],132,(8,0),false⟩,⟨[(9,3),(10,2),(10,3)],9,(8,2),false⟩,⟨[(9,4),(10,4),(10,5)],15,(8,2),false⟩]⟩,
]
theorem Width9_vertical_2_entries_match : CatalogLinksCheck catalog Width9_vertical_2_entries := by decide +kernel
theorem Width9_vertical_2_entries_links : CertifiedLinks (localEntries Width9_vertical_2_entries) :=
  catalogLinks_sound catalog_sound Width9_vertical_2_entries_match

theorem Width9_vertical_2_same : EntryTiles (localEntries Width9_vertical_2_entries) = Width9_b1_tiles := by rfl
theorem Width9_vertical_2_cover : EdgeCoverCheck (localEntries Width9_vertical_2_entries)
    (shiftOwner (9,0) Width9_b0_owner) 9 0 6 9 := by decide +kernel
theorem Width9_vertical_2 : ∀ A B, Width9_b1.tiles A → Width9_b0.tiles B → Rigid A (Shift (9,0) B) := by
  have hp := localSeam_rigid (h := 9) (w := 9)
    (Width9_vertical_2_same.symm ▸ Width9_b1.partition) Width9_b0_partition
    Width9_vertical_2_entries_links Width9_vertical_2_cover
    (side_disjoint 9 9 6 9).1
  rw [Width9_vertical_2_same] at hp
  exact hp

def Width9_vertical_3_entries : List EntryData := [
  ⟨[(0,0),(0,1),(0,2)],[]⟩,
  ⟨[(0,3),(1,2),(1,3)],[]⟩,
  ⟨[(0,4),(1,4),(1,5)],[]⟩,
  ⟨[(0,5),(0,6),(0,7)],[]⟩,
  ⟨[(0,8),(1,8),(2,8)],[]⟩,
  ⟨[(1,0),(1,1),(2,1)],[]⟩,
  ⟨[(1,6),(1,7),(2,6)],[]⟩,
  ⟨[(2,0),(3,0),(4,0)],[]⟩,
  ⟨[(2,2),(2,3),(2,4)],[]⟩,
  ⟨[(2,5),(3,5),(3,6)],[]⟩,
  ⟨[(2,7),(3,7),(3,8)],[]⟩,
  ⟨[(3,1),(3,2),(4,1)],[]⟩,
  ⟨[(3,3),(3,4),(4,3)],[]⟩,
  ⟨[(4,2),(5,2),(5,3)],[]⟩,
  ⟨[(4,4),(5,4),(6,4)],[]⟩,
  ⟨[(4,5),(5,5),(5,6)],[]⟩,
  ⟨[(4,6),(4,7),(4,8)],[]⟩,
  ⟨[(5,0),(6,0),(7,0)],[]⟩,
  ⟨[(5,1),(6,1),(6,2)],[]⟩,
  ⟨[(5,7),(6,6),(6,7)],[]⟩,
  ⟨[(5,8),(6,8),(7,8)],[]⟩,
  ⟨[(6,3),(7,2),(7,3)],[]⟩,
  ⟨[(6,5),(7,4),(7,5)],[]⟩,
  ⟨[(7,1),(8,0),(8,1)],[⟨[(9,0),(9,1),(9,2)],110,(7,0),false⟩]⟩,
  ⟨[(7,6),(8,5),(8,6)],[⟨[(9,5),(9,6),(9,7)],110,(7,5),false⟩]⟩,
  ⟨[(7,7),(8,7),(8,8)],[⟨[(9,5),(9,6),(9,7)],146,(7,5),false⟩,⟨[(9,8),(10,8),(11,8)],69,(7,7),false⟩]⟩,
  ⟨[(8,2),(8,3),(8,4)],[⟨[(9,0),(9,1),(9,2)],132,(8,0),false⟩,⟨[(9,3),(10,2),(10,3)],9,(8,2),false⟩,⟨[(9,4),(10,4),(10,5)],15,(8,2),false⟩]⟩,
]
theorem Width9_vertical_3_entries_match : CatalogLinksCheck catalog Width9_vertical_3_entries := by decide +kernel
theorem Width9_vertical_3_entries_links : CertifiedLinks (localEntries Width9_vertical_3_entries) :=
  catalogLinks_sound catalog_sound Width9_vertical_3_entries_match

theorem Width9_vertical_3_same : EntryTiles (localEntries Width9_vertical_3_entries) = Width9_b1_tiles := by rfl
theorem Width9_vertical_3_cover : EdgeCoverCheck (localEntries Width9_vertical_3_entries)
    (shiftOwner (9,0) Width9_b1_owner) 9 0 9 9 := by decide +kernel
theorem Width9_vertical_3 : ∀ A B, Width9_b1.tiles A → Width9_b1.tiles B → Rigid A (Shift (9,0) B) := by
  have hp := localSeam_rigid (h := 9) (w := 9)
    (Width9_vertical_3_same.symm ▸ Width9_b1.partition) Width9_b1_partition
    Width9_vertical_3_entries_links Width9_vertical_3_cover
    (side_disjoint 9 9 9 9).1
  rw [Width9_vertical_3_same] at hp
  exact hp

def Width9_palette : VerticalPalette (fun h => h = 6 ∨ h = 9) 9 where
  tiles h := if h = 6 then Width9_b0.tiles else Width9_b1.tiles
  partition := by
    intro h hh
    rcases hh with rfl | rfl
    · exact Width9_b0.partition
    · exact Width9_b1.partition
  internal := by
    intro h hh
    rcases hh with rfl | rfl
    · exact Width9_b0.internal
    · exact Width9_b1.internal
  vertical := by
    intro h k hh hk
    rcases hh with rfl | rfl <;> rcases hk with rfl | rfl
    · exact Width9_vertical_0
    · exact Width9_vertical_1
    · exact Width9_vertical_2
    · exact Width9_vertical_3

end LockedTromino.Witnesses
