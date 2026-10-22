import Generated.Catalog

namespace LockedTromino.Witnesses
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def Tail_b0_entries : List EntryData := [
  ⟨[(0,0),(1,0),(2,0)],[⟨[(0,1),(1,1),(1,2)],71,(0,0),false⟩,⟨[(2,1),(3,0),(3,1)],79,(0,0),false⟩]⟩,
  ⟨[(0,1),(1,1),(1,2)],[⟨[(0,0),(1,0),(2,0)],71,(0,0),true⟩,⟨[(0,2),(0,3),(0,4)],50,(0,1),false⟩,⟨[(1,3),(2,2),(2,3)],58,(0,1),false⟩,⟨[(2,1),(3,0),(3,1)],125,(0,0),false⟩]⟩,
  ⟨[(0,2),(0,3),(0,4)],[⟨[(0,1),(1,1),(1,2)],50,(0,1),true⟩,⟨[(0,5),(0,6),(0,7)],0,(0,2),false⟩,⟨[(1,3),(2,2),(2,3)],9,(0,2),false⟩,⟨[(1,4),(1,5),(2,5)],14,(0,2),false⟩]⟩,
  ⟨[(0,5),(0,6),(0,7)],[⟨[(0,2),(0,3),(0,4)],0,(0,2),true⟩,⟨[(1,4),(1,5),(2,5)],88,(0,4),false⟩,⟨[(1,6),(1,7),(2,6)],8,(0,5),false⟩]⟩,
  ⟨[(1,3),(2,2),(2,3)],[⟨[(0,1),(1,1),(1,2)],58,(0,1),true⟩,⟨[(0,2),(0,3),(0,4)],9,(0,2),true⟩,⟨[(1,4),(1,5),(2,5)],100,(1,2),false⟩,⟨[(2,1),(3,0),(3,1)],156,(1,0),false⟩,⟨[(2,4),(3,3),(3,4)],107,(1,2),false⟩,⟨[(3,2),(4,1),(4,2)],142,(1,1),false⟩]⟩,
  ⟨[(1,4),(1,5),(2,5)],[⟨[(0,2),(0,3),(0,4)],14,(0,2),true⟩,⟨[(0,5),(0,6),(0,7)],88,(0,4),true⟩,⟨[(1,3),(2,2),(2,3)],100,(1,2),true⟩,⟨[(1,6),(1,7),(2,6)],31,(1,4),false⟩,⟨[(2,4),(3,3),(3,4)],98,(1,3),false⟩,⟨[(3,5),(3,6),(4,5)],45,(1,4),false⟩]⟩,
  ⟨[(1,6),(1,7),(2,6)],[⟨[(0,5),(0,6),(0,7)],8,(0,5),true⟩,⟨[(1,4),(1,5),(2,5)],31,(1,4),true⟩,⟨[(2,7),(3,7),(4,7)],25,(1,6),false⟩,⟨[(3,5),(3,6),(4,5)],93,(1,5),false⟩]⟩,
  ⟨[(2,1),(3,0),(3,1)],[⟨[(0,0),(1,0),(2,0)],79,(0,0),true⟩,⟨[(0,1),(1,1),(1,2)],125,(0,0),true⟩,⟨[(1,3),(2,2),(2,3)],156,(1,0),true⟩,⟨[(3,2),(4,1),(4,2)],107,(2,0),false⟩,⟨[(4,0),(5,0),(5,1)],112,(2,0),false⟩]⟩,
  ⟨[(2,4),(3,3),(3,4)],[⟨[(1,3),(2,2),(2,3)],107,(1,2),true⟩,⟨[(1,4),(1,5),(2,5)],98,(1,3),true⟩,⟨[(3,2),(4,1),(4,2)],156,(2,1),false⟩,⟨[(3,5),(3,6),(4,5)],105,(2,3),false⟩,⟨[(4,3),(5,2),(5,3)],142,(2,2),false⟩,⟨[(4,4),(5,4),(5,5)],118,(2,3),false⟩]⟩,
  ⟨[(2,7),(3,7),(4,7)],[⟨[(1,6),(1,7),(2,6)],25,(1,6),true⟩,⟨[(3,5),(3,6),(4,5)],147,(2,5),false⟩,⟨[(4,6),(5,6),(5,7)],126,(2,6),false⟩]⟩,
  ⟨[(3,2),(4,1),(4,2)],[⟨[(1,3),(2,2),(2,3)],142,(1,1),true⟩,⟨[(2,1),(3,0),(3,1)],107,(2,0),true⟩,⟨[(2,4),(3,3),(3,4)],156,(2,1),true⟩,⟨[(4,0),(5,0),(5,1)],138,(3,0),false⟩,⟨[(4,3),(5,2),(5,3)],107,(3,1),false⟩]⟩,
  ⟨[(3,5),(3,6),(4,5)],[⟨[(1,4),(1,5),(2,5)],45,(1,4),true⟩,⟨[(1,6),(1,7),(2,6)],93,(1,5),true⟩,⟨[(2,4),(3,3),(3,4)],105,(2,3),true⟩,⟨[(2,7),(3,7),(4,7)],147,(2,5),true⟩,⟨[(4,4),(5,4),(5,5)],90,(3,4),false⟩,⟨[(4,6),(5,6),(5,7)],24,(3,5),false⟩]⟩,
  ⟨[(4,0),(5,0),(5,1)],[⟨[(2,1),(3,0),(3,1)],112,(2,0),true⟩,⟨[(3,2),(4,1),(4,2)],138,(3,0),true⟩,⟨[(4,3),(5,2),(5,3)],54,(4,0),false⟩]⟩,
  ⟨[(4,3),(5,2),(5,3)],[⟨[(2,4),(3,3),(3,4)],142,(2,2),true⟩,⟨[(3,2),(4,1),(4,2)],107,(3,1),true⟩,⟨[(4,0),(5,0),(5,1)],54,(4,0),true⟩,⟨[(4,4),(5,4),(5,5)],101,(4,2),false⟩]⟩,
  ⟨[(4,4),(5,4),(5,5)],[⟨[(2,4),(3,3),(3,4)],118,(2,3),true⟩,⟨[(3,5),(3,6),(4,5)],90,(3,4),true⟩,⟨[(4,3),(5,2),(5,3)],101,(4,2),true⟩,⟨[(4,6),(5,6),(5,7)],52,(4,4),false⟩]⟩,
  ⟨[(4,6),(5,6),(5,7)],[⟨[(2,7),(3,7),(4,7)],126,(2,6),true⟩,⟨[(3,5),(3,6),(4,5)],24,(3,5),true⟩,⟨[(4,4),(5,4),(5,5)],52,(4,4),true⟩]⟩,
]
theorem Tail_b0_entries_match : CatalogLinksCheck catalog Tail_b0_entries := by decide +kernel
theorem Tail_b0_entries_links : CertifiedLinks (localEntries Tail_b0_entries) :=
  catalogLinks_sound catalog_sound Tail_b0_entries_match

def Tail_b0_tiles := EntryTiles (localEntries Tail_b0_entries)
def Tail_b0_owner : Cell → List Cell := tableOwner 8 Tail_b0_tiles [0,1,2,2,2,3,3,3,0,1,1,4,5,5,6,6,0,7,4,4,8,5,6,9,7,7,10,8,8,11,11,9,12,10,10,13,14,11,15,9,12,12,13,13,14,14,15,15]
theorem Tail_b0_partition : OwnerPartitionCheck 6 8 Tail_b0_tiles Tail_b0_owner := by decide +kernel
theorem Tail_b0_cover : EdgeCoverCheck (localEntries Tail_b0_entries) Tail_b0_owner 0 0 6 8 := by decide +kernel
def Tail_b0 : RigidBlock 6 8 :=
  localCheckedBlock Tail_b0_partition Tail_b0_entries_links Tail_b0_cover

def Tail_b1_entries : List EntryData := [
  ⟨[(0,0),(0,1),(1,0)],[⟨[(0,2),(0,3),(1,3)],19,(0,0),false⟩,⟨[(1,1),(1,2),(2,1)],22,(0,0),false⟩,⟨[(2,0),(3,0),(3,1)],28,(0,0),false⟩]⟩,
  ⟨[(0,2),(0,3),(1,3)],[⟨[(0,0),(0,1),(1,0)],19,(0,0),true⟩,⟨[(0,4),(0,5),(1,4)],31,(0,2),false⟩,⟨[(1,1),(1,2),(2,1)],96,(0,1),false⟩,⟨[(2,2),(2,3),(2,4)],41,(0,2),false⟩]⟩,
  ⟨[(0,4),(0,5),(1,4)],[⟨[(0,2),(0,3),(1,3)],31,(0,2),true⟩,⟨[(0,6),(0,7),(0,8)],17,(0,4),false⟩,⟨[(1,5),(1,6),(2,6)],23,(0,4),false⟩,⟨[(2,2),(2,3),(2,4)],136,(0,2),false⟩]⟩,
  ⟨[(0,6),(0,7),(0,8)],[⟨[(0,4),(0,5),(1,4)],17,(0,4),true⟩,⟨[(1,5),(1,6),(2,6)],88,(0,5),false⟩,⟨[(1,7),(1,8),(2,7)],8,(0,6),false⟩]⟩,
  ⟨[(1,1),(1,2),(2,1)],[⟨[(0,0),(0,1),(1,0)],22,(0,0),true⟩,⟨[(0,2),(0,3),(1,3)],96,(0,1),true⟩,⟨[(2,0),(3,0),(3,1)],90,(1,0),false⟩,⟨[(2,2),(2,3),(2,4)],21,(1,1),false⟩]⟩,
  ⟨[(1,5),(1,6),(2,6)],[⟨[(0,4),(0,5),(1,4)],23,(0,4),true⟩,⟨[(0,6),(0,7),(0,8)],88,(0,5),true⟩,⟨[(1,7),(1,8),(2,7)],31,(1,5),false⟩,⟨[(2,5),(3,4),(3,5)],98,(1,4),false⟩,⟨[(3,6),(3,7),(4,6)],45,(1,5),false⟩]⟩,
  ⟨[(1,7),(1,8),(2,7)],[⟨[(0,6),(0,7),(0,8)],8,(0,6),true⟩,⟨[(1,5),(1,6),(2,6)],31,(1,5),true⟩,⟨[(2,8),(3,8),(4,8)],25,(1,7),false⟩,⟨[(3,6),(3,7),(4,6)],93,(1,6),false⟩]⟩,
  ⟨[(2,0),(3,0),(3,1)],[⟨[(0,0),(0,1),(1,0)],28,(0,0),true⟩,⟨[(1,1),(1,2),(2,1)],90,(1,0),true⟩,⟨[(3,2),(4,1),(4,2)],58,(2,0),false⟩,⟨[(4,0),(5,0),(5,1)],62,(2,0),false⟩]⟩,
  ⟨[(2,2),(2,3),(2,4)],[⟨[(0,2),(0,3),(1,3)],41,(0,2),true⟩,⟨[(0,4),(0,5),(1,4)],136,(0,2),true⟩,⟨[(1,1),(1,2),(2,1)],21,(1,1),true⟩,⟨[(2,5),(3,4),(3,5)],3,(2,2),false⟩,⟨[(3,2),(4,1),(4,2)],89,(2,1),false⟩,⟨[(3,3),(4,3),(4,4)],10,(2,2),false⟩]⟩,
  ⟨[(2,5),(3,4),(3,5)],[⟨[(1,5),(1,6),(2,6)],98,(1,4),true⟩,⟨[(2,2),(2,3),(2,4)],3,(2,2),true⟩,⟨[(3,3),(4,3),(4,4)],138,(2,3),false⟩,⟨[(3,6),(3,7),(4,6)],105,(2,4),false⟩,⟨[(4,5),(5,5),(5,6)],118,(2,4),false⟩]⟩,
  ⟨[(2,8),(3,8),(4,8)],[⟨[(1,7),(1,8),(2,7)],25,(1,7),true⟩,⟨[(3,6),(3,7),(4,6)],147,(2,6),false⟩,⟨[(4,7),(5,7),(5,8)],126,(2,7),false⟩]⟩,
  ⟨[(3,2),(4,1),(4,2)],[⟨[(2,0),(3,0),(3,1)],58,(2,0),true⟩,⟨[(2,2),(2,3),(2,4)],89,(2,1),true⟩,⟨[(3,3),(4,3),(4,4)],101,(3,1),false⟩,⟨[(4,0),(5,0),(5,1)],138,(3,0),false⟩,⟨[(5,2),(5,3),(5,4)],114,(3,1),false⟩]⟩,
  ⟨[(3,3),(4,3),(4,4)],[⟨[(2,2),(2,3),(2,4)],10,(2,2),true⟩,⟨[(2,5),(3,4),(3,5)],138,(2,3),true⟩,⟨[(3,2),(4,1),(4,2)],101,(3,1),true⟩,⟨[(4,5),(5,5),(5,6)],59,(3,3),false⟩,⟨[(5,2),(5,3),(5,4)],122,(3,2),false⟩]⟩,
  ⟨[(3,6),(3,7),(4,6)],[⟨[(1,5),(1,6),(2,6)],45,(1,5),true⟩,⟨[(1,7),(1,8),(2,7)],93,(1,6),true⟩,⟨[(2,5),(3,4),(3,5)],105,(2,4),true⟩,⟨[(2,8),(3,8),(4,8)],147,(2,6),true⟩,⟨[(4,5),(5,5),(5,6)],90,(3,5),false⟩,⟨[(4,7),(5,7),(5,8)],24,(3,6),false⟩]⟩,
  ⟨[(4,0),(5,0),(5,1)],[⟨[(2,0),(3,0),(3,1)],62,(2,0),true⟩,⟨[(3,2),(4,1),(4,2)],138,(3,0),true⟩,⟨[(5,2),(5,3),(5,4)],55,(4,0),false⟩]⟩,
  ⟨[(4,5),(5,5),(5,6)],[⟨[(2,5),(3,4),(3,5)],118,(2,4),true⟩,⟨[(3,3),(4,3),(4,4)],59,(3,3),true⟩,⟨[(3,6),(3,7),(4,6)],90,(3,5),true⟩,⟨[(4,7),(5,7),(5,8)],52,(4,5),false⟩,⟨[(5,2),(5,3),(5,4)],158,(4,2),false⟩]⟩,
  ⟨[(4,7),(5,7),(5,8)],[⟨[(2,8),(3,8),(4,8)],126,(2,7),true⟩,⟨[(3,6),(3,7),(4,6)],24,(3,6),true⟩,⟨[(4,5),(5,5),(5,6)],52,(4,5),true⟩]⟩,
  ⟨[(5,2),(5,3),(5,4)],[⟨[(3,2),(4,1),(4,2)],114,(3,1),true⟩,⟨[(3,3),(4,3),(4,4)],122,(3,2),true⟩,⟨[(4,0),(5,0),(5,1)],55,(4,0),true⟩,⟨[(4,5),(5,5),(5,6)],158,(4,2),true⟩]⟩,
]
theorem Tail_b1_entries_match : CatalogLinksCheck catalog Tail_b1_entries := by decide +kernel
theorem Tail_b1_entries_links : CertifiedLinks (localEntries Tail_b1_entries) :=
  catalogLinks_sound catalog_sound Tail_b1_entries_match

def Tail_b1_tiles := EntryTiles (localEntries Tail_b1_entries)
def Tail_b1_owner : Cell → List Cell := tableOwner 9 Tail_b1_tiles [0,0,1,1,2,2,3,3,3,0,4,4,1,2,5,5,6,6,7,4,8,8,8,9,5,6,10,7,7,11,12,9,9,13,13,10,14,11,11,12,12,15,13,16,10,14,14,17,17,17,15,15,16,16]
theorem Tail_b1_partition : OwnerPartitionCheck 6 9 Tail_b1_tiles Tail_b1_owner := by decide +kernel
theorem Tail_b1_cover : EdgeCoverCheck (localEntries Tail_b1_entries) Tail_b1_owner 0 0 6 9 := by decide +kernel
def Tail_b1 : RigidBlock 6 9 :=
  localCheckedBlock Tail_b1_partition Tail_b1_entries_links Tail_b1_cover

def Tail_b2_entries : List EntryData := [
  ⟨[(0,0),(0,1),(1,0)],[⟨[(0,2),(0,3),(1,3)],19,(0,0),false⟩,⟨[(1,1),(1,2),(2,2)],23,(0,0),false⟩,⟨[(2,0),(2,1),(3,1)],27,(0,0),false⟩]⟩,
  ⟨[(0,2),(0,3),(1,3)],[⟨[(0,0),(0,1),(1,0)],19,(0,0),true⟩,⟨[(0,4),(0,5),(1,4)],31,(0,2),false⟩,⟨[(1,1),(1,2),(2,2)],97,(0,1),false⟩,⟨[(2,3),(2,4),(3,3)],45,(0,2),false⟩]⟩,
  ⟨[(0,4),(0,5),(1,4)],[⟨[(0,2),(0,3),(1,3)],31,(0,2),true⟩,⟨[(0,6),(0,7),(1,6)],18,(0,4),false⟩,⟨[(1,5),(2,5),(2,6)],24,(0,4),false⟩,⟨[(2,3),(2,4),(3,3)],93,(0,3),false⟩]⟩,
  ⟨[(0,6),(0,7),(1,6)],[⟨[(0,4),(0,5),(1,4)],18,(0,4),true⟩,⟨[(1,5),(2,5),(2,6)],90,(0,5),false⟩,⟨[(1,7),(2,7),(3,7)],25,(0,6),false⟩]⟩,
  ⟨[(1,1),(1,2),(2,2)],[⟨[(0,0),(0,1),(1,0)],23,(0,0),true⟩,⟨[(0,2),(0,3),(1,3)],97,(0,1),true⟩,⟨[(2,0),(2,1),(3,1)],97,(1,0),false⟩,⟨[(2,3),(2,4),(3,3)],36,(1,1),false⟩,⟨[(3,2),(4,1),(4,2)],47,(1,1),false⟩]⟩,
  ⟨[(1,5),(2,5),(2,6)],[⟨[(0,4),(0,5),(1,4)],24,(0,4),true⟩,⟨[(0,6),(0,7),(1,6)],90,(0,5),true⟩,⟨[(1,7),(2,7),(3,7)],53,(1,5),false⟩,⟨[(2,3),(2,4),(3,3)],143,(1,3),false⟩,⟨[(3,4),(3,5),(4,4)],123,(1,4),false⟩,⟨[(3,6),(4,6),(4,7)],68,(1,5),false⟩]⟩,
  ⟨[(1,7),(2,7),(3,7)],[⟨[(0,6),(0,7),(1,6)],25,(0,6),true⟩,⟨[(1,5),(2,5),(2,6)],53,(1,5),true⟩,⟨[(3,6),(4,6),(4,7)],126,(1,6),false⟩]⟩,
  ⟨[(2,0),(2,1),(3,1)],[⟨[(0,0),(0,1),(1,0)],27,(0,0),true⟩,⟨[(1,1),(1,2),(2,2)],97,(1,0),true⟩,⟨[(3,0),(4,0),(5,0)],34,(2,0),false⟩,⟨[(3,2),(4,1),(4,2)],38,(2,0),false⟩]⟩,
  ⟨[(2,3),(2,4),(3,3)],[⟨[(0,2),(0,3),(1,3)],45,(0,2),true⟩,⟨[(0,4),(0,5),(1,4)],93,(0,3),true⟩,⟨[(1,1),(1,2),(2,2)],36,(1,1),true⟩,⟨[(1,5),(2,5),(2,6)],143,(1,3),true⟩,⟨[(3,2),(4,1),(4,2)],135,(2,1),false⟩,⟨[(3,4),(3,5),(4,4)],22,(2,3),false⟩,⟨[(4,3),(5,2),(5,3)],95,(2,2),false⟩]⟩,
  ⟨[(3,0),(4,0),(5,0)],[⟨[(2,0),(2,1),(3,1)],34,(2,0),true⟩,⟨[(3,2),(4,1),(4,2)],72,(3,0),false⟩,⟨[(5,1),(6,0),(6,1)],79,(3,0),false⟩]⟩,
  ⟨[(3,2),(4,1),(4,2)],[⟨[(1,1),(1,2),(2,2)],47,(1,1),true⟩,⟨[(2,0),(2,1),(3,1)],38,(2,0),true⟩,⟨[(2,3),(2,4),(3,3)],135,(2,1),true⟩,⟨[(3,0),(4,0),(5,0)],72,(3,0),true⟩,⟨[(4,3),(5,2),(5,3)],107,(3,1),false⟩,⟨[(5,1),(6,0),(6,1)],142,(3,0),false⟩]⟩,
  ⟨[(3,4),(3,5),(4,4)],[⟨[(1,5),(2,5),(2,6)],123,(1,4),true⟩,⟨[(2,3),(2,4),(3,3)],22,(2,3),true⟩,⟨[(3,6),(4,6),(4,7)],20,(3,4),false⟩,⟨[(4,3),(5,2),(5,3)],135,(3,2),false⟩,⟨[(4,5),(5,5),(5,6)],24,(3,4),false⟩,⟨[(5,4),(6,3),(6,4)],95,(3,3),false⟩]⟩,
  ⟨[(3,6),(4,6),(4,7)],[⟨[(1,5),(2,5),(2,6)],68,(1,5),true⟩,⟨[(1,7),(2,7),(3,7)],126,(1,6),true⟩,⟨[(3,4),(3,5),(4,4)],20,(3,4),true⟩,⟨[(4,5),(5,5),(5,6)],120,(3,5),false⟩,⟨[(5,7),(6,7),(7,7)],69,(3,6),false⟩]⟩,
  ⟨[(4,3),(5,2),(5,3)],[⟨[(2,3),(2,4),(3,3)],95,(2,2),true⟩,⟨[(3,2),(4,1),(4,2)],107,(3,1),true⟩,⟨[(3,4),(3,5),(4,4)],135,(3,2),true⟩,⟨[(5,1),(6,0),(6,1)],156,(4,0),false⟩,⟨[(5,4),(6,3),(6,4)],107,(4,2),false⟩,⟨[(6,2),(7,1),(7,2)],142,(4,1),false⟩]⟩,
  ⟨[(4,5),(5,5),(5,6)],[⟨[(3,4),(3,5),(4,4)],24,(3,4),true⟩,⟨[(3,6),(4,6),(4,7)],120,(3,5),true⟩,⟨[(5,4),(6,3),(6,4)],145,(4,3),false⟩,⟨[(5,7),(6,7),(7,7)],60,(4,5),false⟩,⟨[(6,5),(6,6),(7,5)],61,(4,5),false⟩]⟩,
  ⟨[(5,1),(6,0),(6,1)],[⟨[(3,0),(4,0),(5,0)],79,(3,0),true⟩,⟨[(3,2),(4,1),(4,2)],142,(3,0),true⟩,⟨[(4,3),(5,2),(5,3)],156,(4,0),true⟩,⟨[(6,2),(7,1),(7,2)],107,(5,0),false⟩,⟨[(7,0),(8,0),(8,1)],112,(5,0),false⟩]⟩,
  ⟨[(5,4),(6,3),(6,4)],[⟨[(3,4),(3,5),(4,4)],95,(3,3),true⟩,⟨[(4,3),(5,2),(5,3)],107,(4,2),true⟩,⟨[(4,5),(5,5),(5,6)],145,(4,3),true⟩,⟨[(6,2),(7,1),(7,2)],156,(5,1),false⟩,⟨[(6,5),(6,6),(7,5)],105,(5,3),false⟩,⟨[(7,3),(8,2),(8,3)],142,(5,2),false⟩,⟨[(7,4),(8,4),(8,5)],118,(5,3),false⟩]⟩,
  ⟨[(5,7),(6,7),(7,7)],[⟨[(3,6),(4,6),(4,7)],69,(3,6),true⟩,⟨[(4,5),(5,5),(5,6)],60,(4,5),true⟩,⟨[(6,5),(6,6),(7,5)],147,(5,5),false⟩,⟨[(7,6),(8,6),(8,7)],126,(5,6),false⟩]⟩,
  ⟨[(6,2),(7,1),(7,2)],[⟨[(4,3),(5,2),(5,3)],142,(4,1),true⟩,⟨[(5,1),(6,0),(6,1)],107,(5,0),true⟩,⟨[(5,4),(6,3),(6,4)],156,(5,1),true⟩,⟨[(7,0),(8,0),(8,1)],138,(6,0),false⟩,⟨[(7,3),(8,2),(8,3)],107,(6,1),false⟩]⟩,
  ⟨[(6,5),(6,6),(7,5)],[⟨[(4,5),(5,5),(5,6)],61,(4,5),true⟩,⟨[(5,4),(6,3),(6,4)],105,(5,3),true⟩,⟨[(5,7),(6,7),(7,7)],147,(5,5),true⟩,⟨[(7,4),(8,4),(8,5)],90,(6,4),false⟩,⟨[(7,6),(8,6),(8,7)],24,(6,5),false⟩]⟩,
  ⟨[(7,0),(8,0),(8,1)],[⟨[(5,1),(6,0),(6,1)],112,(5,0),true⟩,⟨[(6,2),(7,1),(7,2)],138,(6,0),true⟩,⟨[(7,3),(8,2),(8,3)],54,(7,0),false⟩]⟩,
  ⟨[(7,3),(8,2),(8,3)],[⟨[(5,4),(6,3),(6,4)],142,(5,2),true⟩,⟨[(6,2),(7,1),(7,2)],107,(6,1),true⟩,⟨[(7,0),(8,0),(8,1)],54,(7,0),true⟩,⟨[(7,4),(8,4),(8,5)],101,(7,2),false⟩]⟩,
  ⟨[(7,4),(8,4),(8,5)],[⟨[(5,4),(6,3),(6,4)],118,(5,3),true⟩,⟨[(6,5),(6,6),(7,5)],90,(6,4),true⟩,⟨[(7,3),(8,2),(8,3)],101,(7,2),true⟩,⟨[(7,6),(8,6),(8,7)],52,(7,4),false⟩]⟩,
  ⟨[(7,6),(8,6),(8,7)],[⟨[(5,7),(6,7),(7,7)],126,(5,6),true⟩,⟨[(6,5),(6,6),(7,5)],24,(6,5),true⟩,⟨[(7,4),(8,4),(8,5)],52,(7,4),true⟩]⟩,
]
theorem Tail_b2_entries_match : CatalogLinksCheck catalog Tail_b2_entries := by decide +kernel
theorem Tail_b2_entries_links : CertifiedLinks (localEntries Tail_b2_entries) :=
  catalogLinks_sound catalog_sound Tail_b2_entries_match

def Tail_b2_tiles := EntryTiles (localEntries Tail_b2_entries)
def Tail_b2_owner : Cell → List Cell := tableOwner 8 Tail_b2_tiles [0,0,1,1,2,2,3,3,0,4,4,1,2,5,3,6,7,7,4,8,8,5,5,6,9,7,10,8,11,11,12,6,9,10,10,13,11,14,12,12,9,15,13,13,16,14,14,17,15,15,18,16,16,19,19,17,20,18,18,21,22,19,23,17,20,20,21,21,22,22,23,23]
theorem Tail_b2_partition : OwnerPartitionCheck 9 8 Tail_b2_tiles Tail_b2_owner := by decide +kernel
theorem Tail_b2_cover : EdgeCoverCheck (localEntries Tail_b2_entries) Tail_b2_owner 0 0 9 8 := by decide +kernel
def Tail_b2 : RigidBlock 9 8 :=
  localCheckedBlock Tail_b2_partition Tail_b2_entries_links Tail_b2_cover

def Tail_b3_entries : List EntryData := [
  ⟨[(0,0),(0,1),(1,0)],[⟨[(0,2),(0,3),(1,3)],19,(0,0),false⟩,⟨[(1,1),(1,2),(2,2)],23,(0,0),false⟩,⟨[(2,0),(2,1),(3,1)],27,(0,0),false⟩]⟩,
  ⟨[(0,2),(0,3),(1,3)],[⟨[(0,0),(0,1),(1,0)],19,(0,0),true⟩,⟨[(0,4),(0,5),(0,6)],30,(0,2),false⟩,⟨[(1,1),(1,2),(2,2)],97,(0,1),false⟩,⟨[(1,4),(2,3),(2,4)],38,(0,2),false⟩]⟩,
  ⟨[(0,4),(0,5),(0,6)],[⟨[(0,2),(0,3),(1,3)],30,(0,2),true⟩,⟨[(0,7),(0,8),(1,7)],1,(0,4),false⟩,⟨[(1,4),(2,3),(2,4)],89,(0,3),false⟩,⟨[(1,5),(2,5),(3,5)],11,(0,4),false⟩,⟨[(1,6),(2,6),(2,7)],15,(0,4),false⟩]⟩,
  ⟨[(0,7),(0,8),(1,7)],[⟨[(0,4),(0,5),(0,6)],1,(0,4),true⟩,⟨[(1,6),(2,6),(2,7)],90,(0,6),false⟩,⟨[(1,8),(2,8),(3,8)],25,(0,7),false⟩]⟩,
  ⟨[(1,1),(1,2),(2,2)],[⟨[(0,0),(0,1),(1,0)],23,(0,0),true⟩,⟨[(0,2),(0,3),(1,3)],97,(0,1),true⟩,⟨[(1,4),(2,3),(2,4)],33,(1,1),false⟩,⟨[(2,0),(2,1),(3,1)],97,(1,0),false⟩,⟨[(3,2),(4,1),(4,2)],47,(1,1),false⟩]⟩,
  ⟨[(1,4),(2,3),(2,4)],[⟨[(0,2),(0,3),(1,3)],38,(0,2),true⟩,⟨[(0,4),(0,5),(0,6)],89,(0,3),true⟩,⟨[(1,1),(1,2),(2,2)],33,(1,1),true⟩,⟨[(1,5),(2,5),(3,5)],102,(1,3),false⟩,⟨[(3,3),(3,4),(4,4)],111,(1,3),false⟩]⟩,
  ⟨[(1,5),(2,5),(3,5)],[⟨[(0,4),(0,5),(0,6)],11,(0,4),true⟩,⟨[(1,4),(2,3),(2,4)],102,(1,3),true⟩,⟨[(1,6),(2,6),(2,7)],71,(1,5),false⟩,⟨[(3,3),(3,4),(4,4)],150,(1,3),false⟩,⟨[(3,6),(4,5),(4,6)],79,(1,5),false⟩]⟩,
  ⟨[(1,6),(2,6),(2,7)],[⟨[(0,4),(0,5),(0,6)],15,(0,4),true⟩,⟨[(0,7),(0,8),(1,7)],90,(0,6),true⟩,⟨[(1,5),(2,5),(3,5)],71,(1,5),true⟩,⟨[(1,8),(2,8),(3,8)],53,(1,6),false⟩,⟨[(3,6),(4,5),(4,6)],125,(1,5),false⟩,⟨[(3,7),(4,7),(4,8)],68,(1,6),false⟩]⟩,
  ⟨[(1,8),(2,8),(3,8)],[⟨[(0,7),(0,8),(1,7)],25,(0,7),true⟩,⟨[(1,6),(2,6),(2,7)],53,(1,6),true⟩,⟨[(3,7),(4,7),(4,8)],126,(1,7),false⟩]⟩,
  ⟨[(2,0),(2,1),(3,1)],[⟨[(0,0),(0,1),(1,0)],27,(0,0),true⟩,⟨[(1,1),(1,2),(2,2)],97,(1,0),true⟩,⟨[(3,0),(4,0),(5,0)],34,(2,0),false⟩,⟨[(3,2),(4,1),(4,2)],38,(2,0),false⟩]⟩,
  ⟨[(3,0),(4,0),(5,0)],[⟨[(2,0),(2,1),(3,1)],34,(2,0),true⟩,⟨[(3,2),(4,1),(4,2)],72,(3,0),false⟩,⟨[(5,1),(6,0),(6,1)],79,(3,0),false⟩]⟩,
  ⟨[(3,2),(4,1),(4,2)],[⟨[(1,1),(1,2),(2,2)],47,(1,1),true⟩,⟨[(2,0),(2,1),(3,1)],38,(2,0),true⟩,⟨[(3,0),(4,0),(5,0)],72,(3,0),true⟩,⟨[(3,3),(3,4),(4,4)],100,(3,1),false⟩,⟨[(4,3),(5,2),(5,3)],107,(3,1),false⟩,⟨[(5,1),(6,0),(6,1)],142,(3,0),false⟩]⟩,
  ⟨[(3,3),(3,4),(4,4)],[⟨[(1,4),(2,3),(2,4)],111,(1,3),true⟩,⟨[(1,5),(2,5),(3,5)],150,(1,3),true⟩,⟨[(3,2),(4,1),(4,2)],100,(3,1),true⟩,⟨[(3,6),(4,5),(4,6)],33,(3,3),false⟩,⟨[(4,3),(5,2),(5,3)],98,(3,2),false⟩,⟨[(5,4),(6,4),(6,5)],48,(3,3),false⟩]⟩,
  ⟨[(3,6),(4,5),(4,6)],[⟨[(1,5),(2,5),(3,5)],79,(1,5),true⟩,⟨[(1,6),(2,6),(2,7)],125,(1,5),true⟩,⟨[(3,3),(3,4),(4,4)],33,(3,3),true⟩,⟨[(3,7),(4,7),(4,8)],101,(3,5),false⟩,⟨[(5,5),(5,6),(5,7)],110,(3,5),false⟩]⟩,
  ⟨[(3,7),(4,7),(4,8)],[⟨[(1,6),(2,6),(2,7)],68,(1,6),true⟩,⟨[(1,8),(2,8),(3,8)],126,(1,7),true⟩,⟨[(3,6),(4,5),(4,6)],101,(3,5),true⟩,⟨[(5,5),(5,6),(5,7)],146,(3,5),false⟩,⟨[(5,8),(6,8),(7,8)],69,(3,7),false⟩]⟩,
  ⟨[(4,3),(5,2),(5,3)],[⟨[(3,2),(4,1),(4,2)],107,(3,1),true⟩,⟨[(3,3),(3,4),(4,4)],98,(3,2),true⟩,⟨[(5,1),(6,0),(6,1)],156,(4,0),false⟩,⟨[(5,4),(6,4),(6,5)],108,(4,2),false⟩,⟨[(6,2),(7,1),(7,2)],142,(4,1),false⟩,⟨[(6,3),(7,3),(7,4)],118,(4,2),false⟩]⟩,
  ⟨[(5,1),(6,0),(6,1)],[⟨[(3,0),(4,0),(5,0)],79,(3,0),true⟩,⟨[(3,2),(4,1),(4,2)],142,(3,0),true⟩,⟨[(4,3),(5,2),(5,3)],156,(4,0),true⟩,⟨[(6,2),(7,1),(7,2)],107,(5,0),false⟩,⟨[(7,0),(8,0),(8,1)],112,(5,0),false⟩]⟩,
  ⟨[(5,4),(6,4),(6,5)],[⟨[(3,3),(3,4),(4,4)],48,(3,3),true⟩,⟨[(4,3),(5,2),(5,3)],108,(4,2),true⟩,⟨[(5,5),(5,6),(5,7)],50,(5,4),false⟩,⟨[(6,3),(7,3),(7,4)],120,(5,3),false⟩,⟨[(6,6),(6,7),(7,6)],56,(5,4),false⟩,⟨[(7,5),(8,5),(8,6)],68,(5,4),false⟩]⟩,
  ⟨[(5,5),(5,6),(5,7)],[⟨[(3,6),(4,5),(4,6)],110,(3,5),true⟩,⟨[(3,7),(4,7),(4,8)],146,(3,5),true⟩,⟨[(5,4),(6,4),(6,5)],50,(5,4),true⟩,⟨[(5,8),(6,8),(7,8)],5,(5,5),false⟩,⟨[(6,6),(6,7),(7,6)],8,(5,5),false⟩]⟩,
  ⟨[(5,8),(6,8),(7,8)],[⟨[(3,7),(4,7),(4,8)],69,(3,7),true⟩,⟨[(5,5),(5,6),(5,7)],5,(5,5),true⟩,⟨[(6,6),(6,7),(7,6)],147,(5,6),false⟩,⟨[(7,7),(8,7),(8,8)],126,(5,7),false⟩]⟩,
  ⟨[(6,2),(7,1),(7,2)],[⟨[(4,3),(5,2),(5,3)],142,(4,1),true⟩,⟨[(5,1),(6,0),(6,1)],107,(5,0),true⟩,⟨[(6,3),(7,3),(7,4)],101,(6,1),false⟩,⟨[(7,0),(8,0),(8,1)],138,(6,0),false⟩,⟨[(8,2),(8,3),(8,4)],114,(6,1),false⟩]⟩,
  ⟨[(6,3),(7,3),(7,4)],[⟨[(4,3),(5,2),(5,3)],118,(4,2),true⟩,⟨[(5,4),(6,4),(6,5)],120,(5,3),true⟩,⟨[(6,2),(7,1),(7,2)],101,(6,1),true⟩,⟨[(7,5),(8,5),(8,6)],59,(6,3),false⟩,⟨[(8,2),(8,3),(8,4)],122,(6,2),false⟩]⟩,
  ⟨[(6,6),(6,7),(7,6)],[⟨[(5,4),(6,4),(6,5)],56,(5,4),true⟩,⟨[(5,5),(5,6),(5,7)],8,(5,5),true⟩,⟨[(5,8),(6,8),(7,8)],147,(5,6),true⟩,⟨[(7,5),(8,5),(8,6)],90,(6,5),false⟩,⟨[(7,7),(8,7),(8,8)],24,(6,6),false⟩]⟩,
  ⟨[(7,0),(8,0),(8,1)],[⟨[(5,1),(6,0),(6,1)],112,(5,0),true⟩,⟨[(6,2),(7,1),(7,2)],138,(6,0),true⟩,⟨[(8,2),(8,3),(8,4)],55,(7,0),false⟩]⟩,
  ⟨[(7,5),(8,5),(8,6)],[⟨[(5,4),(6,4),(6,5)],68,(5,4),true⟩,⟨[(6,3),(7,3),(7,4)],59,(6,3),true⟩,⟨[(6,6),(6,7),(7,6)],90,(6,5),true⟩,⟨[(7,7),(8,7),(8,8)],52,(7,5),false⟩,⟨[(8,2),(8,3),(8,4)],158,(7,2),false⟩]⟩,
  ⟨[(7,7),(8,7),(8,8)],[⟨[(5,8),(6,8),(7,8)],126,(5,7),true⟩,⟨[(6,6),(6,7),(7,6)],24,(6,6),true⟩,⟨[(7,5),(8,5),(8,6)],52,(7,5),true⟩]⟩,
  ⟨[(8,2),(8,3),(8,4)],[⟨[(6,2),(7,1),(7,2)],114,(6,1),true⟩,⟨[(6,3),(7,3),(7,4)],122,(6,2),true⟩,⟨[(7,0),(8,0),(8,1)],55,(7,0),true⟩,⟨[(7,5),(8,5),(8,6)],158,(7,2),true⟩]⟩,
]
theorem Tail_b3_entries_match : CatalogLinksCheck catalog Tail_b3_entries := by decide +kernel
theorem Tail_b3_entries_links : CertifiedLinks (localEntries Tail_b3_entries) :=
  catalogLinks_sound catalog_sound Tail_b3_entries_match

def Tail_b3_tiles := EntryTiles (localEntries Tail_b3_entries)
def Tail_b3_owner : Cell → List Cell := tableOwner 9 Tail_b3_tiles [0,0,1,1,2,2,2,3,3,0,4,4,1,5,6,7,3,8,9,9,4,5,5,6,7,7,8,10,9,11,12,12,6,13,14,8,10,11,11,15,12,13,13,14,14,10,16,15,15,17,18,18,18,19,16,16,20,21,17,17,22,22,19,23,20,20,21,21,24,22,25,19,23,23,26,26,26,24,24,25,25]
theorem Tail_b3_partition : OwnerPartitionCheck 9 9 Tail_b3_tiles Tail_b3_owner := by decide +kernel
theorem Tail_b3_cover : EdgeCoverCheck (localEntries Tail_b3_entries) Tail_b3_owner 0 0 9 9 := by decide +kernel
def Tail_b3 : RigidBlock 9 9 :=
  localCheckedBlock Tail_b3_partition Tail_b3_entries_links Tail_b3_cover

def Tail_vertical_0_entries : List EntryData := [
  ⟨[(0,0),(1,0),(2,0)],[]⟩,
  ⟨[(0,1),(1,1),(1,2)],[]⟩,
  ⟨[(0,2),(0,3),(0,4)],[]⟩,
  ⟨[(0,5),(0,6),(0,7)],[]⟩,
  ⟨[(1,3),(2,2),(2,3)],[]⟩,
  ⟨[(1,4),(1,5),(2,5)],[]⟩,
  ⟨[(1,6),(1,7),(2,6)],[]⟩,
  ⟨[(2,1),(3,0),(3,1)],[]⟩,
  ⟨[(2,4),(3,3),(3,4)],[]⟩,
  ⟨[(2,7),(3,7),(4,7)],[]⟩,
  ⟨[(3,2),(4,1),(4,2)],[]⟩,
  ⟨[(3,5),(3,6),(4,5)],[]⟩,
  ⟨[(4,0),(5,0),(5,1)],[⟨[(6,0),(7,0),(8,0)],63,(4,0),false⟩,⟨[(6,1),(7,1),(7,2)],68,(4,0),false⟩]⟩,
  ⟨[(4,3),(5,2),(5,3)],[⟨[(6,2),(6,3),(6,4)],110,(4,2),false⟩]⟩,
  ⟨[(4,4),(5,4),(5,5)],[⟨[(6,2),(6,3),(6,4)],146,(4,2),false⟩,⟨[(6,5),(6,6),(6,7)],64,(4,4),false⟩]⟩,
  ⟨[(4,6),(5,6),(5,7)],[⟨[(6,5),(6,6),(6,7)],122,(4,5),false⟩]⟩,
]
theorem Tail_vertical_0_entries_match : CatalogLinksCheck catalog Tail_vertical_0_entries := by decide +kernel
theorem Tail_vertical_0_entries_links : CertifiedLinks (localEntries Tail_vertical_0_entries) :=
  catalogLinks_sound catalog_sound Tail_vertical_0_entries_match

theorem Tail_vertical_0_same : EntryTiles (localEntries Tail_vertical_0_entries) = Tail_b0_tiles := by rfl
theorem Tail_vertical_0_cover : EdgeCoverCheck (localEntries Tail_vertical_0_entries)
    (shiftOwner (6,0) Tail_b0_owner) 6 0 6 8 := by decide +kernel
theorem Tail_vertical_0 : ∀ A B, Tail_b0.tiles A → Tail_b0.tiles B → Rigid A (Shift (6,0) B) := by
  have hp := localSeam_rigid (h := 6) (w := 8)
    (Tail_vertical_0_same.symm ▸ Tail_b0.partition) Tail_b0_partition
    Tail_vertical_0_entries_links Tail_vertical_0_cover
    (side_disjoint 6 8 6 8).1
  rw [Tail_vertical_0_same] at hp
  exact hp

def Tail_vertical_1_entries : List EntryData := [
  ⟨[(0,0),(1,0),(2,0)],[]⟩,
  ⟨[(0,1),(1,1),(1,2)],[]⟩,
  ⟨[(0,2),(0,3),(0,4)],[]⟩,
  ⟨[(0,5),(0,6),(0,7)],[]⟩,
  ⟨[(1,3),(2,2),(2,3)],[]⟩,
  ⟨[(1,4),(1,5),(2,5)],[]⟩,
  ⟨[(1,6),(1,7),(2,6)],[]⟩,
  ⟨[(2,1),(3,0),(3,1)],[]⟩,
  ⟨[(2,4),(3,3),(3,4)],[]⟩,
  ⟨[(2,7),(3,7),(4,7)],[]⟩,
  ⟨[(3,2),(4,1),(4,2)],[]⟩,
  ⟨[(3,5),(3,6),(4,5)],[]⟩,
  ⟨[(4,0),(5,0),(5,1)],[⟨[(6,0),(6,1),(7,0)],61,(4,0),false⟩]⟩,
  ⟨[(4,3),(5,2),(5,3)],[⟨[(6,2),(6,3),(7,3)],111,(4,2),false⟩]⟩,
  ⟨[(4,4),(5,4),(5,5)],[⟨[(6,4),(6,5),(7,4)],61,(4,4),false⟩]⟩,
  ⟨[(4,6),(5,6),(5,7)],[⟨[(6,6),(6,7),(7,6)],61,(4,6),false⟩]⟩,
]
theorem Tail_vertical_1_entries_match : CatalogLinksCheck catalog Tail_vertical_1_entries := by decide +kernel
theorem Tail_vertical_1_entries_links : CertifiedLinks (localEntries Tail_vertical_1_entries) :=
  catalogLinks_sound catalog_sound Tail_vertical_1_entries_match

theorem Tail_vertical_1_same : EntryTiles (localEntries Tail_vertical_1_entries) = Tail_b0_tiles := by rfl
theorem Tail_vertical_1_cover : EdgeCoverCheck (localEntries Tail_vertical_1_entries)
    (shiftOwner (6,0) Tail_b2_owner) 6 0 9 8 := by decide +kernel
theorem Tail_vertical_1 : ∀ A B, Tail_b0.tiles A → Tail_b2.tiles B → Rigid A (Shift (6,0) B) := by
  have hp := localSeam_rigid (h := 6) (w := 8)
    (Tail_vertical_1_same.symm ▸ Tail_b0.partition) Tail_b2_partition
    Tail_vertical_1_entries_links Tail_vertical_1_cover
    (side_disjoint 6 8 9 8).1
  rw [Tail_vertical_1_same] at hp
  exact hp

def Tail_vertical_2_entries : List EntryData := [
  ⟨[(0,0),(0,1),(1,0)],[]⟩,
  ⟨[(0,2),(0,3),(1,3)],[]⟩,
  ⟨[(0,4),(0,5),(1,4)],[]⟩,
  ⟨[(0,6),(0,7),(1,6)],[]⟩,
  ⟨[(1,1),(1,2),(2,2)],[]⟩,
  ⟨[(1,5),(2,5),(2,6)],[]⟩,
  ⟨[(1,7),(2,7),(3,7)],[]⟩,
  ⟨[(2,0),(2,1),(3,1)],[]⟩,
  ⟨[(2,3),(2,4),(3,3)],[]⟩,
  ⟨[(3,0),(4,0),(5,0)],[]⟩,
  ⟨[(3,2),(4,1),(4,2)],[]⟩,
  ⟨[(3,4),(3,5),(4,4)],[]⟩,
  ⟨[(3,6),(4,6),(4,7)],[]⟩,
  ⟨[(4,3),(5,2),(5,3)],[]⟩,
  ⟨[(4,5),(5,5),(5,6)],[]⟩,
  ⟨[(5,1),(6,0),(6,1)],[]⟩,
  ⟨[(5,4),(6,3),(6,4)],[]⟩,
  ⟨[(5,7),(6,7),(7,7)],[]⟩,
  ⟨[(6,2),(7,1),(7,2)],[]⟩,
  ⟨[(6,5),(6,6),(7,5)],[]⟩,
  ⟨[(7,0),(8,0),(8,1)],[⟨[(9,0),(10,0),(11,0)],63,(7,0),false⟩,⟨[(9,1),(10,1),(10,2)],68,(7,0),false⟩]⟩,
  ⟨[(7,3),(8,2),(8,3)],[⟨[(9,2),(9,3),(9,4)],110,(7,2),false⟩]⟩,
  ⟨[(7,4),(8,4),(8,5)],[⟨[(9,2),(9,3),(9,4)],146,(7,2),false⟩,⟨[(9,5),(9,6),(9,7)],64,(7,4),false⟩]⟩,
  ⟨[(7,6),(8,6),(8,7)],[⟨[(9,5),(9,6),(9,7)],122,(7,5),false⟩]⟩,
]
theorem Tail_vertical_2_entries_match : CatalogLinksCheck catalog Tail_vertical_2_entries := by decide +kernel
theorem Tail_vertical_2_entries_links : CertifiedLinks (localEntries Tail_vertical_2_entries) :=
  catalogLinks_sound catalog_sound Tail_vertical_2_entries_match

theorem Tail_vertical_2_same : EntryTiles (localEntries Tail_vertical_2_entries) = Tail_b2_tiles := by rfl
theorem Tail_vertical_2_cover : EdgeCoverCheck (localEntries Tail_vertical_2_entries)
    (shiftOwner (9,0) Tail_b0_owner) 9 0 6 8 := by decide +kernel
theorem Tail_vertical_2 : ∀ A B, Tail_b2.tiles A → Tail_b0.tiles B → Rigid A (Shift (9,0) B) := by
  have hp := localSeam_rigid (h := 9) (w := 8)
    (Tail_vertical_2_same.symm ▸ Tail_b2.partition) Tail_b0_partition
    Tail_vertical_2_entries_links Tail_vertical_2_cover
    (side_disjoint 9 8 6 8).1
  rw [Tail_vertical_2_same] at hp
  exact hp

def Tail_vertical_3_entries : List EntryData := [
  ⟨[(0,0),(0,1),(1,0)],[]⟩,
  ⟨[(0,2),(0,3),(1,3)],[]⟩,
  ⟨[(0,4),(0,5),(1,4)],[]⟩,
  ⟨[(0,6),(0,7),(1,6)],[]⟩,
  ⟨[(1,1),(1,2),(2,2)],[]⟩,
  ⟨[(1,5),(2,5),(2,6)],[]⟩,
  ⟨[(1,7),(2,7),(3,7)],[]⟩,
  ⟨[(2,0),(2,1),(3,1)],[]⟩,
  ⟨[(2,3),(2,4),(3,3)],[]⟩,
  ⟨[(3,0),(4,0),(5,0)],[]⟩,
  ⟨[(3,2),(4,1),(4,2)],[]⟩,
  ⟨[(3,4),(3,5),(4,4)],[]⟩,
  ⟨[(3,6),(4,6),(4,7)],[]⟩,
  ⟨[(4,3),(5,2),(5,3)],[]⟩,
  ⟨[(4,5),(5,5),(5,6)],[]⟩,
  ⟨[(5,1),(6,0),(6,1)],[]⟩,
  ⟨[(5,4),(6,3),(6,4)],[]⟩,
  ⟨[(5,7),(6,7),(7,7)],[]⟩,
  ⟨[(6,2),(7,1),(7,2)],[]⟩,
  ⟨[(6,5),(6,6),(7,5)],[]⟩,
  ⟨[(7,0),(8,0),(8,1)],[⟨[(9,0),(9,1),(10,0)],61,(7,0),false⟩]⟩,
  ⟨[(7,3),(8,2),(8,3)],[⟨[(9,2),(9,3),(10,3)],111,(7,2),false⟩]⟩,
  ⟨[(7,4),(8,4),(8,5)],[⟨[(9,4),(9,5),(10,4)],61,(7,4),false⟩]⟩,
  ⟨[(7,6),(8,6),(8,7)],[⟨[(9,6),(9,7),(10,6)],61,(7,6),false⟩]⟩,
]
theorem Tail_vertical_3_entries_match : CatalogLinksCheck catalog Tail_vertical_3_entries := by decide +kernel
theorem Tail_vertical_3_entries_links : CertifiedLinks (localEntries Tail_vertical_3_entries) :=
  catalogLinks_sound catalog_sound Tail_vertical_3_entries_match

theorem Tail_vertical_3_same : EntryTiles (localEntries Tail_vertical_3_entries) = Tail_b2_tiles := by rfl
theorem Tail_vertical_3_cover : EdgeCoverCheck (localEntries Tail_vertical_3_entries)
    (shiftOwner (9,0) Tail_b2_owner) 9 0 9 8 := by decide +kernel
theorem Tail_vertical_3 : ∀ A B, Tail_b2.tiles A → Tail_b2.tiles B → Rigid A (Shift (9,0) B) := by
  have hp := localSeam_rigid (h := 9) (w := 8)
    (Tail_vertical_3_same.symm ▸ Tail_b2.partition) Tail_b2_partition
    Tail_vertical_3_entries_links Tail_vertical_3_cover
    (side_disjoint 9 8 9 8).1
  rw [Tail_vertical_3_same] at hp
  exact hp

def Tail_vertical_4_entries : List EntryData := [
  ⟨[(0,0),(0,1),(1,0)],[]⟩,
  ⟨[(0,2),(0,3),(1,3)],[]⟩,
  ⟨[(0,4),(0,5),(1,4)],[]⟩,
  ⟨[(0,6),(0,7),(0,8)],[]⟩,
  ⟨[(1,1),(1,2),(2,1)],[]⟩,
  ⟨[(1,5),(1,6),(2,6)],[]⟩,
  ⟨[(1,7),(1,8),(2,7)],[]⟩,
  ⟨[(2,0),(3,0),(3,1)],[]⟩,
  ⟨[(2,2),(2,3),(2,4)],[]⟩,
  ⟨[(2,5),(3,4),(3,5)],[]⟩,
  ⟨[(2,8),(3,8),(4,8)],[]⟩,
  ⟨[(3,2),(4,1),(4,2)],[]⟩,
  ⟨[(3,3),(4,3),(4,4)],[]⟩,
  ⟨[(3,6),(3,7),(4,6)],[]⟩,
  ⟨[(4,0),(5,0),(5,1)],[⟨[(6,0),(6,1),(7,0)],61,(4,0),false⟩]⟩,
  ⟨[(4,5),(5,5),(5,6)],[⟨[(6,4),(6,5),(7,4)],123,(4,4),false⟩,⟨[(6,6),(6,7),(6,8)],64,(4,5),false⟩]⟩,
  ⟨[(4,7),(5,7),(5,8)],[⟨[(6,6),(6,7),(6,8)],122,(4,6),false⟩]⟩,
  ⟨[(5,2),(5,3),(5,4)],[⟨[(6,2),(6,3),(7,3)],6,(5,2),false⟩,⟨[(6,4),(6,5),(7,4)],13,(5,2),false⟩]⟩,
]
theorem Tail_vertical_4_entries_match : CatalogLinksCheck catalog Tail_vertical_4_entries := by decide +kernel
theorem Tail_vertical_4_entries_links : CertifiedLinks (localEntries Tail_vertical_4_entries) :=
  catalogLinks_sound catalog_sound Tail_vertical_4_entries_match

theorem Tail_vertical_4_same : EntryTiles (localEntries Tail_vertical_4_entries) = Tail_b1_tiles := by rfl
theorem Tail_vertical_4_cover : EdgeCoverCheck (localEntries Tail_vertical_4_entries)
    (shiftOwner (6,0) Tail_b1_owner) 6 0 6 9 := by decide +kernel
theorem Tail_vertical_4 : ∀ A B, Tail_b1.tiles A → Tail_b1.tiles B → Rigid A (Shift (6,0) B) := by
  have hp := localSeam_rigid (h := 6) (w := 9)
    (Tail_vertical_4_same.symm ▸ Tail_b1.partition) Tail_b1_partition
    Tail_vertical_4_entries_links Tail_vertical_4_cover
    (side_disjoint 6 9 6 9).1
  rw [Tail_vertical_4_same] at hp
  exact hp

def Tail_vertical_5_entries : List EntryData := [
  ⟨[(0,0),(0,1),(1,0)],[]⟩,
  ⟨[(0,2),(0,3),(1,3)],[]⟩,
  ⟨[(0,4),(0,5),(1,4)],[]⟩,
  ⟨[(0,6),(0,7),(0,8)],[]⟩,
  ⟨[(1,1),(1,2),(2,1)],[]⟩,
  ⟨[(1,5),(1,6),(2,6)],[]⟩,
  ⟨[(1,7),(1,8),(2,7)],[]⟩,
  ⟨[(2,0),(3,0),(3,1)],[]⟩,
  ⟨[(2,2),(2,3),(2,4)],[]⟩,
  ⟨[(2,5),(3,4),(3,5)],[]⟩,
  ⟨[(2,8),(3,8),(4,8)],[]⟩,
  ⟨[(3,2),(4,1),(4,2)],[]⟩,
  ⟨[(3,3),(4,3),(4,4)],[]⟩,
  ⟨[(3,6),(3,7),(4,6)],[]⟩,
  ⟨[(4,0),(5,0),(5,1)],[⟨[(6,0),(6,1),(7,0)],61,(4,0),false⟩]⟩,
  ⟨[(4,5),(5,5),(5,6)],[⟨[(6,4),(6,5),(6,6)],122,(4,4),false⟩]⟩,
  ⟨[(4,7),(5,7),(5,8)],[⟨[(6,7),(6,8),(7,7)],61,(4,7),false⟩]⟩,
  ⟨[(5,2),(5,3),(5,4)],[⟨[(6,2),(6,3),(7,3)],6,(5,2),false⟩,⟨[(6,4),(6,5),(6,6)],12,(5,2),false⟩]⟩,
]
theorem Tail_vertical_5_entries_match : CatalogLinksCheck catalog Tail_vertical_5_entries := by decide +kernel
theorem Tail_vertical_5_entries_links : CertifiedLinks (localEntries Tail_vertical_5_entries) :=
  catalogLinks_sound catalog_sound Tail_vertical_5_entries_match

theorem Tail_vertical_5_same : EntryTiles (localEntries Tail_vertical_5_entries) = Tail_b1_tiles := by rfl
theorem Tail_vertical_5_cover : EdgeCoverCheck (localEntries Tail_vertical_5_entries)
    (shiftOwner (6,0) Tail_b3_owner) 6 0 9 9 := by decide +kernel
theorem Tail_vertical_5 : ∀ A B, Tail_b1.tiles A → Tail_b3.tiles B → Rigid A (Shift (6,0) B) := by
  have hp := localSeam_rigid (h := 6) (w := 9)
    (Tail_vertical_5_same.symm ▸ Tail_b1.partition) Tail_b3_partition
    Tail_vertical_5_entries_links Tail_vertical_5_cover
    (side_disjoint 6 9 9 9).1
  rw [Tail_vertical_5_same] at hp
  exact hp

def Tail_vertical_6_entries : List EntryData := [
  ⟨[(0,0),(0,1),(1,0)],[]⟩,
  ⟨[(0,2),(0,3),(1,3)],[]⟩,
  ⟨[(0,4),(0,5),(0,6)],[]⟩,
  ⟨[(0,7),(0,8),(1,7)],[]⟩,
  ⟨[(1,1),(1,2),(2,2)],[]⟩,
  ⟨[(1,4),(2,3),(2,4)],[]⟩,
  ⟨[(1,5),(2,5),(3,5)],[]⟩,
  ⟨[(1,6),(2,6),(2,7)],[]⟩,
  ⟨[(1,8),(2,8),(3,8)],[]⟩,
  ⟨[(2,0),(2,1),(3,1)],[]⟩,
  ⟨[(3,0),(4,0),(5,0)],[]⟩,
  ⟨[(3,2),(4,1),(4,2)],[]⟩,
  ⟨[(3,3),(3,4),(4,4)],[]⟩,
  ⟨[(3,6),(4,5),(4,6)],[]⟩,
  ⟨[(3,7),(4,7),(4,8)],[]⟩,
  ⟨[(4,3),(5,2),(5,3)],[]⟩,
  ⟨[(5,1),(6,0),(6,1)],[]⟩,
  ⟨[(5,4),(6,4),(6,5)],[]⟩,
  ⟨[(5,5),(5,6),(5,7)],[]⟩,
  ⟨[(5,8),(6,8),(7,8)],[]⟩,
  ⟨[(6,2),(7,1),(7,2)],[]⟩,
  ⟨[(6,3),(7,3),(7,4)],[]⟩,
  ⟨[(6,6),(6,7),(7,6)],[]⟩,
  ⟨[(7,0),(8,0),(8,1)],[⟨[(9,0),(9,1),(10,0)],61,(7,0),false⟩]⟩,
  ⟨[(7,5),(8,5),(8,6)],[⟨[(9,4),(9,5),(10,4)],123,(7,4),false⟩,⟨[(9,6),(9,7),(9,8)],64,(7,5),false⟩]⟩,
  ⟨[(7,7),(8,7),(8,8)],[⟨[(9,6),(9,7),(9,8)],122,(7,6),false⟩]⟩,
  ⟨[(8,2),(8,3),(8,4)],[⟨[(9,2),(9,3),(10,3)],6,(8,2),false⟩,⟨[(9,4),(9,5),(10,4)],13,(8,2),false⟩]⟩,
]
theorem Tail_vertical_6_entries_match : CatalogLinksCheck catalog Tail_vertical_6_entries := by decide +kernel
theorem Tail_vertical_6_entries_links : CertifiedLinks (localEntries Tail_vertical_6_entries) :=
  catalogLinks_sound catalog_sound Tail_vertical_6_entries_match

theorem Tail_vertical_6_same : EntryTiles (localEntries Tail_vertical_6_entries) = Tail_b3_tiles := by rfl
theorem Tail_vertical_6_cover : EdgeCoverCheck (localEntries Tail_vertical_6_entries)
    (shiftOwner (9,0) Tail_b1_owner) 9 0 6 9 := by decide +kernel
theorem Tail_vertical_6 : ∀ A B, Tail_b3.tiles A → Tail_b1.tiles B → Rigid A (Shift (9,0) B) := by
  have hp := localSeam_rigid (h := 9) (w := 9)
    (Tail_vertical_6_same.symm ▸ Tail_b3.partition) Tail_b1_partition
    Tail_vertical_6_entries_links Tail_vertical_6_cover
    (side_disjoint 9 9 6 9).1
  rw [Tail_vertical_6_same] at hp
  exact hp

def Tail_vertical_7_entries : List EntryData := [
  ⟨[(0,0),(0,1),(1,0)],[]⟩,
  ⟨[(0,2),(0,3),(1,3)],[]⟩,
  ⟨[(0,4),(0,5),(0,6)],[]⟩,
  ⟨[(0,7),(0,8),(1,7)],[]⟩,
  ⟨[(1,1),(1,2),(2,2)],[]⟩,
  ⟨[(1,4),(2,3),(2,4)],[]⟩,
  ⟨[(1,5),(2,5),(3,5)],[]⟩,
  ⟨[(1,6),(2,6),(2,7)],[]⟩,
  ⟨[(1,8),(2,8),(3,8)],[]⟩,
  ⟨[(2,0),(2,1),(3,1)],[]⟩,
  ⟨[(3,0),(4,0),(5,0)],[]⟩,
  ⟨[(3,2),(4,1),(4,2)],[]⟩,
  ⟨[(3,3),(3,4),(4,4)],[]⟩,
  ⟨[(3,6),(4,5),(4,6)],[]⟩,
  ⟨[(3,7),(4,7),(4,8)],[]⟩,
  ⟨[(4,3),(5,2),(5,3)],[]⟩,
  ⟨[(5,1),(6,0),(6,1)],[]⟩,
  ⟨[(5,4),(6,4),(6,5)],[]⟩,
  ⟨[(5,5),(5,6),(5,7)],[]⟩,
  ⟨[(5,8),(6,8),(7,8)],[]⟩,
  ⟨[(6,2),(7,1),(7,2)],[]⟩,
  ⟨[(6,3),(7,3),(7,4)],[]⟩,
  ⟨[(6,6),(6,7),(7,6)],[]⟩,
  ⟨[(7,0),(8,0),(8,1)],[⟨[(9,0),(9,1),(10,0)],61,(7,0),false⟩]⟩,
  ⟨[(7,5),(8,5),(8,6)],[⟨[(9,4),(9,5),(9,6)],122,(7,4),false⟩]⟩,
  ⟨[(7,7),(8,7),(8,8)],[⟨[(9,7),(9,8),(10,7)],61,(7,7),false⟩]⟩,
  ⟨[(8,2),(8,3),(8,4)],[⟨[(9,2),(9,3),(10,3)],6,(8,2),false⟩,⟨[(9,4),(9,5),(9,6)],12,(8,2),false⟩]⟩,
]
theorem Tail_vertical_7_entries_match : CatalogLinksCheck catalog Tail_vertical_7_entries := by decide +kernel
theorem Tail_vertical_7_entries_links : CertifiedLinks (localEntries Tail_vertical_7_entries) :=
  catalogLinks_sound catalog_sound Tail_vertical_7_entries_match

theorem Tail_vertical_7_same : EntryTiles (localEntries Tail_vertical_7_entries) = Tail_b3_tiles := by rfl
theorem Tail_vertical_7_cover : EdgeCoverCheck (localEntries Tail_vertical_7_entries)
    (shiftOwner (9,0) Tail_b3_owner) 9 0 9 9 := by decide +kernel
theorem Tail_vertical_7 : ∀ A B, Tail_b3.tiles A → Tail_b3.tiles B → Rigid A (Shift (9,0) B) := by
  have hp := localSeam_rigid (h := 9) (w := 9)
    (Tail_vertical_7_same.symm ▸ Tail_b3.partition) Tail_b3_partition
    Tail_vertical_7_entries_links Tail_vertical_7_cover
    (side_disjoint 9 9 9 9).1
  rw [Tail_vertical_7_same] at hp
  exact hp

def Tail_horizontal_0_entries : List EntryData := [
  ⟨[(0,0),(1,0),(2,0)],[]⟩,
  ⟨[(0,1),(1,1),(1,2)],[]⟩,
  ⟨[(0,2),(0,3),(0,4)],[]⟩,
  ⟨[(0,5),(0,6),(0,7)],[⟨[(0,8),(1,8),(2,8)],5,(0,5),false⟩]⟩,
  ⟨[(1,3),(2,2),(2,3)],[]⟩,
  ⟨[(1,4),(1,5),(2,5)],[]⟩,
  ⟨[(1,6),(1,7),(2,6)],[⟨[(0,8),(1,8),(2,8)],147,(0,6),true⟩]⟩,
  ⟨[(2,1),(3,0),(3,1)],[]⟩,
  ⟨[(2,4),(3,3),(3,4)],[]⟩,
  ⟨[(2,7),(3,7),(4,7)],[⟨[(0,8),(1,8),(2,8)],127,(0,7),true⟩,⟨[(2,9),(3,8),(3,9)],72,(2,7),false⟩,⟨[(4,8),(5,8),(5,9)],80,(2,7),false⟩]⟩,
  ⟨[(3,2),(4,1),(4,2)],[]⟩,
  ⟨[(3,5),(3,6),(4,5)],[]⟩,
  ⟨[(4,0),(5,0),(5,1)],[]⟩,
  ⟨[(4,3),(5,2),(5,3)],[]⟩,
  ⟨[(4,4),(5,4),(5,5)],[]⟩,
  ⟨[(4,6),(5,6),(5,7)],[⟨[(4,8),(5,8),(5,9)],52,(4,6),false⟩]⟩,
]
theorem Tail_horizontal_0_entries_match : CatalogLinksCheck catalog Tail_horizontal_0_entries := by decide +kernel
theorem Tail_horizontal_0_entries_links : CertifiedLinks (localEntries Tail_horizontal_0_entries) :=
  catalogLinks_sound catalog_sound Tail_horizontal_0_entries_match

theorem Tail_horizontal_0_same : EntryTiles (localEntries Tail_horizontal_0_entries) = Tail_b0_tiles := by rfl
theorem Tail_horizontal_0_cover : EdgeCoverCheck (localEntries Tail_horizontal_0_entries)
    (shiftOwner (0,8) Tail_b0_owner) 0 8 6 8 := by decide +kernel
theorem Tail_horizontal_0 : ∀ A B, Tail_b0.tiles A → Tail_b0.tiles B → Rigid A (Shift (0,8) B) := by
  have hp := localSeam_rigid (h := 6) (w := 8)
    (Tail_horizontal_0_same.symm ▸ Tail_b0.partition) Tail_b0_partition
    Tail_horizontal_0_entries_links Tail_horizontal_0_cover
    (side_disjoint 6 8 6 8).2
  rw [Tail_horizontal_0_same] at hp
  exact hp

def Tail_horizontal_1_entries : List EntryData := [
  ⟨[(0,0),(1,0),(2,0)],[]⟩,
  ⟨[(0,1),(1,1),(1,2)],[]⟩,
  ⟨[(0,2),(0,3),(0,4)],[]⟩,
  ⟨[(0,5),(0,6),(0,7)],[⟨[(0,8),(0,9),(1,8)],1,(0,5),false⟩]⟩,
  ⟨[(1,3),(2,2),(2,3)],[]⟩,
  ⟨[(1,4),(1,5),(2,5)],[]⟩,
  ⟨[(1,6),(1,7),(2,6)],[⟨[(0,8),(0,9),(1,8)],133,(0,6),true⟩]⟩,
  ⟨[(2,1),(3,0),(3,1)],[]⟩,
  ⟨[(2,4),(3,3),(3,4)],[]⟩,
  ⟨[(2,7),(3,7),(4,7)],[⟨[(2,8),(3,8),(3,9)],71,(2,7),false⟩,⟨[(4,8),(5,8),(5,9)],80,(2,7),false⟩]⟩,
  ⟨[(3,2),(4,1),(4,2)],[]⟩,
  ⟨[(3,5),(3,6),(4,5)],[]⟩,
  ⟨[(4,0),(5,0),(5,1)],[]⟩,
  ⟨[(4,3),(5,2),(5,3)],[]⟩,
  ⟨[(4,4),(5,4),(5,5)],[]⟩,
  ⟨[(4,6),(5,6),(5,7)],[⟨[(4,8),(5,8),(5,9)],52,(4,6),false⟩]⟩,
]
theorem Tail_horizontal_1_entries_match : CatalogLinksCheck catalog Tail_horizontal_1_entries := by decide +kernel
theorem Tail_horizontal_1_entries_links : CertifiedLinks (localEntries Tail_horizontal_1_entries) :=
  catalogLinks_sound catalog_sound Tail_horizontal_1_entries_match

theorem Tail_horizontal_1_same : EntryTiles (localEntries Tail_horizontal_1_entries) = Tail_b0_tiles := by rfl
theorem Tail_horizontal_1_cover : EdgeCoverCheck (localEntries Tail_horizontal_1_entries)
    (shiftOwner (0,8) Tail_b1_owner) 0 8 6 9 := by decide +kernel
theorem Tail_horizontal_1 : ∀ A B, Tail_b0.tiles A → Tail_b1.tiles B → Rigid A (Shift (0,8) B) := by
  have hp := localSeam_rigid (h := 6) (w := 8)
    (Tail_horizontal_1_same.symm ▸ Tail_b0.partition) Tail_b1_partition
    Tail_horizontal_1_entries_links Tail_horizontal_1_cover
    (side_disjoint 6 8 6 9).2
  rw [Tail_horizontal_1_same] at hp
  exact hp

def Tail_horizontal_2_entries : List EntryData := [
  ⟨[(0,0),(0,1),(1,0)],[]⟩,
  ⟨[(0,2),(0,3),(1,3)],[]⟩,
  ⟨[(0,4),(0,5),(1,4)],[]⟩,
  ⟨[(0,6),(0,7),(0,8)],[⟨[(0,9),(1,9),(2,9)],5,(0,6),false⟩]⟩,
  ⟨[(1,1),(1,2),(2,1)],[]⟩,
  ⟨[(1,5),(1,6),(2,6)],[]⟩,
  ⟨[(1,7),(1,8),(2,7)],[⟨[(0,9),(1,9),(2,9)],147,(0,7),true⟩]⟩,
  ⟨[(2,0),(3,0),(3,1)],[]⟩,
  ⟨[(2,2),(2,3),(2,4)],[]⟩,
  ⟨[(2,5),(3,4),(3,5)],[]⟩,
  ⟨[(2,8),(3,8),(4,8)],[⟨[(0,9),(1,9),(2,9)],127,(0,8),true⟩,⟨[(2,10),(3,9),(3,10)],72,(2,8),false⟩,⟨[(4,9),(5,9),(5,10)],80,(2,8),false⟩]⟩,
  ⟨[(3,2),(4,1),(4,2)],[]⟩,
  ⟨[(3,3),(4,3),(4,4)],[]⟩,
  ⟨[(3,6),(3,7),(4,6)],[]⟩,
  ⟨[(4,0),(5,0),(5,1)],[]⟩,
  ⟨[(4,5),(5,5),(5,6)],[]⟩,
  ⟨[(4,7),(5,7),(5,8)],[⟨[(4,9),(5,9),(5,10)],52,(4,7),false⟩]⟩,
  ⟨[(5,2),(5,3),(5,4)],[]⟩,
]
theorem Tail_horizontal_2_entries_match : CatalogLinksCheck catalog Tail_horizontal_2_entries := by decide +kernel
theorem Tail_horizontal_2_entries_links : CertifiedLinks (localEntries Tail_horizontal_2_entries) :=
  catalogLinks_sound catalog_sound Tail_horizontal_2_entries_match

theorem Tail_horizontal_2_same : EntryTiles (localEntries Tail_horizontal_2_entries) = Tail_b1_tiles := by rfl
theorem Tail_horizontal_2_cover : EdgeCoverCheck (localEntries Tail_horizontal_2_entries)
    (shiftOwner (0,9) Tail_b0_owner) 0 9 6 8 := by decide +kernel
theorem Tail_horizontal_2 : ∀ A B, Tail_b1.tiles A → Tail_b0.tiles B → Rigid A (Shift (0,9) B) := by
  have hp := localSeam_rigid (h := 6) (w := 9)
    (Tail_horizontal_2_same.symm ▸ Tail_b1.partition) Tail_b0_partition
    Tail_horizontal_2_entries_links Tail_horizontal_2_cover
    (side_disjoint 6 9 6 8).2
  rw [Tail_horizontal_2_same] at hp
  exact hp

def Tail_horizontal_3_entries : List EntryData := [
  ⟨[(0,0),(0,1),(1,0)],[]⟩,
  ⟨[(0,2),(0,3),(1,3)],[]⟩,
  ⟨[(0,4),(0,5),(1,4)],[]⟩,
  ⟨[(0,6),(0,7),(0,8)],[⟨[(0,9),(0,10),(1,9)],1,(0,6),false⟩]⟩,
  ⟨[(1,1),(1,2),(2,1)],[]⟩,
  ⟨[(1,5),(1,6),(2,6)],[]⟩,
  ⟨[(1,7),(1,8),(2,7)],[⟨[(0,9),(0,10),(1,9)],133,(0,7),true⟩]⟩,
  ⟨[(2,0),(3,0),(3,1)],[]⟩,
  ⟨[(2,2),(2,3),(2,4)],[]⟩,
  ⟨[(2,5),(3,4),(3,5)],[]⟩,
  ⟨[(2,8),(3,8),(4,8)],[⟨[(2,9),(3,9),(3,10)],71,(2,8),false⟩,⟨[(4,9),(5,9),(5,10)],80,(2,8),false⟩]⟩,
  ⟨[(3,2),(4,1),(4,2)],[]⟩,
  ⟨[(3,3),(4,3),(4,4)],[]⟩,
  ⟨[(3,6),(3,7),(4,6)],[]⟩,
  ⟨[(4,0),(5,0),(5,1)],[]⟩,
  ⟨[(4,5),(5,5),(5,6)],[]⟩,
  ⟨[(4,7),(5,7),(5,8)],[⟨[(4,9),(5,9),(5,10)],52,(4,7),false⟩]⟩,
  ⟨[(5,2),(5,3),(5,4)],[]⟩,
]
theorem Tail_horizontal_3_entries_match : CatalogLinksCheck catalog Tail_horizontal_3_entries := by decide +kernel
theorem Tail_horizontal_3_entries_links : CertifiedLinks (localEntries Tail_horizontal_3_entries) :=
  catalogLinks_sound catalog_sound Tail_horizontal_3_entries_match

theorem Tail_horizontal_3_same : EntryTiles (localEntries Tail_horizontal_3_entries) = Tail_b1_tiles := by rfl
theorem Tail_horizontal_3_cover : EdgeCoverCheck (localEntries Tail_horizontal_3_entries)
    (shiftOwner (0,9) Tail_b1_owner) 0 9 6 9 := by decide +kernel
theorem Tail_horizontal_3 : ∀ A B, Tail_b1.tiles A → Tail_b1.tiles B → Rigid A (Shift (0,9) B) := by
  have hp := localSeam_rigid (h := 6) (w := 9)
    (Tail_horizontal_3_same.symm ▸ Tail_b1.partition) Tail_b1_partition
    Tail_horizontal_3_entries_links Tail_horizontal_3_cover
    (side_disjoint 6 9 6 9).2
  rw [Tail_horizontal_3_same] at hp
  exact hp

def Tail_horizontal_4_entries : List EntryData := [
  ⟨[(0,0),(0,1),(1,0)],[]⟩,
  ⟨[(0,2),(0,3),(1,3)],[]⟩,
  ⟨[(0,4),(0,5),(1,4)],[]⟩,
  ⟨[(0,6),(0,7),(1,6)],[⟨[(0,8),(0,9),(1,8)],18,(0,6),false⟩]⟩,
  ⟨[(1,1),(1,2),(2,2)],[]⟩,
  ⟨[(1,5),(2,5),(2,6)],[]⟩,
  ⟨[(1,7),(2,7),(3,7)],[⟨[(0,8),(0,9),(1,8)],91,(0,7),true⟩,⟨[(2,8),(2,9),(3,9)],75,(1,7),false⟩,⟨[(3,8),(4,8),(5,8)],81,(1,7),false⟩]⟩,
  ⟨[(2,0),(2,1),(3,1)],[]⟩,
  ⟨[(2,3),(2,4),(3,3)],[]⟩,
  ⟨[(3,0),(4,0),(5,0)],[]⟩,
  ⟨[(3,2),(4,1),(4,2)],[]⟩,
  ⟨[(3,4),(3,5),(4,4)],[]⟩,
  ⟨[(3,6),(4,6),(4,7)],[⟨[(3,8),(4,8),(5,8)],53,(3,6),false⟩]⟩,
  ⟨[(4,3),(5,2),(5,3)],[]⟩,
  ⟨[(4,5),(5,5),(5,6)],[]⟩,
  ⟨[(5,1),(6,0),(6,1)],[]⟩,
  ⟨[(5,4),(6,3),(6,4)],[]⟩,
  ⟨[(5,7),(6,7),(7,7)],[⟨[(3,8),(4,8),(5,8)],127,(3,7),true⟩,⟨[(5,9),(6,8),(6,9)],72,(5,7),false⟩,⟨[(7,8),(8,8),(8,9)],80,(5,7),false⟩]⟩,
  ⟨[(6,2),(7,1),(7,2)],[]⟩,
  ⟨[(6,5),(6,6),(7,5)],[]⟩,
  ⟨[(7,0),(8,0),(8,1)],[]⟩,
  ⟨[(7,3),(8,2),(8,3)],[]⟩,
  ⟨[(7,4),(8,4),(8,5)],[]⟩,
  ⟨[(7,6),(8,6),(8,7)],[⟨[(7,8),(8,8),(8,9)],52,(7,6),false⟩]⟩,
]
theorem Tail_horizontal_4_entries_match : CatalogLinksCheck catalog Tail_horizontal_4_entries := by decide +kernel
theorem Tail_horizontal_4_entries_links : CertifiedLinks (localEntries Tail_horizontal_4_entries) :=
  catalogLinks_sound catalog_sound Tail_horizontal_4_entries_match

theorem Tail_horizontal_4_same : EntryTiles (localEntries Tail_horizontal_4_entries) = Tail_b2_tiles := by rfl
theorem Tail_horizontal_4_cover : EdgeCoverCheck (localEntries Tail_horizontal_4_entries)
    (shiftOwner (0,8) Tail_b2_owner) 0 8 9 8 := by decide +kernel
theorem Tail_horizontal_4 : ∀ A B, Tail_b2.tiles A → Tail_b2.tiles B → Rigid A (Shift (0,8) B) := by
  have hp := localSeam_rigid (h := 9) (w := 8)
    (Tail_horizontal_4_same.symm ▸ Tail_b2.partition) Tail_b2_partition
    Tail_horizontal_4_entries_links Tail_horizontal_4_cover
    (side_disjoint 9 8 9 8).2
  rw [Tail_horizontal_4_same] at hp
  exact hp

def Tail_horizontal_5_entries : List EntryData := [
  ⟨[(0,0),(0,1),(1,0)],[]⟩,
  ⟨[(0,2),(0,3),(1,3)],[]⟩,
  ⟨[(0,4),(0,5),(1,4)],[]⟩,
  ⟨[(0,6),(0,7),(1,6)],[⟨[(0,8),(0,9),(1,8)],18,(0,6),false⟩]⟩,
  ⟨[(1,1),(1,2),(2,2)],[]⟩,
  ⟨[(1,5),(2,5),(2,6)],[]⟩,
  ⟨[(1,7),(2,7),(3,7)],[⟨[(0,8),(0,9),(1,8)],91,(0,7),true⟩,⟨[(2,8),(2,9),(3,9)],75,(1,7),false⟩,⟨[(3,8),(4,8),(5,8)],81,(1,7),false⟩]⟩,
  ⟨[(2,0),(2,1),(3,1)],[]⟩,
  ⟨[(2,3),(2,4),(3,3)],[]⟩,
  ⟨[(3,0),(4,0),(5,0)],[]⟩,
  ⟨[(3,2),(4,1),(4,2)],[]⟩,
  ⟨[(3,4),(3,5),(4,4)],[]⟩,
  ⟨[(3,6),(4,6),(4,7)],[⟨[(3,8),(4,8),(5,8)],53,(3,6),false⟩]⟩,
  ⟨[(4,3),(5,2),(5,3)],[]⟩,
  ⟨[(4,5),(5,5),(5,6)],[]⟩,
  ⟨[(5,1),(6,0),(6,1)],[]⟩,
  ⟨[(5,4),(6,3),(6,4)],[]⟩,
  ⟨[(5,7),(6,7),(7,7)],[⟨[(3,8),(4,8),(5,8)],127,(3,7),true⟩,⟨[(5,9),(6,8),(6,9)],72,(5,7),false⟩,⟨[(7,8),(8,8),(8,9)],80,(5,7),false⟩]⟩,
  ⟨[(6,2),(7,1),(7,2)],[]⟩,
  ⟨[(6,5),(6,6),(7,5)],[]⟩,
  ⟨[(7,0),(8,0),(8,1)],[]⟩,
  ⟨[(7,3),(8,2),(8,3)],[]⟩,
  ⟨[(7,4),(8,4),(8,5)],[]⟩,
  ⟨[(7,6),(8,6),(8,7)],[⟨[(7,8),(8,8),(8,9)],52,(7,6),false⟩]⟩,
]
theorem Tail_horizontal_5_entries_match : CatalogLinksCheck catalog Tail_horizontal_5_entries := by decide +kernel
theorem Tail_horizontal_5_entries_links : CertifiedLinks (localEntries Tail_horizontal_5_entries) :=
  catalogLinks_sound catalog_sound Tail_horizontal_5_entries_match

theorem Tail_horizontal_5_same : EntryTiles (localEntries Tail_horizontal_5_entries) = Tail_b2_tiles := by rfl
theorem Tail_horizontal_5_cover : EdgeCoverCheck (localEntries Tail_horizontal_5_entries)
    (shiftOwner (0,8) Tail_b3_owner) 0 8 9 9 := by decide +kernel
theorem Tail_horizontal_5 : ∀ A B, Tail_b2.tiles A → Tail_b3.tiles B → Rigid A (Shift (0,8) B) := by
  have hp := localSeam_rigid (h := 9) (w := 8)
    (Tail_horizontal_5_same.symm ▸ Tail_b2.partition) Tail_b3_partition
    Tail_horizontal_5_entries_links Tail_horizontal_5_cover
    (side_disjoint 9 8 9 9).2
  rw [Tail_horizontal_5_same] at hp
  exact hp

def Tail_horizontal_6_entries : List EntryData := [
  ⟨[(0,0),(0,1),(1,0)],[]⟩,
  ⟨[(0,2),(0,3),(1,3)],[]⟩,
  ⟨[(0,4),(0,5),(0,6)],[]⟩,
  ⟨[(0,7),(0,8),(1,7)],[⟨[(0,9),(0,10),(1,9)],18,(0,7),false⟩]⟩,
  ⟨[(1,1),(1,2),(2,2)],[]⟩,
  ⟨[(1,4),(2,3),(2,4)],[]⟩,
  ⟨[(1,5),(2,5),(3,5)],[]⟩,
  ⟨[(1,6),(2,6),(2,7)],[]⟩,
  ⟨[(1,8),(2,8),(3,8)],[⟨[(0,9),(0,10),(1,9)],91,(0,8),true⟩,⟨[(2,9),(2,10),(3,10)],75,(1,8),false⟩,⟨[(3,9),(4,9),(5,9)],81,(1,8),false⟩]⟩,
  ⟨[(2,0),(2,1),(3,1)],[]⟩,
  ⟨[(3,0),(4,0),(5,0)],[]⟩,
  ⟨[(3,2),(4,1),(4,2)],[]⟩,
  ⟨[(3,3),(3,4),(4,4)],[]⟩,
  ⟨[(3,6),(4,5),(4,6)],[]⟩,
  ⟨[(3,7),(4,7),(4,8)],[⟨[(3,9),(4,9),(5,9)],53,(3,7),false⟩]⟩,
  ⟨[(4,3),(5,2),(5,3)],[]⟩,
  ⟨[(5,1),(6,0),(6,1)],[]⟩,
  ⟨[(5,4),(6,4),(6,5)],[]⟩,
  ⟨[(5,5),(5,6),(5,7)],[]⟩,
  ⟨[(5,8),(6,8),(7,8)],[⟨[(3,9),(4,9),(5,9)],127,(3,8),true⟩,⟨[(5,10),(6,9),(6,10)],72,(5,8),false⟩,⟨[(7,9),(8,9),(8,10)],80,(5,8),false⟩]⟩,
  ⟨[(6,2),(7,1),(7,2)],[]⟩,
  ⟨[(6,3),(7,3),(7,4)],[]⟩,
  ⟨[(6,6),(6,7),(7,6)],[]⟩,
  ⟨[(7,0),(8,0),(8,1)],[]⟩,
  ⟨[(7,5),(8,5),(8,6)],[]⟩,
  ⟨[(7,7),(8,7),(8,8)],[⟨[(7,9),(8,9),(8,10)],52,(7,7),false⟩]⟩,
  ⟨[(8,2),(8,3),(8,4)],[]⟩,
]
theorem Tail_horizontal_6_entries_match : CatalogLinksCheck catalog Tail_horizontal_6_entries := by decide +kernel
theorem Tail_horizontal_6_entries_links : CertifiedLinks (localEntries Tail_horizontal_6_entries) :=
  catalogLinks_sound catalog_sound Tail_horizontal_6_entries_match

theorem Tail_horizontal_6_same : EntryTiles (localEntries Tail_horizontal_6_entries) = Tail_b3_tiles := by rfl
theorem Tail_horizontal_6_cover : EdgeCoverCheck (localEntries Tail_horizontal_6_entries)
    (shiftOwner (0,9) Tail_b2_owner) 0 9 9 8 := by decide +kernel
theorem Tail_horizontal_6 : ∀ A B, Tail_b3.tiles A → Tail_b2.tiles B → Rigid A (Shift (0,9) B) := by
  have hp := localSeam_rigid (h := 9) (w := 9)
    (Tail_horizontal_6_same.symm ▸ Tail_b3.partition) Tail_b2_partition
    Tail_horizontal_6_entries_links Tail_horizontal_6_cover
    (side_disjoint 9 9 9 8).2
  rw [Tail_horizontal_6_same] at hp
  exact hp

def Tail_horizontal_7_entries : List EntryData := [
  ⟨[(0,0),(0,1),(1,0)],[]⟩,
  ⟨[(0,2),(0,3),(1,3)],[]⟩,
  ⟨[(0,4),(0,5),(0,6)],[]⟩,
  ⟨[(0,7),(0,8),(1,7)],[⟨[(0,9),(0,10),(1,9)],18,(0,7),false⟩]⟩,
  ⟨[(1,1),(1,2),(2,2)],[]⟩,
  ⟨[(1,4),(2,3),(2,4)],[]⟩,
  ⟨[(1,5),(2,5),(3,5)],[]⟩,
  ⟨[(1,6),(2,6),(2,7)],[]⟩,
  ⟨[(1,8),(2,8),(3,8)],[⟨[(0,9),(0,10),(1,9)],91,(0,8),true⟩,⟨[(2,9),(2,10),(3,10)],75,(1,8),false⟩,⟨[(3,9),(4,9),(5,9)],81,(1,8),false⟩]⟩,
  ⟨[(2,0),(2,1),(3,1)],[]⟩,
  ⟨[(3,0),(4,0),(5,0)],[]⟩,
  ⟨[(3,2),(4,1),(4,2)],[]⟩,
  ⟨[(3,3),(3,4),(4,4)],[]⟩,
  ⟨[(3,6),(4,5),(4,6)],[]⟩,
  ⟨[(3,7),(4,7),(4,8)],[⟨[(3,9),(4,9),(5,9)],53,(3,7),false⟩]⟩,
  ⟨[(4,3),(5,2),(5,3)],[]⟩,
  ⟨[(5,1),(6,0),(6,1)],[]⟩,
  ⟨[(5,4),(6,4),(6,5)],[]⟩,
  ⟨[(5,5),(5,6),(5,7)],[]⟩,
  ⟨[(5,8),(6,8),(7,8)],[⟨[(3,9),(4,9),(5,9)],127,(3,8),true⟩,⟨[(5,10),(6,9),(6,10)],72,(5,8),false⟩,⟨[(7,9),(8,9),(8,10)],80,(5,8),false⟩]⟩,
  ⟨[(6,2),(7,1),(7,2)],[]⟩,
  ⟨[(6,3),(7,3),(7,4)],[]⟩,
  ⟨[(6,6),(6,7),(7,6)],[]⟩,
  ⟨[(7,0),(8,0),(8,1)],[]⟩,
  ⟨[(7,5),(8,5),(8,6)],[]⟩,
  ⟨[(7,7),(8,7),(8,8)],[⟨[(7,9),(8,9),(8,10)],52,(7,7),false⟩]⟩,
  ⟨[(8,2),(8,3),(8,4)],[]⟩,
]
theorem Tail_horizontal_7_entries_match : CatalogLinksCheck catalog Tail_horizontal_7_entries := by decide +kernel
theorem Tail_horizontal_7_entries_links : CertifiedLinks (localEntries Tail_horizontal_7_entries) :=
  catalogLinks_sound catalog_sound Tail_horizontal_7_entries_match

theorem Tail_horizontal_7_same : EntryTiles (localEntries Tail_horizontal_7_entries) = Tail_b3_tiles := by rfl
theorem Tail_horizontal_7_cover : EdgeCoverCheck (localEntries Tail_horizontal_7_entries)
    (shiftOwner (0,9) Tail_b3_owner) 0 9 9 9 := by decide +kernel
theorem Tail_horizontal_7 : ∀ A B, Tail_b3.tiles A → Tail_b3.tiles B → Rigid A (Shift (0,9) B) := by
  have hp := localSeam_rigid (h := 9) (w := 9)
    (Tail_horizontal_7_same.symm ▸ Tail_b3.partition) Tail_b3_partition
    Tail_horizontal_7_entries_links Tail_horizontal_7_cover
    (side_disjoint 9 9 9 9).2
  rw [Tail_horizontal_7_same] at hp
  exact hp

def tailPalette : Palette (fun h => h = 6 ∨ h = 9) (fun w => w = 8 ∨ w = 9) where
  tiles h w := if h = 6 then (if w = 8 then Tail_b0.tiles else Tail_b1.tiles)
    else (if w = 8 then Tail_b2.tiles else Tail_b3.tiles)
  partition := by
    intro h w hh hw
    rcases hh with rfl | rfl <;> rcases hw with rfl | rfl
    · exact Tail_b0.partition
    · exact Tail_b1.partition
    · exact Tail_b2.partition
    · exact Tail_b3.partition
  internal := by
    intro h w hh hw
    rcases hh with rfl | rfl <;> rcases hw with rfl | rfl
    · exact Tail_b0.internal
    · exact Tail_b1.internal
    · exact Tail_b2.internal
    · exact Tail_b3.internal
  vertical := by
    intro h k w hh hk hw
    rcases hh with rfl | rfl <;> rcases hk with rfl | rfl <;> rcases hw with rfl | rfl
    · exact Tail_vertical_0
    · exact Tail_vertical_4
    · exact Tail_vertical_1
    · exact Tail_vertical_5
    · exact Tail_vertical_2
    · exact Tail_vertical_6
    · exact Tail_vertical_3
    · exact Tail_vertical_7
  horizontal := by
    intro h w v hh hw hv
    rcases hh with rfl | rfl <;> rcases hw with rfl | rfl <;> rcases hv with rfl | rfl
    · exact Tail_horizontal_0
    · exact Tail_horizontal_1
    · exact Tail_horizontal_2
    · exact Tail_horizontal_3
    · exact Tail_horizontal_4
    · exact Tail_horizontal_5
    · exact Tail_horizontal_6
    · exact Tail_horizontal_7

end LockedTromino.Witnesses
