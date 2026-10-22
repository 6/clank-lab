import Generated.Tail

namespace LockedTromino.Witnesses
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- Remove all links for the first tile of the actual 6-by-8 tail block. -/
private def brokenEntries : List EntryData := match Tail_b0_entries with
  | [] => []
  | e::es => {e with links := []} :: es

-- Cell sets and ownership are still the exact original rectangle partition.
example : OwnerPartitionCheck 6 8 (EntryTiles (localEntries brokenEntries)) Tail_b0_owner := by decide +kernel
-- Nevertheless the actual edge-cover check detects the planted gap.
example : ¬ EdgeCoverCheck (localEntries brokenEntries) Tail_b0_owner 0 0 6 8 := by decide +kernel

end LockedTromino.Witnesses
