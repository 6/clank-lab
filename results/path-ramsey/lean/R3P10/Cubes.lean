import R3P10.Rung

/-! # The final K_18 cube list, read from the data files

`data/k18/cubes.txt` (the depth-10 cubes) without the 16 split parents
(`data/k18/split/parents.txt`, line numbers from 0), followed by
`data/k18/split/children.txt`: 15,956 cubes. `Checks.lean` tests its length
and first entries. -/

namespace R3P10

/-- Lines of space-separated integers, each ended by `0`; zero tokens are
dropped, so no cube contains the literal 0. -/
def parseCubes (s : String) : List (List Int) :=
  (s.splitOn "\n").filterMap fun line =>
    let toks := (line.splitOn " ").filterMap String.toInt?
    if toks.isEmpty then none else some (toks.filter (· ≠ 0))

def parseNats (s : String) : List ℕ :=
  ((s.replace "\n" " ").splitOn " ").filterMap String.toNat?

def cubesTxt : String := include_str "../../data/k18/cubes.txt"
def parentsTxt : String := include_str "../../data/k18/split/parents.txt"
def childrenTxt : String := include_str "../../data/k18/split/children.txt"

/-- The final cube list. -/
def finalCubes : List (List Int) :=
  let L := (parseCubes cubesTxt).toArray
  let par := parseNats parentsTxt
  (List.range L.size).filterMap (fun i => if par.contains i then none else L[i]?) ++
    parseCubes childrenTxt

theorem parseCubes_ne_zero (s : String) : ∀ c ∈ parseCubes s, ∀ l ∈ c, l ≠ 0 := by
  intro c hc l hl
  simp only [parseCubes, List.mem_filterMap] at hc
  obtain ⟨line, _, h⟩ := hc
  split_ifs at h
  simp only [Option.some.injEq] at h
  subst h
  simpa using (List.mem_filter.1 hl).2

theorem finalCubes_ne_zero : ∀ c ∈ finalCubes, ∀ l ∈ c, l ≠ 0 := by
  intro c hc
  simp only [finalCubes, List.mem_append, List.mem_filterMap, List.mem_range] at hc
  rcases hc with ⟨i, _, h⟩ | h
  · split_ifs at h
    rw [List.getElem?_toArray] at h
    exact parseCubes_ne_zero _ c (List.mem_of_getElem? h)
  · exact parseCubes_ne_zero _ c h

end R3P10
