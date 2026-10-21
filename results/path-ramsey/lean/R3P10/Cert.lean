import R3P10.Sat
import R3P10.Cubes
import Std.Tactic.BVDecide.LRAT.Parser

/-! # Certificates as Lean terms, checked by native evaluation

A certificate is two string literals: the path clauses its proof uses (one
line per clause, `c p0 p1 ... p9`) and an LRAT proof (text or binary,
parsed by Lean's own `Std.Tactic.BVDecide.LRAT.parseLRATProof`). The
command `lrat_cert` reads them from files, adds them as definitions, and
proves the stated fact with `Lean.ofReduceBool` applied to the Boolean
`checkUnsat` (R3P10/Sat.lean), which the kernel evaluates with Lean's
compiler and interpreter. Parsing is untrusted: a wrong parse only makes
the check fail. -/

namespace R3P10

open Std.Tactic.BVDecide

/-! ## The base formula, from the DIMACS file -/

/-- Clauses of a DIMACS file: every line that is not a comment or the
header, read as integers up to the terminating `0`. -/
def parseDimacs (s : String) : CNF :=
  (s.splitOn "\n").filterMap fun line =>
    if line.startsWith "c" || line.startsWith "p" then none else
    let toks := (line.splitOn " ").filterMap String.toInt?
    if toks.isEmpty then none else some (toks.takeWhile (· ≠ 0))

/-- `data/cnf/k18p10.cnf`, the formula the solver and the cube certificates use. -/
def k18Txt : String := include_str "../../data/cnf/k18p10.cnf"

/-- `data/cnf/k18p10.cnf` as a clause list. -/
def k18Base : CNF := parseDimacs k18Txt

/-! ## Decoding -/

/-- Lines `c p0 ... p_{m-1}`. -/
def parsePaths (s : String) : Array (ℕ × List ℕ) :=
  ((s.splitOn "\n").filterMap fun line =>
    match (line.splitOn " ").filterMap String.toNat? with
    | c :: p => some (c, p)
    | [] => none).toArray

def parseProof (s : String) : Array LRAT.IntAction :=
  match LRAT.parseLRATProof s.toUTF8 with
  | .ok p => p
  | .error _ => #[]

/-! ## The compact certificate format

One ASCII string: a stream of natural numbers, each a little-endian
base-64 numeral whose digits are bytes `0..63` (more digits follow) or
`64..127` (last digit). The stream is: the number of paths, then each
path as its colour and its `m` vertices; then the proof's steps, with
lemma ids implicit and consecutive from `id0`:

* `0, k, d_1, ..., d_k`: delete ids `d_1, d_1 + d_2, ...`;
* `l + 1, u_1, ..., u_l, h, e_1, ..., e_h`: add lemma `id` with literals
  `u / 2` (negated when `u` is odd) and hints `id - e_j`; the empty
  clause when `l = 0`.

Every function here is total (structural recursion on fuel), so the
evaluated term contains no `partial` or `implemented_by` definitions. -/

/-- The number at byte `i`: its value and the position after it. -/
def rdNat (b : ByteArray) : (fuel i acc sh : ℕ) → ℕ × ℕ
  | 0, i, acc, _ => (acc, i)
  | fuel + 1, i, acc, sh =>
    if h : i < b.size then
      let x := b[i].toNat
      if 64 ≤ x then (acc + ((x - 64) <<< sh), i + 1)
      else rdNat b fuel (i + 1) (acc + (x <<< sh)) (sh + 6)
    else (acc, i)

@[inline] def rd (b : ByteArray) (i : ℕ) : ℕ × ℕ := rdNat b 12 i 0 0

/-- `k` numbers from byte `i`, each mapped by `f` from the previous result. -/
def rdMany (b : ByteArray) (f : ℕ → ℕ → ℕ) : (k : ℕ) → (i : ℕ) → (prev : ℕ) → Array ℕ → Array ℕ × ℕ
  | 0, i, _, acc => (acc, i)
  | k + 1, i, prev, acc =>
    let (x, i) := rd b i
    let y := f prev x
    rdMany b f k i y (acc.push y)

def decLit (u : ℕ) : Int := if u % 2 = 1 then -((u / 2 : ℕ) : Int) else ((u / 2 : ℕ) : Int)

/-- The paths: `n` of them, each a colour and `m` vertices. -/
def rdPaths (b : ByteArray) (m : ℕ) : (n : ℕ) → (i : ℕ) → Array (ℕ × List ℕ) → Array (ℕ × List ℕ) × ℕ
  | 0, i, acc => (acc, i)
  | n + 1, i, acc =>
    let (c, i) := rd b i
    let (vs, i) := rdMany b (fun _ x => x) m i 0 #[]
    rdPaths b m n i (acc.push (c, vs.toList))

/-- The proof steps from byte `i`, the next lemma being `id`. -/
def rdSteps (b : ByteArray) : (fuel i id : ℕ) → Array LRAT.IntAction → Array LRAT.IntAction
  | 0, _, _, acc => acc
  | fuel + 1, i, id, acc =>
    if i < b.size then
      let (v, i) := rd b i
      if v = 0 then
        let (k, i) := rd b i
        let (ids, i) := rdMany b (· + ·) k i 0 #[]
        rdSteps b fuel i id (acc.push (.del ids))
      else
        let (ls, i) := rdMany b (fun _ u => u) (v - 1) i 0 #[]
        let (h, i) := rd b i
        let (hs, i) := rdMany b (fun _ e => id - e) h i 0 #[]
        let a : LRAT.IntAction :=
          if v = 1 then .addEmpty id hs else .addRup id (ls.map decLit) hs
        rdSteps b fuel i (id + 1) (acc.push a)
    else acc

/-- Decode a compact certificate for a formula of `nF` clauses. -/
def decodeCert (m nF : ℕ) (s : String) : Array (ℕ × List ℕ) × Array LRAT.IntAction :=
  let b := s.toUTF8
  let (np, i) := rd b 0
  let (ps, i) := rdPaths b m np i #[]
  (ps, rdSteps b b.size i (nF + np + 1) #[])

/-- The check for a compact certificate. -/
def checkCompact (n m : ℕ) (F : CNF) (cert : String) : Bool :=
  let (ps, pf) := decodeCert m F.length cert
  checkUnsat n m F ps pf

theorem checkCompact_sound {n m : ℕ} {F : CNF} {cert : String}
    (h : checkCompact n m F cert = true) : UnsatWithPaths n m F :=
  checkUnsat_sound h

/-- The check for a certificate given as two strings. -/
def checkStr (n m : ℕ) (F : CNF) (paths proof : String) : Bool :=
  checkUnsat n m F (parsePaths paths) (parseProof proof)

theorem checkStr_sound {n m : ℕ} {F : CNF} {paths proof : String}
    (h : checkStr n m F paths proof = true) : UnsatWithPaths n m F :=
  checkUnsat_sound h

/-! ## The K_18 cubes -/

/-- Cube `i` of the final list, against the base formula read from the file. -/
def checkCube (i : ℕ) (paths proof : String) : Bool :=
  checkStr 18 10 (k18Base ++ cubeUnits (finalCubes.getD i [])) paths proof

/-- Cube `i` of the final list is refuted. -/
def CubeOK (i : ℕ) : Prop := UnsatWithPaths 18 10 (encode 18 9 ++ cubeUnits (finalCubes.getD i []))

/-! ## Ranges of cubes -/

theorem range_nil {P : ℕ → Prop} (a : ℕ) : ∀ i, a ≤ i → i < a → P i :=
  fun _ h1 h2 => absurd (Nat.lt_of_le_of_lt h1 h2) (Nat.lt_irrefl _)

theorem range_cons {P : ℕ → Prop} {a b : ℕ} (h : P a) (t : ∀ i, a + 1 ≤ i → i < b → P i) :
    ∀ i, a ≤ i → i < b → P i := by
  intro i h1 h2
  rcases Nat.eq_or_lt_of_le h1 with rfl | h1
  · exact h
  · exact t i h1 h2

theorem range_join {P : ℕ → Prop} {a b c : ℕ} (h1 : ∀ i, a ≤ i → i < b → P i)
    (h2 : ∀ i, b ≤ i → i < c → P i) : ∀ i, a ≤ i → i < c → P i := by
  intro i ha hc
  by_cases hb : i < b
  · exact h1 i ha hb
  · exact h2 i (Nat.le_of_not_lt hb) hc

/-- All cubes refuted, from a range covering the list's length. -/
theorem cubes_of_range {N : ℕ} (hN : finalCubes.length = N) (h : ∀ i, 0 ≤ i → i < N → CubeOK i) :
    ∀ c ∈ finalCubes, UnsatWithPaths 18 10 (encode 18 9 ++ cubeUnits c) := by
  intro c hc
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
  have := h i (Nat.zero_le _) (hN ▸ hi)
  unfold CubeOK at this
  rwa [List.getD_eq_getElem _ _ hi] at this

def checkCubeC (i : ℕ) (cert : String) : Bool :=
  checkCompact 18 10 (k18Base ++ cubeUnits (finalCubes.getD i [])) cert

theorem checkCubeC_sound {i : ℕ} {cert : String} (hb : encode 18 9 = k18Base)
    (h : checkCubeC i cert = true) :
    UnsatWithPaths 18 10 (encode 18 9 ++ cubeUnits (finalCubes.getD i [])) := by
  rw [hb]; exact checkCompact_sound h

theorem checkCube_sound {i : ℕ} {paths proof : String} (hb : encode 18 9 = k18Base)
    (h : checkCube i paths proof = true) :
    UnsatWithPaths 18 10 (encode 18 9 ++ cubeUnits (finalCubes.getD i [])) := by
  rw [hb]; exact checkStr_sound h

end R3P10
