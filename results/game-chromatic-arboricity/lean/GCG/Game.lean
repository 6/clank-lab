import Mathlib

/-!
# The graph colouring game

Alice and Bob alternately colour an uncoloured vertex of a graph `G` with one of `k`
colours not used on any of its neighbours; Alice moves first. The game ends when the
player to move has no legal move. Alice wins if every vertex is then coloured; otherwise
Bob wins. The game chromatic number of `G` is the least `k` for which Alice has a
winning strategy.
-/

namespace GCG

variable {V : Type*}

/-- `Move G c c'`: the position `c'` arises from the position `c` by one legal move, that
is, by giving one uncoloured vertex `v` a colour `i` that no neighbour of `v` has. -/
def Move (G : SimpleGraph V) {k : ℕ} (c c' : V → Option (Fin k)) : Prop :=
  ∃ v i, c v = none ∧ (∀ w, G.Adj v w → c w ≠ some i) ∧ c' v = some i ∧
    ∀ u, u ≠ v → c' u = c u

/-- `AliceWins G k b c`: in the `k`-colour game on `G`, Alice has a winning strategy from
the position `c` (a partial colouring) with Alice to move if `b = true` and Bob to move if
`b = false`. -/
inductive AliceWins (G : SimpleGraph V) (k : ℕ) : Bool → (V → Option (Fin k)) → Prop
  | full (b : Bool) (c : V → Option (Fin k)) : (∀ v, c v ≠ none) → AliceWins G k b c
  | alice (c c' : V → Option (Fin k)) :
      Move G c c' → AliceWins G k false c' → AliceWins G k true c
  | bob (c : V → Option (Fin k)) :
      (∃ c', Move G c c') → (∀ c', Move G c c' → AliceWins G k true c') →
      AliceWins G k false c

/-- Alice wins the `k`-colour game on `G`: she has a winning strategy from the empty
colouring, moving first. The game chromatic number of `G` exceeds `K` exactly when
`¬ AliceWinsGame G k` for every `k ≤ K`. -/
def AliceWinsGame (G : SimpleGraph V) (k : ℕ) : Prop :=
  AliceWins G k true (fun _ => none)

/-- No 4-cycle: there are no `a, b, c, d` with `a ≠ c`, `b ≠ d` and `a ~ b ~ c ~ d ~ a`. -/
def C4Free (G : SimpleGraph V) : Prop :=
  ∀ a b c d, a ≠ c → b ≠ d → G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → False

end GCG
