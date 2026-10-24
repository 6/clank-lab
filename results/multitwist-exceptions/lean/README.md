# Lean proof

From this directory, with [elan](https://github.com/leanprover/elan) installed:

```sh
lake exe cache get
lake build
```

The toolchain and Mathlib dependency are pinned in `lean-toolchain`,
`lakefile.toml` and the standard Lake dependency manifest: Lean 4.32.2 and
Mathlib v4.32.2. Only dependency artifacts come from the Mathlib cache; Lake
checks the local proof sources. After the cache download, the build takes
about a minute.

## What is stated

[Multitwist.lean](Multitwist.lean) works in the free group
`F := FreeGroup (Fin 4)` on generators `x 0, …, x 3`, the fundamental group
of the disk with four punctures (the generators are loops around $p_1, \dots, p_4$).
The Artin automorphisms and their inverses are defined by the images of
the generators, for example

```lean
def s1 : Monoid.End F := FreeGroup.lift ![x 0 * x 1 * (x 0)⁻¹, x 0, x 2, x 3]
```

and the twists and curve words are

```lean
def Ta : Monoid.End F := s1 * s1          -- twist about a  = round{1,2}
def Td : Monoid.End F := s2 * s2          -- twist about d  = round{2,3}
def Tc : Monoid.End F := s3 * s3          -- twist about c  = round{3,4}
def TCp : Monoid.End F := (s1 * s2) ^ 3   -- twist about C' = round{1,2,3}
def TC : Monoid.End F := (s2 * s3) ^ 3    -- twist about C  = round{2,3,4}
def wa : F := x 0 * x 1
def wd : F := x 1 * x 2
def wc : F := x 2 * x 3
def wCp : F := x 0 * x 1 * x 2
def wC : F := x 1 * x 2 * x 3
```

with `Tai`, `Tci` the inverses of `Ta`, `Tc` (built from the inverse
generators and proved inverse). A curve is the conjugacy class of its word
up to inversion. In these terms the file proves, with $\varepsilon = 1$
written `Ta * Tc` and $\varepsilon = -1$ written `Ta * Tci`:

| Fact of the paper | Lean statements |
|---|---|
| Braid relations (sanity of the model) | `braid12`, `braid23`, `comm13` |
| F0: each twist fixes its curve | `F0_a`, `F0_d`, `F0_c`, `F0_Cp`, `F0_C`, as equalities of words |
| F1: the pentagon pattern | 20 statements `F1_meet_u_v` and `F1_disjoint_u_v` over the ordered pairs: `IsConj (Tu wv) wv` for disjoint pairs, `¬ IsConj (Tu wv) wv ∧ ¬ IsConj (Tu wv) wv⁻¹` for meeting pairs |
| F2: the components of $t$ commute | `F2 : Ta * Tc = Tc * Ta` |
| $t$ and its inverse | `t_pos_inv`, `t_neg_inv` |
| F3, every `k : ℕ` | `F3_j0 k : (Ta ^ k * Td) wCp = wCp`; `F3_jk_pos k : ((Tai * Tci) ^ k * (Ta ^ k * Td)) wC = wC` and `F3_jk_neg k` for the other sign; `member_pos`, `member_neg` simplify $t^{-k} f_k$ to $T_c^{\mp k} T_d$ |
| F4, every `k : ℕ` | `F4_a k`, `F4_c k`: $T_a(f_k(a))$ and $T_c(f_k(a))$ are conjugate neither to $f_k(a)$ nor to its inverse |

For a disjoint pair the proof gives an explicit conjugating word (the
identity for six of the ten pairs; for the twists about $C'$ and $C$ acting
on $a$, $d$, $c$ the twist moves the word to a conjugate). For a meeting pair it gives a homomorphism from `F` to the
permutations of a three-element set that sends exactly one of `Tu wv` and
`wv` to the identity; since conjugacy and inversion preserve being sent to
the identity, the two words are not conjugate up to inversion. The base
cases are closed by `decide`. For every `k`, F3 follows by commuting and
canceling twists (F2 and the inverse statements), and F4 by applying the
automorphism `Ta ^ k`, which preserves conjugacy, to the case `k = 0`.

[Check.lean](Check.lean) restates each fact above with its exact type, so
that the build fails if a statement changes. It contains a negative control:
with $C$ and $C'$ exchanged, the $j = 0$ statement is false, and
`example : (Ta * Td) wC ≠ wC := by decide` is proved. It ends with
`#guard_msgs in #print axioms` for 38 statements, so the build fails if any
of them uses an axiom beyond `propext`, `Classical.choice` and
`Quot.sound` (in particular `sorryAx` or `native_decide`).

## The pseudo-Anosov-base extension

[V2.lean](V2.lean) imports the original Artin model and defines

```lean
def g (k : ℕ) : Monoid.End F := Tai * Tci ^ (k+1) * Td
def t : Monoid.End F := Ta * Tc
```

These are the algebraic counterparts of $g_k=T_a^{-1}T_c^{-(k+1)}T_d$
and $t=T_aT_c$ in the extension. Its written surface theorem uses $k\geq1$;
the Lean identities hold for every `k : ℕ`, including zero.

| Algebraic fact | Lean statements in `Multitwist.V2` |
|---|---|
| Integer normal form, in any group with `Commute A C`, for all `k n : ℤ` | `integer_identity A C D h k n : (A * C) ^ n * (A ^ (-1 : ℤ) * C ^ (-(k+1)) * D) = A ^ (n-1) * C ^ (n-k-1) * D` |
| The two exceptional members in the Artin model | `first_member k : t * g k = Tci ^ k * Td`; `second_member k : t ^ (k+1) * g k = Ta ^ k * Td` |
| The fixed words at the exceptional exponents | `fixed_C k : ((t ^ 1) * g k) wC = wC`; `fixed_Cp k : ((t ^ (k+1)) * g k) wCp = wCp` |
| The image of `wa` under `g k` is moved by both component twists | `nonconj_a k` and `nonconj_c k`: the twisted image is conjugate neither to the original image nor to its inverse |

The nonconjugacy proof transports the original base cases through
`initial k := Tai * Tci ^ (k+1)`, using its proved left inverse `undo k`
and its commutation with `Ta` and `Tc`.

[V2Check.lean](V2Check.lean) restates all 18 new declarations with their
exact types and guards each exact axiom set, all contained in `propext`,
`Classical.choice` and `Quot.sound`. Its concrete controls prove that
swapping the fixed curves, shifting the exceptional exponents or changing
the exponent inside `g k` breaks the corresponding identities; omitting
`Td` breaks the nonconjugacy conclusions; and dropping commutation breaks
the integer identity in the permutation group on three elements. The
default `lake build` checks both original modules and both extension modules.

## What is not stated

This development does not formalize mapping class groups, isotopy classes
of curves or pseudo-Anosov maps, so the surface topology remains written. The written
proof in the paper supplies it: that the Artin automorphisms are the maps
the Dehn twists induce on the fundamental group; that essential simple
closed-curve classes inject into conjugacy classes up to inversion; that
$i(u, v) = 0$ exactly when $T_u(v) = v$; the exact intersection numbers;
the argument that $a$, $c$ and $f_k(a)$ fill the surface; and that a
mapping class fixing an essential curve is not pseudo-Anosov.
For the extension, Lean also does not prove the pseudo-Anosov property of
$g_k$, Penner's theorem or its application, the filling property of the
three curves $a$, $c$ and $g_k(a)$, or any bound on intervals of exceptional exponents.
The written proof supplies these surface arguments, using the finite
diagram checks supplied outside this Lean project.
