# Lean proof

The proofs, the Lean formalization and the text were produced by AI models
(from OpenAI and Anthropic), working under the author's direction.

With [elan](https://github.com/leanprover/elan) installed, run from this directory:

```sh
lake exe cache get
lake build
```

The project pins Lean 4.19.0 and Mathlib commit
`c44e0c8ee63ca166450922a373c7409c5d26b00b`. Lake fetches Mathlib and its
pinned dependencies; the first command retrieves their compiled cache.
The second builds every proof and [Checks.lean](Checks.lean), including
explicit endpoint types, unfolded endpoint definitions, small definition
checks and axiom guards. No separate script is required. With the dependencies cached, the proof
build takes about a minute.

The main theorem is
`LNEDExtension.field_shift_counterexample` in [FieldClaim.lean](FieldClaim.lean).
For every characteristic-zero field $K$ and every nonzero $c$ in $K$, it
constructs the algebra endomorphism $f(X)\mapsto f(X+c)$, its difference
$D(f)=f(X)-f(X+c)$ and the ideal $J=(X(X-c/2))$. The map $D$ is linear,
locally nilpotent and satisfies the E-derivation identity. Every positive
power of $X^2$ lies in $D(J)$, and multiplying any such power by $X$ gives
a polynomial outside $D(J)$. Thus the actual ideal image fails the
Mathieu condition.

`Mathieu` in [Statements.lean](Statements.lean) means that, whenever all
positive powers of a polynomial $a$ belong to a subset $W$, every product
$ba^md$ belongs to $W$ for all sufficiently large $m$, for each pair of
polynomials $b,d$. The threshold may depend on $a,b,d$.

The proof files have the following roles.

- [Endpoint.lean](Endpoint.lean) defines the rational shift, its difference,
  the generating ideal and its image. [HardUnit.lean](HardUnit.lean)
  proves the all-index Bernoulli identities and nonvanishing statements
  using Mathlib's Bernoulli and zeta-value results. `D0.lean` through
  `D3.lean` prove linearity, local nilpotence, the E-identity and the
  monomial image criterion. [D5.lean](D5.lean) assembles the infinite
  power witnesses, and [Claim.lean](Claim.lean) gives the rational
  ideal-image counterexample.
- [Generic.lean](Generic.lean) and [Unit.lean](Unit.lean) transport the
  rational proof to characteristic-zero integral domains with a rational
  algebra structure. [Rescale.lean](Rescale.lean) handles every nonzero
  shift over a characteristic-zero field and proves that the zero-shift
  image is zero and is Mathieu. [FieldClaim.lean](FieldClaim.lean) states
  the counterexamples with the actual algebra map, linear map and ideal.
- [Multivariable.lean](Multivariable.lean) and
  [ChosenVariable.lean](ChosenVariable.lean) prove the counterexample
  for an arbitrary index set with a chosen variable: that variable is
  shifted by one and every other generator is fixed. The endpoint
  `LNEDExtension.chosen_variable_counterexample` includes the locally
  nilpotent linear E-map and the same power witnesses.
  `finite_variable_endpoint` specializes to every positive finite number
  of variables.
- [Beta.lean](Beta.lean), [Half.lean](Half.lean),
  [Translate.lean](Translate.lean) and [BetaReplay.lean](BetaReplay.lean)
  prove the signed rational families for the unit shift and
  $J_\beta=(X(X-\beta))$. For every natural $r$, the images for
  $\beta=\pm(r+1/2)$ fail the Mathieu condition; the positive witness is
  $P_r=X^2\prod_{j<r}(X^2-(j+1/2)^2)$, with multiplier $X$.
  Translation gives the negative witness $P_r(X+r+1/2)$ and multiplier
  $X+r+1/2$. For every positive integer $N$, the images for
  $\beta=\pm N$ are Mathieu. These endpoints address the nonzero
  half-integral lattice over the rationals.
- [NegativeHalf.lean](NegativeHalf.lean) separately gives the translated
  counterexample at $\beta=-1/2$ over every characteristic-zero field.
- [ScopeFunctional.lean](ScopeFunctional.lean),
  [ScopeIdeal.lean](ScopeIdeal.lean) and [ScopeRadical.lean](ScopeRadical.lean)
  prove that the unit-shift image of $(X(X-1/2))$ contains no nonzero ideal
  and has strong radical zero, over every characteristic-zero field.
  `LNEDScope.scope_literal` states this directly using polynomial
  composition and the principal ideal. The strong radical consists of
  polynomials $a$ such that for each $b$ there is a threshold after which
  $ba^m$ always belongs to the image.
- [RootOne.lean](RootOne.lean) and [ScopeControl.lean](ScopeControl.lean)
  check the contrasting $\beta=1$ case: its image is the ideal $(X)$,
  and its strong radical contains $X$. [Replay.lean](Replay.lean) and
  [ExtensionReplay.lean](ExtensionReplay.lean) check the assembled endpoints.

[Checks.lean](Checks.lean) requires the recorded declarations to use only
`propext`, `Classical.choice` and `Quot.sound`; a changed axiom list fails
the build. The proof uses neither `sorry` nor additional axioms nor
`native_decide`. The mathematical proofs are checked by Lean's kernel;
the cached Mathlib dependencies, Lean installation and elaborator are
part of the checking environment. The statement's interpretation and its
relation to the literature require the accompanying mathematical review.

The positive integer family is a consequence of the established
finite-evaluation framework, including van den Essen and van Hove's
[Theorem 1](https://arxiv.org/abs/1907.06106v1); it is not a new criterion.
Zhao's Lemma 4.8 already treats the unit cases. The additional code does
not classify arbitrary rational parameters, and it does not supply a new
proof for the parameter zero. The signed families are over the rationals
with unit shift, apart from the separately stated field-generic cases.

See the [literature reading notes](LITERATURE.md) for the source reading
record and its limits.

## Source versions and reading limits

The paper cites Zhao's final journal articles; numbered references to the
univariate article follow the fully read arXiv:1701.06125v1, and references
to the conjecture paper follow arXiv:1701.05992v2. Only the abstract and
first page of the final univariate journal article were read; final
pages 2–18 remain unread. The 2021 chapter by van den Essen, Kuroda and
Crachiola was read through its abstract/bibliography and Scott Nollet's
whole-book review, not through its body or a chapter-specific review.
The [literature table](LITERATURE.md) gives each source's individual reading
depth, including review-only and abstract-only sources.
