# The formal statement and its mathematical interpretation

The main theorem checked by Lean is
`ADKZPricing.Generated.source_frozen_endpoint : ADKZPricing.ProposedEndpoint`.
The proposition, in the notation of the paper, is exactly:

```lean
def ProposedEndpoint : Prop :=
  ∃ A : Matrix (Fin 80) (Fin 41) ℚ, Uniform A ∧
    ∃ X Y : SignVector, Cocircuit A X ∧ Cocircuit A Y ∧
      Complementary X Y ∧ ¬ ShortWalk A X Y
```

`Uniform A` says that every 41-row minor is nonzero. A sign vector is a
function from the 80 row labels to the integers. A covector is a real sign
pattern of the rational matrix acting on a real vector, so its entries
are −1, 0 or 1. `Complementary X Y` says that each zero set has 40 elements
and, in each coordinate, one endpoint is zero and the other is positive.
Thus the zero sets partition the rows and both cocircuits are positive
elsewhere, exactly as in the construction.

`ShortWalk A X Y` allows any length at most 41, all signed intermediate
cocircuits, and repeated vertices. Antipodal vertices remain distinct.
An absent walk of at most 41 edges gives a distance lower bound of 42 for
this pair, and therefore the same lower bound for the graph's diameter.
It does not assert an exact value for the whole diameter.

## Cocircuits, adjacency and the paper's conventions

Composition of sign vectors takes the first nonzero coordinate:
$(X\circ Y)_i=X_i$ when $X_i\ne0$, and $Y_i$ otherwise.
A conformal face $Z$ of $X$ has $`Z_i\in\{0,X_i\}`$ in every coordinate.
The formal `Cocircuit` definition is a nonzero covector minimal under
conformal faces. For a uniform matrix, the formal proof identifies these
with the nonzero covectors of inclusion-minimal support used in the paper.

For distinct cocircuits, formal adjacency says that $X\circ Y=Y\circ X$
is a covector whose only cocircuit conformal faces are $X$ and $Y$.
The published-definition bridge proves that this is equivalent to an
empty separation set and exactly 39 common zero rows. Thus it is the
paper's cocircuit graph, including both signs and all intermediate
vertices. The equivalent published weak inequality is equality in the
uniform rank-41 case. The seven bridge theorems and their build command
are listed in [the Lean guide](README.md).

The interpretation of real sign covectors as a realizable oriented matroid
is standard mathematics, as in Adler, De Loera, Klee and Zhang, Section 2,
printed page 8. The paper's upper bound of 42 for the designated pair is a
written deduction from the two source paths and the preserved graphs.
The formally verified endpoint is the lower bound.

## Construction, source data and logical principles

The formal proof uses ordered generic perturbations. The paper instead
displays a Vandermonde perturbation for its written realization. Both
prove an existential rational-matrix assertion; no identity between the
two resulting matrices is asserted. The formal proof checks sign counting,
first and second preservation, row-label transport and factor-walk bounds.
It directly checks the source matrix, complete vertex and edge cover,
integer distance-potential inequalities, and positive-functional identities.
It concludes the displayed proposition without undischarged certificate
hypotheses. Generator output is checked by the Lean kernel, rather than
trusted as a compiled numerical answer.

The paper's appendix prints a shorter positive-functional witness for the
same integer source matrix. Its functional and weights differ from those
in `data/chart.json` and the generated formal data. Its 41 identities and
strictly positive coefficients are verified by the separate exact
written-certificate checker. No equality of the two witnesses, or Lean
verification of the new appendix's coefficients, is asserted. Positivity
on the same cones suffices for the written construction; the formal
source matrix, witness and proof terms remain unchanged.

The endpoint and seven bridge guards admit only `propext`,
`Classical.choice` and `Quot.sound` (propositional extensionality, classical
choice and quotient constructions). The guide gives the exact axiom-print
commands. The independently accepted proof established these outputs;
the separate fresh standalone replay has now reproduced the endpoint
and all seven bridge lists exactly. It completed all 1,264 proof modules
without reusing old target proof objects. No `sorryAx`, `native_decide` or
`Lean.ofReduceBool` is admitted. A source-level audit alone does not
establish that a build or its axiom guards succeeded.

The pinned toolchain, Mathlib revision, build instructions, certificate
checker commands and measured replay evidence are in the guides, rather
than in the paper's mathematical argument. See also
[the literature notes](LITERATURE.md) for source versions, exact locators
and reading limits.
