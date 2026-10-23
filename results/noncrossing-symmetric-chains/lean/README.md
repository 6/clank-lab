# Lean development

From this directory, with [elan](https://github.com/leanprover/elan) installed:

```sh
lake build
```

`lean-toolchain` pins Lean 4.34.0, which elan installs. Only Lean's bundled
standard library is used: there is no Mathlib or other dependency, so there
is no cache to fetch. The default target builds every proof module and
`Check.lean`, which checks the endpoint's exact type, small definition
controls, and the axioms of the main constructions and theorems.

`Endpoint.lean` defines reflection-length absolute order, its interval,
actual order-theoretic covers, and a rank-indexed partition into nonempty
saturated symmetric chains. Its `GeneralEndpoint` is the requested
universal assertion:

```lean
def GeneralEndpoint
    (eligible : (W : Type u) → IntervalData W → Prop)
    (coxeter : {W : Type u} → IntervalData W → W → Prop) : Prop :=
  ∀ (W : Type u) (D : IntervalData W), eligible W D → ∀ c, coxeter D c →
    Nonempty (SCD (Interval D c)
      (Cover (fun x y => AbsoluteLE D x.val y.val))
      (fun x => D.reflectionLength x.val) D.essentialRank)
```

The eligibility and Coxeter predicates are semantic interfaces, rather than
definitions of complex-linear representations. There is no unconditional
Lean theorem proving `GeneralEndpoint`. No classification theorem or finite
certificate is asserted as an axiom. The general theorem in the paper
combines published results and written identifications with the checked
lemmas and the separate exact computations.

The proved components are:

- `Product.lean`: the constructive decomposition of a grid of two chains,
  the resulting product decomposition, partition and rank properties, and
  equivalence between product covers and actual order-theoretic covers.
- `Transfer.lean`: decomposition transport, preservation of shortest
  reflection-word length and absolute order, product length additivity,
  interval equality, transport on actual interval covers, and the zero-
  and one-rank base decompositions.
- `Reduction.lean`: the exceptional-type table partition, the conditional
  reduction from published cases and six additional cases, and closure
  under arbitrary finite products, including zero factors.
- `IntervalCertificate.lean`: the abstract rank-bound argument showing that
  exhaustive closure under rank-decreasing reflection edges captures the
  exact geodesic interval. Its hypotheses are explicit checker obligations.
- `Check.lean`: the endpoint type, definition controls, and guarded axiom
  reports.

The finite group computations are not imported into Lean. Their exact
arithmetic, group algorithms, models, and connection to the abstract
hypotheses remain as disclosed in [the checker documentation](../checks/README.md)
and the paper. The Lean development uses no added axioms, `sorry`, or
compiled evaluation (`native_decide`).
