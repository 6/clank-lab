# Corrections and interpretation of historical records

The earlier background, checking account, bibliography and landing page are
retained without rewriting them. The following annotations correct their
reporting and explain the boundary of the records. The theorem, Lean
sources, checkers, inputs and certificates are unchanged.

## Audit controls

The historical checking account says that the encoding auditor rejects
30 planted corruptions. There are 30 controls: 29 expected rejections and
one expected acceptance. In [audit/corruptions.py](audit/corruptions.py), the
incomplete lazy path-log control is accepted by design. Omitting valid path
clauses weakens the formula; a checked refutation of the weaker formula
still suffices. The old unqualified rejection count is incorrect. The
parenthetical exception in [the original checking notes](README.md) gives
the intended behavior.

The same notes call all seven formalization edits “unsound.” They are
mutation controls: some changes are mathematically sound in isolation but
fail because a proved statement or certified formula has changed. The
paper's preserved discussion makes that distinction. Their rejection is
evidence that the development binds its definitions and certificate
inputs, rather than proof that every edited formula is logically unsound.

## Native evaluation

Some comments in the unchanged Lean sources call the certificate evaluation
“kernel” evaluation. The certificate command executes compiled code through
`Lean.ofReduceBool`, with `Lean.trustCompiler`; the kernel does not reduce
all these checks itself. See [CertCmd.lean](../lean/R3P10/CertCmd.lean).
The closed native checks also include the final cube-list length in
[R3P10Ladder.lean](../lean/R3P10Ladder.lean), besides certificate checks and
the base-formula comparison. The historical account's “two kinds” list is
therefore incomplete. These checks use the same compiler/native trust
already disclosed in the paper and the final axiom list; no new logical
assumption or theorem is introduced by this annotation.

## Historical sources and measurements

The retained background cites older original articles, including Faudree
and Schelp's 1975 paper. The October 24, 2026 source check confirmed their
bibliographic identities but could not retrieve every original full text.
In particular its page 159 wording and proof of Theorem 6 were not directly
read in that check. The current introduction instead identifies the
attribution made in Dybizbański, Dzido and Radziszowski's
[arXiv:1207.5851v3, Section 2](https://arxiv.org/abs/1207.5851v3); the lower-bound
construction is quoted from the directly read Gyárfás–Ruszinkó–Sárközy–Szemerédi
[author manuscript, Section 1.1, after Theorem 1](https://www.renyi.hu/~gyarfas/Cikkek/120_sharp3cfin.pdf).
Older historical quotations remain records of the preceding edition,
not newly certified transcriptions of inaccessible originals.

[COMPLETION.md](../COMPLETION.md) and the retained timing accounts describe
the earlier completed computation. This edition reports no new mathematical
search, Lean build or certificate acceptance. Rounded phase timings need
not add exactly to a rounded total; CPU time, wall time, compressed archive
size and replay disk space describe different quantities. The timings
remain historical reported measurements, rather than new measurements.
