# Checking details

The standard proof commands and exact statements are in
[the Lean README](../lean/README.md). The paper gives the full written
proof and distinguishes its written deductions from separate Lean theorems.
[Detailed source interfaces](details.tex) retain the axiom output, file map
and statement-by-statement correspondence. The optional numerical
illustration is described in [data/README.md](../data/README.md).

[Source context](context.tex) records the exact prior-work expressions and
convention comparisons used by the paper, with their original references.
It adds no theorem or verification claim.


The inherited PNT source comments cite
[Romyar Sharifi's Algebraic number theory notes](https://www.math.ucla.edu/~sharifi/algnum.pdf).
Theorem 7.1.12 supports the continuation and simple-pole portion of the
comment that cites it; it does not itself assert nonvanishing on the whole
line with real part 1. Corollary 7.2.3 states Dirichlet density, rather than
by itself the stronger weighted asymptotic mentioned in the surrounding
comment. These qualifications concern source commentary. The imported
files and the audited Lean proofs remain unchanged.
