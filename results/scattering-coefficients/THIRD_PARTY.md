# Third-party material

The Lean sources in `lean/` are distributed under Apache-2.0. The package
depends on the following upstream projects, fetched by Lake at the revisions
in `lean/lake-manifest.json`. Their source trees and compiled caches are not
included in this bundle, and no changes to them are supplied. Lake retains
their upstream license and attribution notices in the downloaded packages.

| Dependency | License |
| --- | --- |
| [mathlib](https://github.com/leanprover-community/mathlib4) | [Apache-2.0](https://github.com/leanprover-community/mathlib4/blob/905b95818eb32af7874a58b427f50c1711a5e96c/LICENSE) |
| [plausible](https://github.com/leanprover-community/plausible) | [Apache-2.0](https://github.com/leanprover-community/plausible/blob/e12c1910fe855cbfc38803cd4e55543906d5fa62/LICENSE) |
| [LeanSearchClient](https://github.com/leanprover-community/LeanSearchClient) | [Apache-2.0](https://github.com/leanprover-community/LeanSearchClient/blob/c5d5b8fe6e5158def25cd28eb94e4141ad97c843/LICENSE) |
| [importGraph](https://github.com/leanprover-community/import-graph) | [Apache-2.0](https://github.com/leanprover-community/import-graph/blob/7e9612bf0b9ee66db3cb5b9988a35afc706f5a12/LICENSE) |
| [proofwidgets](https://github.com/leanprover-community/ProofWidgets4) | [Apache-2.0](https://github.com/leanprover-community/ProofWidgets4/blob/6e311e2a844da9b2cc3971187df2fe0066947b93/LICENSE) |
| [aesop](https://github.com/leanprover-community/aesop) | [Apache-2.0](https://github.com/leanprover-community/aesop/blob/a7dbf0c63b694e47f425f3dcddbc0e178bb432d3/LICENSE) |
| [Qq](https://github.com/leanprover-community/quote4) | [Apache-2.0](https://github.com/leanprover-community/quote4/blob/38d591e778f100aec9762bb582f9c7f55f50e9dc/LICENSE) |
| [batteries](https://github.com/leanprover-community/batteries) | [Apache-2.0](https://github.com/leanprover-community/batteries/blob/023ce7d62a0531e22a5331e20b587817a80d49ff/LICENSE) |
| [Cli](https://github.com/leanprover/lean4-cli) | [MIT](https://github.com/leanprover/lean4-cli/blob/88679d088c9720c27ebdf2ba4dafe17341747f94/LICENSE) |

The Lean compiler and Lake are supplied by
[Lean](https://github.com/leanprover/lean4) under
[Apache-2.0](https://github.com/leanprover/lean4/blob/v4.32.2/LICENSE).
Elan installs the toolchain selected by `lean/lean-toolchain`.

Mathematical background follows Elgin, Reading and Stella, *Cluster
scattering coefficients in rank 2* (arXiv 2404.11381); Burcroff, Lee, Mou,
Musiker and Reineke (arXiv 2511.14672); and Gross, Pandharipande and
Siebert, *The tropical vertex* (arXiv 0902.0779). These works are cited for
their mathematics; no text, tables or code from them are reproduced.
