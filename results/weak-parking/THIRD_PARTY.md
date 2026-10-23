# Third-party material

The computation programs, certificate checkers and certificates in this
folder are supplied under Apache-2.0. No upstream program source is
included. The mathematical definitions and the short attributed quotation
in the paper come from Armstrong, Reiner and Rhoades's *Parking spaces*;
the other cited works are used for their mathematics.

The checks require independently installed software:

| Dependency | License | Use |
| --- | --- | --- |
| [GAP](https://www.gap-system.org/) | [GPL-2.0](https://github.com/gap-system/gap/blob/master/LICENSE) | Exact group and linear algebra algorithms |
| [SmallGrp](https://gap-packages.github.io/smallgrp/) | Artistic-2.0 | GAP group algorithms |
| [TransGrp](https://www.math.colostate.edu/~hulpke/transgrp) | Artistic-2.0 AND (GPL-2.0-only OR GPL-3.0-only) | GAP group algorithms |
| [SymPy](https://www.sympy.org/) | [BSD-3-Clause](https://github.com/sympy/sympy/blob/master/LICENSE) | Exact rational polynomial crosschecks |
| [Python](https://www.python.org/) | [PSF license](https://docs.python.org/3/license.html) | Certificate parsing and checker orchestration |

These dependencies are distributed separately under their own licenses;
no modified copies of them are supplied here. The two group checkers use
the same GAP kernel.
