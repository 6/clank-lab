"""Check a G4 certificate against the live interval family implementation."""
from fractions import Fraction
import copy
import json
import sys

import fans


def check(c):
    if c["schema"] != 1 or c["families"] != ["44", "333", "36", "ii"]:
        raise ValueError("incomplete family chart certificate")
    limits = {key: Fraction(*c[key]) for key in ("tau_bound", "gamma0_norm_bound", "Pi_abs_bound")}
    out = {}
    for kind in c["families"]:
        f = fans.FanFamily(kind)
        result = fans.certify_family_chart(f, c["free_box"])
        for key, value in (("tau_bound", result["tau_upper"]),
                           ("gamma0_norm_bound", result["gamma0_norm_upper"]),
                           ("Pi_abs_bound", result["Pi_abs_upper"])):
            if Fraction(value) > limits[key]:
                raise ValueError(f"{kind}: false {key}")
        out[kind] = result
    return out


def corruptions(c):
    for field, value in (("free_box", [[-1, 1], [-1, 1], [-1, 1]]),
                         ("gamma0_norm_bound", [1, 2]), ("tau_bound", [1, 10]),
                         ("Pi_abs_bound", [139, 100])):
        bad = copy.deepcopy(c)
        bad[field] = value
        try:
            check(bad)
        except ValueError:
            continue
        raise ValueError(f"corrupt certificate accepted: {field}")
    return 4


if __name__ == "__main__":
    with open(sys.argv[1]) as f:
        c = json.load(f)
    print(json.dumps({"families": check(c), "corruptions_rejected": corruptions(c)},
                     sort_keys=True, indent=2))
