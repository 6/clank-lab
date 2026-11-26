"""Construct and independently replay one admissible finite-level certificate."""
import hashlib
import json
from pathlib import Path

from sage.all import EllipticCurve, ZZ, kronecker, prime_range

import brandt
import check_brandt
import check_segments
import check_form
import check_theta
import forms
import segments
import theta


def digest(value):
    data = json.dumps(value, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(data).hexdigest()


def admissible(case, ell):
    p, N = case["p"], case["N"]
    E = EllipticCurve(case["ainvs"])
    return (ZZ(ell).is_prime() and N % ell != 0 and kronecker(case["D"], ell) == -1
            and ell**2 % p != 1 and (E.ap(ell) - case["eps"]*(1+ell)) % p == 0)


def certify(case, ell, directory):
    """case must already have passed the arithmetic gates in arithmetic.py."""
    directory = Path(directory)
    if case["Nminus"] != 1 or not admissible(case, ell):
        raise ValueError("requires Nminus=1 and a sign-matched admissible prime")
    N, p, D = case["N"], case["p"], case["D"]
    good = [int(q) for q in prime_range(50) if N*ell % q][:4]
    degrees = good + case["levels"]
    brandt.build(case, ell, directory, degrees)
    check_brandt.verify(case, ell, directory, degrees)
    if ZZ(N).is_squarefree():
        try:
            forms.solve(case, ell, directory, good[:-1])
        except (ValueError, forms.PriceLimit):
            # A nonzero lower-level eigenspace can obstruct the signed shortcut.
            # The unreduced system uses only the actual good and bad Hecke equations.
            segments.solve(case, ell, directory, good)
            check_segments.check(case, ell, directory, good)
        else:
            check_form.check(case, ell, directory, good)
    else:
        segments.solve(case, ell, directory, good)
        check_segments.check(case, ell, directory, good)
    h = ZZ(D).class_number(proof=True)
    if h > 1:
        from class_moment import evaluate
        result = evaluate(case, ell, directory)
        import check_class_moment
        replay = check_class_moment.evaluate(case, ell, directory)
        check_class_moment.compare_variants(result, replay, D, p)
    else:
        result = theta.evaluate(case, ell, directory)
        check_theta.check(case, ell, directory, result)
        if not ZZ(N).is_squarefree():
            from tame_cm import check
            check(case, ell, directory, result)
    variants = result.get("checks", result).get("variants", [])
    magnitudes = {abs(min(v["first_moment"], p-v["first_moment"])) for v in variants}
    if len(magnitudes) > 1:
        raise ArithmeticError("CM choices give inconsistent moments up to sign")
    vector = json.loads((directory/"eigen.json").read_text())
    # Store one compact commitment for the complete audit over coordinate choices.
    (directory/"moment.json").write_text(json.dumps(result, sort_keys=True) + "\n")
    return {"ell": ell, "a_ell": int(EllipticCurve(case["ainvs"]).ap(ell)),
            "epsilon_ell": case["eps"], "good_hecke": good, "raw_flags": len(vector),
            "eigen_sha256": digest(vector), "audit_sha256": digest(result),
            "coefficients": result["coefficients"], "T": result["first_moment"]}
