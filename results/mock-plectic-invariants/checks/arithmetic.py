"""Exact FG input checks and the rational rank-two census (Sage 10.8)."""

from functools import lru_cache
from math import gcd, prod

from sage.all import EllipticCurve, QQ, QuadraticField, ZZ, infinity, kronecker, pari


@lru_cache(maxsize=128)
def _curve(ainvs):
    return EllipticCurve(ainvs).minimal_model()


@lru_cache(maxsize=128)
def _conductor_data(E):
    N = int(E.conductor())
    factors = tuple((int(q), int(e)) for q, e in ZZ(N).factor())
    return N, factors


@lru_cache(maxsize=128)
def _rank(E):
    lower, upper = map(int, pari(E).ellrank()[:2])
    if lower == upper:
        return {"rank": lower, "pari_bounds": [lower, upper], "proof": "PARI ellrank"}
    try:
        rank = int(E.rank(use_database=False, proof=True))
    except (RuntimeError, NotImplementedError):
        return {"rank": None, "pari_bounds": [lower, upper], "proof": None}
    return {"rank": rank, "pari_bounds": [lower, upper], "proof": "Sage rank(proof=True)"}


@lru_cache(maxsize=256)
def _modular_symbol(E, sign):
    # The nonzero scaling of the exact rational eigensymbol is immaterial.
    return E.modular_symbol(sign=sign, implementation="eclib")


@lru_cache(maxsize=256)
def _twist(E, D):
    twist = E.quadratic_twist(D).minimal_model()
    chi = [int(kronecker(D, j)) for j in range(abs(D))]
    odd = _modular_symbol(E, -1)
    symbol_sum = sum(chi[j] * odd(QQ(j) / abs(D))
                     for j in range(1, abs(D)) if chi[j])
    # The Gauss sum identity multiplies the central value by a nonzero scalar.
    if symbol_sum:
        rank = {"rank": 0, "proof": "exact nonzero twisted central symbol; Kolyvagin"}
    else:
        rank = _rank(twist)
    return twist, str(symbol_sum), bool(symbol_sum), rank


@lru_cache(maxsize=128)
def _image(E, p):
    # True and False are certificates; None means Sage could not decide.
    image = E.galois_representation().is_surjective(p)
    return None if image is None else bool(image)


@lru_cache(maxsize=64)
def _class_number(D):
    return int(QuadraticField(D).class_number(proof=True))


def case(ainvs, D, p, *, all_rank_two=False):
    """Return a JSON-serializable audit of E, K=Q(sqrt(D)), and p.

    The canonical equation in 'ainvs' is minimal. For valid FG 1.1 inputs,
    'levels' lists the primes of the Eichler level p*Nplus. 'eps' is the
    auxiliary sign for the eligible component, and 'level_signs' maps decimal
    string keys to the reversal signs -a_q at multiplicative level primes.
    'ap' and 'vdelta' are a_p(E) and v_p(minimal discriminant). At a repeated
    level prime the segment solver uses flags modulo its full prime power. An auxiliary
    prime has its own eigenvalue 'epsilon_ell' in admissible_ells().
    """
    if len(ainvs) != 5:
        raise ValueError("expected five Weierstrass coefficients")
    E = _curve(tuple(ZZ(a) for a in ainvs))
    D, p = int(ZZ(D)), int(ZZ(p))
    if not ZZ(p).is_prime():
        raise ValueError("p must be prime")
    N, factors = _conductor_data(E)
    multiplicative = bool(E.local_data(p).has_multiplicative_reduction())
    ap = int(E.ap(p))
    vdelta = int(E.discriminant().valuation(p))
    imaginary_fundamental = D < 0 and bool(ZZ(D).is_fundamental_discriminant())
    symbols = {str(q): int(kronecker(D, q)) for q in sorted({p, *(q for q, _ in factors)})}
    fg11 = {
        "imaginary_fundamental_D": imaginary_fundamental,
        "not_exceptional_unit_field": D not in (-3, -4),
        "p_inert": symbols[str(p)] == -1,
        "N_unramified_in_K": gcd(N, D) == 1,
        "multiplicative_at_p": multiplicative,
    }
    inert_factors = [(q, e) for q, e in factors if q != p and symbols[str(q)] == -1]
    fg11["Nminus_squarefree"] = all(e == 1 for _, e in inert_factors)
    fg11["Nminus_even_number_of_primes"] = len(inert_factors) % 2 == 0
    fg12 = {"p_at_least_5": p >= 5, "surjective_mod_p": None, "ramification": None}
    result = {
        "p": p, "D": D, "N": N, "ainvs": list(map(int, E.a_invariants())),
        "levels": [], "eps": None, "level_signs": {}, "ap": ap, "vdelta": vdelta,
        "N_factors": [list(pair) for pair in factors],
        "kronecker_D": symbols, "FG_1_1": fg11, "FG_1_2": fg12,
        "status": "fails_FG_1_1_or_p_bound", "eligible": False,
        "quaternion_backend": False, "quaternion_squarefree_h1": False,
        "generic_segment_domain": False,
    }
    if not all(fg11.values()) or p < 5:
        return result

    Nminus = prod(q**e for q, e in inert_factors)
    Nplus = N // (p * Nminus)
    levels = [q for q, _ in factors if Nminus % q]
    if N != p * Nplus * Nminus or N % (p * p) == 0:
        raise ArithmeticError("inconsistent multiplicative conductor factorization")
    ramification = {}
    for q, _ in inert_factors:
        if (q*q - 1) % p == 0:
            if not E.local_data(q).has_multiplicative_reduction():
                raise ArithmeticError("squarefree inert part must be multiplicative")
            vq = int(E.discriminant().valuation(q))
            ramification[str(q)] = {"vdelta": vq, "ramified": vq % p != 0}
    image = _image(E, p)
    fg12.update(surjective_mod_p=image, ramification=ramification)
    result.update(
        Nplus=Nplus, Nminus=Nminus, eichler_level=p*Nplus,
        levels=levels, level_signs={str(q): -int(E.ap(q)) for q, e in factors
                                    if q in levels and e == 1},
        class_number=_class_number(D), squarefree_N=all(e == 1 for _, e in factors),
        tate_normalization_is_p_unit=vdelta % p != 0,
        residual_at_p_distinct_inertia_characters=True,
    )
    if image is False or any(not datum["ramified"] for datum in ramification.values()):
        result["status"] = "fails_FG_1_2"
        return result
    if image is None:
        result["status"] = "unknown_residual_image"
        return result

    central = _modular_symbol(E, +1)(0)
    twist, twisted_symbol, twisted_nonzero, twist_rank = _twist(E, D)
    plus_rank = _rank(E)
    root = int(E.root_number())
    twist_root = int(twist.root_number())
    ap_twist = int(twist.ap(p))
    if root * twist_root != 1 or ap_twist != -ap or ap not in (-1, 1):
        raise ArithmeticError("inconsistent global root or inert local twist sign")
    bad_ramification_witness = int(ZZ(abs(D)).prime_divisors()[0])
    result.update(
        root_number_plus=root, root_number_minus=twist_root, root_number_K=root*twist_root,
        central_symbol_plus=str(central), central_symbol_minus_twisted=twisted_symbol,
        central_L_EK_zero=(central == 0 or not twisted_nonzero),
        rank_plus=plus_rank, rank_minus=twist_rank, twist_conductor=int(twist.conductor()),
        ap_twist=ap_twist, twist_analytic_rank_zero=twisted_nonzero,
        global_component_sign=-ap*root, local_component_sign=-ap,
        tensor_conjugation_sign=root,
        residual_restriction={"image": "GL2(F_p)", "ramified_prime_of_K": bad_ramification_witness,
                              "good_prime_away_from_p": N*p % bad_ramification_witness != 0},
    )
    rp, rm = plus_rank["rank"], twist_rank["rank"]
    delta_plus, delta_minus = int(ap == 1), int(ap_twist == 1)
    result.update(
        rank_K=rp+rm if rp is not None and rm is not None else None,
        delta_plus=delta_plus, delta_minus=delta_minus,
        exceptional_zero_obstruction=(rp is not None and rp+delta_plus > 2
                                      or rm is not None and rm+delta_minus > 2),
    )
    if result["central_L_EK_zero"] and result["exceptional_zero_obstruction"]:
        result["status"] = "FG_nonvanishing_obstructed"
    elif rp is None or rm is None:
        result["status"] = "unknown_component_rank"
    elif not result["central_L_EK_zero"] or rp + rm != 2:
        result["status"] = "fails_rank_two_over_K" if all_rank_two else "fails_rank_two_plus_component"
    elif not all_rank_two and (rp, rm, root) != (2, 0, 1):
        result["status"] = "fails_rank_two_plus_component"
    else:
        principal = result["class_number"] == 1
        squarefree = result["squarefree_N"]
        result.update(status="eligible", eligible=True, eps=-ap*root,
                      quaternion_backend=principal and squarefree and Nminus == 1,
                      quaternion_squarefree_h1=principal and squarefree,
                      generic_segment_domain=principal and Nminus == 1)
    return result


def admissible_ells(ainvs, D, p, *, k=1, sign=None, start=2, stop=None):
    """Yield all k-admissible primes in [start,stop), ascending, lazily.

    sign=None allows both FG signs. sign=+1 selects the odd first-moment
    branch for the nonsplit, root-number-plus cases in this census.
    """
    E = _curve(tuple(ZZ(a) for a in ainvs))
    N = int(E.conductor())
    p, k, D = int(ZZ(p)), int(ZZ(k)), int(ZZ(D))
    if (p < 5 or not ZZ(p).is_prime() or k < 1 or sign not in (None, -1, 1)
            or D >= 0 or not ZZ(D).is_fundamental_discriminant()):
        raise ValueError("require imaginary fundamental D, prime p >= 5, k >= 1, sign ±1 or None")
    modulus = p**k
    ell = ZZ(max(2, start) - 1).next_prime()
    while stop is None or ell < stop:
        if N*p % ell and (ell*ell - 1) % p and kronecker(D, ell) == -1:
            aell = int(E.ap(ell))
            for epsilon in ((1, -1) if sign is None else (sign,)):
                if (aell - epsilon * (ell + 1)) % modulus == 0:
                    yield {"ell": int(ell), "a_ell": aell, "epsilon_ell": epsilon, "k": k,
                           "frobenius_Q_eigenvalues_mod_pk": [epsilon % modulus,
                                                              int(epsilon*ell % modulus)],
                           "frobenius_K_eigenvalues_mod_pk": [1, int(ell*ell % modulus)]}
        ell = ell.next_prime()


def sw_status(data, depths=(2, 3), max_summands=50_000):
    """Certify order 2 from a rigorous degree-2 coefficient and Kato's lower bound."""
    if not data["eligible"] or data["rank_plus"]["rank"] != 2:
        return {"status": "outside_census_component"}
    p, D = data["p"], data["D"]
    E = _curve(tuple(map(ZZ, data["ainvs"])))
    attempts = []
    lseries = None
    for n in depths:
        terms = (p - 1) * p**(n - 1)
        if terms > max_summands:
            attempts.append({"depth": n, "summands": terms, "status": "over_term_cap"})
            continue
        try:
            if lseries is None:
                lseries = E.padic_lseries(p, implementation="eclib")
            series = lseries.series(n, prec=3)
            if series.precision_absolute() < 3:
                attempts.append({"depth": n, "summands": terms, "status": "missing_T2"})
                continue
            c2 = series[2]
            if c2.precision_absolute() == infinity or c2.valuation() == infinity:
                # Sage can omit an exactly zero coefficient of the finite sum.
                # An omitted coefficient supplies no nonzero certificate.
                attempts.append({"depth": n, "summands": terms, "status": "unknown_precision",
                                 "T2": str(c2), "T2_absolute_precision": None,
                                 "T2_valuation_lower_bound": None})
                continue
            prec = int(c2.precision_absolute())
            valuation = int(c2.valuation())
            known_nonzero = not c2.is_zero() and valuation < prec
            attempt = {"depth": n, "summands": terms, "T2": str(c2),
                       "T2_absolute_precision": prec, "T2_valuation_lower_bound": valuation,
                       "status": "nonzero" if known_nonzero else "unknown_precision"}
            if known_nonzero:
                attempt["T2_valuation"] = valuation
                if prec > 0:
                    attempt["T2_residue"] = str(c2.lift())
            attempts.append(attempt)
        except (ArithmeticError, NotImplementedError, RuntimeError, ValueError) as exc:
            attempts.append({"depth": n, "summands": terms, "status": "software_error",
                             "error": f"{type(exc).__name__}: {exc}"})
            continue
        if known_nonzero:
            if any(not series[i].is_zero() for i in (0, 1)):
                raise ArithmeticError("computed nonzero below the proven lower bound")
            return {
                "status": "ord_T_eq_2", "ord_T_lower_bound": 2, "ord_T_upper_bound": 2,
                "attempts": attempts, "p_primary_Sha_plus": "finite",
                "p_primary_Sha_K": "finite" if data["twist_analytic_rank_zero"] else None,
                "Sha_K_evidence": "quadratic +/- restriction and twist Kolyvagin"
                if data["twist_analytic_rank_zero"] else None,
                "D": D,
            }
    return {"status": "unknown", "ord_T_lower_bound": 2, "ord_T_upper_bound": None,
            "attempts": attempts, "p_primary_Sha_plus": None, "p_primary_Sha_K": None}
