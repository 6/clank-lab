"""Theta coefficients from coprime ideal representatives and proper form composition."""
from collections import Counter
from itertools import product

from brandt import BrandtGraph
from class_orbit import class_transfers, representative_form
from class_projection import project
from segments import Flags, act, adj, column, label
from tame_cm import generator, ray_value, stable_lines


def evaluate(case, ell, directory):
    flags = Flags(case, ell, directory)
    values = flags.read("eigen.json")
    p, D = case["p"], case["D"]
    graph = BrandtGraph.from_case(case, ell)
    raw = list(graph.cm_embeddings(D))
    records = flags.data["cm"]
    if len(raw) != len(records):
        raise ValueError("CM graph replay changed the embedding count")
    variants = []
    for (i, omega), cm in zip(raw, records):
        if cm["index"] != i or cm["omega"] != str(omega):
            raise ValueError("CM graph replay changed the embedding coordinates")
        shift, rays = generator(cm[f"p{p}"], p)
        transfers = class_transfers(graph.ideals, D, i, omega, [ell, *flags.levels],
                                    locate=graph.classify)
        forms = [representative_form(z.representative, D) for z in transfers]
        step, offsets = project(D, p, shift, forms)
        charts = [graph.encode(graph.local_transport(i, z.vertex, z.beta)) for z in transfers]
        choices = [[None] if q == p else stable_lines(cm[f"p{q}"], q, m)
                   for q, m in zip(flags.levels, flags.powers)]
        for orientation in product(*choices):
            coeff = [0]*p
            label_counts = Counter()
            for z, mats, offset in zip(transfers, charts, offsets):
                lines = tuple(None if q == p else label(act(adj(mats[f"p{q}"]), column(s,q,m)),q,m)
                              for s,q,m in zip(orientation, flags.levels, flags.powers))
                for k, ray in enumerate(rays):
                    target_ray = act(adj(mats[f"p{p}"]), column(ray, p, p*p))
                    value = ray_value(flags, p, z.vertex, lines, target_ray, values)
                    exponent = (offset + k*step) % p
                    label_counts[exponent] += 1
                    coeff[exponent] += case["vdelta"]*pow(case["ap"], -2, p)*value
            if set(label_counts.values()) != {len(forms)*(p+1)} or len(label_counts) != p:
                raise ArithmeticError("unequal degree-p Galois fibres")
            coeff = [int(x % p) for x in coeff]
            if sum(coeff) % p:
                raise ArithmeticError("nonzero constant term")
            moment = sum(j*a for j, a in enumerate(coeff)) % p
            variants.append(dict(index=i, omega=str(omega), tame_flags=list(orientation),
                                 generator_shift=shift, local_step=step, offsets=offsets,
                                 forms=forms, first_moment=moment, coefficients=coeff))
    if not variants:
        raise ArithmeticError("empty CM set")
    # Freeze an explicit ordering independent of Sage's norm-shell iteration.
    variants.sort(key=lambda r:(r["omega"],r["index"],r["tame_flags"]))
    return dict(first_moment=variants[0]["first_moment"], coefficients=variants[0]["coefficients"],
                checks=dict(variants=variants, selected_variant=0))
