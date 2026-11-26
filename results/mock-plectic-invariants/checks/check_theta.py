"""Independent theta checker. Run with CASE.json ELL DIRECTORY RESULT.json.

The checker pushes terminal columns towards the base through products of
certified transport matrices. It separately computes Galois labels in the
quadratic ring and requires both covers to be exactly the two affine charts.
Deleting a graph edge breaks the cover. Altering a claimed theta coefficient
breaks the comparison even if the claimed first moment has been adjusted.
The input graph supplies the global ideal identifications. This checker
verifies the ray cover and theta arithmetic without the evaluator.
Over a tame ring of size m = q^e, the first m flags are (1,s) and the
next m/q are (q*s,1). This is the lexicographic local index used in
eigen.json, with class first and the primes in ascending order.
"""

import argparse
import json
from collections import Counter, defaultdict
from itertools import product
from math import isqrt, prod
from pathlib import Path


IDENTITY = (1, 0, 0, 1)
PINNED_OMEGA = "1/2 + 25/64*i + 1/32*j - 3/64*k"


def insist(ok, what):
    if not ok:
        raise ValueError(what)


def load(filename):
    return json.loads(filename.read_text())


def is_prime(q):
    return type(q) is int and q > 1 and not any(q % d == 0 for d in range(2, isqrt(q)+1))


def splitting(D, q):
    if D % q == 0:
        return 0
    if q == 2:
        return 1 if D % 8 in (1, 7) else -1
    return 1 if pow(D, (q-1)//2, q) == 1 else -1


def class_number(D):
    def squarefree(n):
        return all(n % (q*q) != 0 for q in range(2, isqrt(n)+1))

    insist(-163 <= D < -4 and (D % 4 == 1 and squarefree(-D)
           or D % 4 == 0 and (D//4) % 4 in (2, 3) and squarefree(-D//4)),
           "unsupported or nonfundamental D")
    # For a reduced primitive positive form |b| <= a <= c, 3a^2 <= |D|.
    # At a boundary, use b >= 0. Fundamental D makes the forms primitive.
    count = 0
    for a in range(1, isqrt(-D//3)+1):
        for b in range(-a, a+1):
            c, remainder = divmod(b*b-D, 4*a)
            if not remainder and a <= c and (b >= 0 or (a != -b and a != c)):
                count += 1
    return count


def coordinates(point, p, modulus):
    x, y = point
    if x % p:
        return (1, (y % modulus)*pow(x, -1, modulus) % modulus)
    if y % p:
        return ((x % modulus)*pow(y, -1, modulus) % modulus, 1)
    return None


def vector(index, q, modulus=None):
    modulus = q if modulus is None else modulus
    if index < modulus:
        return 1, index
    return q*(index-modulus), 1


def index_of(point, q, modulus):
    ray = coordinates(point, q, modulus)
    insist(ray is not None, "zero flag")
    x, y = ray
    return modulus+x//q if x % q == 0 else y


def times(m, point):
    a, b, c, d = m
    x, y = point
    return a*x+b*y, c*x+d*y


def multiply(m, n, modulus):
    x, z = times(m, (n[0], n[2]))
    y, w = times(m, (n[1], n[3]))
    return x % modulus, y % modulus, z % modulus, w % modulus


def determinant(m):
    return m[0]*m[3]-m[1]*m[2]


def mod_matrix(m, modulus):
    return tuple(x % modulus for x in m)


def key_of(unit, factors):
    signature = []
    for A, (q, modulus) in zip(unit, factors):
        pivots = [x for x in A if x % q]
        insist(pivots, "zero unit matrix")
        scale = pow(pivots[0], -1, modulus)
        signature.append(tuple(x*scale % modulus for x in A))
    return tuple(signature)


def unpack(record, primes, moduli):
    result = []
    for q, base in zip(primes, moduli):
        m = record[f"p{q}"]
        insist(type(m) is list and len(m) == 4
               and all(type(x) is int and x in range(base) for x in m), f"matrix p{q}")
        result.append(tuple(m))
    return tuple(result)


def get_precision(meta, field, records, p, start):
    limit = p**start
    digit = start
    for record in records:
        for value in record[f"p{p}"]:
            while value >= limit:
                limit *= p
                digit += 1
    explicit = meta.get(field, digit)
    insist(type(explicit) is int and digit <= explicit <= 3, f"invalid {field}")
    return explicit


def field_product(z, w, trace, norm, modulus):
    a, b = z
    c, d = w
    return (a*c-norm*b*d) % modulus, (a*d+b*c+trace*b*d) % modulus


def power(z, exponent, trace, norm, modulus):
    result = (1, 0)
    while exponent > 0:
        if exponent & 1:
            result = field_product(result, z, trace, norm, modulus)
        exponent >>= 1
        z = field_product(z, z, trace, norm, modulus)
    return result


def find_generator(p, trace, norm):
    # For a tame representative (s,1), its order can be checked by ruling
    # out every proper divisor of p+1. Raising to p+1 checks the wild part.
    proper = [i for i in range(1, p+1) if (p+1) % i == 0]
    for s in range(2*p):
        g = (s, 1)
        if (all(power(g, i, trace, norm, p)[1] for i in proper)
                and power(g, p+1, trace, norm, p*p)[1]):
            return s
    raise ValueError("missing projective generator")


def labelled_rays(w, shift, p, depth, trace, norm):
    modulus = p**depth
    wild_size = p**(depth-1)
    total = (p+1)*wild_size
    g = (shift, 1)
    tame_step = power(g, wild_size, trace, norm, modulus)
    wild_step = power(g, p+1, trace, norm, modulus)
    labels = {}
    tame = (1, 0)
    for t in range(p+1):
        z = tame
        for u in range(wild_size):
            a, b = z
            # Inertness makes e_1, omega e_1 a Z/p^n basis.
            ray = coordinates((a+b*w[0], b*w[2]), p, modulus)
            insist(ray is not None and ray not in labels, "quadratic-ring ray cover")
            labels[ray] = (wild_size*t+(p+1)*u) % total
            z = field_product(z, wild_step, trace, norm, modulus)
        tame = field_product(tame, tame_step, trace, norm, modulus)
    charts = {(1, s) for s in range(modulus)}
    charts.update((s, 1) for s in range(0, modulus, p))
    insist(labels.keys() == charts and len(set(labels.values())) == total,
           "quadratic-ring chart cover")
    return labels


def preimage(m, s, q, modulus):
    a, b, c, d = m
    x, y = vector(s, q, modulus)
    u, v = x*c-y*a, x*d-y*b
    answer = index_of((v, -u), q, modulus)
    insist(index_of(times(m, vector(answer, q, modulus)), q, modulus) == s,
           "tame transport preimage")
    return answer


def fixed_flags(m, q, modulus, trace, norm):
    # Each simple root mod q has one Hensel lift. Every invariant primitive
    # column has an eigenvalue (read it in a unit coordinate), so these
    # two kernels exhaust the possibilities. A kernel can have eigenvalue 0.
    a, b, c, d = m
    flags = set()
    for r in range(q):
        if (r*r-trace*r+norm) % q == 0:
            inverse = pow(2*r-trace, -1, q)
            precision = q
            while precision < modulus:
                error = (r*r-trace*r+norm)//precision
                r += precision*((-error*inverse) % q)
                precision *= q
            u, v = (a-r, b) if (a-r) % q or b % q else (c, d-r)
            s = index_of((v, -u), q, modulus)
            x, y = vector(s, q, modulus)
            X, Y = times(m, (x, y))
            insist((X-r*x) % modulus == (Y-r*y) % modulus == 0, "unstable tame eigenline")
            flags.add(s)
    insist(len(flags) == 2, "stable split tame flags")
    return sorted(flags)


def pushed_cover(rows, root, p, depth, factors, p_index):
    """Map source rays to terminal flags and tame products.

    A path product has primitive rank one reduction exactly while it
    continues away from the root. A kernel flag at the last vertex is
    the returning edge. The two-chart equality checks exhaustiveness
    independently of these tree descriptions. A lift of the final flag
    does not affect its image ray modulo p^depth. Changing a primitive
    representative by p times another column changes the wedge of the
    two images by a multiple of p det(path), which is divisible by p^depth.
    """
    moduli = [p**depth if q == p else m for q, m in factors]
    paths = [(root, (IDENTITY,)*len(factors))]
    for _ in range(depth-1):
        new_paths = []
        for index, path in paths:
            for target, matrices in rows[index]:
                result = tuple(multiply(a, b, m) for a, b, m in zip(path, matrices, moduli))
                if any(x % p for x in result[p_index]):
                    new_paths.append((target, result))
        paths = new_paths
    cover = {}
    for target, path in paths:
        for s in range(p+1):
            ray = coordinates(times(path[p_index], vector(s, p)), p, p**depth)
            if ray is not None:
                insist(ray not in cover, "p-graph cover: repeated forward ray")
                cover[ray] = (target, s, path[:p_index]+path[p_index+1:])
    return cover


def independently_evaluate(case, ell, directory):
    directory = Path(directory)
    p, D = case["p"], case["D"]
    levels = tuple(case["levels"])
    ap, vdelta = case["ap"], case["vdelta"]
    insist(class_number(D) == 1, "requires class number one")
    insist(is_prime(p) and p >= 5 and is_prime(ell), "invalid p or ell")
    insist(p in levels and ell not in levels and levels == tuple(sorted(set(levels)))
           and all(is_prime(q) for q in levels), "invalid level primes")
    N = case["N"]
    insist(type(N) is int and N > 0 and N % (p*p) != 0, "invalid level")
    factors = []
    for q in levels:
        modulus = q
        while N % (modulus*q) == 0:
            modulus *= q
        factors.append((q, modulus))
    insist(prod(m for _, m in factors) == N, "level primes do not exhaust N")
    flag_sizes = [m+m//q for q, m in factors]
    p_index = levels.index(p)
    tame = levels[:p_index]+levels[p_index+1:]
    tame_factors = factors[:p_index]+factors[p_index+1:]
    insist(splitting(D, p) == splitting(D, ell) == -1
           and all(splitting(D, q) == 1 for q in tame), "local splitting conditions")
    insist(type(ap) is int and abs(ap) == 1 and type(vdelta) is int and vdelta >= 1,
           "bad normalization factor")
    data = load(directory/"classes.json")
    cm, raw_units = data["cm"], data["units"]
    rows = load(directory/f"q{p}.json")
    nclasses = len(raw_units)
    insist(data["ell"] == ell and cm and nclasses and nclasses == len(rows) and all(raw_units),
           "missing classes, units or CM data")
    insist(all(len(row) == p+1 for row in rows), "p-graph cover: missing or extra first edge")
    depth = get_precision(data, "p_depth", [e for row in rows for e in row], p, 2)
    cm_depth = get_precision(data, "cm_p_depth", cm, p, 2)
    unit_depth = get_precision(data, "unit_p_depth", sum(raw_units, []), p, 1)
    graph_moduli = [p**depth if q == p else m for q, m in factors]
    cm_moduli = [p**cm_depth if q == p else m for q, m in factors]
    unit_moduli = [p**unit_depth if q == p else m for q, m in factors]

    for i, row in enumerate(rows):
        edges = []
        first = set()
        for entry in row:
            j = entry["index"]
            insist(type(j) is int and 0 <= j < nclasses, "invalid edge target")
            matrices = unpack(entry, levels, graph_moduli)
            m = matrices[p_index]
            d = determinant(m)
            insist(d % p == 0 and d % (p*p) != 0, "graph determinant at p")
            insist(all(determinant(A) % q for k, (A, q) in enumerate(zip(matrices, levels))
                       if k != p_index), "singular tame transport")
            nonzero_images = {coordinates(times(m, vector(s, p)), p, p) for s in range(p+1)}
            nonzero_images.discard(None)
            insist(len(nonzero_images) == 1, "p-graph edge rank")
            first.update(nonzero_images)
            edges.append((j, matrices))
        insist(len(first) == p+1, "p-graph cover: repeated first edge")
        rows[i] = edges

    units = []
    for entries in raw_units:
        listed = [unpack(u, levels, unit_moduli) for u in entries]
        insist(len(set(listed)) == len(listed), "duplicate unit record")
        group = {min(u, tuple(mod_matrix((-x for x in A), m)
                              for A, m in zip(u, unit_moduli))) for u in listed}
        insist(all((determinant(A)-1) % m == 0
                   for u in group for A, m in zip(u, unit_moduli)), "unit norm")
        signatures = {key_of(u, factors) for u in group}
        insist(len({s[p_index] for s in signatures}) == len(group)
               and (IDENTITY,)*len(levels) in signatures, "invalid projective units")
        for u in group:
            generated = {key_of(tuple(multiply(a, b, m)
                                     for a, b, (_, m) in zip(u, v, factors)), factors)
                         for v in group}
            insist(generated == signatures, "unit multiplication")
        units.append(group)

    eigen = load(directory/"eigen.json")
    insist(type(eigen) is list and len(eigen) == nclasses*prod(flag_sizes)
           and all(type(x) is int and x in range(p) for x in eigen), "bad eigen shape")
    insist(next((x for x in eigen if x), 0) == 1, "bad eigen normalization")
    weights = [prod(flag_sizes[j:]) for j in range(len(levels)+1)]
    samples = {}

    def sample(i, flags):
        key = i, flags
        if key not in samples:
            def lookup(f):
                return eigen[i*weights[0] + sum(s*w for s, w in zip(f, weights[1:]))]
            visited = Counter(tuple(index_of(times(A, vector(s, q, m)), q, m)
                                    for A, s, (q, m) in zip(u, flags, factors))
                              for u in units[i])
            stabilizer = visited[flags]
            insist(stabilizer > 0 and all(a == stabilizer for a in visited.values()),
                   "terminal orbit-stabilizer")
            value = lookup(flags)
            insist(all(lookup(f) == value for f in visited), "eigen units")
            samples[key] = value, str(stabilizer)
        return samples[key]

    trace = data.get("omega_trace", D % 2)
    insist(type(trace) is int and (trace*trace-D) % 4 == 0, "invalid omega trace")
    norm = (trace*trace-D)//4
    roots = {rec["index"] for rec in cm}
    insist(len(roots) == 1, "embedding root cover")
    root = next(iter(roots))
    insist(type(root) is int and root in range(nclasses)
           and len(cm) == 2*len(units[root]), "embedding mass")
    embeddings = {}
    conjugation = {}
    residues = defaultdict(set)
    unit_comparison = [min(m, n) for m, n in zip(cm_moduli, unit_moduli)]
    for rec in cm:
        name = rec["omega"]
        matrices = unpack(rec, levels, cm_moduli)
        insist(type(name) is str and name and name not in embeddings
               and matrices not in conjugation, "duplicate embedding")
        for A, m in zip(matrices, cm_moduli):
            square = multiply(A, A, m)
            poly = (trace*A[0]-norm, trace*A[1], trace*A[2], trace*A[3]-norm)
            insist(square == mod_matrix(poly, m) and (A[0]+A[3]-trace) % m == 0
                   and (determinant(A)-norm) % m == 0, "bad quadratic embedding")
        embeddings[name] = matrices
        conjugation[matrices] = name
        residues[tuple(mod_matrix(A, m) for A, m in zip(matrices, unit_comparison))].add(name)

    orbits = set()
    definite = True
    for matrices in embeddings.values():
        orbit = set()
        for u in units[root]:
            conjugated = []
            for A, U, m in zip(matrices, u, unit_comparison):
                # Solve B U = U A in the four-dimensional matrix ring.
                a, b, c, d = U
                V = tuple(pow(determinant(U), -1, m)*x % m for x in (d, -b, -c, a))
                conjugated.append(multiply(multiply(U, A, m), V, m))
            selected = residues[tuple(conjugated)]
            insist(selected, "embedding unit closure")
            orbit.update(selected)
        insist(len(orbit) in (len(units[root]), len(cm)), "embedding unit orbit")
        if len(orbit) == len(cm):
            definite = False
        else:
            orbits.add(tuple(sorted(orbit)))

    covers = [pushed_cover(rows, root, p, n, factors, p_index)
              for n in range(1, depth+1)]
    sizes = [len(cover) for cover in covers]
    shift = find_generator(p, trace, norm)
    variants = []
    for name, matrices in sorted(embeddings.items()):
        conjugate_matrices = tuple(mod_matrix((trace-a, -b, -c, trace-d), m)
                                   for (a, b, c, d), m in zip(matrices, cm_moduli))
        conj = conjugation.get(conjugate_matrices)
        insist(conj is not None and conj != name, "missing conjugate embedding")
        logs = [labelled_rays(matrices[p_index], shift, p, n, trace, norm)
                for n in range(1, depth+1)]
        for chart, labels in zip(covers, logs):
            insist(chart.keys() == labels.keys(), "p-graph and quadratic-ring cover differ")
        tame_m = matrices[:p_index]+matrices[p_index+1:]
        options = [fixed_flags(A, q, m, trace, norm)
                   for A, (q, m) in zip(tame_m, tame_factors)]
        for flag in product(*options):
            stabilizers = []
            previous = None
            for n, (cover, labels) in enumerate(zip(covers, logs), 1):
                current = {}
                hist = Counter()
                projected = [0]*p
                lower_sums = Counter()
                lower_counts = Counter()
                for ray, (i, s, transport) in cover.items():
                    f = tuple(preimage(A, x, q, m)
                              for A, x, (q, m) in zip(transport, flag, tame_factors))
                    a, stabilizer = sample(i, f[:p_index]+(s,)+f[p_index:])
                    current[ray] = a
                    hist[stabilizer] += 1
                    if n > 1:
                        reduction = coordinates(ray, p, p**(n-1))
                        insist(labels[ray] % sizes[n-2] == logs[n-2][reduction],
                               "incompatible geometric Galois labels")
                        lower_sums[reduction] += a
                        lower_counts[reduction] += 1
                        # a_p is a sign, so a_p^n equals a_p^(-n).
                        projected[labels[ray] % p] += vdelta*(ap**n)*a
                stabilizers.append(dict(hist))
                if previous is None:
                    insist(sum(current.values()) % p == 0, "depth-one augmentation")
                else:
                    insist(lower_counts.keys() == previous.keys()
                           and all(lower_counts[r] == p and (lower_sums[r]-ap*a) % p == 0
                                   for r, a in previous.items()), f"depth-{n} norm compatibility")
                    projected = [x % p for x in projected]
                if n == 2:
                    coefficients = projected
                if n == 3:
                    insist(projected == coefficients, "depth-three projected coefficients")
                previous = current
            moment = sum(j*a for j, a in enumerate(coefficients)) % p
            insist(sum(coefficients) % p == 0, "theta augmentation")
            # Every ray occurs as an origin with a discrete log from the
            # chart cover. The C_p action gives precisely these p shifts.
            insist(all(sum(j*coefficients[(j+r) % p] for j in range(p)) % p == moment
                       for r in range(p)), "base ray moment")
            variants.append(dict(index=root, omega=name, conjugate_omega=conj,
                                 tame_flags=list(flag), generator_shift=shift,
                                 coefficients=coefficients, first_moment=moment,
                                 terminal_stabilizers=stabilizers))
    paired = {(v["omega"], tuple(v["tame_flags"])): v for v in variants}
    for variant in variants:
        other = paired[variant["conjugate_omega"], tuple(variant["tame_flags"])]
        coeffs = variant["coefficients"]
        insist(all(coeffs[j] == other["coefficients"][(p-j) % p] for j in range(p)),
               "conjugation changes more than Galois inversion")

    pinned = (p, D, case["N"], ell, tuple(case["ainvs"])) == (19, -7, 817, 269, (0, 1, 1, 1, 6))
    selected = 0
    if pinned:
        matches = [i for i, v in enumerate(variants)
                   if root == 19 and v["omega"] == PINNED_OMEGA
                   and v["tame_flags"] == [22] and shift == 0]
        insist(len(matches) == 1, "missing pinned 817 CM coordinates")
        selected = matches[0]
    choice = variants[selected]
    return dict(first_moment=choice["first_moment"], coefficients=choice["coefficients"],
                checks=dict(class_number=1, embedding_orbit_count=2, embedding_records=len(cm),
                            unit_orbits=[list(orbit) for orbit in sorted(orbits)] if definite else None,
                            ray_counts=sizes, base_ray=[1, 0], tame_primes=list(tame),
                            conjugation_inverts=True, base_ray_moments_invariant=True,
                            norm_compatible=True,
                            augmentation=0, pinned_817=pinned, selected_variant=selected, variants=variants))


def check(case, ell, directory, result):
    calculated = independently_evaluate(case, ell, directory)
    insist(json.dumps(result.get("coefficients")) == json.dumps(calculated["coefficients"]),
           "theta coefficients")
    insist(type(result.get("first_moment")) is int
           and result["first_moment"] == calculated["first_moment"], "first moment")
    insist(json.dumps(result, sort_keys=True) == json.dumps(calculated, sort_keys=True),
           "theta check data")
    return calculated


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("case", type=Path)
    parser.add_argument("ell", type=int)
    parser.add_argument("directory", type=Path)
    parser.add_argument("result", type=Path)
    args = parser.parse_args()
    outcome = check(load(args.case), args.ell, args.directory, load(args.result))
    print(json.dumps({k: outcome[k] for k in ("first_moment", "coefficients")}))
