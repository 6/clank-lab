"""Depth-two CM orbits on maximal-order Brandt classes (SageMath 10.8).

The graph callback is local_matrix(source, target, left_map, prime, depth).
It returns the matrix of left_map between bases of the two localized ideal
column lattices, modulo prime**depth, as four row-major entries or a 2x2
matrix. The same callback with source == target represents a left-order
element, which may be singular modulo a tame prime.
A tame flag is the slope of (1, s), with prime denoting (0, 1). A ray is a
primitive column modulo p**2, up to a scalar unit.

The multiplication convention is [c] : I -> c(omega) I. When c**h = (alpha),
the local identification after h steps is alpha**-1. Thus the coset offset
is the discrete logarithm of alpha**-1 divided by h modulo p. A local
generator a+omega acts on columns by left multiplication, so its ideal
representative for this same convention is (a+omega)**-1.
"""

from dataclasses import dataclass
from math import prod
from typing import NamedTuple

from sage.all import BinaryQF, QuadraticField, ZZ, Zmod, crt, kronecker, matrix, pari


class OrbitPoint(NamedTuple):
    vertex: int
    tame_flags: tuple
    ray: tuple
    exponent: int


@dataclass(frozen=True)
class Coset:
    representative: object
    principal_generator: object
    vertex: int
    beta: object
    omega: object
    tame_flags: tuple
    ray_map: tuple
    offset: int


def _projective(x, y, p, depth):
    modulus = p**depth
    x, y = int(x) % modulus, int(y) % modulus
    if x % p:
        return 1, y * pow(x, -1, modulus) % modulus
    if not y % p:
        raise ValueError(f"column is not primitive at {p}")
    return x * pow(y, -1, modulus) % modulus, 1


def _image(entries, ray, p, depth):
    a, b, c, d = entries
    x, y = ray
    return _projective(a*x + b*y, c*x + d*y, p, depth)


def _entries(m):
    return tuple(int(x) for x in m.list())


def _chart(local_matrix, source, target, left_map, q, depth):
    entries = local_matrix(source, target, left_map, q, depth)
    if hasattr(entries, "list"):
        entries = entries.list()
    elif len(entries) == 2:
        entries = [x for row in entries for x in row]
    return matrix(Zmod(q**depth), 2, 2, [int(entry) for entry in entries])


def _scalar(m):
    return m[0, 1] == m[1, 0] == 0 and m[0, 0] == m[1, 1]


def _field_coordinates(value, trace):
    """Coordinates in 1, (trace + sqrt(D))/2."""
    a, b = value.list()
    return a - trace*b, 2*b


def _embed(value, omega, trace):
    a, b = _field_coordinates(value, trace)
    return a + b*omega


def _primitive_ideal(ideal):
    content = ZZ(0)
    for value in ideal.integral_basis():
        for coordinate in _field_coordinates(value, ideal.number_field().discriminant() % 2):
            content = content.gcd(ZZ(coordinate))
    return ideal if content == 1 else ideal/content


def _coprime_representative(ideal, primes):
    """Rescale in its ideal class using a vector of unit norm at each prime."""
    if ideal.is_integral() and all(ideal.norm() % q for q in primes):
        return _primitive_ideal(ideal)

    u, v = (ideal**-1).integral_basis()
    norm = ideal.norm()
    # An inverse-ideal basis identifies the ideal norm with a primitive
    # integral binary quadratic form, including at primes above 2.
    a = ZZ(norm*u.norm())
    c = ZZ(norm*v.norm())
    b = ZZ(norm*(u*v.conjugate()).trace())

    def value(x, y):
        return a*x*x + b*x*y + c*y*y

    pairs = [(x, y) for x in range(-8, 9) for y in range(9)
             if y or x > 0]
    pairs.sort(key=lambda xy: value(*xy))
    for x, y in pairs:
        if all(value(x, y) % q for q in primes):
            break
    else:
        local = [next((x, y) for x, y in ((1, 0), (0, 1), (1, 1))
                      if value(x, y) % q) for q in primes]
        x = crt([xy[0] for xy in local], list(primes))
        y = crt([xy[1] for xy in local], list(primes))
        modulus = prod(primes)
        x = (x + modulus//2) % modulus - modulus//2
        y = (y + modulus//2) % modulus - modulus//2

    result = (x*u + y*v)*ideal
    if not result.is_integral() or any(result.norm() % q == 0 for q in primes):
        raise ArithmeticError("failed to make an integral coprime class representative")
    return _primitive_ideal(result)


def representative_form(ideal, D):
    """Return [A,B,C] with ideal (A, (-B+sqrt(D))/2) and A = norm(ideal)."""
    trace = D % 2
    u, v = ideal.integral_basis()
    _, b = map(ZZ, _field_coordinates(u, trace))
    _, d = map(ZZ, _field_coordinates(v, trace))
    g, s, t = b.xgcd(d)
    if g != 1:
        raise ValueError("form representative requires a primitive integral ideal")
    x, _ = _field_coordinates(s*u + t*v, trace)
    A, B = ZZ(ideal.norm()), ZZ(-2*x - trace)
    field = ideal.number_field()
    if field.ideal(A, (-B + field.gen())/2) != ideal:
        raise ArithmeticError("form does not represent the specified ideal")
    return tuple(map(int, (A, B, ZZ((B**2-D)/(4*A)))))


class ClassTransfer(NamedTuple):
    representative: object
    vertex: int
    beta: object
    omega: object


def _brandt_locator(ideals):
    """Index the same theta-series buckets as the maximal Brandt graph."""
    buckets = {}
    for index, ideal in enumerate(ideals):
        key = tuple(ideal.theta_series_vector(16))
        buckets.setdefault(key, []).append(index)

    def locate(ideal):
        key = tuple(ideal.theta_series_vector(16))
        for index in buckets.get(key, ()):
            equivalent, beta = ideal.is_right_equivalent(
                ideals[index], 0, certificate=True
            )
            if equivalent:
                return index, beta
        raise ArithmeticError("right ideal is missing from the Brandt classes")

    return locate


def _class_transfers(ideals, classes, base_vertex, omega, avoid_primes, locate):
    ideal = ideals[base_vertex]
    trace = int(omega.reduced_trace())
    transfers = []
    for cl in classes:
        representative = _coprime_representative(cl.ideal(), avoid_primes)
        generators = [_embed(value, omega, trace) for value in representative.integral_basis()]
        J = ideal.right_order().right_ideal([x*y for x in generators for y in ideal.basis()])
        if representative.norm() == 1:
            vertex, beta = base_vertex, omega.parent()(1)
        else:
            if locate is None:
                locate = _brandt_locator(ideals)
            vertex, beta = locate(J)
        if not 0 <= vertex < len(ideals):
            raise ArithmeticError("right-ideal lookup returned an invalid Brandt index")
        target = ideals[vertex]
        if (J.norm() != representative.norm()*ideal.norm()
                or beta.reduced_norm()*target.norm() != J.norm()
                or beta*target != J):
            raise ArithmeticError("Brandt equivalence failed the norm or lattice check")
        transported_omega = (~beta)*omega*beta
        if transported_omega not in target.left_order():
            raise ArithmeticError("transported embedding is not integral")
        transfers.append(ClassTransfer(representative, vertex, beta, transported_omega))
    if len(transfers) != classes.order():
        raise ArithmeticError("wrong number of maximal-order class representatives")
    return tuple(transfers)


def class_transfers(ideals, D, base_vertex, omega, avoid_primes, *, locate=None):
    """Return (c, j, beta, beta^-1*omega*beta) for every maximal-order class.

    The caller supplies all primes where c must be locally trivial. This
    operation also applies when p divides the class number.
    """
    ideals = tuple(ideals)
    if D >= -4 or not ZZ(D).is_fundamental_discriminant():
        raise ValueError("D must be a fundamental imaginary discriminant below -4")
    if not 0 <= base_vertex < len(ideals):
        raise ValueError("invalid base Brandt class")
    if (omega.reduced_trace() != D % 2 or omega.reduced_norm() != (D % 2 - D)//4
            or omega not in ideals[base_vertex].left_order()):
        raise ValueError("omega does not give the required optimal embedding")
    primes = tuple(dict.fromkeys(map(int, avoid_primes)))
    if any(not ZZ(q).is_prime() for q in primes):
        raise ValueError("avoid_primes must contain only primes")
    classes = QuadraticField(D, "s").class_group(proof=True)
    return _class_transfers(ideals, classes, base_vertex, omega, primes, locate)


def _local_cycle(omega_matrix, p, generator_shift):
    """List all rays and logarithms, allowing any prescribed wild generator."""
    order = p*(p + 1)
    identity = omega_matrix.parent().one()
    tame_factors = ZZ(p + 1).prime_divisors()
    for a in range(p**2):
        step = a*identity + omega_matrix
        if (not _scalar(step**(p + 1))
                and all(not _scalar(step**(order // q)) for q in tame_factors)):
            break
    else:
        raise ArithmeticError("no full-order generator a + omega at conductor p^2")

    base = (1, 0)
    entries = _entries(step)
    rays, logs = [], {}
    ray = base
    for k in range(order):
        if ray in logs:
            raise ArithmeticError("projective orbit closed before p(p+1) steps")
        rays.append(ray)
        logs[ray] = k
        ray = _image(entries, ray, p, 2)
    if ray != base:
        raise ArithmeticError("projective orbit failed to close at p(p+1) steps")

    if generator_shift is None:
        generator_shift = a
    requested = _entries(generator_shift*identity + omega_matrix)
    wild_log = logs[_image(requested, base, p, 2)] % p
    if not wild_log:
        raise ValueError("a + omega has trivial wild coordinate at conductor p^2")
    return a, generator_shift, tuple(rays), logs, pow(wild_log, -1, p)


@dataclass(frozen=True)
class ClassOrbit:
    D: int
    p: int
    class_number: int
    generator_shift: int
    base_ray: tuple
    cosets: tuple
    _full_shift: int
    _rays: tuple
    _logs: dict
    _scale: int

    def __iter__(self):
        return self.points()

    def __len__(self):
        return len(self.cosets)*len(self._rays)

    def points(self, base_ray=None):
        """Iterate the orbit, optionally based at another ray in the same chart.

        Re-basing subtracts its local logarithm from every exponent. The
        geometric points and the transported tame flags are independent of
        the choice of the base ray.
        """
        p = self.p
        ray = self.base_ray if base_ray is None else _projective(*base_ray, p, 2)
        origin = self._logs[ray]
        for coset in self.cosets:
            for k, source_ray in enumerate(self._rays):
                yield OrbitPoint(
                    coset.vertex,
                    coset.tame_flags,
                    _image(coset.ray_map, source_ray, p, 2),
                    (coset.offset + (k - origin)*self._scale) % p,
                )

    def verify_ring_class_forms(self):
        """Verify every exponent and the orbit size using PARI binary forms.

        For c coprime to f=p**2, contract c to Z+f*O_K and take the
        norm form on a positively oriented basis. Raising a form to
        h_K*(p+1) kills its prime-to-p part. The normalizing form comes
        from the principal ideal inverse to the local generator, with a
        rational factor cleared using its conjugate.
        """
        p, h, f = self.p, self.class_number, self.p**2
        field = self.cosets[0].representative.number_field()
        trace = self.D % 2
        w = (trace + field.gen())/2
        generator = _ring_form(field.ideal((self.generator_shift + w).conjugate()),
                               f, trace)
        local_step = _ring_form(field.ideal((self._full_shift + w).conjugate()),
                                f, trace)
        prime_to_p = h*(p + 1)
        projected = generator.qfbpow(prime_to_p)
        expected = [projected.qfbpow(i) for i in range(p)]
        if len({tuple(form.Vec()) for form in expected}) != p:
            raise ArithmeticError("ring-class generator has insufficient p-order")
        expected_count = int(pari(self.D*f**2).qfbclassno())
        origin = self._logs[self.base_ray]
        rebase = local_step.qfbpow(-origin)
        points = iter(self)
        seen = set()
        for coset in self.cosets:
            form = (_ring_form(coset.representative, f, trace) * rebase).qfbred()
            for _ in self._rays:
                key = tuple(form.Vec())
                exponent = next(points).exponent
                if key in seen or form.qfbpow(prime_to_p) != expected[exponent]:
                    raise ArithmeticError(f"ring-class form or exponent mismatch at {key}")
                seen.add(key)
                form = (form * local_step).qfbred()
        if len(seen) != expected_count or expected_count != h*p*(p + 1):
            raise ArithmeticError("ring-class form count disagrees with the CM orbit")
        return expected_count


def _ring_form(ideal, conductor, trace):
    u, v = ideal.integral_basis()
    a, b = map(ZZ, _field_coordinates(u, trace))
    c, d = map(ZZ, _field_coordinates(v, trace))
    g, s, t = b.xgcd(d)
    if g.gcd(conductor) != 1:
        raise ArithmeticError("ring-class contraction requires a coprime ideal")
    # The y-coordinates in the basis below are respectively f*g and 0.
    first = conductor*(s*u + t*v)
    second = (-d*u + b*v)/g
    if a*d - b*c < 0:
        second = -second
    n = ideal.norm()
    coefficients = [ZZ(first.norm()/n),
                    ZZ((first*second.conjugate()).trace()/n),
                    ZZ(second.norm()/n)]
    return pari(BinaryQF(coefficients)).qfbred()


def class_orbit(ideals, local_matrix, D, p, tame_primes, base_vertex, omega,
                tame_flags, *, base_ray=(1, 0), generator_shift=None, locate=None):
    """Return the depth-two orbit for fixed optimal omega and tame flags.

    Supply one maximal right ideal per Brandt class and the graph chart
    callback described above. The optional locate(J) returns (j, beta) with
    J = beta*ideals[j]. Both that equality and the expected norms are
    checked even when the graph supplies the lookup.

    The supported domain is fundamental D < -4, inert p >= 5 coprime to
    h_K, one inert finite quaternion discriminant prime ell (N^- = 1),
    and distinct split tame primes. The output retains all points of the
    ring class orbit, including any multiplicities after forgetting CM.
    There is no averaging or automorphic normalization here.
    """
    D, p = int(D), int(p)
    tame_primes = tuple(map(int, tame_primes))
    tame_flags = tuple(map(int, tame_flags))
    ideals = tuple(ideals)
    if not ideals or not 0 <= base_vertex < len(ideals):
        raise ValueError("invalid base Brandt class")
    if D >= -4 or not ZZ(D).is_fundamental_discriminant():
        raise ValueError("D must be a fundamental imaginary discriminant below -4")
    if p < 5 or not ZZ(p).is_prime() or kronecker(D, p) != -1:
        raise ValueError("p must be an inert prime at least 5")
    field = QuadraticField(D, "s")
    classes = field.class_group(proof=True)
    h = int(classes.order())
    if h % p == 0:
        raise NotImplementedError("p divides h_K; depth-two projection is unsupported")

    ideal = ideals[base_vertex]
    ell = int(ideal.quaternion_algebra().discriminant())
    if not ZZ(ell).is_prime() or ell == p or kronecker(D, ell) != -1:
        raise ValueError("expected a single inert auxiliary discriminant prime")
    if (len(tame_primes) != len(tame_flags)
            or len(set(tame_primes)) != len(tame_primes)
            or any(q in (p, ell) or not ZZ(q).is_prime() or kronecker(D, q) != 1
                   for q in tame_primes)):
        raise ValueError("tame flags must have distinct split prime levels away from p and ell")

    trace = D % 2
    if (omega.reduced_trace() != trace or omega.reduced_norm() != (trace - D)//4
            or omega not in ideal.left_order()):
        raise ValueError("omega does not give the required optimal embedding")
    tame_data = []
    for q, slope in zip(tame_primes, tame_flags):
        if not 0 <= slope <= q:
            raise ValueError(f"invalid tame flag at {q}")
        ray = (0, 1) if slope == q else (1, slope)
        source_omega = _chart(local_matrix, base_vertex, base_vertex, omega, q, 1)
        x, y = ray
        a, b, c, d = _entries(source_omega)
        if (x*(c*x + d*y) - y*(a*x + b*y)) % q:
            raise ValueError(f"tame flag at {q} is not stable under omega")
        tame_data.append((q, ray, source_omega))

    omega_p = _chart(local_matrix, base_vertex, base_vertex, omega, p, 2)
    full_shift, generator_shift, rays, logs, scale = _local_cycle(
        omega_p, p, generator_shift
    )
    base_ray = _projective(*base_ray, p, 2)
    identity = omega_p.parent().one()
    inverse_h = pow(h, -1, p)
    coprime_to = (p, ell) + tame_primes
    cosets = []
    for representative, vertex, beta, transported_omega in _class_transfers(
            ideals, classes, base_vertex, omega, coprime_to, locate):
        power = representative**h
        alpha, = power.gens_reduced(proof=True)
        if field.ideal(alpha) != power:
            raise ArithmeticError("class representative power is not (alpha)")
        a, b = map(ZZ, _field_coordinates(alpha, trace))
        alpha_p = a*identity + b*omega_p
        alpha_ray = _image(_entries(~alpha_p), (1, 0), p, 2)
        offset = logs[alpha_ray]*scale*inverse_h % p

        inverse = ~beta

        def transport(q, depth, source_omega):
            change = _chart(local_matrix, base_vertex, vertex, inverse, q, depth)
            if not change.det().is_unit():
                raise ArithmeticError(f"local transport is singular at {q}")
            target_omega = _chart(local_matrix, vertex, vertex, transported_omega, q, depth)
            if change*source_omega != target_omega*change:
                raise ArithmeticError(f"local transport fails to intertwine omega at {q}")
            return _entries(change)

        flags = []
        for q, ray, source_omega in tame_data:
            x, y = _image(transport(q, 1, source_omega), ray, q, 1)
            flags.append(y if x == 1 else q)
        ray_map = transport(p, 2, omega_p)
        cosets.append(Coset(representative, alpha, vertex, beta, transported_omega,
                            tuple(flags), ray_map, offset))

    return ClassOrbit(D, p, h, generator_shift, base_ray, tuple(cosets),
                      full_shift, rays, logs, scale)
