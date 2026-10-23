"""Check the connected seven-dimensional construction of Árnadóttir and Godsil.

The connection set is their construction for odd dimension, specialized to
dimension seven. Both the character criterion and exact spectral projections
are computed; the latter does not use the character criterion.
"""

from spectral import K_char, sc_class_direct


def connection_set():
    d = 7
    e = lambda i: 1 << (i - 1)
    return sorted(
        {e(i) for i in range(1, d + 1)}
        | {e(1) ^ e(2), e(1) ^ e(3), e(2) ^ e(3)}
        | {e(i) ^ e(j) for i in range(4, d + 1) for j in range(i + 1, d + 1)}
        | {e(1) ^ e(2) ^ e(3) ^ e(i) for i in range(4, d + 1)}
    )


def check():
    S = connection_set()
    basis = []
    for s in S:
        for b in basis:
            s = min(s, s ^ b)
        if s:
            basis.append(s)
    assert len(S) == 20 and 0 not in S
    assert len(basis) == 7, "connection set does not span the vertex group"
    expected = {0, 7, 120, 127}
    character_class = K_char(7, S)
    direct_class, spectrum = sc_class_direct(7, S)
    assert character_class == direct_class == expected
    # Both omissions and spurious vertices in a claimed class are detected.
    assert direct_class != {0, 7, 120}
    assert direct_class != {0, 1, 7, 120, 127}
    print("Connected attaining graph: degree 20, rank 7, class", sorted(direct_class))
    print("Exact adjacency-matrix spectrum (eigenvalue, multiplicity):", sorted(spectrum.items()))
    print("PASS: attainment and two corrupted class claims")


if __name__ == "__main__":
    check()
