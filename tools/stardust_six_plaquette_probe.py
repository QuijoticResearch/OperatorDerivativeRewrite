"""Exact rational research probe, NOT a Lean certificate or a mass-gap result.

Run with Python3; standard library only. Enumerates the complete4D box with
vertices[-1,2]^4. Integrates the32 links inside{0,1}^4 at quadratic/cubic jet
level; all other links are fixed except three specified boundary sources.
No repository files, manuscript bytes, network or Git state are read or changed.
"""
from fractions import Fraction as Q
from itertools import combinations, product
import json


def shift(v, a):
    return v[:a] + (v[a] + 1,) + v[a + 1:]


def solve(matrix, rhs):
    n = len(matrix)
    rows = [list(a) + list(b) for a, b in zip(matrix, rhs)]
    for col in range(n):
        pivot = next(i for i in range(col, n) if rows[i][col])
        rows[col], rows[pivot] = rows[pivot], rows[col]
        q = rows[col][col]
        rows[col] = [v / q for v in rows[col]]
        for i in range(n):
            if i != col:
                q = rows[i][col]
                rows[i] = [a - q * b for a, b in zip(rows[i], rows[col])]
    assert all(rows[i][j] == int(i == j) for i in range(n) for j in range(n))
    return [row[n:] for row in rows]


def det(a, b, c):
    return (a[0] * (b[1] * c[2] - b[2] * c[1])
            - a[1] * (b[0] * c[2] - b[2] * c[0])
            + a[2] * (b[0] * c[1] - b[1] * c[0]))


def diagnostic():
    vertices = list(product(range(-1, 3), repeat=4))
    edges = [(v, a) for v in vertices for a in range(4) if v[a] < 2]
    interior = [(v, a) for v in product(range(2), repeat=4)
                for a in range(4) if v[a] == 0]
    index = {e: i for i, e in enumerate(interior)}
    faces = [[(v, a), (shift(v, a), b), (shift(v, b), a), (v, b)]
             for v in vertices for a, b in combinations(range(4), 2)
             if v[a] < 2 and v[b] < 2]
    source = {((1, 0, 1, 1), 2): (Q(1), Q(0), Q(0)),
              ((0, 0, 2, 1), 0): (Q(0), Q(-1), Q(0)),
              ((0, 0, 1, 1), 2): (Q(0), Q(0), Q(-1))}
    n = len(interior)
    signs = [1, 1, -1, -1]
    gram = [[Q(0)] * n for _ in range(n)]
    rhs = [[Q(0)] * 3 for _ in range(n)]
    incidence = []
    for face in faces:
        row, boundary = {}, [Q(0)] * 3
        for sign, edge in zip(signs, face):
            if edge in index:
                i = index[edge]
                row[i] = row.get(i, Q(0)) + sign
            else:
                for j, q in enumerate(source.get(edge, (0, 0, 0))):
                    boundary[j] += sign * q
        incidence.append(row)
        for i, di in row.items():
            for k, dk in row.items():
                gram[i][k] += di * dk
            for j in range(3):
                rhs[i][j] -= di * boundary[j]
    response = solve(gram, rhs)
    assert all(sum(gram[i][k] * response[k][j] for k in range(n)) == rhs[i][j]
               for i in range(n) for j in range(3))
    incident_counts = [sum(i in row for row in incidence) for i in range(n)]
    assert n == 32 and set(incident_counts) == {6}
    velocity = {edge: tuple(response[i]) for i, edge in enumerate(interior)}
    velocity.update(source)
    cubic, energy = Q(0), Q(0)
    for face in faces:
        word = [tuple(sign * q for q in velocity.get(edge, (0, 0, 0)))
                for sign, edge in zip(signs, face)]
        cubic += sum(det(word[i], word[j], word[k])
                     for i, j, k in combinations(range(4), 3))
        energy += sum(sum(v[j] for v in word) ** 2 for j in range(3))
    negative = [k for k, (face, row) in enumerate(zip(faces, incidence))
                if row and any(min(v) < 0 for v, _ in face)]
    assert len(negative) == 48
    assert all(len(incidence[k]) == 1 and not any(e in source for e in faces[k])
               for k in negative)
    negative_count = [sum(i in incidence[k] for k in negative) for i in range(n)]
    expected_count = [sum(v[j] == 0 for j in range(4) if j != a) for v, a in interior]
    assert negative_count == expected_count
    native_gram = [row[:] for row in gram]
    for i, count in enumerate(negative_count):
        native_gram[i][i] -= count
    positive = [k for k, row in enumerate(incidence) if row and k not in negative]
    assert len(positive) == 72 and sum(bool(row) for row in incidence) == 120
    native_response = [[Q(0)] * 3] + solve([row[1:] for row in native_gram[1:]], rhs[1:])
    assert all(sum(native_gram[i][j] * native_response[j][a] for j in range(n)) == rhs[i][a]
               for i in range(n) for a in range(3))
    native_velocity = {edge: tuple(native_response[i]) for i, edge in enumerate(interior)}
    native_velocity.update(source)
    native_cubic = Q(0)
    for k in positive:
        word = [tuple(sign * q for q in native_velocity.get(edge, (0, 0, 0)))
                for sign, edge in zip(signs, faces[k])]
        native_cubic += sum(det(word[i], word[j], word[l])
                            for i, j, l in combinations(range(4), 3))
    assert native_cubic == Q(31877443263, 69438734552)
    gauge = [int(v == (0, 0, 0, 0)) for v, _ in interior]
    assert all(sum(native_gram[i][j] * gauge[j] for j in range(n)) == 0 for i in range(n))
    assert any(sum(gram[i][j] * gauge[j] for j in range(n)) != 0 for i in range(n))
    exterior = [face for face, row in zip(faces, incidence) if not row]
    assert all(sum(e in source for e in face) <= 1 for face in exterior)
    source_cost = {str(e): sum(e in face for face in exterior) for e in source}
    assert sorted(source_cost.values()) == [3, 3, 4]
    isolation = []
    for edge in interior:
        v, a = edge
        j = 1 if a == 0 else 0
        base = list(v)
        if v[j] == 0:
            base[j] -= 1
        u = tuple(base)
        aa, bb = sorted((a, j))
        face = [(u, aa), (shift(u, aa), bb), (shift(u, bb), aa), (u, bb)]
        assert face in faces and edge in face
        assert sum(e in index for e in face) == 1
        assert all(e not in source for e in face if e != edge)
        isolation.append(faces.index(face))
    assert len(set(isolation)) == n
    assert cubic == Q(1784975, 2750517) and energy == Q(3467, 231)
    return dict(status="EXACT_RATIONAL_DIAGNOSTIC_NOT_LEAN_PROOF",
                vertices=len(vertices), links=len(edges), faces=len(faces),
                integrated_links=n, frozen_exterior_links=len(edges)-n,
                incident_face_counts=sorted(set(incident_counts)),
                interior_gram_rank=n, normal_equations_checked=3*n,
                harmonic_cubic_xyz=str(cubic), effective_raw_energy=str(energy),
                response=[[str(q) for q in row] for row in response],
                negative_side_faces=len(negative), positive_native_faces=len(positive),
                native_harmonic_cubic_xyz=str(native_cubic), diagonal_completion=negative_count,
                native_origin_gauge_lifted=True, exterior_source_face_costs=source_cost,
                isolation_face_indices=isolation,
                scope="Standard nearest-neighbor finite4D Dirichlet box. Exact jets and "
                      "combinatorial witnesses only. No Lean graph/coercivity/normal "
                      "certificate, full-Haar asymptotic, integrated Hessian theorem, "
                      "volume-uniform estimate, physical stationary transfer or mass gap.")


if __name__ == "__main__":
    print(json.dumps(diagnostic(), indent=2))
