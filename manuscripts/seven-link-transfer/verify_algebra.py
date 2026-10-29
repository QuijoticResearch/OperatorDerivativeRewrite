"""Exact transcription checks for the seven-link manuscript.

No numerical integration or eigensolver is used. These checks supplement
the complete printed proofs and frozen Lean audit; they do not replace them.
"""
from fractions import Fraction as Q
import json

WIDTH = 6  # alpha, r, t, A, B, q
ZERO = (0,) * WIDTH


class Poly:
    def __init__(self, terms=0):
        if isinstance(terms, (int, Q)):
            terms = {ZERO: Q(terms)}
        self.terms = {m: Q(c) for m, c in terms.items() if c}

    @staticmethod
    def variable(i):
        m = list(ZERO)
        m[i] = 1
        return Poly({tuple(m): 1})

    def __add__(self, other):
        other = other if isinstance(other, Poly) else Poly(other)
        result = self.terms.copy()
        for m, c in other.terms.items():
            result[m] = result.get(m, Q(0)) + c
        return Poly(result)

    __radd__ = __add__

    def __neg__(self):
        return Poly({m: -c for m, c in self.terms.items()})

    def __sub__(self, other):
        return self + (-other if isinstance(other, Poly) else -Q(other))

    def __rsub__(self, other):
        return other + (-self)

    def __mul__(self, other):
        other = other if isinstance(other, Poly) else Poly(other)
        result = {}
        for a, ca in self.terms.items():
            for b, cb in other.terms.items():
                m = tuple(x + y for x, y in zip(a, b))
                result[m] = result.get(m, Q(0)) + ca * cb
        return Poly(result)

    __rmul__ = __mul__

    def __pow__(self, n):
        assert isinstance(n, int) and n >= 0
        result = Poly(1)
        for _ in range(n):
            result = result * self
        return result

    def __truediv__(self, scalar):
        return self * (1 / Q(scalar))


checks = []


def equal(label, lhs, rhs):
    residual = lhs - rhs
    if residual.terms:
        raise AssertionError((label, residual.terms))
    checks.append({"identity": label, "residual_monomials": 0})


alpha, r, t, A, B, q = [Poly.variable(i) for i in range(WIDTH)]
radial = Q(1, 4) + t * (A + 3 * B) * q / 8 + t**2 * ((A - B)**2 + 8 * B * (A + B) * q**2) / 64
equal("radial sum of squares", radial,
      (1 + t * (A + 3 * B) * q / 4)**2 / 4
      + t**2 * (A - B)**2 * (1 - q**2) / 64)
A0, B0 = -(A + 3 * B) / 2, B * (A + B) / 2
R0 = (A - B)**2 / 64 + B * (A + B) / 32
equal("radial Taylor regrouping", radial,
      (1 + A0 * (-t) * q + B0 * t**2 * (q**2 - Q(1, 4))) / 4 + t**2 * R0)
weighted = (1 - t * q + t**2 * q**2 / 2) * radial
averaged = {}
for monomial, coefficient in weighted.terms.items():
    if monomial[2] > 2:
        continue
    degree = monomial[5]
    assert degree <= 2
    if degree == 1:
        continue
    m = list(monomial)
    m[5] = 0
    c = coefficient * (Q(1, 4) if degree == 2 else 1)
    averaged[tuple(m)] = averaged.get(tuple(m), Q(0)) + c
equal("Haar denominator coefficient", Poly(averaged),
      Q(1, 4) + t**2 * (A**2 + 3 * B**2 - 2 * A - 6 * B + 2) / 64)

# Multiply 64*Delta by (1-alpha)^2*(1-alpha*r)^2*(1-alpha^2).
d1, d2, d3 = 1 - alpha, 1 - alpha * r, 1 - alpha**2
cleared = (alpha**3 * d2**2 * d3 + 3 * alpha**3 * r * d1**2 * d3
           - alpha**2 * (d2**2 * d3 + 3 * d1**2 * d3
                         - 2 * d1 * d2**2 * d3 - 6 * d2 * d1**2 * d3
                         + 2 * d1**2 * d2**2 * d3)
           - 2 * alpha**2 * (1 + alpha**2) * d1**2 * d2**2)
equal("optimized positive margin after exact denominator clearing", cleared,
      alpha**3 * (1 + 3 * r - alpha * (3 + r)) * d1**2 * d2)


def qmul(x, y):
    a, b, c, d = x
    e, f, g, h = y
    return (a*e-b*f-c*g-d*h, a*f+b*e+c*h-d*g,
            a*g-b*h+c*e+d*f, a*h+b*g-c*f+d*e)


basis = [tuple(int(i == j) for i in range(4)) for j in range(4)]
rotations = []
for imaginary in basis[1:]:
    columns = [qmul(vector, imaginary) for vector in basis]
    rotations.append([[columns[j][i] for j in range(4)] for i in range(4)])

# The identity is linear in symmetric T. Check a full ten-element basis.
for i in range(4):
    for j in range(i, 4):
        matrix = [[int((a == i and b == j) or (a == j and b == i))
                   for b in range(4)] for a in range(4)]
        trace = sum(matrix[a][a] for a in range(4))
        lhs = [[sum(rot[a][u] * matrix[a][b] * rot[b][v]
                    for rot in rotations for a in range(4) for b in range(4))
                for v in range(4)] for u in range(4)]
        rhs = [[trace * int(u == v) - matrix[u][v] for v in range(4)] for u in range(4)]
        assert lhs == rhs, (i, j, lhs, rhs)
        checks.append({"identity": f"quaternion quadratic twirl symmetric unit ({i},{j})",
                       "residual_matrix_entries": 0})

if __name__ == "__main__":
    print(json.dumps({"status": "PASS", "arithmetic": "exact rational polynomials and integer matrices",
                      "checks": checks, "count": len(checks)}, indent=2))
