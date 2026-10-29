"""Exact sparse-polynomial check of the manuscript's jump Gamma2 identity.

This is a transcription check, not a substitute for the printed proof or
the frozen Lean verification. Only Python's standard library is used.
"""
from fractions import Fraction as Q

WIDTH = 7  # lambda, k, f(k-2), ..., f(k+2)
ZERO = (0,) * WIDTH


class Polynomial:
    def __init__(self, terms=None):
        if isinstance(terms, (int, Q)):
            terms = {ZERO: Q(terms)}
        self.terms = {m: Q(c) for m, c in (terms or {}).items() if c}

    @staticmethod
    def variable(i):
        m = list(ZERO)
        m[i] = 1
        return Polynomial({tuple(m): 1})

    def __add__(self, other):
        other = other if isinstance(other, Polynomial) else Polynomial(other)
        terms = self.terms.copy()
        for m, c in other.terms.items():
            terms[m] = terms.get(m, Q(0)) + c
        return Polynomial(terms)

    __radd__ = __add__

    def __neg__(self):
        return Polynomial({m: -c for m, c in self.terms.items()})

    def __sub__(self, other):
        return self + (-other if isinstance(other, Polynomial) else -Q(other))

    def __rsub__(self, other):
        return other + (-self)

    def __mul__(self, other):
        other = other if isinstance(other, Polynomial) else Polynomial(other)
        terms = {}
        for a, ca in self.terms.items():
            for b, cb in other.terms.items():
                m = tuple(x + y for x, y in zip(a, b))
                terms[m] = terms.get(m, Q(0)) + ca * cb
        return Polynomial(terms)

    __rmul__ = __mul__

    def square(self):
        return self * self


lam = Polynomial.variable(0)
state = Polynomial.variable(1)
values = {i: Polynomial.variable(i + 4) for i in range(-2, 3)}
half, quarter = Q(1, 2), Q(1, 4)


def check(center):
    # center=None gives the identity polynomial for k>=2; centers 0,1
    # separately enforce the actual half-line boundary conventions.
    rate = lambda i: state + i if center is None else Polynomial(center + i)
    f = lambda i: values[i]

    def generator(h, i):
        birth = lam * (h(i + 1) - h(i))
        if center is not None and center + i == 0:
            return birth
        return birth + rate(i) * (h(i - 1) - h(i))

    def carre(h, j, i):
        return half * (generator(lambda z: h(z) * j(z), i)
                       - h(i) * generator(j, i)
                       - j(i) * generator(h, i))

    gamma = lambda i: carre(f, f, i)
    lhs = half * generator(gamma, 0) - carre(f, lambda i: generator(f, i), 0)
    k = rate(0)
    u, v = f(1) - f(0), f(0) - f(-1)
    a, b = f(2) - 2 * f(1) + f(0), f(0) - 2 * f(-1) + f(-2)
    rhs = (quarter * lam.square() * a.square()
           + quarter * k * (k - 1) * b.square()
           + half * lam * k * (u - v).square()
           + 3 * quarter * lam * u.square() + quarter * k * v.square())
    residual = lhs - rhs
    if residual.terms:
        raise AssertionError((center, residual.terms))
    return {"case": "symbolic k>=2" if center is None else f"boundary k={center}",
            "gamma2_monomials": len(lhs.terms), "residual_monomials": 0}


if __name__ == "__main__":
    import json
    print(json.dumps({"arithmetic": "exact rational sparse polynomials",
                      "checks": [check(k) for k in [None, 0, 1]],
                      "status": "PASS"}, indent=2))
