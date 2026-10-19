"""Exact-integer interval Taylor prototype, NOT a Lean certificate.

Uses outward rounding to dyadic intervals, including exp/trig evaluation.
Lean verifies the normalized derivative recurrences and local Taylor
integral bound in Foundation.RiemannQuarticTaylorJets. The interval
propagation and complete printed calculation are not checked in Lean.
The pi bracket is Mathlib's pi_gt_d20 / pi_lt_d20. This is a feasibility
test for a future kernel-checked certificate.
No floating-point number enters an enclosure computation.
"""
import argparse
import json
from fractions import Fraction
from math import factorial

BITS = 160
SCALE = 1 << BITS


def ceildiv(a, b):
    return -((-a) // b)


class I:
    def __init__(self, lo, hi=None, raw=False):
        if raw:
            self.lo, self.hi = lo, hi
        else:
            lo = Fraction(lo)
            hi = lo if hi is None else Fraction(hi)
            self.lo = lo.numerator*SCALE//lo.denominator
            self.hi = ceildiv(hi.numerator*SCALE, hi.denominator)
        assert self.lo <= self.hi

    def __add__(self, other):
        other = cast(other)
        return I(self.lo+other.lo, self.hi+other.hi, raw=True)

    __radd__ = __add__

    def __neg__(self):
        return I(-self.hi, -self.lo, raw=True)

    def __sub__(self, other):
        return self+-cast(other)

    def __mul__(self, other):
        other = cast(other)
        v = [a*b for a in (self.lo, self.hi) for b in (other.lo, other.hi)]
        return I(min(v)//SCALE, ceildiv(max(v), SCALE), raw=True)

    __rmul__ = __mul__

    def __truediv__(self, n):
        assert isinstance(n, int) and n > 0
        return I(self.lo//n, ceildiv(self.hi, n), raw=True)

    def __pow__(self, n):
        assert n >= 0
        v, a = I(1), self
        while n:
            if n % 2:
                v = v*a
            a, n = a*a, n//2
        return v

    def absmax(self):
        return max(abs(self.lo), abs(self.hi))

    def summary(self):
        return {'lower_dyadic': str(self.lo), 'upper_dyadic': str(self.hi),
                'binary_denominator_exponent': BITS,
                'display_lower': float(Fraction(self.lo, SCALE)),
                'display_upper': float(Fraction(self.hi, SCALE)),
                'display_width': float(Fraction(self.hi-self.lo, SCALE))}


def cast(x):
    return x if isinstance(x, I) else I(x)


def exp_endpoint(v):
    # Scalar monotonicity reduces the interval exponential to two endpoints.
    if v < -BITS*SCALE:
        # exp(v) <= 2^-BITS because exp(1) >= 2.
        return I(0, 1, raw=True)
    s = max(0, abs(v).bit_length()-BITS+1)
    x = I(v, v, raw=True)/(1 << s)
    assert x.absmax() <= SCALE
    term = total = I(1)
    for k in range(1, 65):
        term = term*x/k
        total = total+term
    # Complex.exp_bound on |x| <= 1, n=65:
    # remainder <= 66/(65!*65) <= 2/65!.
    err = I(Fraction(2, factorial(65)))
    total = total+I(-err.hi, err.hi, raw=True)
    for _ in range(s):
        total = total*total
    return total


def exp(x):
    lo, hi = exp_endpoint(x.lo), exp_endpoint(x.hi)
    return I(max(0, lo.lo), hi.hi, raw=True)


def trig_point(v):
    s = max(0, abs(v).bit_length()-BITS+1)
    x = I(v, v, raw=True)/(1 << s)
    assert x.absmax() <= SCALE
    # The real and imaginary parts of exp(i*x), through degree64.
    re, im = I(1), I(0)
    term = I(1)
    for k in range(1, 65):
        term = term*x/k
        if k % 4 == 0:
            re = re+term
        elif k % 4 == 1:
            im = im+term
        elif k % 4 == 2:
            re = re-term
        else:
            im = im-term
    e = I(Fraction(2, factorial(65))).hi
    re, im = re+I(-e, e, raw=True), im+I(-e, e, raw=True)
    for _ in range(s):
        re, im = re*re-im*im, 2*re*im
    return re, im


def trig(x):
    # |sin(a)-sin(b)|, |cos(a)-cos(b)| <= |a-b|.
    mid = (x.lo+x.hi)//2
    rad = max(mid-x.lo, x.hi-mid)
    re, im = trig_point(mid)
    widening = I(-rad, rad, raw=True)
    return re+widening, im+widening


def add(a, b):
    return [x+y for x, y in zip(a, b)]


def mul(a, b):
    return [sum((a[k]*b[n-k] for k in range(n+1)), I(0)) for n in range(len(a))]


def scale(a, c):
    return [c*x for x in a]


def ex(a):
    b = [exp(a[0])]
    for n in range(1, len(a)):
        b.append(sum((k*a[k]*b[n-k] for k in range(1, n+1)), I(0))/n)
    return b


def jets(u, point, degree, terms):
    zero = [I(0) for _ in range(degree+1)]
    v = zero.copy()
    v[0], v[1] = u, I(1)
    u2 = mul(v, v)
    u4 = mul(u2, u2)
    e4 = ex(scale(v, 4))
    # Mathlib.Analysis.Real.Pi.Bounds: Real.pi_gt_d20 / pi_lt_d20.
    pi_lo = Fraction('3.14159265358979323846')
    pi = I(pi_lo, pi_lo+Fraction(1, 10**20))
    weight = zero.copy()
    for n in range(1, terms+1):
        phase9 = add(add(scale(u4, 8), scale(v, 9)), scale(e4, -pi*n*n))
        phase5 = add(add(scale(u4, 8), scale(v, 5)), scale(e4, -pi*n*n))
        weight = add(weight, add(scale(ex(phase9), 2*pi*pi*n**4),
                                 scale(ex(phase5), -3*pi*n*n)))
    co, si = trig(point*u)
    cosjet, sinjet = [], []
    for n in range(degree+1):
        cosjet.append([co, -si, -co, si][n % 4]*(point**n)/factorial(n))
        sinjet.append([si, co, -si, -co][n % 4]*(point**n)/factorial(n))
    return [mul(weight, cosjet), scale(mul(mul(weight, v), sinjet), -1),
            scale(mul(mul(weight, u2), cosjet), -1)]


def probe(panels, degree, terms):
    half = Fraction(4, 5*panels)
    point = I(Fraction('63.2083'))
    totals = [I(0), I(0), I(0)]
    for j in range(panels):
        center = half*(2*j+1)
        cj = jets(I(center), point, degree, terms)
        dj = jets(I(center-half, center+half), point, degree, terms)
        for k in range(3):
            cell = sum((cj[k][n]*I(2*half**(n+1))/ (n+1)
                        for n in range(0, degree, 2)), I(0))
            # Coarse cell bound matches local_integral_error in Lean:
            # sup |f^(degree)/degree!| * half^degree * cell_length.
            remainder = I(Fraction(dj[k][degree].absmax(), SCALE)*
                          2*half**(degree+1)).hi
            totals[k] = totals[k]+cell+I(-remainder, remainder, raw=True)
    laguerre = totals[1]*totals[1]-totals[0]*totals[2]
    boxes = [totals[0].hi*10**12 <= -163*SCALE,
             totals[1].absmax()*10**13 <= 4*SCALE,
             totals[2].hi*10**12 <= -145*SCALE]
    return {'status': 'EXACT-DYADIC PROTOTYPE; interval propagation and output NOT Lean-verified',
            't': '8', 'x': '632083/10000', 'cutoff': '8/5',
            'bits': BITS, 'panels': panels, 'degree': degree, 'theta_terms': terms,
            'endpoint_box_arithmetic_passes': boxes,
            'finite_integrals': [v.summary() for v in totals],
            'finite_laguerre': laguerre.summary()}


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--panels', type=int, default=160)
    p.add_argument('--degree', type=int, default=16)
    p.add_argument('--terms', type=int, default=4)
    p.add_argument('--bits', type=int, default=160)
    a = p.parse_args()
    assert a.panels > 0 and a.degree >= 2 and a.degree % 2 == 0 and a.terms > 0
    assert a.bits >= 64
    BITS, SCALE = a.bits, 1 << a.bits
    print(json.dumps(probe(a.panels, a.degree, a.terms), indent=2))
