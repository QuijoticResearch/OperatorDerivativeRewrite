"""Nonrigorous consistency probes, NOT interval enclosures or Lean proofs.

Uses only Python's standard library. Reproduces the literal manuscript kernel
with 15 theta terms and a finite cutoff, at two trapezoidal grid spacings.
Agreement between grids does not certify truncation or quadrature error.
"""
from decimal import Decimal as D, getcontext
import datetime
import json

getcontext().prec = 70
PI = D("3.141592653589793238462643383279502884197169399375105820974944592307816406286208998628")
TIME = D(8)
POINT = D("63.2083")
THRESHOLD = D("1e-73")


def trig(value):
    value %= 2 * PI
    if value > PI:
        value -= 2 * PI
    cosine = cosine_term = D(1)
    sine = sine_term = value
    j = 0
    while True:
        j += 1
        cosine_term *= -value * value / D((2 * j - 1) * (2 * j))
        sine_term *= -value * value / D((2 * j) * (2 * j + 1))
        cosine += cosine_term
        sine += sine_term
        if abs(cosine_term) + abs(sine_term) < THRESHOLD:
            return cosine, sine


def phi(u):
    e4, e5, e9 = ((k * u).exp() for k in (4, 5, 9))
    return sum(
        (2 * PI * PI * n**4 * e9 - 3 * PI * n * n * e5)
        * (-PI * n * n * e4).exp()
        for n in range(1, 16)
    )


def probe(panels):
    step = D("1.6") / panels
    sums = [D(0), D(0), D(0)]
    for j in range(panels + 1):
        u = step * j
        cosine, sine = trig(POINT * u)
        weight = (TIME * u**4).exp() * phi(u)
        if j in (0, panels):
            weight *= D("0.5")
        for k, value in enumerate(
            [weight * cosine, -weight * u * sine, -weight * u * u * cosine]
        ):
            sums[k] += value
    values = [value * step for value in sums]
    return {
        "panels": panels,
        "step": str(step),
        "H_Hprime_Hsecond": [str(value) for value in values],
        "Laguerre": str(values[1] ** 2 - values[0] * values[2]),
    }


if __name__ == "__main__":
    print(json.dumps({
        "time_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "status": "NONRIGOROUS; not interval enclosures or a Lean proof",
        "t": str(TIME), "x": str(POINT), "decimal_precision": 70,
        "n_terms": 15, "cutoff": "1.6",
        "probes": [probe(800), probe(1600)],
    }, indent=2))
