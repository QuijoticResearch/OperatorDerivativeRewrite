"""Exact finite checks of the printed covariance and localization constants."""
from collections import Counter
from fractions import Fraction as F
import json

def pairings(items):
    if not items:
        yield ()
        return
    first,*rest=items
    for j,second in enumerate(rest):
        for pairs in pairings(rest[:j]+rest[j+1:]):
            yield ((first,second),)+pairs

if __name__=='__main__':
    counts=Counter(sum((a<4)!=(b<4) for a,b in pairs)
                   for pairs in pairings(list(range(8))))
    assert counts=={0:9,2:72,4:24},counts
    assert sum(counts.values())==105
    assert 105-9==96
    rates={
        'bad-clock twentieth-moment rate':1-10+20*F(4,9),
        'weighted endpoint diagonal':1-4*F(4,9),
        'weighted endpoint off-diagonal':2-5*F(4,9),
        'crossing initial time':-2*F(4,9),
        'crossing positive times':1-3*F(4,9),
    }
    assert list(rates.values())==[F(-1,9),F(-7,9),F(-2,9),F(-8,9),F(-1,3)]
    print(json.dumps(dict(status='PASS',pairing_counts=dict(counts),
        pairings_enumerated=105,diagonal_centered_coefficient=96,
        localization_rates={k:str(v) for k,v in rates.items()},
        scope='Exact finite pairing enumeration and rational localization exponents only; the probability estimates and limit are proved in the manuscript.')))
