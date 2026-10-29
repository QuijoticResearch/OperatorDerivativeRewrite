"""Exact finite transcription checks, not probability-limit evidence."""
from fractions import Fraction as Q
from itertools import product
import json

def inner_increment(r,i,j):
    return min(r[i+1],r[j+1])-min(r[i+1],r[j])-min(r[i],r[j+1])+min(r[i],r[j])

checks=0
for n in (2,3,4):
    for tail in product((Q(0),Q(1,2),Q(1)),repeat=n):
        r=(Q(0),)+tail
        d=[r[i+1]-r[i] for i in range(n)]
        mass=sum(x*x for x in d)
        gram=sum(inner_increment(r,i,j)**2 for i in range(n) for j in range(n))
        overlap=sum(max(Q(0), min(max(r[i],r[i+1]),max(r[j],r[j+1]))-max(min(r[i],r[i+1]),min(r[j],r[j+1])))**2 for i in range(n) for j in range(n))
        assert gram==overlap
        # Independently expand the four-Gaussian covariance of the raw products.
        energy=sum(inner_increment(r,i,j)*min(r[i],r[j])+(min(r[i+1],r[j])-min(r[i],r[j]))*(min(r[i],r[j+1])-min(r[i],r[j])) for i in range(n) for j in range(n))
        cap=sum((min(r[-1],r[i+1])-min(r[-1],r[i]))**2 for i in range(n))
        assert energy==Q(1,2)*(r[-1]**2-2*cap+gram)
        assert energy>=0 and gram<=2*energy+2*mass
        eta=max(abs(x) for x in d);M=max(r)
        assert mass**2<=2*M*eta*gram
        correction=sum(min(r[i],r[i+1])-r[i] for i in range(n))
        assert 2*correction==r[-1]-sum(abs(x) for x in d)
        checks+=1

def sign(x):return (x>0)-(x<0)
tanaka=0
for x,y in product(map(Q,(-2,-1,0,1,2)),repeat=2):
    crossing=abs(y-x)-abs(abs(y)-abs(x))
    remainder=abs(y)-abs(x)-sign(x)*(y-x)
    assert 0<=crossing<=remainder
    tanaka+=1
print(json.dumps(dict(status='PASS',arithmetic='exact fractions',finite_radius_sequences=checks,discrete_tanaka_pairs=tanaka,scope='kernel mass/Gram, independent Wick-energy expansion, endpoint telescope, band concentration and elementary folding inequality; no stochastic limit oracle'),indent=2))
