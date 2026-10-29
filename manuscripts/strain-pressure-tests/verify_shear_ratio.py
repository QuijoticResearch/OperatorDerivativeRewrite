"""Exact finite algebra checks; infinite-series convergence is proved in the PDF."""
from fractions import Fraction as F
import json
checks=[]
def check(name,ok):
    assert ok,name
    checks.append(name)
# Polynomial identity in a,b,d, independent of any sampled flow parameters.
def mul(p,q):
    r={}
    for i,x in p.items():
        for j,y in q.items():
            k=tuple(a+b for a,b in zip(i,j));r[k]=r.get(k,0)+x*y
    return {k:v for k,v in r.items() if v}
def add(p,q,c=1):
    r=dict(p)
    for k,v in q.items():r[k]=r.get(k,0)+c*v
    return {k:v for k,v in r.items() if v}
a={(1,0,0):1};b={(0,1,0):1};d={(0,0,1):1}
num=mul(add(a,b),add(d,b,-1));den=mul(add(d,b),add(a,b,-1))
check('ratio-minus-one polynomial identity',add(num,den,-1)==mul({(0,1,0):2},add(d,a,-1)))
# The normalized numerator/denominator reduction is cross-multiplied.
for av,bv,dv in [(F(3),F(1),F(7)),(F(9,5),F(2,7),F(13,4)),(F(101,100),F(1),F(103,100))]:
    t=av+bv;p0=av/t;p1=bv/t;e0=p0-F(1,2);e1=p1-F(1,2)
    raw=(e0*(dv/av)*p0+e1*p1)/(((dv+bv)/t)*(e0*e0+e1*e1))
    reduced=t*(dv-bv)/((dv+bv)*(av-bv))
    check('exact normalized reduction '+str(av),raw==reduced and raw>1)
# Axis modes and transverse modes have the stated antipodal angular labels.
sector=lambda k: int(abs(k[2])>abs(k[1]))
axis=[(0,n,0) for n in range(-12,13)]
trans=[(0,0,1),(0,0,-1)]
check('support labels and zero weighted mode',all(sector(k)==0 for k in axis) and all(sector(k)==1 for k in trans) and sum(x*x for x in axis[12])==0)
check('angular antipodes and positive scaling',all(sector(k)==sector(tuple(-x for x in k))==sector(tuple(7*x for x in k)) for k in axis+trans))
# sin(y)=(exp(iy)-exp(-iy))/(2i): phases and squared norm add to 1/2.
plus=(F(0),F(-1,2));minus=(F(0),F(1,2))
check('transverse Fourier phases and energy',plus[0]==minus[0] and plus[1]==-minus[1] and sum(x*x for x in plus+minus)==F(1,2))
check('integer fourth-minus-second positivity',all(n**4-n*n>=0 for n in range(-20,21)) and 2**4-2**2==12)
print(json.dumps(dict(status='PASS',count=len(checks),checks=checks,scope='Exact algebra, support and phase checks only; no numerical truncation is used to establish the infinite Gaussian tail.'),indent=2))
