"""Exact finite identities supporting the analytic probability-law proofs."""
from fractions import Fraction as F
from math import factorial,comb
from itertools import product
import json
checks=[]
def check(name,ok):
 assert ok,name
 checks.append(name)
# Universal polynomial coefficient equality, not a numerical Poisson tail.
check('Poisson transform formal coefficients through degree 12',all(F((-1)**(n-j),factorial(n-j)*factorial(j))==F(comb(n,j)*(-1)**(n-j),factorial(n)) for n in range(13) for j in range(n+1)))
# Fourier-box intersections factor exactly by coordinate.
for n in [0,1,3]:
 box=set(product(range(-n,n+1),repeat=3))
 ok=True
 for k in product(range(-3,4),repeat=3):
  count=sum(tuple(j[i]+k[i] for i in range(3)) in box for j in box)
  expected=1
  for ki in k:expected*=max(0,2*n+1-abs(ki))
  ok &= count==expected
 check('exact Fourier-box overlap N='+str(n),ok)
# A symmetric rational law on Z/4: actual complex characters in Q(i).
law=[F(1,2),F(1,4),F(0),F(1,4)]
times=lambda z,w:(z[0]*w[0]-z[1]*w[1],z[0]*w[1]+z[1]*w[0])
chars=[(F(1),F(0)),(F(0),F(1)),(F(-1),F(0)),(F(0),F(-1))]
phi=[sum(law[x]*chars[(k*x)%4][0] for x in range(4)) for k in range(4)]
q=[1-u for u in phi];ok=True
for k,l in product(range(4),repeat=2):
 val=[F(0),F(0)]
 for x in range(4):
  a=chars[(-k*x)%4];b=chars[(l*x)%4]
  z=times((a[0]-1,a[1]),(b[0]-1,b[1]))
  val=[val[i]+law[x]*z[i] for i in range(2)]
 ok &= val==[q[k]+q[l]-q[(k-l)%4],0]
check('actual rational jump-law character Gram identity',ok)
# Centered correction is (exp(-lambda*a)-1)(exp(-lambda*b)-1).
check('centered mean-product has zero value and first derivative at zero',all(sum((F((-a)**i,factorial(i)) if i else F(0))*(F((-b)**(n-i),factorial(n-i)) if n-i else F(0)) for i in range(n+1))==0 for a,b in [(1,2),(0,3),(2,2)] for n in [0,1]))
print(json.dumps(dict(status='PASS',count=len(checks),checks=checks,scope='Finite exact algebra only; analytic convergence, compactness, conditional laws and null-singleton arguments are proved in the paper.'),indent=2))
