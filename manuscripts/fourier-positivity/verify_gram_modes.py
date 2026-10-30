"""Finite exact Wick covariance and realified matrix transcriptions."""
from fractions import Fraction as F
from math import factorial
from itertools import permutations
import json
class P(dict):
 def __add__(self,b):
  out=P(self)
  for k,v in p(b).items():out[k]=out.get(k,F(0))+v
  return P({k:v for k,v in out.items() if v})
 __radd__=__add__
 def __neg__(self):return P({k:-v for k,v in self.items()})
 def __sub__(self,b):return self+-p(b)
 def __rsub__(self,b):return p(b)+-self
 def __mul__(self,b):
  out=P()
  for k,v in self.items():
   for l,w in p(b).items():
    q=(k[0]+l[0],k[1]+l[1]);out[q]=out.get(q,F(0))+v*w
  return P({k:v for k,v in out.items() if v})
 __rmul__=__mul__
 def __pow__(self,n):
  out=p(1)
  for _ in range(n):out=out*self
  return out
def p(v):return v if isinstance(v,P) else P({(0,0):F(v)}) if v else P()
x=P({(1,0):F(1)});y=P({(0,1):F(1)})
def moment(n):
 if n%2:return 0
 out=1
 for j in range(1,n,2):out*=j
 return out
def mean(a):return sum(v*moment(k[0])*moment(k[1]) for k,v in a.items())
def wick(X,var,n):
 u=p(1)
 if n==0:return u
 v=X
 for q in range(1,n):u,v=v,X*v-q*var*u
 return v
def det(A):
 n=len(A);out=p(0)
 for s in permutations(range(n)):
  sign=(-1)**sum(s[i]>s[j] for i in range(n) for j in range(i+1,n));term=p(sign)
  for i in range(n):term=term*A[i][s[i]]
  out=out+term
 return out
checks=[]
for q in range(6):
 U=wick(x,1,q);V=wick(x+y,2,q)
 for label,value,target in [('first norm',mean(U*U),factorial(q)),('second norm',mean(V*V),factorial(q)*2**q),('cross pairing',mean(U*V),factorial(q))]:
  assert value==target,(q,label,value,target);checks.append(f'Wick {label} degree={q}')
R=[[1,1],[1,2]];M=[[1,1],[1,4]]
assert det(R)==p(1) and det(M)==p(3);checks.append('actual Gram determinants')
assert x*x+2*x*y+2*y*y==(x+y)**2+y*y;checks.append('R orthogonal innovation energy')
assert x*x+2*x*y+4*y*y==(x+y)**2+3*y*y;checks.append('P generalized mode energy')
assert x**4-x**6==x**4*(1-x*x);checks.append('strict false-rate difference factor')
T=[[1,1,0,0],[0,x,0,0],[0,0,1,1],[0,0,0,x]]
assert det(T)==x*x;checks.append('real double factor determinant')
assert (x+y)**2+(x*y)**2==x*x+2*x*y+(1+x*x)*y*y;checks.append('triangular factor Gram energy')
print(json.dumps(dict(status='PASS',count=len(checks),checks=checks,arithmetic='exact rational bivariate polynomials, Gaussian integer moments and permutation determinants',scope='Degrees zero through five of the two-source Brownian Gram pair, exact generalized-mode algebra and realification determinant. Not a numerical fractional-process or full-domain theorem.')))
