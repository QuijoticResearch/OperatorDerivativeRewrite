"""Exact checks of the human radial-map factorization and its sharp witness."""
from fractions import Fraction as F
import json
class P(dict):
 def __add__(self,b):
  b=poly(b);z=P(self)
  for k,v in b.items():z[k]=z.get(k,F(0))+v
  return P({k:v for k,v in z.items() if v})
 __radd__=__add__
 def __neg__(self):return P({k:-v for k,v in self.items()})
 def __sub__(self,b):return self+-poly(b)
 def __rsub__(self,b):return poly(b)+-self
 def __mul__(self,b):
  z=P()
  for k,v in self.items():
   for l,w in poly(b).items():
    a=tuple(x+y for x,y in zip(k,l));z[a]=z.get(a,F(0))+v*w
  return P({k:v for k,v in z.items() if v})
 __rmul__=__mul__
 def __pow__(self,n):
  z=poly(1)
  for _ in range(n):z=z*self
  return z
def poly(v):return v if isinstance(v,P) else P({(0,0,0):F(v)}) if v else P()
r,s,c=[P({tuple(int(j==i) for j in range(3)):F(1)}) for i in range(3)]
d=r*r-r*s+s*s
assert not r**6+s**6-2*r*r*s*s*c-d*d*(r*r+s*s-2*c)-2*(r*r+s*s)*(r-s)**2*(c+r*s)
assert not d-((s-F(1,2)*r)**2+F(3,4)*r*r)
checks=['full symbolic squared-chord factorization','exact square-completion constant']
def dot(x,y):return sum((a*b for a,b in zip(x,y)),F(0))
for h0 in [(1,),(1,2),(0,1,2),(1,-2,3,4)]:
 h=list(map(F,h0));r2=dot(h,h);k=[-x/2 for x in h];s2=dot(k,k)
 source=dot([x-y for x,y in zip(h,k)],[x-y for x,y in zip(h,k)])
 image=dot([3*r2*x-3*s2*y for x,y in zip(h,k)],[3*r2*x-3*s2*y for x,y in zip(h,k)])
 assert source==F(16,81)/(r2*r2)*image
 n=len(h);J=[[3*r2*int(i==j)+6*h[i]*h[j] for j in range(n)] for i in range(n)]
 K=[[(F(int(i==j))-F(2,3)*h[i]*h[j]/r2)/(3*r2) for j in range(n)] for i in range(n)]
 for M,L in [(J,K),(K,J)]:
  for i in range(n):
   for j in range(n):assert sum((M[i][q]*L[q][j] for q in range(n)),F(0))==int(i==j)
 checks.extend(['sharp opposite half-source '+str(h0),'exact two-sided derivative inverse '+str(h0)])
print(json.dumps(dict(status='PASS',count=len(checks),arithmetic='exact rational polynomial coefficients and Hilbert-coordinate matrices',checks=checks,scope='Transcription checks for the explicitly human radial factorization, optimal witness and derivative formula. Does not add Lean verification or certify novelty.')))
