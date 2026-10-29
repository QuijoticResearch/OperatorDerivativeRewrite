"""Exact finite Gaussian recovery/projection checks; compactness is proved analytically."""
from fractions import Fraction as F
from math import factorial,comb
import json
def add(a,b):
 out=dict(a)
 for k,v in b.items():out[k]=out.get(k,0)+v
 return {k:v for k,v in out.items() if v}
def scale(a,c):return {k:c*v for k,v in a.items() if c*v}
def mul(a,b):
 out={}
 for (i,j),v in a.items():
  for (k,l),w in b.items():out[(i+k,j+l)]=out.get((i+k,j+l),0)+v*w
 return {k:v for k,v in out.items() if v}
def power(a,n):
 out={(0,0):F(1)}
 for _ in range(n):out=mul(out,a)
 return out
def wick(x,var,d):
 out={}
 for k in range(d//2+1):out=add(out,scale(power(x,d-2*k),F(factorial(d),2**k*factorial(k)*factorial(d-2*k))*(-var)**k))
 return out
def gm(n,var):
 if n%2:return F(0)
 return F(factorial(n),2**(n//2)*factorial(n//2))*var**(n//2)
def moment(p,v=F(1),w=F(1)):return sum(c*gm(i,v)*gm(j,w) for (i,j),c in p.items())
def cond(p,w):
 out={}
 for (i,j),c in p.items():out=add(out,{(i,0):c*gm(j,w)})
 return out

X={(1,0):F(1)};Y={(0,1):F(1)};checks=[]
def check(label,ok):
 assert ok,label
 checks.append(label)
u=add(scale(X,F(3,5)),scale(Y,F(4,5)));p=scale(X,F(3,5));v=F(9,25)
for q in range(1,9):
 check(f'degree {q} conditional Wick source projection',cond(wick(u,F(1),q),F(1))==wick(p,v,q))
 defect=scale(wick(p,v,q-1),F(4,5))
 check(f'degree {q} exact missing coefficient-projection energy',moment(mul(defect,defect))==factorial(q-1)*F(16,25)*v**(q-1))
def derivative(a,j):
 out={}
 for k,c in a.items():
  if k[j]:
   t=list(k);t[j]-=1;out[tuple(t)]=c*k[j]
 return out
for q in range(1,5):
 for a in range(q+1):
  b=q-a;f=mul(wick(X,F(1),a),wick(Y,F(1),b));dx=derivative(f,0);dy=derivative(f,1)
  energy=moment(add(mul(dx,dx),mul(dy,dy)))/q**2
  check(f'two-coordinate Hermite recovery energy multi-index {a},{b}',energy==F(factorial(a)*factorial(b),q))
print(json.dumps(dict(status='PASS',check_count=len(checks),checks=checks,arithmetic='Exact rational Gaussian polynomial, derivative and moment arithmetic',scope='Conditional monic Wick identities and missing source-projection energies through degree eight; original finite derivative/recovery energies for two-coordinate Hermite products through total degree four. Compactness, density, norm tails and infinite-dimensional distance are proved analytically in the manuscript.')))
