"""Finite exact Gaussian polynomial checks, with analytic limits proved in text."""
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
s=F(3,4);h=F(2,5)
for d in range(1,9):
 old=wick(X,s,d);new=wick(add(X,Y),s+h,d)
 check(f'degree {d} exact full-increment conditional Wick polynomial',cond(new,h)==old)
 diff=add(new,scale(old,-1))
 check(f'degree {d} exact positive-time Wick increment energy',moment(mul(diff,diff),s,h)==factorial(d)*((s+h)**d-s**d))
V=add(scale(X,F(3,5)),scale(Y,F(4,5)))
for d in range(1,7):
 check(f'degree {d} correlated monic Wick covariance with factorial normalization',moment(mul(wick(X,F(1),d),wick(V,F(1),d)))==factorial(d)*F(3,5)**d)
for N in [3,8,32]:
 # t=log(2)/2 makes each exact exponential factor 2^(-n-1).
 energies=[(1-F(1,2**(n+1)))/F(2*(n+1)) for n in range(N+3)]
 check(f'linear-rate exact tail amplitude bound N={N}',all(energies[n]<=F(1,2*(N+1)) for n in range(N,len(energies))))
check('harmonic square positive-time lower polynomial at time one half',all(2*((F(1,2)+q)**2-F(1,2)**2)>=2*q for q in [F(1,100),F(1,4),F(1,2)]))
print(json.dumps(dict(status='PASS',check_count=len(checks),checks=checks,arithmetic='Exact rational polynomial and Gaussian-moment arithmetic',scope='Finite Wick conditional polynomials, factorial covariance, positive-time increment identities and actual linear-rate tail bounds at t=log(2)/2. Infinite series convergence, compactness and no-higher-power statements rely on the printed proofs.')))
