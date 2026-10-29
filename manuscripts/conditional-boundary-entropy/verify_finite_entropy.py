"""Exact finite transcription checks, including rational logarithm coefficients.

This validates a two-boundary, two-interior example, not the continuous SU(2)
proof. Entropies are represented as rational linear combinations of log primes.
"""
from fractions import Fraction as F
from collections import defaultdict
import json

def factors(n):
 d={};p=2
 while p*p<=n:
  while n%p==0:d[p]=d.get(p,0)+1;n//=p
  p+=1
 if n>1:d[n]=d.get(n,0)+1
 return d

def kl(p,q):
 out=defaultdict(F)
 for a,b in zip(p,q):
  if not a:continue
  assert b>0
  r=a/b
  for prime,n in factors(r.numerator).items():out[prime]+=a*n
  for prime,n in factors(r.denominator).items():out[prime]-=a*n
 return {p:v for p,v in out.items() if v}

def plus(a,b):
 out=defaultdict(F,a)
 for p,v in b.items():out[p]+=v
 return {p:v for p,v in out.items() if v}

def forward(p,T):return [sum(p[i]*T[i][j] for i in range(4)) for j in range(4)]
def joint(p,K):return [p[i]*K[i][j] for i in range(2) for j in range(2)]
rho=[F(1,3),F(2,3)];nu=[F(2,5),F(3,5)]
weights=[[F(1),F(2)],[F(3),F(5)]]
z=[sum(weights[i][j]*nu[j] for j in range(2)) for i in range(2)]
Z=sum(rho[i]*z[i] for i in range(2))
K=[[weights[i][j]*nu[j]/z[i] for j in range(2)] for i in range(2)]
tau=[rho[i]*z[i]/Z for i in range(2)]
Q=[rho[i]*nu[j]*weights[i][j]/Z for i in range(2) for j in range(2)]
T=[[K[a//2][b%2] if a//2==b//2 else F(0) for b in range(4)] for a in range(4)]
checks=[]
assert Q==joint(tau,K) and sum(Q)==1 and tau!=rho
checks.append('global normalization uses interaction-reweighted boundary')
assert all(sum(row)==1 for row in T)
assert [[sum(T[i][k]*T[k][j] for k in range(4)) for j in range(4)] for i in range(4)]==T
checks.append('actual resampling matrix is Markov and idempotent')
J=[F(1,10),F(2,10),F(3,10),F(4,10)];marg=[sum(J[:2]),sum(J[2:])]
JT=forward(J,T)
assert JT==joint(marg,K) and forward(Q,T)==Q
checks.append('update law and actual joint stationarity')
assert kl(J,Q)==plus(kl(JT,Q),kl(J,JT))
checks.append('exact entropy decomposition as rational log-prime coefficients')
assert kl(JT,Q)==kl(marg,tau)
checks.append('exact entropy after update equals boundary entropy')
perturbed=joint([F(1),F(0)],K)
assert forward(perturbed,T)==perturbed
assert kl(perturbed,Q)==kl([F(1),F(0)],tau) and kl(perturbed,perturbed)=={}
checks.append('conditioned stationary input retains its exact boundary entropy')
print(json.dumps(dict(status='PASS',checks=checks,count=len(checks),arithmetic='Fraction; exact rational coefficients of logarithms of primes',scope='Finite 2x2 transcription only; continuous probability and SU(2) proofs remain analytic.')))
