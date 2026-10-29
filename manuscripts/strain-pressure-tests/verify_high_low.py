"""Independent exact Fourier convolution checks for the full Leray derivative."""
from fractions import Fraction as F
import json
Z=(F(0),F(0));I=(F(0),F(1))
def add(a,b):return (a[0]+b[0],a[1]+b[1])
def mul(a,b):return (a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])
def scale(t,a):return (t*a[0],t*a[1])
def norm(a):return a[0]**2+a[1]**2
def adv(U,V):
 out={}
 for k,u in U.items():
  for l,v in V.items():
   wave=tuple(k[j]+l[j] for j in range(3));dot=Z
   for j in range(3):dot=add(dot,scale(l[j],u[j]))
   vec=tuple(mul(mul(I,dot),v[j]) for j in range(3))
   if wave not in out:out[wave]=(Z,Z,Z)
   out[wave]=tuple(add(out[wave][j],vec[j]) for j in range(3))
 return {k:v for k,v in out.items() if any(q!=Z for q in v)}
checks=[]
for N in [4,5,8,16]:
 low={(1,0,0):(Z,I,Z),(-1,0,0):(Z,scale(-1,I),Z)}
 high={(0,N,0):(Z,Z,I),(0,-N,0):(Z,Z,scale(-1,I))}
 cross=adv(low,high);reverse=adv(high,low)
 assert not reverse;checks.append(f'vanishing reverse advection N={N}')
 assert set(cross)=={(s,t*N,0) for s in [-1,1] for t in [-1,1]};checks.append(f'full response support N={N}')
 for (s,t,_),v in cross.items():assert v==(Z,Z,scale(-s*N,I)),v
 checks.append(f'actual derivative Fourier coefficients N={N}')
 for k,v in cross.items():
  dot=Z
  for j in range(3):dot=add(dot,scale(k[j],v[j]))
  assert dot==Z
 checks.append(f'Leray projection acts identically N={N}')
 assert sum(norm(q) for v in cross.values() for q in v)==4*N*N
 checks.append(f'Parseval derivative energy N={N}')
 assert all(sum(q*q for q in k)>F(N*N,4) for k in high) and all(sum(q*q for q in k)>F(N*N,4) for k in cross)
 assert all(sum(q*q for q in k)<=F(N*N,4) for k in low)
 checks.append(f'low input retained but background and response discarded N={N}')
 assert F(sum(norm(q) for v in high.values() for q in v),N*N)==F(2,N*N)
 assert F(sum(norm(q) for v in cross.values() for q in v),N*N)==4
 checks.append(f'amplitude one over N velocity and response energies N={N}')
print(json.dumps(dict(status='PASS',count=len(checks),checks=checks,arithmetic='exact rational Gaussian-integer pairs and finite Fourier convolution',scope='Four actual integer-frequency trigonometric fields and full Leray derivative support/energies. No Navier-Stokes evolution, low-output counterexample or novelty test.')))
