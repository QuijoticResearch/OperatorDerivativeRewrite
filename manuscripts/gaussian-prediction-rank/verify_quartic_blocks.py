"""Exact Gaussian integration for finite blocks with retained and residual directions."""
from fractions import Fraction as F
import json
N=4;ZERO=(0,)*N

def add(*ps):
 z={}
 for p in ps:
  for k,v in p.items():z[k]=z.get(k,F(0))+v
 return {k:v for k,v in z.items() if v}
def scale(p,a):return {k:a*v for k,v in p.items() if a*v}
def mul(p,q):
 z={}
 for k,v in p.items():
  for l,w in q.items():
   a=tuple(x+y for x,y in zip(k,l));z[a]=z.get(a,F(0))+v*w
 return {k:v for k,v in z.items() if v}
def power(p,n):
 z={ZERO:F(1)}
 for _ in range(n):z=mul(z,p)
 return z
def moment(n):
 if n%2:return F(0)
 r=F(1)
 for j in range(1,n,2):r*=j
 return r
def mean(p):
 r=F(0)
 for k,v in p.items():
  for n in k:v*=moment(n)
  r+=v
 return r
def cond(p):
 z={}
 for k,v in p.items():
  q=k[:2]+(0,0);z[q]=z.get(q,F(0))+v*moment(k[2])*moment(k[3])
 return {k:v for k,v in z.items() if v}
def linear(u):return {tuple(int(j==i) for j in range(N)):F(a) for i,a in enumerate(u) if a}
def dot(u,v):return sum((F(a)*F(b) for a,b in zip(u,v)),F(0))
def W(d,e,M):return sum((d[i]*e[j]*M[i][j]**2 for i in range(len(d)) for j in range(len(d))),F(0))
def T1(M):return W([M[i][i] for i in range(len(M))],[M[i][i] for i in range(len(M))],M)
def T2(M):return sum((x**4 for row in M for x in row),F(0))
checks=[]
fixtures=[[],[(1,0,0,0)],[(1,1,2,-1),(-1,2,1,1),(0,1,2,3)],[(1,0,1,0),(1,0,-1,0),(0,0,1,1)]]
for number,U in enumerate(fixtures):
 C=[[dot(u,v) for v in U] for u in U];B=[[dot(u[:2],v[:2]) for v in U] for u in U];c=[dot(u,u) for u in U];b=[dot(u[:2],u[:2]) for u in U];r=[x-y for x,y in zip(c,b)]
 targets=[add(power(linear(u),4),{ZERO:-3*c[i]**2}) for i,u in enumerate(U)];pred=[cond(p) for p in targets]
 V=scale(add(*targets),F(1,24));PV=cond(V)
 assert mean(mul(V,V))==(72*T1(C)+24*T2(C))/576
 checks.append(f'actual full block moment fixture {number}')
 assert mean(mul(PV,PV))==(72*W(c,c,B)+24*T2(B))/576
 checks.append(f'actual retained block moment fixture {number}')
 assert mean(mul(PV,PV))==(72*T1(B)+24*T2(B))/576+W(r,r,B)/8+W(b,r,B)/4
 checks.append(f'exact three-term retained split fixture {number}')
 assert all(mean(mul(pred[i],pred[j]))==72*c[i]*c[j]*B[i][j]**2+24*B[i][j]**4 for i in range(len(U)) for j in range(len(U)))
 checks.append(f'all retained pair moments fixture {number}')
 assert all(pred[i]==add(power(linear(U[i][:2]+(0,0)),4),scale(power(linear(U[i][:2]+(0,0)),2),6*r[i]),{ZERO:3*b[i]**2-6*c[i]*b[i]}) for i in range(len(U)))
 checks.append(f'literal independent-residual conditional polynomial fixture {number}')
for shift in map(F,[-2,-1,0,F(1,2),3]):
 for sigma in map(F,[0,F(1,2),1,2]):
  r=sigma*sigma;P=add(power(add({ZERO:shift},linear((sigma,0,0,0))),4),{ZERO:-(shift**4+6*shift**2*r+3*r*r)})
  v=mean(mul(P,P));assert mean(P)==0 and v==16*shift**6*r+168*shift**4*r*r+384*shift**2*r**3+96*r**4
  assert v>=96*r**4 and (v>96*r**4)==bool(shift and r)
  checks.append(f'exact shifted centered fourth-power variance b={shift},sigma={sigma}')
print(json.dumps(dict(status='PASS',count=len(checks),checks=checks,arithmetic='Exact rational four-coordinate Gaussian polynomial integration',scope='Four finite block fixtures, including empty and deterministic-residual cases, all covariance pairs and twenty scalar shifts/scales. General conditional laws and all-parameter positivity are proved in the manuscript.')))
