"""Exact finite algebra checks. The infinite operator/domain proofs are printed."""
from fractions import Fraction as F
import json
checks=[]
def check(k,v):
 assert v,k
 checks.append(k)
def add(A,B):return [[x+y for x,y in zip(a,b)] for a,b in zip(A,B)]
def neg(A):return [[-x for x in row] for row in A]
def mul(A,B):return [[sum((A[i][k]*B[k][j] for k in range(len(B))),F(0)) for j in range(len(B[0]))] for i in range(len(A))]
def tr(A):return [list(row) for row in zip(*A)]
def inv(A):
 a,b=A[0];c,d=A[1];q=a*d-b*c;assert q
 return [[d/q,-b/q],[-c/q,a/q]]
I=[[F(1),F(0)],[F(0),F(1)]];J=[[F(1),F(0)],[F(0),F(-1)]]
T=[[F(1),F(2)],[F(0),F(1)]];A=mul(tr(T),T);R=inv(add(I,A));G=mul(T,R)
check('unit resolvent and true Hilbert energy factorization',mul(add(I,A),R)==I and R==tr(R))
check('graph variational identity',add(R,mul(tr(T),G))==I)
check('graph projection energy identity',add(mul(tr(R),R),mul(tr(G),G))==R)
check('signed adjoint conjugation and pairing',mul(J,mul(J,mul(tr(T),J)))==mul(tr(T),J) and mul(J,J)==I)
# Exact block quadratic matrix of the graph-projection Pythagorean identity.
def block(A,B,C,D):return [a+b for a,b in zip(A,B)]+[c+d for c,d in zip(C,D)]
zero=[[F(0),F(0)],[F(0),F(0)]]
L=block(I,neg(I),neg(I),add(I,A))
res=block(add(I,neg(R)),zero,neg(G),zero)
err=block(neg(R),I,neg(G),T)
check('full energy-gap quadratic coefficients',add(mul(tr(res),res),mul(tr(err),err))==L)
def moment(n,variance):
 if n%2:return F(0)
 out=F(1)
 for j in range(1,n,2):out*=j*variance
 return out
def monmean(poly,variance):return sum((c*moment(n,variance) for n,c in poly.items()),F(0))
def padd(p,q):
 out=dict(p)
 for n,c in q.items():out[n]=out.get(n,F(0))+c
 return {n:c for n,c in out.items() if c}
def pmul(p,q):
 out={}
 for n,c in p.items():
  for m,d in q.items():out[n+m]=out.get(n+m,F(0))+c*d
 return {n:c for n,c in out.items() if c}
def deriv(p):return {n-1:n*c for n,c in p.items() if n}
p={1:F(1),2:F(1)};kp=padd(deriv(p),pmul({1:F(-2)},p))
check('raw signed kernel simple zero negative value and positive Gaussian mass',p.get(0,0)==0 and kp[0]==1 and sum(c*F(-1,2)**n for n,c in p.items())<0 and monmean(p,F(1,2))==F(1,2))
check('actual polynomial-Gaussian Stein integral transcriptions',all(monmean(padd(pmul(p,padd(deriv({n:F(1)}),{n+1:F(-2)})),pmul({n:F(1)},kp)),F(1,4))==0 for n in range(21)))
print(json.dumps(dict(status='PASS',count=len(checks),checks=checks,scope='Finite exact matrix and Gaussian-polynomial transcriptions; not a proof of closability, domain equality or analytic limits.')))
