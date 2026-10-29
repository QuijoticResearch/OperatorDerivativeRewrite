"""Exact polynomial checks of curl and central-frequency transcription.

No numerical quadrature or bump/support theorem is substituted for the proof.
The four variables are kappa,p1,p2,p3; coefficients are exact rationals.
"""
from fractions import Fraction as F
import json
def const(c):return {(0,0,0,0):F(c)} if c else {}
def variable(i):
 a=[0]*4;a[i]=1;return {tuple(a):F(1)}
def add(*terms):
 r={}
 for t in terms:
  for m,c in t.items():r[m]=r.get(m,F(0))+c
 return {m:c for m,c in r.items() if c}
def mul(a,b):
 r={}
 for m,c in a.items():
  for n,d in b.items():
   e=tuple(x+y for x,y in zip(m,n));r[e]=r.get(e,F(0))+c*d
 return {m:c for m,c in r.items() if c}
def scale(c,a):return mul(const(c),a)
def dot(a,b):return add(*(mul(x,y) for x,y in zip(a,b)))
k,x,y,z=map(variable,range(4));zero={}
p=[x,y,z];q=[add(const(2),scale(-1,x)),scale(-1,y),scale(-1,z)]
u=[mul(k,y),scale(-1,mul(k,x)),zero]
v=[mul(mul(mul(k,k),q[1]),q[2]),zero,scale(-1,mul(mul(mul(k,k),q[1]),q[0]))]
checks=[]
assert dot(p,u)==zero;checks.append('first curl symbol is solenoidal')
assert dot(q,v)==zero;checks.append('second transverse curl symbol is solenoidal')
central=mul(mul(k,dot(u,q)),v[2])
expected=scale(2,mul(mul(mul(mul(k,k),mul(k,k)),mul(y,y)),add(const(2),scale(-1,x))))
assert central==expected;checks.append('complete central kernel is 2*kappa^4*p2^2*(2-p1)')
response=[mul(k,z),zero,scale(-1,mul(k,x))]
assert dot(p,response)==zero;checks.append('response curl symbol is solenoidal')
assert (1j)**4==1;checks.append('four derivative phases have positive sign')
# (xi,p)->(p,xi-p), in one coordinate, has determinant -1;
# its three-coordinate direct sum has absolute determinant one.
assert 0*(-1)-1*1==-1 and abs((-1)**3)==1
checks.append('product-space Fourier shear has absolute Jacobian one')
print(json.dumps(dict(status='PASS',count=len(checks),checks=checks,arithmetic='Exact sparse polynomials over Fraction; integer Jacobian',scope='Finite symbol transcription only. Schwartz integrability, bump positivity and closed support are proved analytically.')))
