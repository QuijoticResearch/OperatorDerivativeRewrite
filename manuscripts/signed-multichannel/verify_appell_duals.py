"""Exact finite Appell, moment-pairing and centered-primitive transcription checks."""
from fractions import Fraction as F
from math import factorial as fac
import json

def trim(a):
 a=list(a)
 while a and not a[-1]:a.pop()
 return a

def add(a,b):return trim([(a[i] if i<len(a) else F(0))+(b[i] if i<len(b) else F(0)) for i in range(max(len(a),len(b)))])
def scale(a,c):return trim([c*x for x in a])
def mul(a,b):
 if not a or not b:return []
 z=[F(0)]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):z[i+j]+=x*y
 return trim(z)
def deriv(a,n=1):
 for _ in range(n):a=[(i+1)*a[i+1] for i in range(len(a)-1)]
 return trim(a)
def mon(n):return [F(0)]*n+[F(1)]
def appell(p,a,n):
 h=[F(0)]*(n+1)
 for j in range(n//p+1):h[n-p*j]=F(fac(n),fac(j)*fac(n-p*j))*(-a)**j
 return trim(h)
def moment(p,a,n):return F(fac(n),fac(n//p))*a**(n//p) if n%p==0 else F(0)
def mean(p,a,P):return sum((v*moment(p,a,n) for n,v in enumerate(P)),F(0))
def coordinate(p,a,n,P):return mean(p,a,deriv(P,n))/fac(n)
def primitive(p,a,P):
 out=[]
 for n in range(len(P)):out=add(out,scale(appell(p,a,n+1),coordinate(p,a,n,P)/F(n+1)))
 return out
checks=[]
for p in [2,4,6,8]:
 for a in map(F,[-2,-1,1,2]):
  H=[appell(p,a,n) for n in range(14)]
  assert all(deriv(H[n+1])==scale(H[n],n+1) for n in range(13))
  assert all(H[n+1]==add([F(0)]+H[n],scale(deriv(H[n],p-1),-p*a)) for n in range(13))
  checks.append(f'raising and derivative p={p},a={a}')
  assert all(coordinate(p,a,n,H[j])==int(n==j) for n in range(12) for j in range(12))
  checks.append(f'full finite coordinate table p={p},a={a}')
  for d in range(7):
   n=(p-1)*d
   assert mean(p,a,mul(appell(p,a,n),mon(d)))==fac(n)*(p*a)**d
   assert all(mean(p,a,mul(appell(p,a,k),mon(d)))==0 for k in [n+1,n+2])
  checks.append(f'exact top pairing and vanishing above p={p},a={a}')
  assert all(mean(p,a,scale([F(0)]+mon(n),1/(p*a)))==mean(p,a,deriv(mon(n),p-1)) for n in range(24))
  checks.append(f'canonical polynomial Stein identity p={p},a={a}')
  P=add(add(mon(p+1),scale(mon(2),2)),[F(7),F(-3)])
  I=primitive(p,a,P);assert deriv(I)==P and mean(p,a,I)==0
  checks.append(f'actual centered primitive algebra p={p},a={a}')
  for r in range(p+2):
   recovered=deriv(P,r)
   for _ in range(r):recovered=primitive(p,a,recovered)
   tail=list(P)
   for n in range(r):tail=add(tail,scale(appell(p,a,n),-coordinate(p,a,n,P)))
   assert recovered==tail
  checks.append(f'all selected derivative-primitive tails p={p},a={a}')
  assert coordinate(p,a,1,mon(p+1))==(p+1)*fac(p)*a
  checks.append(f'nonzero missing low coordinate p={p},a={a}')
print(json.dumps(dict(status='PASS',count=len(checks),checks=checks,arithmetic='exact rational polynomial coefficients and exact pure-order signed moments',scope='Finite algebra checks for orders 2,4,6,8 at four nonzero parameters. Actual Schwartz density integrability and unrestricted polynomial theorems are proved in the manuscript, not certified by these finite checks.')))
