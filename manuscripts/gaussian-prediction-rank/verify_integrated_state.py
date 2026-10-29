"""Independent exact integrated-source covariance and regression checks.

Hilbert-span closure, all-terminal-L2 sufficiency and noncompactness require
the manuscript's analytic proofs; they are not inferred from these checks.
"""
from fractions import Fraction as F
import json
checks=[]
def check(label,value):
 assert value,label
 checks.append(label)
def cov(t,r):
 r,t=sorted([r,t])
 # Direct antiderivative of (t-x)(r-x) on the overlapping supports.
 return t*r*r-(t+r)*r*r/2+r*r*r/3
for s in [F(1,2),F(1),F(2),F(3)]:
 for h in [F(0),F(1,2),F(1),F(2)]:
  t=s+h
  check(f'forecast orthogonality on three past probes s={s}, h={h}',all(cov(t,r)==cov(s,r)+h*r*r/2 for r in [F(0),s/3,s]))
  gram=cov(s,s)*s-(s*s/2)**2
  state_error=cov(t,t)-(cov(s,s)+h*s*s+h*h*s)
  scalar_error=cov(t,t)-cov(t,s)**2/cov(s,s)
  check(f'two-state Gram and full/scalar regression errors s={s}, h={h}',gram==s**4/12 and state_error==h**3/3 and scalar_error==s*h*h/4+h**3/3)
for s in [F(1),F(2),F(3)]:
 for a in [F(0),s/3,2*s/3]:
  h=s-a
  # Integrate (x-a)^2/h^2 from a to s using its expanded primitive.
  primitive=lambda x:(x**3/3-a*x*x+a*a*x)/(h*h)
  check(f'backward quotient exact source error a={a}, s={s}',primitive(s)-primitive(a)==h/3)
check('actual times 1,2,3 scalar versus history witness',cov(F(3),F(1))==F(4,3) and cov(F(3),F(2))/cov(F(2),F(2))*cov(F(2),F(1))==F(35,24))
print(json.dumps(dict(status='PASS',count=len(checks),checks=checks,arithmetic='Unbounded integer and Fraction',scope='Exact source covariance integration, two-state Gram, forecast and regression variance algebra, quotient error and actual three-time counterexample. No sampled path or infinite-dimensional conclusion.')))
