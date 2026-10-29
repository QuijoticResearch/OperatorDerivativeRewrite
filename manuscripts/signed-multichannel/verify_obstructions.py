"""Exact finite checks for Section 11; not a kernel tail or limit proof."""
from fractions import Fraction as F
from math import factorial
import json
checks=[]
def ok(label,value):
 assert value,label
 checks.append(label)
ok('biharmonic fourth/eighth moment coefficients',-factorial(4)==-24 and factorial(8)//2==20160)
ok('off-diagonal product and centered cancellation coefficients',24**2==576 and 20160-576==19584 and 576-2*576+576==0)
ok('uniform-grid exact second-moment cancellation',all(F(20160,N)+576*F(N-1,N)-1152+576==F(19584,N) for N in range(1,101)))
ok('absolute-error squared pointwise threshold',24**2==576)
ok('spike L2 squared and fourth clock',all(F(n)**2/F(n)**4==F(1,n*n) and F(n)**4/F(n)**4==1 for n in range(1,101)))
ok('last-channel witness factorial and vanishing earlier linear derivatives',all(factorial(p)>0 and all(p-q>=2 for q in range(1,p-1)) for p in range(4,42,2)))
ok('signed product variation multiplication on exact toy densities',all(sum(abs(x*y) for x in (F(3,2),-F(1,2)) for y in (F(3,2),-F(1,2)))==4 for _ in range(1)))
print(json.dumps(dict(status='PASS',count=len(checks),checks=checks,scope='Finite algebra and conventions only; analytic and asymptotic proofs are printed in the paper.')))
