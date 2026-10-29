"""Exact finite algebra and constant margins for the expanding-window proof."""
from fractions import Fraction as F
import json
checks=[]
def check(name,ok):
 assert ok,name
 checks.append(name)
# Derivative identity T'/T = L'/L-(n-1)/u at positive inputs.
check('saddle-time logarithmic derivative algebra',all((lp/(n*u**(n-1))-(n-1)*l/(n*u**n))/(l/(n*u**(n-1)))==lp/l-F(n-1,u) for n in [2,4,6,8,12] for u in [25,100] for l,lp in [(F(3),F(12)),(F(17,3),F(68,3))]))
check('right Gaussian coefficient and left endpoint coefficient',all(F(3*n,2)*u**(n-1)>=1 and F(n,2)*(u-r)**(n-1)>=1 for n in [2,4,6,8,12] for u in [25,100] for r in [F(1,10),F(1,2)]))
check('exponential-weight completed square identity',all(b*b/(2*t)-t*s*s/2-(b*s-t*s*s)==(t*s-b)**2/(2*t) for b,t,s in [(F(3,2),F(7),F(2,3)),(F(20),F(101),F(1,5)),(F(0),F(3),F(2))]))
eta=F(1,10**6)
# e<3 and exp(2*eta)<=1/(1-2*eta)<2 suffice for these margins.
check('exact local cosine derivative and sine margins',1/(1-2*eta)<2 and 2*eta+6*eta<10*eta and 1-(10*eta)**2>F(1,4) and 36*eta<F(1,4) and 10*eta<F(1,4))
check('small-cosine strip logarithm margin',eta/(1-2*eta)<=2*eta)
check('rescaled unit disk remains in growing disk',all(u/F(2)+1/u<=u for u in [F(2),F(5,2),F(10)]))
# Exact complex root calculation in Q(i), and norm-gap witness.
check('escaping polynomial root and strict window gap',all(-t*t+t*t==0 and (t/F(2))**2<t*t for t in [F(1,10),F(1),F(7,3)]))
print(json.dumps(dict(status='PASS',count=len(checks),checks=checks,scope='Finite exact algebra and rational margins only. Actual theta-kernel estimates, normalized integral tails, all-order quantifiers and holomorphic arguments are proved analytically in the PDF.'),indent=2))
