"""Exact elementary-plaquette moments and polynomial remainder in the actual 32-state model."""
import sys
sys.dont_write_bytecode=True
import contextlib,io,json
from fractions import Fraction as F
from math import comb
capture=io.StringIO()
with contextlib.redirect_stdout(capture):
 import verify_homogeneous_z2 as z
retained=json.loads(capture.getvalue());assert retained['status']=='PASS' and retained['count']==16
add=z.poly_add;scale=z.poly_scale

def trim(a):
 a=list(a)
 while a and not a[-1]:a.pop()
 return a

def mul(a,b):
 if not a or not b:return []
 c=[F(0)]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):c[i+j]+=x*y
 return trim(c)

def sub(a,b):return trim(add(a,scale(b,-1)))

def rem(a,b):
 a=trim(a);b=trim(b)
 while len(a)>=len(b):a=sub(a,[F(0)]*(len(a)-len(b))+scale(b,a[-1]/b[-1]))
 return a

def sum_poly(arr):
 a=[]
 for b in arr:a=add(a,b)
 return trim(a)
checks=[]
def check(name,v):
 assert v,name
 checks.append(name)
score=[F([4,0,0,-4][z.o(i)]) for i in range(32)]
check('literal bare centered score',sum(score)==0)
check('literal bare score variance four',sum(x*x for x in score)/32==4)
check('all bare plaquette-sum eigen equations',all(sum(z.K(i,j)*score[j] for j in range(32))==score[i]/16 for i in range(32)))
V=z.v;V2=[mul(a,a) for a in V];Z=sum_poly(scale(a,b) for a,b in zip(V2,[1,4,2,1]))
C=sum_poly([scale(V2[0],F(3177,2048)),scale(mul(V[0],V[3]),F(-450,2048)),scale(V2[3],F(353,18432))])
g=[V[z.o(i)] for i in range(32)]
check('actual full stationary normalizer polynomial',sum_poly(mul(a,a) for a in g)==scale(Z,4))
check('actual full score mean numerator polynomial',sum_poly(scale(mul(g[i],g[i]),score[i]) for i in range(32))==scale(sub(V2[0],V2[3]),16))
check('actual full score second-moment numerator polynomial',sum_poly(scale(mul(g[i],g[i]),score[i]**2) for i in range(32))==scale(add(V2[0],V2[3]),64))
check('all 1024 transfer terms give the exact lag numerator',sum_poly(scale(mul(g[i],g[j]),score[i]*z.T(i,j)*score[j]) for i in range(32) for j in range(32))==scale(C,64))
D=sub(sub(scale(mul(Z,C),256),scale([F(0)]+mul(Z,add(V2[0],V2[3])),16)),scale([F(0)]+mul(sub(V2[0],V2[3]),sub(V2[0],V2[3])),240))
R=scale(list(map(F,[-3243610334169528005827,1953654217580403423644027,-101506400370404313095928928,452893609599424244451318528])),F(73153125,65536))
check('exact Euclidean polynomial remainder',rem(D,z.P)==R)
r=[sum(c*comb(i,k)*2**(i-k) for i,c in enumerate(R) if i>=k)/F(73153125,65536) for k in range(4)]
check('exact positive shifted remainder coefficients',r==list(map(F,[3221027340138603340546114739,5030651367929054084455750651,2615855257226141153611982240,452893609599424244451318528])) and all(c>0 for c in r))
print(json.dumps(dict(status='PASS',count=len(checks),retained_homogeneous_groups=16,checks=checks,arithmetic='Exact rational arrays, all finite microscopic quotient rows and Euclidean polynomial division',scope='Checks the actual centered elementary-plaquette covariance certificate. Root existence, centering, positivity and the variational scope are proved in the manuscript.')))
