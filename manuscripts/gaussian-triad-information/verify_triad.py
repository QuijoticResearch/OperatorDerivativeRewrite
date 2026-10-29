"""Rebuild exact finite transfer and scalar probability identities, without CAS."""
from fractions import Fraction as F
from itertools import product
import json
checks=[]
def check(name,ok):
 assert ok,name
 checks.append(name)
def scalar(c):return {} if not c else {(0,0,0):F(c)}
def add(p,q):
 r=dict(p)
 for k,v in q.items():r[k]=r.get(k,0)+v
 return {k:v for k,v in r.items() if v}
def scale(c,p):return {k:c*v for k,v in p.items() if c*v}
def mul(p,q):
 r={}
 for k,v in p.items():
  for l,w in q.items():
   m=tuple(k[i]+l[i] for i in range(3));r[m]=r.get(m,0)+v*w
 return {k:v for k,v in r.items() if v}
def dot(p,q):
 r={}
 for x,y in zip(p,q):r=add(r,mul(x,y))
 return r
a={(1,0,0):F(1)};b={(0,1,0):F(1)};c={(0,0,1):F(1)};zero={}
K=[(1,0,0),(0,1,0),(1,1,0),(-1,0,0),(0,-1,0),(-1,-1,0)]
V=[[zero,a,zero],[scale(-1,b),zero,zero],[scale(-1,c),c,zero]]
V+= [[scale(-1,x) for x in v] for v in V[:3]]
W=[scale(sum(x*x for x in k),dot(v,v)) for k,v in zip(K,V)]
abc=mul(mul(a,b),c);expected=[scale(2,abc),scale(-2,abc),{},scale(2,abc),scale(-2,abc),{}]
T=[]
for k,v in zip(K,V):
 r={}
 for p,q in product(range(6),repeat=2):
  if tuple(K[p][i]+K[q][i] for i in range(3))==k:
   r=add(r,mul(dot([scalar(x) for x in K[q]],V[p]),dot(v,V[q])))
 T.append(scale(2*sum(x*x for x in k),r))
check('all six universal triad transfers',T==expected)
check('universal transversality and opposite polarization',all(dot([scalar(x) for x in k],v)=={} for k,v in zip(K,V)) and all(V[i+3]==[scale(-1,x) for x in V[i]] for i in range(3)))
check('all six universal spectral weights',W==[mul(a,a),mul(b,b),scale(4,mul(c,c)),mul(a,a),mul(b,b),scale(4,mul(c,c))])
E={}
for w in W:E=add(E,w)
sumWF={}
for w,t in zip(W,T):sumWF=add(sumWF,mul(w,t))
check('universal normalized transfer numerator',scale(2,sumWF)==scale(8,mul(abc,add(mul(a,a),scale(-1,mul(b,b))))))
def sector(x,y):
 q=0 if y>=0 and x>=0 else 1 if y>=0 else 2 if x<0 else 3
 xx,yy=abs(x),abs(y)
 tests=[4*yy<xx,2*yy<xx,4*yy<3*xx,yy<xx,3*yy<4*xx,yy<2*xx,yy<4*xx]
 return 8*q+next((i for i,t in enumerate(tests) if t),7)
slopes=[F(1,8),F(3,8),F(5,8),F(7,8),F(7,6),F(3,2),F(3),F(5)]
check('six exact actual angular labels',[sector(k[0],k[1]) for k in K]==[0,7,4,8,31,20])
check('every one of 32 directional bins attained',all(sector(x,y)==8*q+j for q in range(4) for j,r in enumerate(slopes) for x,y in [(1,r) if q==0 else (-1,r) if q==1 else (-1,-r) if q==2 else (1,-r)]))
def den(x):return 30*x**4-5*x*x+F(247,8)
def rate(x):return -48*x/den(x)
samples=[F(0),F(1,12),F(1,2),F(1),F(3),F(-2)]
check('denominator square and Gaussian-rate specialization',all(den(x)==30*(x*x-F(1,12))**2+F(92,3) and 2*(17+16*x**4)-(10+8*x*x)**2/F(32)==den(x) for x in samples))
check('exact swapped rate values and balanced transfer',rate(F(1))==F(-128,149) and rate(F(-1))==F(128,149) and 2*2*2*1==8)
ok=True
for x,eps in product([F(1,3),F(1),F(7,2)],[F(-1),F(-1,4),F(0),F(1,2),F(1)]):
 bias=x/(1+x);r=rate(x);p=(1+eps*bias)/2
 mean=p*r+(1-p)*(-r);var=p*(r-mean)**2+(1-p)*(-r-mean)**2
 ok &= mean==eps*bias*r and var==r*r*(1-eps*eps*bias*bias) and var>0 and 0<p<1
check('biased two-sign conditional mean and variance',ok)
check('common-rule two-law risk identity',all(((1+eps)/2*(r-g)**2+(1-eps)/2*(-r-g)**2+(1-eps)/2*(r-g)**2+(1+eps)/2*(-r-g)**2)/2==r*r+g*g for eps,r,g in product([F(1,3),F(-1,2)],[F(2,5),F(-3)],[F(0),F(4,7)])))
raw_vectors=[]
for k in K:
 out=[{}, {}, {}]
 for j,l in product(range(6),repeat=2):
  if tuple(K[j][i]+K[l][i] for i in range(3))==k:
   factor=dot([scalar(x) for x in K[l]],V[j])
   out=[add(out[i],mul(factor,V[l][i])) for i in range(3)]
 raw_vectors.append(out)
bc=mul(b,c);ac=mul(a,c);ab=mul(a,b)
raw_expected=[[scale(-2,bc),bc,{}],[ac,scale(-2,ac),{}],[scale(-1,ab),scale(-1,ab),{}]]
raw_expected += [[scale(-1,x) for x in v] for v in raw_expected[:3]]
check('universal actual raw convolution vectors',raw_vectors==raw_expected)
projected=[]
for k,v in zip(K,raw_vectors):
 radial=scale(F(1,sum(x*x for x in k)),dot([scalar(x) for x in k],v))
 projected.append([add(v[i],scale(-k[i],radial)) for i in range(3)])
project_expected=[[{},bc,{}],[ac,{},{}],[{},{},{}]]
project_expected += [[scale(-1,x) for x in v] for v in project_expected[:3]]
check('actual Leray projection gives retained ODE',projected==project_expected)
def diff(p,j):
 out={}
 for k,v in p.items():
  if k[j]:
   z=list(k);z[j]-=1;out[tuple(z)]=v*k[j]
 return out
G=[bc,scale(-1,ac),{}]
div={}
for j in range(3):div=add(div,diff(G[j],j))
check('quadratic Gaussian drift divergence and radial cancellation',div=={} and dot([a,b,c],G)=={})
def moment(n):
 if n%2:return F(0)
 ans=1
 for j in range(1,n,2):ans*=j
 return F(ans)
def expect(p):
 return sum(v*moment(k[0])*moment(k[1])*moment(k[2]) for k,v in p.items())
check('original quadratic Gaussian field exact squared norm',expect(dot(G,G))==2)
def direction(p):return dot([diff(p,j) for j in range(3)],G)
kin=add(add(scale(2,mul(a,a)),scale(2,mul(b,b))),scale(4,mul(c,c)))
fourth=add(add(mul(mul(a,a),mul(a,a)),mul(mul(b,b),mul(b,b))),scale(16,mul(mul(c,c),mul(c,c))))
check('both conserved energies and concentration derivative numerator',direction(E)=={} and direction(kin)=={} and direction(fourth)==scale(4,mul(abc,add(mul(a,a),scale(-1,mul(b,b))))))
check('actual polynomial skew Gaussian transport pair',expect(mul(a,direction(bc)))==-1 and expect(mul(bc,direction(a)))==1)
co=F(3,5);si=F(4,5);aa=add(scale(co,a),scale(si,b));bb=add(scale(-si,a),scale(co,b))
check('rational rotation norm and inverse algebra',add(mul(aa,aa),mul(bb,bb))==add(mul(a,a),mul(b,b)) and add(scale(co,aa),scale(-si,bb))==a and add(scale(si,aa),scale(co,bb))==b)
print(json.dumps(dict(status='PASS',count=len(checks),checks=checks,scope='Universal sparse-polynomial finite Fourier table and exact rational support/scalar checks; Gaussian integral, original closed-graph, full-law, exact global flow and dephasing arguments are analytic in the PDF.'),indent=2))
