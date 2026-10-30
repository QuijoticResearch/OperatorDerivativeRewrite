"""Full exact 4^4-to-2^4 periodic lattice witness; no floating matrix inverse."""
from fractions import Fraction as F
from itertools import product,combinations
import json
V=list(product(range(4),repeat=4));CV=list(product(range(2),repeat=4));bits=list(product(range(2),repeat=4))
edges=[(v,i) for v in V for i in range(4)];faces=[(v,i,j) for v in V for i,j in combinations(range(4),2)]
def shift(v,i,n=4,delta=1):return tuple((x+delta)%n if k==i else x for k,x in enumerate(v))
def field(fn):return {e:F(fn(*e)) for e in edges}
def add(a,b,ca=F(1),cb=F(1)):return {e:ca*a[e]+cb*b[e] for e in edges}
def scale(a,c):return {e:c*a[e] for e in edges}
def dot(a,b):return sum(a[e]*b[e] for e in edges)
def curl(a):return {(v,i,j):a[v,i]+a[shift(v,i),j]-a[shift(v,j),i]-a[v,j] for v,i,j in faces}
def gram(a):
 out={e:F(0) for e in edges}
 for (v,i,j),x in curl(a).items():
  for e,sg in [((v,i),1),((shift(v,i),j),1),((shift(v,j),i),-1),((v,j),-1)]:out[e]+=sg*x
 return out
def energy(a):return sum(x*x for x in curl(a).values())
def average(a):return {(q,i):sum(a[tuple(2*q[k]+b[k] for k in range(4)),i] for b in bits if b[i]==1)/8 for q in CV for i in range(4)}
def phi(v):return (-1)**v[0]*(-1)**(v[1]//2)
d=field(lambda v,i:phi(shift(v,i))-phi(v));c=average(d)
a=field(lambda v,i:F((-1)**(v[1]//2),8) if i==0 else 0)
p=field(lambda v,i:F((-1)**(v[1]//2)*(3-(-1)**v[0]),24) if i==0 else -F((-1)**v[0]*((-1)**(shift(v,1)[1]//2)-(-1)**(v[1]//2)),24) if i==1 else 0)
astar=field(lambda v,i:c[tuple(k//2 for k in v),i]/8 if v[i]%2==1 else 0)
z=add(p,a,F(1,6),F(1,3));j=scale(p,F(12));h=scale(z,F(144,5));r=add(p,a,F(36),F(-48))
checks=[]
def check(name,value):
 assert value,name
 checks.append(name)
check('all actual vertices edges and oriented plaquettes',len(V)==256 and len(edges)==1024 and len(faces)==1536 and len(c)==64)
check('fine gradient has all plaquette curls zero',all(x==0 for x in curl(d).values()))
check('raw average and nonzero coarse curl',all(c[q,i]==(2*(-1)**q[1] if i==0 else 0) for q in CV for i in range(4)) and c[(0,0,0,0),0]-c[(0,1,0,0),0]==4)
check('exact adjoint-minus-gradient realization',p==add(astar,d,F(1),-F(1,24)))
check('all fine planar curls of a',all(x==(F((-1)**(v[1]//2),4) if (i,j)==(0,1) and v[1]%2 else 0) for (v,i,j),x in curl(a).items()))
check('all fine planar curls of p',all(x==(F((-1)**(v[1]//2),2) if (i,j)==(0,1) and v[0]%2 and v[1]%2 else 0) for (v,i,j),x in curl(p).items()))
check('full sparse incidence Gram of a and p',gram(a)==scale(a,2) and gram(p)==add(p,a,F(6),F(-4)))
check('exact full averaged fields',all(average(a)[q,i]==c[q,i]/16 and average(p)[q,i]==c[q,i]/12 and average(z)[q,i]==F(5,144)*c[q,i] for q in CV for i in range(4)))
check('actual coarse norm and fine dot products',sum(x*x for x in c.values())==64 and dot(a,a)==4 and dot(p,p)==F(16,3) and dot(p,a)==4 and energy(p)==16)
check('actual Green witness and norm',gram(z)==p and dot(z,z)==F(28,27) and dot(z,p)==energy(z)==F(20,9))
check('two feasible distinct lifts',average(j)==average(h)==c and j!=h)
check('exact norm-energy tradeoff',dot(j,j)==768 and dot(h,h)==F(21504,25) and energy(j)==2304 and energy(h)==F(9216,5))
check('unrestricted right inverse norm',average(scale(astar,F(8)))==c and dot(scale(astar,F(8)),scale(astar,F(8)))==512)
check('feasible constrained gradient residual',all(x==0 for x in average(r).values()) and gram(j)==add(r,p,F(1),F(36)) and dot(r,r)==2304 and energy(r)==11520)
check('optimal feasible step reaches actual minimizer',add(j,r,F(1),-F(1,5))==h and dot(r,r)/energy(r)==F(1,5))
check('exact line energy for nine rational steps',all(energy(add(j,r,F(1),-alpha))==2304-4608*alpha+11520*alpha*alpha for alpha in [F(k,5) for k in range(-3,6)]))
# Independent incidence enumeration of the three-mask and checkerboard modes.
def sig(v):return (-1)**sum(v[k]//2 for k in range(3))
a3=field(lambda v,i:sig(v) if i==3 else 0)
w3=field(lambda v,i:sig(v) if i==3 and v[3]%2 else 0)
g3=gram(w3);b3=add(g3,a3,F(1),F(-3))
p3=add(a3,b3,F(1,16),F(1,80));z3=add(a3,b3,F(1,96),F(1,800));h3=scale(z3,F(1200,17))
c3={(q,i):F((-1)**sum(q[:3]) if i==3 else 0) for q in CV for i in range(4)}
def div(a):return {v:sum(a[v,i]-a[shift(v,i,delta=-1),i] for i in range(4)) for v in V}
def cg(a):
 out={e:F(0) for e in a}
 for v in CV:
  for i,j in combinations(range(4),2):
   val=a[v,i]+a[shift(v,i,2),j]-a[shift(v,j,2),i]-a[v,j]
   for e,sg in [((v,i),1),((shift(v,i,2),j),1),((shift(v,j,2),i),-1),((v,j),-1)]:out[e]+=sg*val
 return out
check('three-mask coarse size and physical coarse Gram',sum(x*x for x in c3.values())==16 and cg(c3)=={e:12*x for e,x in c3.items()})
check('three-mask full explicit fine Gram formula',all(g3[v,i]==(6*w3[v,i] if i==3 else (-2*sig(v)*(2*(v[3]%2)-1) if v[i]%2 else 0)) for v,i in edges))
check('three-mask orthogonal positive-eigenvalue directions',gram(a3)==scale(a3,6) and gram(b3)==scale(b3,10) and dot(a3,b3)==0)
check('three-mask full fine divergences vanish',all(x==0 for x in div(a3).values()) and all(x==0 for x in div(b3).values()))
check('three-mask all averaged directions',average(a3)==c3 and average(g3)=={e:6*x for e,x in c3.items()} and average(b3)=={e:3*x for e,x in c3.items()})
check('three-mask actual projected and Green identities',gram(p3)==scale(g3,F(1,8)) and gram(z3)==p3)
check('three-mask projection removes a closed fine field',all(x==0 for x in curl(add(p3,w3,F(1),F(-1,8))).values()))
check('three-mask actual compression and compliance',average(p3)=={e:x/10 for e,x in c3.items()} and average(z3)=={e:F(17,1200)*x for e,x in c3.items()})
check('three-mask constrained energy and feasibility',average(h3)==c3 and energy(h3)==F(19200,17) and dot(p3,h3)==16)
check('strict comparison with proposed checkerboard floor',F(17,1200)<F(1,64) and F(19200,17)>64*16)
cc={(q,i):F((-1)**sum(q)*((i==0)-(i==1))) for q in CV for i in range(4)}
ell=field(lambda v,i:cc[tuple(k//2 for k in v),i] if v[i]%2 else 0)
check('checkerboard coarse physicality and norm',cg(cc)=={e:16*x for e,x in cc.items()} and sum(x*x for x in cc.values())==32)
check('checkerboard full fine divergence and Gram',all(x==0 for x in div(ell).values()) and gram(ell)==scale(ell,8))
check('checkerboard actual average and compliance',average(ell)==cc and average(scale(ell,F(1,64)))=={e:x/64 for e,x in cc.items()})
check('checkerboard actual energy minimizing lift',energy(ell)==2048 and dot(ell,ell)==256)
print(json.dumps(dict(status='PASS',count=len(checks),checks=checks,arithmetic='Unbounded rational arithmetic; every one of 1024 edges and 1536 plaquettes',scope='Actual periodic witnesses, exact line energies, full three-mask compliance and checkerboard comparison. Uniqueness and physical-domain arguments use the printed proofs.')))
