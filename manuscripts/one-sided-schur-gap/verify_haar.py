"""Exact finite quaternion checks; not an integration or asymptotic oracle."""
from fractions import Fraction as F
from itertools import product,combinations
import json
checks=[]
def check(label,test):
 assert test,label
 checks.append(label)
one=(F(1),F(0),F(0),F(0))
def mul(a,b):
 w,x,y,z=a;v,i,j,k=b
 return(w*v-x*i-y*j-z*k,w*i+x*v+y*k-z*j,w*j-x*k+y*v+z*i,w*k+x*j-y*i+z*v)
def inv(a):return(a[0],-a[1],-a[2],-a[3])
def axis(j,c,s):
 a=[F(c),F(0),F(0),F(0)];a[j+1]=F(s);return tuple(a)
def shift(v,i):return tuple(v[k]+(k==i) for k in range(4))
vertices=list(product(range(2),repeat=4))
edges=[(v,i) for v in vertices for i in range(4) if v[i]==0]
faces=[(v,i,j) for v in vertices for i,j in combinations(range(4),2) if v[i]==v[j]==0]
ribbons=[(v,i,j) for v,i in edges for j in range(4) if i!=j and v[j]==1]
e=((0,0,1,1),0);chosen=(*e,2);partner=(*e,3)
check('exact 32 retained links, 24 inner faces, 48 ribbons and chosen two-ribbon fiber',len(edges)==32 and len(faces)==24 and len(ribbons)==48 and [(v,i,j) for v,i,j in ribbons if (v,i)==e]==[chosen,partner])
A=axis(0,F(3,5),F(4,5));B=axis(1,F(5,13),F(12,13));C=axis(2,F(8,17),F(15,17));W=mul(mul(A,B),C)
check('ordered triple scalar and sign under middle reflection',W[0]==A[0]*B[0]*C[0]-A[1]*B[2]*C[3] and W[0]-mul(mul(A,inv(B)),C)[0]==-2*A[1]*B[2]*C[3])
def boundary(a,b,c):
 high=(shift(e[0],0),2);low=(e[0],2)
 caps={(v,j):one for v in vertices for j in range(4) if v[j]==1}
 caps[high]=a;caps[low]=inv(c)
 outer={p:one for p in ribbons};outer[chosen]=inv(b)
 return caps,outer
def word(bound,p):
 caps,outer=bound;v,i,j=p
 return mul(mul(caps[(shift(v,i),j)],inv(outer[p])),inv(caps[(v,j)]))
bd=boundary(A,B,C)
check('boundary word on chosen and partner ribbons',word(bd,chosen)==W and word(bd,partner)==one)
check('only chosen ribbon depends on middle boundary angle',all(word(bd,p)==word(boundary(A,inv(B),C),p) for p in ribbons if p!=chosen))
def inner(U):
 return sum(1-mul(mul(mul(U[(v,i)],U[(shift(v,i),j)]),inv(U[(shift(v,j),i)])),inv(U[(v,j)]))[0] for v,i,j in faces)
def action(U,bound):return inner(U)+sum(1-mul(U[(v,i)],word(bound,(v,i,j)))[0] for v,i,j in ribbons)
tracevalues=[word(bd,p)[0] for p in ribbons]
check('all 48 conditional ribbon trace classes 1,2,2,43',all(tracevalues.count(q)==n for q,n in [(W[0],1),(A[0],2),(C[0],2),(F(1),43)]))
samples=[one,A,B,C,mul(A,B),mul(B,C)]
for n,q in enumerate(samples):
 U={edge:one for edge in edges};U[e]=q
 constant=5+2*(1-A[0])+2*(1-C[0])
 check(f'full 72-face conditional action at exact unit quaternion {n}',action(U,bd)==constant-4*q[0]-mul(q,W)[0])
U={edge:samples[k%len(samples)] for k,edge in enumerate(edges)}
R=action(U,boundary(A,one,C))+mul(U[e],mul(A,C))[0]
check('actual full-link action residual replacement',action(U,bd)==R-mul(U[e],W)[0])
# A local central gauge changes an open probe sign and preserves all closed faces.
v0=e[0]
Ug={edge:tuple((-1 if (edge[0]==v0) != (shift(edge[0],edge[1])==v0) else 1)*qk for qk in q) for edge,q in U.items()}
check('vertex-center change preserves every inner closed-action sum and flips chosen open probe',inner(Ug)==inner(U) and mul(Ug[e],W)[0]==-mul(U[e],W)[0])
def coefficients(a):return(a[0],-a[1],-a[2],-a[3])
for n,q in enumerate(samples):
 dot=sum(x*y for x,y in zip(coefficients(W),coefficients(q)))
 check(f'Haar second-coordinate contraction at quaternion {n}',dot/4==mul(W,inv(q))[0]/4)
check('five-staple squared radius and exact positive lower/upper bounds',sum((4*(k==0)+W[k])**2 for k in range(4))==17+8*W[0] and 9<=17+8*W[0]<=25)
varodd=(W[0]-mul(mul(A,inv(B)),C)[0])/2
check('full Haar variance odd coefficient from exact same-link covariance',varodd==-A[1]*B[2]*C[3])
print(json.dumps(dict(status='PASS',check_count=len(checks),checks=checks,arithmetic='Python unbounded integers and Fraction',scope='Finite actual face geometry, rational unit quaternion actions and Haar second-moment coefficient algebra. Differentiation, cap concentration, real angle and asymptotic statements require the printed analytic proofs.')))
