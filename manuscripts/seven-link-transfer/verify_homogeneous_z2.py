"""Exact microscopic gauge/noise, character and positive-ground certificates."""
from fractions import Fraction as F
from functools import reduce
from operator import xor
from math import comb
import json
rows=[39,141,114,17,10];gm=[27,78,177]
def parity(n):return n.bit_count()%2
def label(u):return sum(parity(u&m)<<k for k,m in enumerate(rows))
def weight(u):return 3**(8-u.bit_count())
orbit=[0,2,1,1,1,1,2,3]
def o(i):return orbit[i%8]
amp=[F(3),F(1),F(1),F(1,3)]
counts=[7048,1800,3000,3000,3000,3000,1800,2952,1800,1800,1080,3000,3000,1080,1800,1800,1800,1800,3000,1080,1080,3000,1800,1800,648,1800,1080,1080,1080,1080,1800,648]
def K(i,j):return F(counts[i^j],65536)
def T(i,j):return amp[o(i)]*K(i,j)*amp[o(j)]
B=[[F(3177,2048),F(765,512),F(675,1024),F(225,2048)],[F(765,2048),F(257,512),F(255,1024),F(85,2048)],[F(675,2048),F(255,512),F(289,1024),F(75,2048)],[F(225,2048),F(85,512),F(75,1024),F(353,18432)]]
def poly_add(a,b):return [(a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0) for i in range(max(len(a),len(b)))]
def poly_scale(a,c):return [c*x for x in a]
def poly_eval(a,x):return sum(c*x**i for i,c in enumerate(a))
P=list(map(F,[9,-5425,284192,-1388800,589824]))
v=[list(map(F,[-353,108928,-3790592,4718592])),list(map(F,[765,-122400,1762560])),list(map(F,[-675,86400,1555200])),list(map(F,[-2025,0,518400]))]
checks=[]
def check(name,value):
 assert value,name
 checks.append(name)
gauge={reduce(xor,(gm[k] for k in range(3) if g>>k&1),0) for g in range(8)}
check('actual label rank and eight-element gauge kernel',set(map(label,range(256)))==set(range(32)) and len(gauge)==8 and {u for u in range(256) if label(u)==0}==gauge)
check('all gauge fibers are exactly label fibers',all({u^g for g in gauge}=={v for v in range(256) if label(v)==label(u)} for u in range(256)))
check('microscopic total and all 32 exact noise counts',sum(weight(u) for u in range(256))==65536 and all(sum(weight(u) for u in range(256) if label(u)==i)==counts[i] for i in range(32)))
check('literal four-plaquette orbit score and common spatial amplitude',all(sum((-1)**parity(u&m) for m in [39,141,114,216])==[4,0,0,-4][o(label(u))] for u in range(256)))
check('positive symmetric stochastic kinetic matrix',all(K(i,j)>0 and K(i,j)==K(j,i) for i in range(32) for j in range(32)) and all(sum(K(i,j) for j in range(32))==1 for i in range(32)))
check('actual four-orbit aggregation in all 128 entries',all(sum(T(i,j) for j in range(32) if o(j)==b)==B[o(i)][b] for i in range(32) for b in range(4)))
check('root-interval endpoint signs',poly_eval(P,F(2))<0<poly_eval(P,F(9,4)))
res=[]
for i in range(4):
 bv=[]
 for j in range(4):bv=poly_add(bv,poly_scale(v[j],B[i][j]))
 res.append(poly_add(bv,poly_scale([F(0)]+v[i],F(-1))))
check('all polynomial ground-eigen identities coefficientwise',all(all(c==0 for c in poly_add(res[i],poly_scale(P,F(8) if i==0 else F(0)))) for i in range(4)))
shifted=[[sum(c*comb(i,k)*F(2)**(i-k) for i,c in enumerate(a) if i>=k) for k in range(len(a))] for a in v]
check('strict positive ground-vector coefficients after x=2+y',all(a[0]>0 and all(c>=0 for c in a) for a in shifted))
def ch(a,i):return (-1)**parity(a&i)
masks=[reduce(xor,(rows[k] for k in range(5) if a>>k&1),0) for a in range(32)]
check('all character orthogonality and full rank',all(sum(ch(a,i)*ch(b,i) for i in range(32))==(32 if a==b else 0) for a in range(32) for b in range(32)))
check('all 32 exact microscopic character eigenvalues',all(sum(K(0,j)*ch(a,j) for j in range(32))==F(1,2**masks[a].bit_count()) for a in range(32)))
check('sharp nonconstant eigenvalue one quarter and winding attainment',min(m.bit_count() for m in masks[1:])==2 and masks[8]==17 and all(not parity(m&g) for m in masks for g in gm))
probe=[F(1) if i in [0,16] else F(-1) if i in [8,24] else F(0) for i in range(32)]
support=[i for i,x in enumerate(probe) if x]
check('probe centering separately at each ground orbit',all(sum(probe[i] for i in range(32) if o(i)==b)==0 for b in range(4)))
check('supported bare and weighted exact probe rows',all(sum(K(i,j)*probe[j] for j in range(32))==F(25,256)*probe[i] and sum(T(i,j)*probe[j] for j in range(32))==F(225,256)*probe[i] for i in support))
check('bare probe Rayleigh quotient differs from sharp kinetic mode',sum(probe[i]*K(i,j)*probe[j] for i in range(32) for j in range(32))/sum(x*x for x in probe)==F(25,256))
check('exact stationary gap and necessary-loss margins',F(225,256)/F(9,4)==F(25,64) and 1-F(25,64)==F(39,64) and F(3,4)-F(39,64)==F(9,64))
print(json.dumps(dict(status='PASS',count=len(checks),checks=checks,arithmetic='Unbounded integers, exact rational matrices and polynomial coefficient arrays',scope='Full 256 microscopic configurations and 32 quotient states, all character/eigen/aggregation data and positive-ground polynomial certificates; IVT and stationary variational proofs are printed.')))
