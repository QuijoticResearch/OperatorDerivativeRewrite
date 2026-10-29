"""Exact independent geometry and integer-certificate checks.

Run with Python's standard library. All arithmetic is integer/Fraction;
no floating eigenvalue, external CAS, Lean build or research mutation is used.
"""
from pathlib import Path
from itertools import product,combinations
from fractions import Fraction as F
import hashlib,json,time
start=time.monotonic();path=Path(__file__).with_name('certificate-data.json')
payload=json.loads(path.read_text(encoding='utf-8'));d=payload['data'];checks=[]
def freeze(x):return tuple(map(freeze,x)) if isinstance(x,list) else x
def shift(v,i):return tuple(x+int(j==i) for j,x in enumerate(v))
def face_edges(p):
 v,(i,j)=p
 return [(v,i),(shift(v,i),j),(shift(v,j),i),(v,j)]
vertices=list(product(range(2),repeat=4))
inside={(v,i) for v in vertices for i in range(4) if v[i]==0}
faces=[]
for v in product(range(3),repeat=4):
 for i,j in combinations(range(4),2):
  if v[i]<2 and v[j]<2 and any(e in inside for e in face_edges((v,(i,j)))):faces.append((v,(i,j)))
all_edges={e for p in faces for e in face_edges(p)}
outside=all_edges-inside
all_vertices={v for v,i in all_edges}|{shift(v,i) for v,i in all_edges}
I=list(map(freeze,d['interiorPoint']));B=list(map(freeze,d['edgeData']));P=list(map(freeze,d['sourceFaceData']))
assert len(I)==len(inside)==32 and set(I)==inside
assert len(B)==len(outside)==80 and set(B)==outside
assert len(P)==len(faces)==72 and set(P)==set(faces) and len(all_vertices)==48
checks.append('source geometry rebuilt from all incident plaquettes: 48 vertices, 32 interior/80 boundary edges, 72 faces')
A=d['Adata'];bmat=d['Bdata'];C=d['cycleData'];n=34;D=d['denominator'];X=d['Xnum'];R=d['Rnum'];H=d['Hdata'];Q=d['Qdata'];T=d['Tdata'];V=d['Vdata'];w=d['weights'];scale=d['scale']
assert all(len(M)==rows and all(len(row)==cols for row in M) for M,rows,cols in [(A,72,32),(bmat,72,80),(C,80,34),(X,32,34),(R,72,34),(H,34,34),(Q,34,34),(T,34,34),(V,34,34)])
imap={e:i for i,e in enumerate(I)};bmap={e:i for i,e in enumerate(B)}
for r,p in enumerate(P):
 aa=[0]*32;bb=[0]*80
 for sgn,e in zip([1,1,-1,-1],face_edges(p)):
  if e in imap:aa[imap[e]]+=sgn
  else:bb[bmap[e]]+=sgn
 assert aa==A[r] and bb==bmat[r]
assert set(d['signData'])<={-1,1}
checks.append('all integer incidence rows match geometric oriented plaquette curls')
vertex_index={0:(0,0,0,0)}
for k,(v,i) in enumerate(B):
 for idx,value in [(d['sourceIndex'][k],v),(d['targetIndex'][k],shift(v,i))]:
  if idx in vertex_index:assert vertex_index[idx]==value
  vertex_index[idx]=value
assert len(vertex_index)==48 and set(vertex_index.values())==all_vertices
G=[[int(v==d['targetIndex'][k])-int(v==d['sourceIndex'][k]) for v in range(48)] for k in range(80)]
assert all(sum(C[k][j]*G[k][v] for k in range(80))==0 for j in range(n) for v in range(48))
assert len(set(d['chord']))==n and all(C[d['chord'][i]][j]==int(i==j) for i in range(n) for j in range(n))
checks.append('actual boundary-gradient balance and identity chord minor for 34 independent cycles')
assert D==193028 and D>0
assert all(sum(A[r][i]*X[i][j] for i in range(32))+D*sum(bmat[r][k]*C[k][j] for k in range(80))==R[r][j] for r in range(72) for j in range(n))
assert all(sum(A[r][i]*R[r][j] for r in range(72))==0 for i in range(32) for j in range(n))
checks.append('full unpinned response and original normal equations over integers')
assert all(sum(C[k][i]*C[k][j] for k in range(80))==H[i][j] for i in range(n) for j in range(n))
assert all(sum(R[k][i]*R[k][j] for k in range(72))==D*Q[i][j] for i in range(n) for j in range(n))
checks.append('metric and residual Gram identities, retaining physical boundary norm')
assert all(T[i][j]==25000*Q[i][j]-69639*48257*H[i][j] for i in range(n) for j in range(n))
assert scale>0 and len(w)==n and all(x>0 for x in w)
assert all(scale*T[i][j]==sum(V[i][k]*w[k]*V[j][k] for k in range(n)) for i in range(n) for j in range(n))
checks.append('all 1156 positive weighted-Gram identities for corrected rational gap, exact huge integers')
z=d['z'];norm=sum(z[i]*H[i][j]*z[j] for i in range(n) for j in range(n));energy_num=sum(z[i]*Q[i][j]*z[j] for i in range(n) for j in range(n))
assert norm==117410484 and energy_num==15782847719760
quotient=F(energy_num,D*norm)
assert quotient==F(729067245,1046910149)
assert F(69639,100000)<=quotient<F(1741,2500)
checks.append('nonzero physical witness brackets rational gap below rounded 0.6964')
def tshift(v,i):return tuple((x+int(j==i))%4 for j,x in enumerate(v))
def potential(v):return int(v[0] in (1,2))
def grad(v,i):return potential(tshift(v,i))-potential(v)
torus=list(product(range(4),repeat=4))
norm_periodic=0
for v in torus:
 for i in range(4):
  a=grad(v,i);norm_periodic+=a*a
  if a:assert tuple(x//2 for x in v)==tuple(x//2 for x in tshift(v,i))
 for i,j in combinations(range(4),2):assert grad(v,i)+grad(tshift(v,i),j)-grad(tshift(v,j),i)-grad(v,j)==0
assert norm_periodic==128
checks.append('actual periodic all-block interior gauge has norm squared 128 and every plaquette curl zero')
def schur(a,b,c):return a-b*b/c
assert schur(F(2),F(1),F(1))==1 and schur(F(2),F(11,10),F(1))==F(79,100)>0
assert F(79,100)<1-4*F(1,10)**2
checks.append('positive 2x2 blocks defeat the proposed purely quadratic arbitrary-coupling perturbation loss')
print(json.dumps(dict(status='PASS',count=len(checks),checks=checks,rayleigh=str(quotient),certificate_sha256=hashlib.sha256(path.read_text(encoding='utf-8').encode('utf-8')).hexdigest(),wall_seconds=time.monotonic()-start,arithmetic='Unbounded Python integers and Fraction only',scope='Exact finite geometry and arithmetic certificate; no nonlinear gauge or continuum identification.')))
