"""Independent periodic SU(2) six-staple action diagnostics.

Run from the repository root with Python and NumPy. This checks explicit
matrix words on all 192 spatial links of three actual side-four fields.
It is numerical evidence, not a Lean proof or a conditional covariance bound.
"""
from pathlib import Path
import argparse
import numpy as np,itertools,json
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output',default='.lake/stardust-periodic-six-staple-probe.json')
args=parser.parse_args()
rng=np.random.default_rng(1781)
verts=list(itertools.product(range(4),repeat=3));idx={v:i for i,v in enumerate(verts)}
n=np.array([[idx[tuple((v[k]+(k==j))%4 for k in range(3))] for j in range(3)] for v in verts])
p=np.array([[idx[tuple((v[k]-(k==j))%4 for k in range(3))] for j in range(3)] for v in verts])
eye=np.eye(2,dtype=complex)
def adj(a):return a.conj().swapaxes(-1,-2)
def ht(a):return np.trace(a,axis1=-2,axis2=-1).real/2
def su2(shape):
 q=rng.normal(size=shape+(4,));q/=np.linalg.norm(q,axis=-1)[...,None]
 a,b,c,d=np.moveaxis(q,-1,0)
 return np.stack([a+1j*b,c+1j*d,-c+1j*d,a-1j*b],axis=-1).reshape(shape+(2,2))
def spatial(v):return sum(np.sum(1-ht(v[:,i]@v[n[:,i],j]@adj(v[n[:,j],i])@adj(v[:,j]))) for i in range(3) for j in range(i+1,3))
def temporal(u,v,g):return sum(np.sum(1-ht(u[:,i]@g[n[:,i]]@adj(v[:,i])@adj(g))) for i in range(3))
def central(u,v,w,a,b):return spatial(v)+temporal(u,v,a)+temporal(v,w,b)
rows=[];wrong_max=0.;total=0
for trial in range(3):
 u,v,w=su2((64,3)),su2((64,3)),su2((64,3));a,b=su2((64,)),su2((64,))
 if trial==0:
  u[:]=eye;v[:]=eye;w[:]=eye;a[:]=eye;b[:]=eye
 errors=[];radii=[]
 for x in range(64):
  for i in range(3):
   staples=[]
   for j in range(3):
    if j==i:continue
    staples.append(v[n[x,i],j]@adj(v[n[x,j],i])@adj(v[x,j]))
    xm=p[x,j]
    staples.append(adj(v[n[xm,i],j])@adj(v[xm,i])@v[xm,j])
   left=adj(a[n[x,i]])@adj(u[x,i])@a[x]
   right=b[n[x,i]]@adj(w[x,i])@adj(b[x])
   staples.extend([left,right]);assert len(staples)==6
   s=sum(staples);r=float(np.linalg.norm(s)/np.sqrt(2));assert r<=6+1e-12
   assert np.allclose(adj(s)@s,r*r*eye,atol=1e-11)
   radii.append(r)
   v0=v.copy();v0[x,i]=eye;baseline=central(u,v0,w,a,b)
   for new in su2((2,)):
    va=v.copy();va[x,i]=new
    actual=central(u,va,w,a,b)-baseline
    predicted=ht(s)-ht(new@s)
    errors.append(float(abs(actual-predicted)));assert abs(actual-predicted)<2e-10
    wrong=sum(staples[:-2])+adj(left)+right
    wrong_max=max(wrong_max,float(abs(actual-(ht(wrong)-ht(new@wrong)))))
    total+=1
 rows.append(dict(trial=trial,max_action_difference_error=max(errors),min_staple_radius=min(radii),max_staple_radius=max(radii)))
assert wrong_max>1e-3
out=dict(status='PASS',actual_middle_link_updates=total,actual_edges_per_field=192,fields=3,
 tests=rows,wrong_left_temporal_orientation_detected=wrong_max,
 scope='Deterministic six-staple central-action identity tests on actual side-four periodic SU2 fields, all spatial links and two temporal neighbours. Not a Lean proof, conditional probability construction, ground sample or covariance bound.')
output=Path(args.output)
output.parent.mkdir(parents=True,exist_ok=True)
output.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
