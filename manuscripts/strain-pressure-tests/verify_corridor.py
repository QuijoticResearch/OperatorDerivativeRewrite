"""Finite exact checks; measure-limit proofs are in the manuscript."""
from fractions import Fraction as F
from itertools import product
import json
checks=[]
def check(k,v):
 assert v,k
 checks.append(k)
def label(r,w):return 0 if r<0 else 1 if w<0 else 2
check('all ordered-label endpoint indicator cases',all(int(new!=old)<=int(new==0)-int(old==0)+int(old==2)-int(new==2) for old in range(3) for new in range(old+1)))
grid=[F(n,4) for n in range(-4,5)];eps=F(1,4)
check('actual disagreement strip inclusion',all(label(r,w)==label(r+dr,w+dw) or abs(r)<=eps or (r>=0 and abs(w)<=eps) for r,w,dr,dw in product(grid,grid,[-eps,0,eps],[-eps,0,eps])))
check('downward labels monotone and eventual boundary detection on rational grid',all(label(r-eps,w-eps)<=label(r,w) and (label(r-F(1,1024),w-F(1,1024))!=label(r,w))==(r==0 or (r>=0 and w==0)) for r,w in product(grid,grid)))
def energy(p):return [F(1,2)+p,F(1,4)-p/2,F(1,4)-p/2]
check('positive normalized strictly dominant actual sector family',all(sum(energy(p))==1 and min(energy(p))>0 and energy(p)[0]-energy(p)[1]>=F(1,16) and max(energy(p))==F(1,2)+p for p in [F(n,128) for n in range(-16,17)]))
check('uniform energy difference with full threshold-label error',all(max(abs(x-y) for x,y in zip(energy(-F(1,n)),energy(0)))<=F(1,n) and label(max(energy(-F(1,n)))-F(1,2),-1)==0 and label(max(energy(0))-F(1,2),-1)==1 for n in range(8,108)))
check('smooth energies exact kink ratio',all(max(1+t+t*t,1-t+t*t)/(2+2*t*t)==F(1,2)+abs(t)/(2*(1+t*t)) for t in grid))
print(json.dumps(dict(status='PASS',count=len(checks),checks=checks,scope='Finite indicator cases and exact scalar transcriptions only; not a substitute for universal or measure-limit proofs.')))
