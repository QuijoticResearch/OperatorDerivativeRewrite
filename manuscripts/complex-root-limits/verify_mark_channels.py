"""Exact complex-rational finite mark reconstruction and energy checks."""
from fractions import Fraction as F
import json
class C:
    def __init__(self,r=0,i=0):self.r=F(r);self.i=F(i)
    def __add__(self,z):
        z=c(z);return C(self.r+z.r,self.i+z.i)
    __radd__=__add__
    def __neg__(self):return C(-self.r,-self.i)
    def __sub__(self,z):return self+-c(z)
    def __rsub__(self,z):return c(z)+-self
    def __mul__(self,z):
        z=c(z);return C(self.r*z.r-self.i*z.i,self.r*z.i+self.i*z.r)
    __rmul__=__mul__
    def __truediv__(self,r):return C(self.r/F(r),self.i/F(r))
    def __pow__(self,n):
        out=C(1)
        for _ in range(n):out=out*self
        return out
    def conj(self):return C(self.r,-self.i)
    def norm2(self):return self.r*self.r+self.i*self.i
    def __eq__(self,z):z=c(z);return self.r==z.r and self.i==z.i
    def __repr__(self):return str((self.r,self.i))
def c(z):return z if isinstance(z,C) else C(z)
def mean(xs):return sum(xs,C())/len(xs)
checks={}
def check(label,left,right):assert left==right,(label,left,right);checks[label]='PASS'
for a in [F(-2),F(1,3),F(1)]:
    roots=[a*C(1,1),a*C(-1,1),a*C(-1,-1),a*C(1,-1)]
    w={r:(2*a*a)**r for r in range(1,4)};q=-4*a**4
    prefix=str(a)
    for r in range(1,5):check(f'{prefix} moment {r}',mean([z**r for z in roots]),q if r==4 else 0)
    for r in range(1,4):
        for s in range(1,4):check(f'{prefix} Gram {r},{s}',mean([z**r*(z**s).conj() for z in roots]),w[r] if r==s else 0)
    def coefficients(g):return {r:mean([g[k]*(roots[k]**r).conj() for k in range(4)])/w[r] for r in range(1,4)}
    for j in range(4):
        g=[C(int(j==k)) for k in range(4)];u=coefficients(g)
        for k in range(4):check(f'{prefix} basis {j} reconstruction {k}',g[k]-mean(g),sum((u[r]*roots[k]**r for r in range(1,4)),C()))
        for r in range(1,4):check(f'{prefix} basis {j} complementary coefficient {r}',u[r],mean([g[k]*roots[k]**(4-r) for k in range(4)])/q)
    # A genuine two-prefix nonlinear complex terminal table.
    table=[[C(3*k*k+(k+1)*(l-2),l-k*l*l) for l in range(4)] for k in range(4)]
    rowmeans=[mean(row) for row in table];total=mean(rowmeans)
    u0=coefficients(rowmeans);u1=[coefficients(row) for row in table]
    for k in range(4):
        for l in range(4):
            integral=sum((u0[r]*roots[k]**r+u1[k][r]*roots[l]**r for r in range(1,4)),C())
            check(f'{prefix} two-prefix terminal {k},{l}',integral,table[k][l]-total)
    terminal_energy=sum((table[k][l]-total).norm2() for k in range(4) for l in range(4))/16
    coefficient_energy=sum(w[r]*u0[r].norm2() for r in range(1,4))+sum(w[r]*u1[k][r].norm2() for k in range(4) for r in range(1,4))/4
    check(f'{prefix} two-prefix Ito energy',terminal_energy,coefficient_energy)
    check(f'{prefix} all centered mark channels have zero mean',mean([sum((C(r,1-r)*z**r for r in range(1,4)),C()) for z in roots]),0)
print(json.dumps(dict(status='PASS',check_count=len(checks),checks=checks,arithmetic='Exact complex rational arithmetic; three nonzero rational amplitudes, every four-point basis function and a full two-prefix terminal table',scope='Finite source transcription, conjugation, complementary powers, telescoping and positive energy. Not a proof of infinite completion, conditional residual life or continuous-time martingale claims.')))
