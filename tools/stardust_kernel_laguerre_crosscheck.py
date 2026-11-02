"""Independent differential-polynomial jet check; NOT a sign certificate."""
from pathlib import Path
from decimal import Decimal as D,localcontext
from fractions import Fraction as F
from math import factorial
import json,datetime,time
r=Path(__file__).resolve().parents[1];d=r/'.lake'
from stardust_kernel_laguerre_probe import laguerre,scale,pi,phi
def poly_next(q):
 p=[0]*(len(q)+1)
 for j,a in enumerate(q):p[j]+=(1+4*j)*a;p[j+1]-=4*a
 return p
def eval_poly(q,x):
 a=D(0)
 for c in reversed(q):a=a*x+c
 return a
def coefficient_matrix(n):
 a=[[F(1)]]
 for k in range(n):
  b=[F(0)]*(k+2)
  for j,c in enumerate(a[k]):b[j]+=F(j-2*k,2)*c;b[j+1]+=c/2
  a.append(b)
 return a

def main():
    rows=[];start=time.perf_counter()
    for precision,terms in [(240,18),(360,24)]:
     with localcontext() as ctx:
      ctx.prec=precision;ctx.Emin=-999999999;ctx.Emax=999999999
      p=pi(precision);N=12;A=coefficient_matrix(N);Q=[[0,-3,2]]
      for j in range(N):Q.append(poly_next(Q[-1]))
      for us in ['0.015625','0.03125','0.01']:
       u=D(us);t=u*u;ys=[p*k*k*(4*u).exp() for k in range(1,terms+1)]
       du=[u.exp()*sum((eval_poly(Q[j],y)*(-y).exp() for y in ys),D(0)) for j in range(N+1)]
       a=[sum((D(c.numerator)/D(c.denominator)*u**(j-2*k)*du[j] for j,c in enumerate(A[k]) if c),D(0))/factorial(k) for k in range(N+1)]
       b=phi(t,N,terms,p)
       errors=[abs(x-y)/max(D(1),abs(x),abs(y)) for x,y in zip(a,b)]
       assert max(errors)<D('1e-150'),max(errors)
       values=[]
       for level in range(1,6):
        a=scale(a,D(1)/a[0]);a=laguerre(a);values.append(str(a[0]));assert (a[0]>0)==(level<5)
       row=dict(precision=precision,terms=terms,u=us,t=str(t),independent_method='Exact integer differential polynomial Q_(j+1)=(1-4y)Q_j+4yQ_jprime; rational D_t=(2u)^-1 D_u recurrence; Horner evaluation',maximum_relative_jet_disagreement=str(max(errors)),normalized_laguerre_values=values)
       rows.append(row);print(precision,terms,'t=',t,'jet disagreement',max(errors),'level5',values[-1][:55],flush=True)
    out=dict(time_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),seconds=time.perf_counter()-start,scope='Independent HIGH-PRECISION EXPERIMENT only; not interval arithmetic/Lean certification; t=1/1024 chosen for exact rational sqrt=1/32',rows=rows)
    (d/'stardust-1947-independent-probe.json').write_text(json.dumps(out,indent=2)+'\n')

if __name__=='__main__':
    main()
