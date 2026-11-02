"""Exploratory theta-kernel jets; decimal evidence only, never a proof."""
from decimal import Decimal as D, localcontext
from pathlib import Path
import json,time,datetime
r=Path(__file__).resolve().parents[1];out=r/'.lake/stardust-1947-kernel-hierarchy-probe.json'
def pi(precision):
 def atan(q):
  x=D(1)/q;x2=x*x;term=x;s=x;k=1
  while abs(term)>D(10)**(-precision-8):
   term *= -x2;s += term/(2*k+1);k+=1
  return s
 return 16*atan(D(5))-4*atan(D(239))
def add(a,b,n):return [(a[i] if i<len(a) else D(0))+(b[i] if i<len(b) else D(0)) for i in range(n+1)]
def scale(a,c):return [c*x for x in a]
def mul(a,b,n):return [sum((a[k]*b[i-k] for k in range(max(0,i-len(b)+1),min(i,len(a)-1)+1)),D(0)) for i in range(n+1)]
def exp(a,n):
 b=[a[0].exp()]
 for i in range(1,n+1):b.append(sum((k*a[k]*b[i-k] for k in range(1,i+1)),D(0))/i)
 return b
def sqrtvar(t,n):
 a=[t.sqrt()]
 for i in range(1,n+1):a.append(((D(1) if i==1 else D(0))-sum((a[k]*a[i-k] for k in range(1,i)),D(0)))/(2*a[0]))
 return a
def laguerre(a):
 n=len(a)-3;df=[(i+1)*a[i+1] for i in range(len(a)-1)];ddf=[(i+1)*(i+2)*a[i+2] for i in range(len(a)-2)]
 return add(mul(df,df,n),scale(mul(a,ddf,n),D(-1)),n)
def phi(t,n,terms,p):
 a=sqrtvar(t,n);e4=exp(scale(a,D(4)),n);e5=exp(scale(a,D(5)),n);e9=exp(scale(a,D(9)),n);s=[D(0)]*(n+1)
 for k in range(1,terms+1):
  q=p*k*k;pref=add(scale(e9,2*q*q),scale(e5,-3*q),n)
  s=add(s,mul(pref,exp(scale(e4,-q),n),n),n)
 return s

def main():
    start=time.perf_counter();runs=[]
    for precision,terms in [(140,12),(240,18)]:
     with localcontext() as ctx:
      ctx.prec=precision;ctx.Emin=-999999999;ctx.Emax=999999999
      p=pi(precision);n=20
      assert laguerre([D(1),D(0),D(0)])[0]==0
      assert laguerre([D(1),D(1),D(0)])[0]==1
      assert laguerre([D(1),D(0),D(1)])[0]==-2
      # Independent analytic controls: exp(-t^2) has positive log curvature at every iterate.
      control=exp([D(-1),D(-2),D(-1)]+[D(0)]*(n-2),n)
      controls=[]
      for j in range(1,9):
       control=scale(control,D(1)/control[0]);control=laguerre(control);controls.append(str(control[0]));assert control[0]>0
      rows=[]
      for text in ['0.0001','0.001','0.01','0.05','0.1','0.25','0.5','1','2','4','9']:
       a=phi(D(text),n,terms,p);assert a[0]>0;values=[]
       for j in range(1,9):
        a=scale(a,D(1)/a[0]);a=laguerre(a);values.append(dict(level=j,normalized_value=str(a[0]),positive=a[0]>0))
        if a[0]<=0:break
       rows.append(dict(t=text,levels=values))
       print(precision,terms,text,[(x['level'],x['positive'],x['normalized_value'][:20]) for x in values],flush=True)
      runs.append(dict(precision=precision,theta_terms=terms,gaussian_controls=controls,rows=rows))
    data=dict(time_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),seconds=time.perf_counter()-start,scope='UNCERTIFIED decimal Taylor-jet experiment on the ACTUAL theta-series formula Phi(sqrt(t)); not interval arithmetic, not a Lean proof, not an RH criterion',normalization='Each step divides jets by their positive value at the test point before applying L(f)=fprime^2-f*fsecond; sign preserved by positive scale squared.',runs=runs)
    out.write_text(json.dumps(data,indent=2)+'\n');print('Saved',out,'seconds',data['seconds'])

if __name__=='__main__':
    main()
