"""Exact rational polynomial and Laurent checks for Gaussian likelihood transcription."""
from fractions import Fraction as F
import json
N=8  # Gaussian x,y; independent symbolic matrix entries a,b,c,d,e,f.
ZERO=(0,)*N
class P(dict):
    def __add__(self,other):
        other=poly(other);out=P(self)
        for k,v in other.items():out[k]=out.get(k,F(0))+v
        return P({k:v for k,v in out.items() if v})
    __radd__=__add__
    def __neg__(self):return P({k:-v for k,v in self.items()})
    def __sub__(self,other):return self+-poly(other)
    def __rsub__(self,other):return poly(other)+-self
    def __mul__(self,other):
        out=P()
        for k,v in self.items():
            for l,w in poly(other).items():
                q=tuple(a+b for a,b in zip(k,l));out[q]=out.get(q,F(0))+v*w
        return P({k:v for k,v in out.items() if v})
    __rmul__=__mul__
    def __pow__(self,n):
        out=poly(1)
        for _ in range(n):out=out*self
        return out
def poly(value):return value if isinstance(value,P) else P({ZERO:F(value)}) if value else P()
def var(i):return P({tuple(int(j==i) for j in range(N)):F(1)})
def moment(k):
    if k%2:return 0
    out=1
    for j in range(1,k,2):out*=j
    return out
def mean(p):
    out=P()
    for k,v in p.items():
        q=(0,0)+k[2:];out=out+P({q:v*moment(k[0])*moment(k[1])})
    return P({k:v for k,v in out.items() if v})

def deriv(p,i):
    out=P()
    for k,v in p.items():
        if k[i]:
            j=list(k);j[i]-=1
            out=out+P({tuple(j):v*k[i]})
    return out

def substitute(p,values):
    out=P()
    for k,v in p.items():
        term=poly(v)
        for i,power in enumerate(k):
            assert power>=0
            term=term*values.get(i,var(i))**power
        out=out+term
    return out


def integrate_coordinate(p,i,variance):
    out=P()
    for k,v in p.items():
        if k[i]%2:continue
        j=list(k);j[i]=0
        out=out+P({tuple(j):v*moment(k[i])})*variance**(k[i]//2)
    return out
if __name__=='__main__':
    x,y,h,L,n,M,T,H=[var(i) for i in range(N)]
    invL=P({(0,0,0,-1,0,0,0,0):F(1)})
    invn=P({(0,0,0,0,-1,0,0,0):F(1)})
    v=h-h*h*invL;a=h*invL
    Q=(a*x+y)**2-h
    prediction=a*a*(x*x-L)
    centered=y*y-h
    errors={
      'bridge exact conditional square':integrate_coordinate(Q,1,v)-prediction,
      'projected square energy':integrate_coordinate(prediction**2,0,L)-2*h**4*invL**2,
      'native square variance':integrate_coordinate(centered**2,1,h)-2*h*h,
      'counterexample coefficient energy':integrate_coordinate((n*(y*y-invn))**2,1,invn)-2,
      'counterexample actual mean':n*integrate_coordinate(n*(y*y-invn)**2,1,invn)-2,
      'uniform mean harmonic factor':2*M*(T*invn)*H-2*M*T*H*invn,
      'cross-row harmonic energy':4*T*T*invn+2*(2*(2*T)*T*H*invn)-(4*T*T*invn+8*T*T*H*invn),
    }
    for name,p in errors.items():assert not p,(name,p)
    print(json.dumps(dict(status='PASS',check_count=len(errors),checks={k:len(v) for k,v in errors.items()},arithmetic='Exact rational polynomial and Laurent Gaussian moments',scope='Finite bridge, variance, counterexample and row-factor transcription; no proof of sigma-algebra identification or limiting L2 convergence.')))
