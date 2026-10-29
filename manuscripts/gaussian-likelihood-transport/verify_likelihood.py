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

if __name__=='__main__':
    x,y,a,b,t,q,z,r=[var(i) for i in range(N)]
    invq=P({(0,0,0,0,0,-1,0,0):F(1)})
    logk=lambda u,v:-u*v-F(1,2)*u*u
    logr=lambda u,v:-F(1,2)*u*v-F(1,4)*u*u
    errors={
      'tilted Gaussian density square':-F(1,2)*y*y+logk(a,y)+F(1,2)*(y+a)**2,
      'root square exponent':2*logr(a,y)-logk(a,y),
      'root normalization exponent':logr(a,y)+F(1,8)*a*a-logk(F(1,2)*a,y),
      'density second moment exponent':2*logk(a,y)-a*a-logk(2*a,y),
      'root overlap exponent':logr(a,y)+logr(b,y)+F(1,8)*(a-b)**2-logk(F(1,2)*(a+b),y),
      'full energy completed square y':2*x*x+2*x*y+y*y-x*x-(y+x)**2,
      'full energy completed square x':2*x*x+2*x*y+y*y-2*(x+F(1,2)*y)**2-F(1,2)*y*y,
      'late root conditional exponent':logr(x,y)+F(1,8)*x*x*(2-t)-(-F(1,2)*x*y-F(1,8)*t*x*x),
    }
    C=[[poly(1),poly(-1)],[poly(-1),poly(2)]]
    A=[[poly(2),poly(1)],[poly(1),poly(1)]]
    for L,B,label in [(A,C,'precision covariance'),(C,A,'covariance precision')]:
        for i in range(2):
            for j in range(2):errors[f'{label} {i},{j}']=sum((L[i][k]*B[k][j] for k in range(2)),poly(0))-int(i==j)
    logearly=-F(1,2)*x*x*invq
    early_t=-deriv(logearly,5)+F(1,2)*invq
    early_x=deriv(logearly,0)
    errors['early backward heat equation']=early_t+F(1,2)*(deriv(early_x,0)+early_x*early_x)
    errors['early coefficient logarithmic derivative']=early_x+x*invq
    loglate=-F(1,2)*x*y-F(1,8)*t*x*x
    late_y=deriv(loglate,1)
    errors['late backward heat equation']=deriv(loglate,4)+F(1,2)*(deriv(late_y,1)+late_y*late_y)
    errors['late coefficient logarithmic derivative']=late_y+F(1,2)*x
    errors['late boundary at one']=substitute(loglate,{1:poly(0),4:poly(1)})+F(1,8)*x*x
    errors['late boundary at two']=substitute(loglate,{4:poly(2)})-logr(x,y)
    errors['full energy split']=poly(F(1,5))-(1-r)-(r-F(4,5))
    for label,p in errors.items():assert not p,(label,p)
    print(json.dumps(dict(status='PASS',check_count=len(errors),arithmetic='Exact rational polynomial and Laurent coefficients',checks={k:len(v) for k,v in errors.items()},scope='Finite exponent, precision-matrix, boundary and backward-heat transcription checks. Conditional laws, domain transport, rare-event limits and stochastic integration require the paper proofs.')))
