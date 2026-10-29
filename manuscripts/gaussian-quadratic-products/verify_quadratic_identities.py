"""Exact symbolic Gaussian integration for two arbitrary symmetric 2x2 matrices."""
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
def mm(A,B):return [[sum((A[i][k]*B[k][j] for k in range(2)),poly(0)) for j in range(2)] for i in range(2)]
def hs(A):return sum((q*q for row in A for q in row),poly(0))
def trace(A):return A[0][0]+A[1][1]
def qform(A,x,y):return A[0][0]*(x*x-1)+2*A[0][1]*x*y+A[1][1]*(y*y-1)
if __name__=='__main__':
    x,y,a,b,c,d,e,f=[var(i) for i in range(N)]
    A=[[a,b],[b,c]];B=[[d,e],[e,f]];AB=mm(A,B);BA=mm(B,A)
    S=[[AB[i][j]+BA[i][j] for j in range(2)] for i in range(2)]
    QA=qform(A,x,y);QB=qform(B,x,y)
    errors={
        'quadratic isometry':mean(QA*QB)-2*trace(AB),
        'fourth cumulant':mean(QA**4)-3*mean(QA**2)**2-48*hs(mm(A,A)),
        'noncommuting mixed square covariance':mean(QA**2*QB**2)-mean(QA**2)*mean(QB**2)-8*trace(AB)**2-16*hs(AB)-8*hs(S),
        'degree-two x-square coefficient':mean(QA*QB*(x*x-1))-4*S[0][0],
        'degree-two y-square coefficient':mean(QA*QB*(y*y-1))-4*S[1][1],
        'degree-two xy coefficient':mean(QA*QB*x*y)-4*S[0][1],
    }
    for name,error in errors.items():assert not error,(name,error)
    print(json.dumps(dict(status='PASS',arithmetic='exact rational polynomial coefficients and Gaussian integer moments',checks={k:len(v) for k,v in errors.items()},count=len(errors),scope='Symbolic transcription checks for arbitrary symmetric 2x2 matrices, including noncommuting mixed terms. Not a proof of completed-space limits or independence.')))
