"""Exact polynomial transcription checks; Python standard library only.
Checks finite algebra, not Lean proofs or measure-theoretic conclusions.
"""
from fractions import Fraction as F
from itertools import permutations
import json

class P:
    def __init__(self, value=0):
        if isinstance(value,P): self.c=dict(value.c)
        elif isinstance(value,dict): self.c={d:F(c) for d,c in value.items() if c}
        else: self.c={(0,)*5:F(value)} if value else {}
    def __add__(self,other):
        out=dict(self.c)
        for d,c in P(other).c.items(): out[d]=out.get(d,F(0))+c
        return P(out)
    __radd__=__add__
    def __neg__(self): return P({d:-c for d,c in self.c.items()})
    def __sub__(self,other): return self+-P(other)
    def __rsub__(self,other): return P(other)+-self
    def __mul__(self,other):
        out={}
        for a,b in self.c.items():
            for d,c in P(other).c.items():
                degree=tuple(i+j for i,j in zip(a,d))
                out[degree]=out.get(degree,F(0))+b*c
        return P(out)
    __rmul__=__mul__
    def __pow__(self,n):
        assert isinstance(n,int) and n>=0
        out=P(1)
        for _ in range(n): out=out*self
        return out

def variable(i): return P({tuple(int(j==i) for j in range(5)):1})
x,v,k,t,m6=(variable(i) for i in range(5))
m=[P(1)]
for n in range(9):
    m.append(v*n*(m[n-1] if n>=1 else 0)+F(1,2)*k*n*(n-1)*(m[n-2] if n>=2 else 0))

def L(p,moments=m):
    out=P()
    for degree,c in P(p).c.items():
        out+=P({(0,)+degree[1:]:c})*moments[degree[0]]
    return out

def determinant(matrix):
    out=P()
    for perm in permutations(range(len(matrix))):
        sign=(-1)**sum(perm[i]>perm[j] for i in range(len(perm)) for j in range(i+1,len(perm)))
        term=P(sign)
        for i,j in enumerate(perm): term*=matrix[i][j]
        out+=term
    return out

checks=[]
def check(name,expression):
    if P(expression).c: raise AssertionError(name)
    checks.append(name)

delta=2*v**3-k**2
D=12*v**6-24*v**3*k**2-9*k**4
Q=288*v**10-1440*v**7*k**2-1620*v*k**6
U=[P(1),x,x**2-v,x**3-3*v*x-k,x**4-6*v*x**2-4*k*x+3*v**2]
G3=[[v,k,0],[k,2*v**2,6*v*k],[0,6*v*k,6*v**3+9*k**2]]
G4=[[v,k,0,0],[k,2*v**2,6*v*k,6*k**2],
    [0,6*v*k,6*v**3+9*k**2,36*v**2*k],
    [0,6*k**2,36*v**2*k,24*v**4+144*v*k**2]]
for i in range(4):
    for j in range(4): check(f'Gram entry {i+1},{j+1}',L(U[i+1]*U[j+1])-G4[i][j])
check('cubic determinant',determinant(G3)-D)
check('quartic determinant',determinant(G4)-Q)
R3=6*v*k**2*U[1]-6*v**2*k*U[2]+delta*U[3]
R4=(-18*k**3*(10*v**3-3*k**2)*U[1]+18*v*k**2*(10*v**3-3*k**2)*U[2]
    -72*v**2*k*(v**3-k**2)*U[3]+D*U[4])
for i in range(3): check(f'cubic orthogonality {i}',L(R3*x**i))
for i in range(4): check(f'quartic orthogonality {i}',L(R4*x**i))
check('cubic norm',L(R3**2)-delta*D)
check('quartic norm',L(R4**2)-D*Q)
check('cubic cross moment',L(x*R3**2)+14*v**2*k*D-24*v**5*k*(10*v**3-17*k**2))
check('quartic cross moment',v*L(x*R4**2)-(-9*k**5+48*v**3*k**3-108*v**6*k)*Q
      -864*v**10*k*(52*v**6-272*v**3*k**2+213*k**4))
check('third Jacobi diagonal, denominators cleared',L(x*R3**2)
      -72*v**2*k*(v**3-k**2)*delta+6*v**2*k*D)
pt=x**3+(4-t)*x**2+(t-7)*x+t-5
check('sharp sixth-moment identity',L(pt**2,[1,0,1,1,3,t,m6])-m6+t**2-8*t+26)
print(json.dumps(dict(status='PASSED',check_count=len(checks),checks=checks,
    arithmetic='exact multivariate polynomials over fractions.Fraction; no external packages',
    lean_or_measure_theory_reverification=False),indent=2))
