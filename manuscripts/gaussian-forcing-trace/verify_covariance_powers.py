"""Exact finite covariance transcriptions; not a process-law oracle."""
from fractions import Fraction as Q
from math import comb
import json

def matmul(A,B):
    return [[sum(a*b for a,b in zip(row,col)) for col in zip(*B)] for row in A]
def cov(n,k):return [[Q(min(i+1,j+1)**k) for j in range(n)] for i in range(n)]
def apply(A,v):return [sum(a*b for a,b in zip(row,v)) for row in A]
factors=0;pairs=0
for n in range(1,7):
    L=[[Q(j<=i) for j in range(n)] for i in range(n)]
    for k in range(1,5):
        d=[Q((j+1)**k-j**k) for j in range(n)]
        D=[[d[i] if i==j else Q(0) for j in range(n)] for i in range(n)]
        assert cov(n,k)==matmul(matmul(L,D),list(map(list,zip(*L))))
        factors+=1
        for ell in range(1,5):
            for j in range(n):
                v=[Q(i==j)-Q(j>0 and i==j-1) for i in range(n)]
                ratio=d[j]/Q((j+1)**ell-j**ell)
                assert apply(cov(n,k),v)==[ratio*x for x in apply(cov(n,ell),v)]
                pairs+=1
assert matmul(cov(2,1),cov(2,1))==[[2,3],[3,5]]!=cov(2,2)
moments=[1,1,3,15,105]  # E G^(2j), j=0..4
assert sum(Q(comb(4,j)*(-1)**(4-j))*moments[j] for j in range(5))/4==15
# For Delta~N(0,h), E Delta^2=h and E(Delta^2-h)^2=2h^2;
# the mixed cubic term is zero, leaving 2h B_s^2+h^2.
assert moments[2]-2*moments[1]+moments[0]==2
print(json.dumps(dict(status='PASS',factorizations=factors,generalized_eigenpairs=pairs,moment_and_matrix_comparisons=3,arithmetic='exact fractions and Gaussian integer moments',scope='Finite covariance factorization, difference-vector ratios, matrix-vs-entrywise powers and quadratic Wick moment coefficients; not a stochastic independence or infinite-time theorem.'),indent=2))
