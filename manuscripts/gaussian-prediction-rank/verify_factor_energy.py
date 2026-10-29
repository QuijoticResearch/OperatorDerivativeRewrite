"""Exact finite Markov-factor checks; no test of countable additivity or limits."""
from fractions import Fraction as F
import json
T=[[F(0),F(1),F(0)],[F(1,2),F(0),F(1,2)],[F(1,2),F(0),F(1,2)]]
Q=[[F(1),F(0),F(0)],[F(0),F(1,2),F(1,2)],[F(0),F(1,2),F(1,2)]]
def mv(A,x):return [sum(a*b for a,b in zip(row,x)) for row in A]
def mul(A,B):return [[sum(A[i][k]*B[k][j] for k in range(3)) for j in range(3)] for i in range(3)]
def energy(x):return sum((a-b)*a for a,b in zip(x,mv(T,x)))/3
checks=[]
def check(name,value):
 assert value,name
 checks.append(name)
check('positive Markov rows and actual uniform stationary columns',all(a>=0 for row in T for a in row) and all(sum(row)==1 for row in T) and all(sum(T[i][j] for i in range(3))==1 for j in range(3)))
check('conditional partition projection is symmetric and idempotent',Q==list(map(list,zip(*Q))) and mul(Q,Q)==Q)
check('retained partition is invariant',mul(Q,mul(T,Q))==mul(T,Q))
check('nonreversibility and noncommutation',T!=list(map(list,zip(*T))) and mul(Q,T)!=mul(T,Q))
x=[F(2),F(-1,4),F(-7,4)];qx=mv(Q,x)
check('actual centered witness and its conditional mean',sum(x)==sum(qx)==0 and qx==[2,-1,-1])
check('exact original and projected defect energies',energy(x)==F(21,8) and energy(qx)==3 and energy(qx)-energy(x)==F(3,8))
check('actual coarse factor and stationary masses',mv(T,[2,-1,-1])==[-1,F(1,2),F(1,2)] and F(1,3)*0+F(2,3)*F(1,2)==F(1,3))
print(json.dumps(dict(status='PASS',count=len(checks),checks=checks,arithmetic='Exact rational matrices and vectors only',scope='Finite Markov and partition identities; measure nonexistence and limiting energy statements use printed proofs.')))
