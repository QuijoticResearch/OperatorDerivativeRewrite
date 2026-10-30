"""Independent character-index enumeration of positive cyclic-walk fourth moments.
The finite checks do not prove generator convergence or infinite probability limits.
"""
from itertools import product
from fractions import Fraction as F
import json
checks=[]
for p in (2,4,6,8,10):
 for k in range(7):
  total=0
  for slots in product(range(k),repeat=4):
   balance=[0]*k
   for j,i in enumerate(slots):balance[i]+=1 if j<2 else -1
   total+=all(v%p==0 for v in balance)
  expected=3*k*k-2*k if p==2 else 2*k*k-k
  assert total==expected,(p,k,total,expected)
  checks.append(f'order {p}, walk length {k}, full four-index character average')
for r in (F(1),F(3,2),F(5),F(17)):
 # Derived Poisson second moment r^2+r applied to the enumerated walk formula.
 fourth=2*(r*r+r)-r
 assert fourth==2*r*r+r and fourth<=3*r*r
 checks.append(f'exact positive compound fourth/second comparison at Poisson mean {r}')
print(json.dumps(dict(status='PASS',check_count=len(checks),checks=checks,arithmetic='Exact integer character balances and rational Poisson moment substitution',scope='All finite index assignments at five even cyclic orders and seven walk lengths. The p=2 real exception is retained. Analytic bounds and all-order asymptotics use the printed proofs.')))
