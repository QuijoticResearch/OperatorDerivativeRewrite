"""Exact Gaussian moment, polynomial heat-sign and normalization checks.

Compact convergence, domination failure and arithmetic Fubini estimates are
analytic proofs in the manuscript, not conclusions of these finite checks.
"""
from math import factorial
from fractions import Fraction as F
import json
checks=[]
moment=1
for m in range(1,13):
 moment*=2*(2*m-1)
 assert moment==F(factorial(2*m),factorial(m))
 checks.append(f'variance-two even moment from integration-by-parts recurrence at degree {2*m}')
 coeff=F((-1)**m*factorial(m),factorial(2*m))
 heat_monomial=coeff*((-1)**m)*moment
 differential_monomial=F((-1)**m,factorial(m))*coeff*factorial(2*m)
 assert heat_monomial==differential_monomial==1
 checks.append(f'imaginary Gaussian and finite backward-heat values agree at degree {2*m}')
 assert abs(coeff)<=F(1,factorial(m)) and 1+heat_monomial==2
 checks.append(f'factorial disk bound and normalized heat value at degree {2*m}')
print(json.dumps(dict(status='PASS',count=len(checks),checks=checks,arithmetic='Unbounded integer and Fraction',scope='Finite variance-two moment recurrence, imaginary shift/backward-heat signs, factorial coefficient and normalization transcriptions. No sampled zero, convergence or domination claim.')))
