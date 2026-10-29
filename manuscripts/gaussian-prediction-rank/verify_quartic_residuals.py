"""Exact two-coordinate Gaussian polynomial verification, without sampling."""
from fractions import Fraction as F
from math import comb
import json
def add(*terms):
 d={}
 for t in terms:
  for e,c in t.items():d[e]=d.get(e,F(0))+c
 return {e:c for e,c in d.items() if c}
def mul(a,b):
 d={}
 for e,c in a.items():
  for f,bv in b.items():
   n=(e[0]+f[0],e[1]+f[1]);d[n]=d.get(n,F(0))+c*bv
 return {e:c for e,c in d.items() if c}
def scale(a,t):return {e:a*c for e,c in t.items() if a*c}
def moment(n):
 if n%2:return F(0)
 a=F(1)
 for j in range(1,n,2):a*=j
 return a
def mean(p):return sum((c*moment(i)*moment(j) for (i,j),c in p.items()),F(0))
def cond(p):
 d={}
 for (i,j),c in p.items():d[(i,0)]=d.get((i,0),F(0))+c*moment(j)
 return {e:c for e,c in d.items() if c}
plus={(4-j,j):F(comb(4,j)) for j in range(5)}
minus={(4-j,j):F((-1)**j*comb(4,j)) for j in range(5)}
fp=add(plus,{(0,0):F(-12)});fm=add(minus,{(0,0):F(-12)})
P={(4,0):F(1),(2,0):F(6),(0,0):F(-9)}
rp=add(fp,scale(-1,P));rm=add(fm,scale(-1,P))
checks=[]
for name,value,expected in [('plus target mean',mean(fp),0),('minus target mean',mean(fm),0),('prediction mean',mean(P),0),('plus variance',mean(mul(fp,fp)),1536),('minus variance',mean(mul(fm,fm)),1536),('full target covariance',mean(mul(fp,fm)),0),('prediction variance',mean(mul(P,P)),312),('plus residual variance',mean(mul(rp,rp)),1224),('minus residual variance',mean(mul(rm,rm)),1224),('residual covariance',mean(mul(rp,rm)),-312),('block residual variance',mean(mul(add(rp,rm),add(rp,rm))),1824)]:
 assert value==expected,(name,value);checks.append(name)
assert cond(fp)==P and cond(fm)==P and cond(rp)=={} and cond(rm)=={}
checks.append('both actual conditional predictions and zero conditional residual means')
assert F(1824,3072)==F(19,32)<F(1224,1536)==F(51,64)
checks.append('exact individual and block unexplained fractions')
print(json.dumps(dict(status='PASS',count=len(checks),checks=checks,arithmetic='Fraction; complete polynomial expansion and exact Gaussian even moments',scope='Two actual independent standard Gaussian coordinates; no sampling or fractional asymptotic verification.')))
