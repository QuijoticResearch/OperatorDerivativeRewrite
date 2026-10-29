"""Independent exact face enumeration and second-order quaternion jets.

This checks the actual finite slice, not a continuum or multiscale estimate.
Real-angle inequalities are proved in the manuscript, not sampled here.
"""
from fractions import Fraction as F
from itertools import product,combinations
from collections import Counter
import json
checks=[]
def check(label,value):
 assert value,label
 checks.append(label)
zero=(F(0),)*4
one=(F(1),F(0),F(0),F(0))
def qm(a,b):
 w,x,y,z=a;v,i,j,k=b
 return(w*v-x*i-y*j-z*k,w*i+x*v+y*k-z*j,w*j-x*k+y*v+z*i,w*k+x*j-y*i+z*v)
def pa(a,b):
 d=dict(a)
 for k,v in b.items():d[k]=tuple(x+y for x,y in zip(d.get(k,zero),v))
 return d
def pm(a,b):
 d={}
 for (i,j),u in a.items():
  for (k,l),v in b.items():
   if i+j+k+l<=2:d=pa(d,{(i+k,j+l):qm(u,v)})
 return d
def pi(a):return {k:(q[0],-q[1],-q[2],-q[3]) for k,q in a.items()}
def shift(v,i):return tuple(v[k]+(k==i) for k in range(4))
V=list(product(range(2),repeat=4))
E=[(v,i) for v in V for i in range(4) if v[i]==0]
I=[(v,i,j) for v in V for i,j in combinations(range(4),2) if v[i]==v[j]==0]
U=[(v,i,j) for v,i in E for j in range(4) if j!=i and v[j]==1]
v=(1,0,0,0);er=(v,1);ey=(shift(v,1),2);ex=(shift(v,2),1)
marks={er:0,ey:1,ex:2}
def ew(e,positive):return ((marks[e],positive),) if e in marks else ()
words=[ew((v,i),True)+ew((shift(v,i),j),True)+ew((shift(v,j),i),False)+ew((v,j),False) for v,i,j in I]
words +=[ew((v,i),i<j) for v,i,j in U]
canonical=[(),((0,True),),((0,False),),((2,True),),((2,False),),((1,True),),((1,False),),((0,True),(1,True),(2,False))]
counts=Counter(words)
check('all 72 exact oriented words and canonical multiplicities',len(words)==72 and counts==Counter(dict(zip(canonical,[60,2,1,3,1,2,2,1]))))
def curl(edge,face):
 v,i,j=face
 return int(edge==(v,i))+int(edge==(shift(v,i),j))-int(edge==(shift(v,j),i))-int(edge==(v,j))
check('two disjoint unit directions, energy five each and origin-star orthogonality',ey!=ex and all(sum(curl(edge,p)**2 for p in I)+sum(int(edge==(v,i)) for v,i,j in U)==5 and edge[0]!=(0,0,0,0) for edge in [ey,ex]))
for c,d in [(F(1),F(0)),(F(3,5),F(4,5)),(F(-3,5),F(4,5)),(F(0),F(1)),(F(-1),F(0)),(F(3,5),F(-4,5))]:
 R={(0,0):(c,F(0),F(0),d)}
 Y={(0,0):one,(1,0):(F(0),F(0),F(1,2),F(0)),(2,0):(F(-1,8),F(0),F(0),F(0))}
 X={(0,0):one,(0,1):(F(0),F(-1,2),F(0),F(0)),(0,2):(F(-1,8),F(0),F(0),F(0))}
 links=[R,Y,X];action={}
 for word in words:
  q={(0,0):one}
  for mark,pos in word:q=pm(q,links[mark] if pos else pi(links[mark]))
  for k,value in q.items():action[k]=action.get(k,F(0))-value[0]
  action[(0,0)]=action.get((0,0),F(0))+1
 a=(4+c)/4;b=-d/4
 check(f'actual 72-face quaternion second jet at c={c}, d={d}',action.get((0,0))==4*(1-c) and action.get((1,0),0)==action.get((0,1),0)==0 and 2*action.get((2,0),0)==2*action.get((0,2),0)==a and action.get((1,1),0)==b)
 S=a-b*b/a
 check(f'exact Schur factors and rational comparison at c={c}, d={d}',S==F(15+8*c+2*c*c,4*(4+c)) and S-F(3,4)==(c+1)*(2*c+3)/(4*(4+c)) and F(5,4)-S==(1-c)*(2*c+5)/(4*(4+c)) and F(3,4)<=S<=F(5,4) and 0<=(2*c+5)/(4*(4+c))<=F(7,20))
 check(f'completed square and minimum at c={c}, d={d}',all(a*(x*x+y*y)+2*b*x*y==S*x*x+a*(y+b*x/a)**2 for x,y in [(F(1),F(1)),(F(2),F(-3)),(F(1),-b/a)]))
print(json.dumps(dict(status='PASS',check_count=len(checks),checks=checks,arithmetic='Python unbounded integers and Fraction; truncated bivariate quaternion jets',scope='All face words, exact direction incidence, actual rational-unit base-point second jets and Schur algebra. No numerical angle, derivative approximation or continuum inference.')))
