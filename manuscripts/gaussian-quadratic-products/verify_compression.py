"""Exact finite Gaussian compression checks; completed limits are proved in the manuscript."""
import sys
sys.dont_write_bytecode=True
from verify_quadratic_identities import P,poly,var,mean,moment,qform,mm,hs
from fractions import Fraction as F
import json
x,y,a,b,c,d,e,f=[var(i) for i in range(8)]
A=[[a,b],[b,c]];QA=qform(A,x,y);pred=a*(x*x-1);err=QA-pred
Y=d+e*x+f*(x*x-1)
def mean_y(p):
 out=P()
 for k,v in p.items():
  q=k[:1]+(0,)+k[2:];out=out+P({q:v*moment(k[1])})
 return out
errors={
 'conditional mean matrix compression':mean_y(QA)-pred,
 'conditional residual mean':mean_y(err),
 'conditional variance retains cross block':mean_y(err**2)-(4*b*b*x*x+2*c*c),
 'mean squared residual block coefficients':mean(err**2)-(4*b*b+2*c*c),
 'prediction energy':mean(pred**2)-2*a*a,
 'nonlinear prediction Pythagoras':mean((QA-Y)**2)-mean(err**2)-mean((pred-Y)**2),
 'mixed residual not independent witness':mean_y((2*x*y)**2)-4*x*x,
}
for u,v in [(F(1),F(0)),(F(0),F(1)),(F(3,5),F(4,5)),(F(4,5),F(-3,5))]:
 # Gaussian coordinates along two orthogonal unit vectors.
 O=[[u*u,u*v],[u*v,v*v]];R=[[1-O[0][0],-O[0][1]],[-O[1][0],1-O[1][1]]]
 PAP=mm(mm(O,A),O);RAP=mm(mm(R,A),O);RAR=mm(mm(R,A),R)
 z=u*x+v*y;w=-v*x+u*y
 aa=a*u*u+2*b*u*v+c*v*v;bb=-a*u*v+b*(u*u-v*v)+c*u*v;cc=a*v*v-2*b*u*v+c*u*u
 adapted=aa*(z*z-1)+2*bb*z*w+cc*(w*w-1)
 errors[f'orthogonal adapted quadratic {u},{v}']=QA-adapted
 errors[f'projection quadratic {u},{v}']=qform(PAP,x,y)-aa*(z*z-1)
 errors[f'full operator block energy {u},{v}']=hs(A)-hs(PAP)-2*hs(RAP)-hs(RAR)
 errors[f'actual residual variance {u},{v}']=mean((QA-qform(PAP,x,y))**2)-4*hs(RAP)-2*hs(RAR)
for name,error in errors.items():assert not error,(name,error)
print(json.dumps(dict(status='PASS',count=len(errors),checks=list(errors),arithmetic='exact rational symbolic polynomials and independent standard Gaussian moments',scope='Arbitrary symmetric 2x2 coefficients, complete conditional second-moment polynomial and four rational orthogonal observation directions. These checks do not establish completed-space limits or novelty.')))
