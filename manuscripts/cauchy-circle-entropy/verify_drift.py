"""Exact finite Fourier checks. Universal identities are proved in the paper."""
from fractions import Fraction as F
import json
checks=[]
def check(label,value):
 assert value,label
 checks.append(label)
def clean(f):return {n:F(x) for n,x in f.items() if x}
def add(*fs):
 out={}
 for f in fs:
  for n,x in f.items():out[n]=out.get(n,F(0))+x
 return clean(out)
def scale(a,f):return clean({n:a*x for n,x in f.items()})
def mul(f,g):
 out={}
 for n,x in f.items():
  for m,y in g.items():out[n+m]=out.get(n+m,F(0))+x*y
 return clean(out)
def mode(n):return {n:F(1)}
def B(h,f):return add(*(add(scale(F(n,2)*x,mode(n-h)),scale(-F(n,2)*x,mode(n+h))) for n,x in f.items()))
def L(a,h,f):return add({n:-abs(n)*x for n,x in f.items()},scale(a,B(h,f)))
def refl(f):return {-n:x for n,x in f.items()}
def gamma(a,h,f,g):return scale(F(1,2),add(L(a,h,mul(refl(f),g)),scale(-1,mul(refl(L(a,h,f)),g)),scale(-1,mul(refl(f),L(a,h,g)))))
def gamma2(a,h,f,g):return scale(F(1,2),add(L(a,h,gamma(a,h,f,g)),scale(-1,gamma(a,h,L(a,h,f),g)),scale(-1,gamma(a,h,f,L(a,h,g)))))
def correction(h,f,g):return add(gamma2(1,h,f,g),scale(-1,gamma2(0,h,f,g)))
def at0(f):return sum(f.values(),F(0))
def K(n,m):return F(abs(n)+abs(m)-abs(m-n),2)
check('kernel and integer identity on signed indices',all((m-n)*K(n,m)+n*K(n+1,m)-m*K(n,m-1)==K(n,m) for n in range(-15,16) for m in range(-15,16)))
check('first Gamma independent of harmonic derivation',all(gamma(F(3,2),h,mode(n),mode(m))==gamma(0,h,mode(n),mode(m)) for h in range(5) for n in range(-5,6) for m in range(-5,6)))
cos=scale(F(1,2),add(mode(1),mode(-1)))
check('first harmonic full frequency correction',all(correction(1,mode(n),mode(m))==scale(F(1,2),mul(cos,gamma(0,1,mode(n),mode(m)))) for n in range(-8,9) for m in range(-8,9)))
check('complex diagonal harmonic formula',all(correction(h,mode(n),mode(n))==scale(F(n*min(n,h),4),add(mode(h),mode(-h))) for h in range(12) for n in range(12)))
check('real cosine correction and first Gamma',all(at0(correction(h,add(mode(n),mode(-n)),add(mode(n),mode(-n))))==n*(n-min(abs(n-h),n)) and at0(gamma(0,h,add(mode(n),mode(-n)),add(mode(n),mode(-n))))==2*n for h in range(12) for n in range(1,12)))
check('real incompatible scalar witnesses',all(at0(correction(h,add(mode(1),mode(-1)),add(mode(1),mode(-1))))==0 and at0(correction(h,add(mode(h),mode(-h)),add(mode(h),mode(-h))))==h*h for h in range(2,13)))
f=add({0:F(2)},cos);lf=L(1,1,f)
check('actual Haar mean variance and negative energy',lf.get(0,0)==F(1,2) and f[0]==2 and mul(f,f)[0]==F(9,2) and -mul(f,lf)[0]==-F(1,2))
def defect(a,g):return add(L(a,1,mul(mul(g,g),g)),scale(-3,mul(g,L(a,1,mul(g,g)))),scale(3,mul(mul(g,g),L(a,1,g))))
check('cubic defect unchanged by all tested rational amplitudes',all(defect(a,cos)==defect(0,cos) and at0(defect(a,cos))==-F(3,2) for a in [F(-7,3),F(0),F(1),F(5,2)]))
check('cosine diffusion right side and actual cubic value',at0(L(0,1,mul(mul(cos,cos),cos)))==-F(3,2) and 3*at0(cos)**2*at0(L(0,1,cos))+6*at0(cos)*at0(gamma(0,1,cos,cos))==0)
print(json.dumps(dict(status='PASS',count=len(checks),checks=checks,scope='Exact finite rational transcription tests; proofs for every integer and polynomial are in the manuscript.')))
