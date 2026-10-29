"""Independent Gaussian-moment transcription checks for a full two-source parameterization."""
from verify_quadratic_identities import P,poly,var,mean
import json
x,y,alpha,beta,gamma=[var(i) for i in range(5)]
X=alpha*x;Y=beta*x+gamma*y
A=alpha**2*(beta**2+gamma**2);c=alpha*beta;Z=X*Y-c
F=x*x-y*y;G=2*x*y;H2x=x*x-1;H2y=y*y-1
errors={
 'two-source mean':mean(X*Y)-c,
 'two-source raw second':mean(X**2*Y**2)-(A+2*c*c),
 'two-source raw third':mean(X**3*Y**3)-(9*A*c+6*c**3),
 'two-source raw fourth':mean(X**4*Y**4)-(9*A*A+72*A*c*c+24*c**4),
 'two-source centered variance':mean(Z**2)-(A+c*c),
 'two-source centered fourth':mean(Z**4)-(9*A*A+42*A*c*c+9*c**4),
 'squared Gram upper deficit':15*mean(Z**2)**2-mean(Z**4)-6*(A-c*c)**2,
 'orthogonality lower deficit':mean(Z**4)-9*mean(Z**2)**2-24*A*c*c,
 'anticommuting orthogonality':mean(F*G),
 'anticommuting F variance':mean(F**2)-4,
 'anticommuting G variance':mean(G**2)-4,
 'anticommuting full cross fourth':mean(F**2*G**2)-48,
 'anticommuting square covariance':mean(F**2*G**2)-mean(F**2)*mean(G**2)-32,
 'mixed degree-two X coefficient':mean(F*G*H2x),
 'mixed degree-two Y coefficient':mean(F*G*H2y),
 'mixed degree-two XY coefficient':mean(F*G*x*y),
 'F-square X contraction coefficient':mean(F**2*H2x)-8,
 'G-square Y contraction coefficient':mean(G**2*H2y)-8,
 'radial pointwise identity':F**2+G**2-(x*x+y*y)**2,
 'pure degree-four Hermite product':F*G-(2*(x**3-3*x)*y-2*x*(y**3-3*y))
}
for name,v in errors.items():assert not v,(name,v)
print(json.dumps(dict(status='PASS',count=len(errors),arithmetic='exact rational symbolic coefficients and independent standard Gaussian integer moments',checks=list(errors),scope='Arbitrary alpha,beta,gamma parameterized two-source Gaussian pair and explicit anticommuting source coordinates. No new completed-space theorem or novelty test.')))
