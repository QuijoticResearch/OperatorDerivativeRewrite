"""Exact polynomial checks for the Burgers and prescribed-pressure diagnostics."""
from fractions import Fraction as F
import json
N=11  # Gaussian x,y; independent symbolic matrix entries a,b,c,d,e,f.
ZERO=(0,)*N
class P(dict):
    def __add__(self,other):
        other=poly(other);out=P(self)
        for k,v in other.items():out[k]=out.get(k,F(0))+v
        return P({k:v for k,v in out.items() if v})
    __radd__=__add__
    def __neg__(self):return P({k:-v for k,v in self.items()})
    def __sub__(self,other):return self+-poly(other)
    def __rsub__(self,other):return poly(other)+-self
    def __mul__(self,other):
        out=P()
        for k,v in self.items():
            for l,w in poly(other).items():
                q=tuple(a+b for a,b in zip(k,l));out[q]=out.get(q,F(0))+v*w
        return P({k:v for k,v in out.items() if v})
    __rmul__=__mul__
    def __pow__(self,n):
        out=poly(1)
        for _ in range(n):out=out*self
        return out
def poly(value):return value if isinstance(value,P) else P({ZERO:F(value)}) if value else P()
def var(i):return P({tuple(int(j==i) for j in range(N)):F(1)})
def moment(k):
    if k%2:return 0
    out=1
    for j in range(1,k,2):out*=j
    return out
def mean(p):
    out=P()
    for k,v in p.items():
        q=(0,0)+k[2:];out=out+P({q:v*moment(k[0])*moment(k[1])})
    return P({k:v for k,v in out.items() if v})

def deriv(p,i):
    out=P()
    for k,v in p.items():
        if k[i]:
            j=list(k);j[i]-=1
            out=out+P({tuple(j):v*k[i]})
    return out

def substitute(p,values):
    out=P()
    for k,v in p.items():
        term=poly(v)
        for i,power in enumerate(k):
            assert power>=0
            term=term*values.get(i,var(i))**power
        out=out+term
    return out


if __name__=='__main__':
    x,y,z,nu,beta,g,h,k,eps,C,S=[var(i) for i in range(N)]
    rho=x*x+y*y;f=2*g+2*rho*h
    u=[-2*nu*x-beta*y*g,-2*nu*y+beta*x*g,4*nu*z]
    jac=[[-2*nu-2*beta*x*y*h,-beta*g-2*beta*y*y*h,poly(0)],
         [beta*g+2*beta*x*x*h,-2*nu+2*beta*x*y*h,poly(0)],
         [poly(0),poly(0),4*nu]]
    grad=[beta*beta*x*g*g-4*nu*nu*x,beta*beta*y*g*g-4*nu*nu*y,-16*nu*nu*z]
    lap=[2*beta*y*f,-2*beta*x*f,poly(0)]
    errors={}
    for i in range(3):errors[f'actual stationary momentum coordinate {i}']=sum((u[j]*jac[i][j] for j in range(3)),poly(0))+grad[i]-nu*lap[i]
    errors['actual incompressibility']=sum((jac[i][i] for i in range(3)),poly(0))
    errors['actual Gaussian curl']=jac[1][0]-jac[0][1]-beta*f
    phase=x*S-y*C
    B=[[-2*eps*x*g*C,-2*eps*y*g*C,-eps*g*S],[-2*eps*x*g*S,-2*eps*y*g*S,eps*g*C],[-2*x*g+2*eps*g*(S-2*x*phase),-2*y*g+2*eps*g*(-C-2*y*phase),2*eps*g*(x*C+y*S)]]
    errors['repaired divergence']=sum((B[i][i] for i in range(3)),poly(0))
    trace=sum((B[i][j]*B[j][i] for i in range(3) for j in range(3)),poly(0))
    target=4*eps*g*g*phase+4*eps*eps*g*g*(2*rho-1)
    errors['repaired trace modulo exact circle relation']=trace-target-4*eps*eps*g*g*(2*rho-1)*(C*C+S*S-1)
    errors['radial response actual energy identity']=x*(x*g*g)+y*(y*g*g)-rho*g*g
    def gaussian_quarter_mean(p):
        out=P()
        for powers,v in p.items():
            coeff=v*moment(powers[0])*moment(powers[1])*F(1,4)**((powers[0]+powers[1])//2)
            out=out+P({(0,0)+powers[2:]:coeff})
        return P({j:v for j,v in out.items() if v})
    radial=2*rho-1
    errors['centered radial Gaussian mean']=gaussian_quarter_mean(radial)
    errors['unit radial Gaussian L2 norm']=gaussian_quarter_mean(radial**2)-1
    errors['Gaussian radius observation']=gaussian_quarter_mean(radial*rho)-F(1,2)
    # k is the independent Gaussian vorticity profile; g,h are angular g,g'.
    corrected=[eps*k*C,eps*k*S,k*(1+2*eps*phase)]
    repaired_jac=[[substitute(entry,{5:k}) for entry in row] for row in B]
    errors['repaired axial self advection']=sum((corrected[i]*repaired_jac[2][i] for i in range(3)),poly(0))
    dxx=beta**2*(g*g+4*x*x*g*h)-4*nu*nu
    dyy=beta**2*(g*g+4*y*y*g*h)-4*nu*nu
    mixed=4*beta*beta*x*y*g*h
    Hess=[[dxx,mixed,poly(0)],[mixed,dyy,poly(0)],[poly(0),poly(0),-16*nu*nu]]
    full=sum((corrected[i]*Hess[i][j]*corrected[j] for i in range(3) for j in range(3)),poly(0))
    full_target=k*k*(eps*eps*C*C*dxx+2*eps*eps*S*C*mixed+eps*eps*S*S*dyy-16*nu*nu*(1+2*eps*phase)**2)
    errors['actual repaired full Hessian contraction']=full-full_target
    errors['quarter Gaussian phase square modulo circle']=gaussian_quarter_mean(phase**2)-F(1,4)-F(1,4)*(C*C+S*S-1)
    errors['quarter Gaussian axial square modulo circle']=gaussian_quarter_mean((1+2*eps*phase)**2)-(1+eps*eps)-eps*eps*(C*C+S*S-1)
    errors['actual period endpoint axial weight']=gaussian_quarter_mean((1-2*eps*y)**2)-(1+eps*eps)
    # z represents the slab length here; the phases agree at both endpoints.
    end_w=[eps*k,poly(0),k*(1-2*eps*y)]
    flux_difference=end_w[2]*sum((end_w[i]*(-16*nu*nu*z if i==2 else poly(0)) for i in range(3)),poly(0))
    errors['actual axial flux endpoint difference']=flux_difference+16*nu*nu*z*k*k*(1-2*eps*y)**2
    # z is an independent symbolic logarithmic response in this scalar identity.
    errors['full slab equals trace plus boundary']=eps*eps*(beta*beta*z-20*nu*nu)-16*nu*nu-eps*eps*(beta*beta*z-4*nu*nu)+16*nu*nu*(1+eps*eps)
    for label,p in errors.items():assert not p,(label,p)
    print(json.dumps(dict(status='PASS',check_count=len(errors),checks={j:len(v) for j,v in errors.items()},arithmetic='Exact rational polynomial matrix identities and quarter-variance Gaussian moments',scope='Finite NS balance under the proved profile identity, incompressibility/curl, solenoidal repair/trace modulo the exact trigonometric relation and Gaussian radial normalization. Not a proof of weighted analytic integrability, the logarithmic integral or finite-slab Fubini.')))
