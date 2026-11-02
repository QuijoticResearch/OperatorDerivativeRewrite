# A(2): stochastic/operator bridge audit — checkpoint1950

Research ledger, November2,2026. A(2)/RH remains ACTIVE. This is a mathematical
research audit, not a manuscript/publication update. No campaign transition.

## Scope and novelty qualification

Three NEW bridge targets within Stardust were selected after searching the
3144-module prior Foundation inventory/signatures and reading the exact relevant
sources. This is NOT a claim of three globally novel mathematical discoveries.
Gaussian/Hermite analysis, Jensen criteria and covariance decompositions are
classical. The useful new verified content is the ACTUAL Xi-domain/Stein and
covariance instantiation, plus explicit tests which rule out insufficient
operator-to-zero implications. No RH theorem or improved threshold is claimed.

Use H_t(z)=RiemannEvenFlow.flow 1 t z and complex spatial derivatives H_t^(j).
This is the literal arithmetic theta-kernel flow. At time0 the existing Xi
identification has normalization entireXi(1/2+I*z/2)/8. No surrogate replaces it.
Write Y~N(0,2s), s>=0. REAL Gaussian shifts DECREASE deformation time:
E H_t^(j)(z+Y)=H_(t-s)^(j)(z). Imaginary shifts INCREASE time. The latter
Gaussian identities existed before this audit and are not counted as new results.

## 1. Actual-Xi Gaussian chaos domains instead of the excluded factorial domain

Exact reusable sources: GaussianBoundedBanachStein.scaled_stein;
GaussianCore.hermiteBasis_hasSum (GaussianHermite.lean);
GaussianCore.hermiteTruncation_tendsto and closedDerivative_graph_iff
(GaussianHermiteAdjoints.lean); RiemannQuadraticGaussian.shifted_jet_average;
RiemannEvenEvolution.flow_iteratedDeriv. RiemannFactorialObstruction already
excludes the actual Xi raw derivative sequence from the older factorial lp-one
realization. That obstruction must not be bypassed by an unexplained domain cast.

The new observable is F_j(Y)=H_t^(j)(z+Y). Proved horizontalBound controls it
uniformly in the REAL coordinate by
 M_j(t,z)=[integral_0^infty u^j exp(t*u^2-Im(z)*u)Phi(u)du
           +integral_0^infty u^j exp(t*u^2+Im(z)*u)Phi(u)du]/2.
Every such bound is finite by the OLD actual weighted-integrability theorem.
All j,t,complex z and all real Y are covered. observable_memLp proves genuine
Gaussian Lp membership for EVERY p including infinity; polynomial_pairing_integrable
proves integrability against EVERY complex polynomial test, without treating a
nonexistent factorial-domain vector as the actual function. Actual derivative
identification, continuity and integrability precede Stein.

NEW VERIFIED actual_xi_stein, for every j,t,z,s>=0:
  E[Y H_t^(j)(z+Y)] = 2s H_(t-s)^(j+1)(z).
This reuses the verified Banach-valued Stein theorem, after discharging its
bounded-function, bounded-actual-derivative and measurability hypotheses. It is
FIRST chaos for every derivative order, not a full chaos reconstruction theorem.

Precise still-missing reconstruction bridge, for s>0:
  E[He_n(Y/sqrt(2s)) H_t(z+Y)] = (2s)^(n/2) H_(t-s)^(n)(z),
followed by the COMPLETED complexified Hermite basis and Parseval:
  E|H_t(z+Y)|^2 = sum_(n>=0) (2s)^n/n! * |H_(t-s)^(n)(z)|^2.
The new proofs establish the integrability/domain and n=0,1 coefficients, NOT the
all-n coefficient identity or completed reconstruction. Existing abstract
Hermite completeness alone does not identify these coefficients with actual Xi
jets. No stochastic derivative/adjoint graph membership beyond what is proved
is silently inferred merely from MemLp.

Even full Parseval would not exclude zeros. A concrete additional Xi-specific
inequality that WOULD do so at t=s and Im(z)!=0 is
  sum_(n>=1) (2s)^n/n! |H_0^(n)(z)|^2
     <= (1-epsilon(z,s))*E|H_s(z+Y)|^2,
with epsilon(z,s)>0 and nonzero total energy, established independently of
H_0(z)!=0. This is a quantitative lower bound on the vacuum share, not generic
positivity or a norm identity. Neither it nor a usable uniform version is proved.
The Gaussian-mixture counterexample below also satisfies benign Gaussian Lp
conditions, so those conditions alone cannot supply this missing bound.

Literature check: classical heat/Hermite isometries are related to Segal–Bargmann
analysis; Driver–Hall–Kemp, https://arxiv.org/abs/1610.00090 (abstract inspected;
author PDF fetch timed out). This is context, not a theorem imported into Lean
or evidence of novelty of the general transform. No full paper proof audit claimed.

## 2. Gaussian–Poisson chaos transfer versus actual Jensen hyperbolicity

Exact reusable sources: GaussianPoissonChaosTransfer.finite_chaos_inner_transfer,
finite_chaos_norm_transfer and concrete_finite_chaos_norm_transfer;
poisson_square_first_inner and gaussian_square_first_inner already warn that
this isometry does not identify ordinary multiplication. FiniteGaussian's actual
Hermite spectral coefficients/Parseval are also available. No Poisson or
Gaussian chaos law is asserted to be the arithmetic Xi-kernel law.

For the ACTUAL flow define the candidate coefficient sequence
 gamma_n(t) = n!/(2n)! * integral_0^infty u^(2n) exp(t*u^2)Phi(u)du.
The exact moment-to-even-Xi expansion must be retained: if G_t(w) is defined by
its entire series sum gamma_n(t)*w^n/n!, then formally G_t(w)=H_t(i*sqrt(w));
the series, not a global square-root branch, is the appropriate definition.
The root-control target is the all-degree/all-shift Jensen family
 J_(d,N)(X)=sum_(j=0)^d binomial(d,j)*gamma_(N+j)(0)*X^j.

Missing bridge: prove that the ACTUAL diagonals gamma_(N+j)(0), with the correct
normalization and domain, preserve hyperbolicity of the needed real polynomials
uniformly in d,N. Positive diagonal coefficients, self-adjointness, contractive
Hilbert norms and matching Gaussian–Poisson inner products DO NOT prove this.
Jensen–Pólya is a classical criterion, not a new stochastic theorem. Griffin,
Ono, Rolen and Zagier https://arxiv.org/abs/1902.07321v2 (abstract inspected)
already establish major Hermite/asymptotic hyperbolicity results. This audit does
not claim that their results settle all degrees/shifts or improve their bounds.

NEW VERIFIED decisive generic obstruction: gamma_n=(1+2^(-n))/2 has 0<gamma_n<=1
and gives a contraction on every finite coefficient l2 space. Nonetheless
 gamma_1^2-gamma_0*gamma_2=-1/16,
 J_2(z)=1+(3/2)z+(5/8)z^2,
 J_2(-6/5+(2/5)i)=0 with nonzero imaginary part.
The conjugate root is independently tested. More generally two_variance_turan
proves (q*r+(1-q)*v)^2-[q*r^2+(1-q)*v^2]
 = -q*(1-q)*(r-v)^2. Nondegenerate positive variance mixtures have the OPPOSITE
Turan sign from the required degree-two Jensen inequality.

This is an ACTUAL positive stochastic mixture, not merely prescribed coefficients:
 mixtureTransform(z)=[exp(-z^2)+exp(-z^2/2)]/2
   =[E_(N(0,2)) exp(i*z*Y)+E_(N(0,1)) exp(i*z*Y)]/2.
mixture_gaussian_representation proves the real-law integral identity, and
mixture_transform_nonreal_zero proves its nonreal zero sqrt(pi)*(1+i) EXACTLY.
No positivity or contraction from the first-chaos/Hilbert geometry can rule out
this witness. It is NOT the Xi function and does not disprove RH. It rules out
using those operator hypotheses alone as the missing arithmetic bridge.

## 3. Closed-span projection and signed calculus expose the exact Laguerre deficit

Relevant exact sources: Gaussian Hermite closed graph/truncation machinery;
IBMCompletedNativeCalculus.fixed_weak_reconstruction, fixed_integrand_norm and
fixed_native_integrand_energy retain an orthogonal residual/initial channel;
HigherHeatSignedPolynomialCalculus.signed_polynomial_stein retains signed-domain
hypotheses. Neither IBM's actual JointL2/IntrinsicSpace nor a higher-order signed
completion is automatically a space of Xi observables. There is NO law-preserving
IBM filtration/source embedding established here, and no such theorem is invoked
as if its hypotheses held. The transfer used and proved here is the genuine
Gaussian constant-channel projection on the ACTUAL Xi observables from bridge1.

For F_j=H_t^(j)(z+Y), define bilinear C_(jk)=E(F_j*F_k)-E(F_j)E(F_k), with NO
complex conjugation. pair_integrable proves all relevant actual products finite.
NEW VERIFIED actual_laguerre_covariance:
 L(H_(t-s))(z) = E[F_1^2-F_0*F_2] - C_(11) + C_(02),
where L(f)=f'^2-f*f''. At real x the observables are real, so C_(11) is variance;
at complex z this bilinear covariance is NOT a nonnegative norm.

Precise missing first-order sign estimate at real x:
 Var(F_1)-Cov(F_0,F_2) <= E[F_1^2-F_0*F_2].
For t=s this would establish the first Laguerre inequality for actual H_0.
It is not proved and would not alone settle RH. To use the generalized Laguerre
route one needs the analogous inequalities for EVERY n,x, with
 a_(n,j)=(-1)^(n+j)*binomial(2n,j),
 sum_j a_(n,j) C_(j,2n-j) <= E sum_j a_(n,j) F_j F_(2n-j),
and the actual entire Taylor/zero-exclusion argument. No completed all-order
projection identity or all-order sign inequality is certified by this checkpoint.
Reconstruction, uniqueness, Parseval and closed-range norms do not bound this
ALTERNATING cross-sector covariance form. Higher-order signed product identities
also do not turn it into a positive quadratic form.

NEW VERIFIED generic failure under the EXACT genuine Gaussian averaging law:
 P(z)=z^2-1 has ONLY real roots and L(P)(x)=2*x^2+2>0 on R;
 E_(Y~N(0,2)) P(z+Y)=z^2+1 has the nonreal root i and L(mean)(0)=-2.
At x=0, E L(P(Y))=6, Var(P'(Y))=8, Cov(P(Y),P''(Y))=0: the deficit is 6-8=-2.
The polynomial stochastic integral, root properties and negative mean Laguerre
value are proved in Lean; the numerical covariance accounting is independently
checked exactly. Thus even true positive Gaussian averaging and fully regular
polynomial stochastic calculus cannot supply the missing sign condition.
This is a transfer obstruction, NOT an actual Xi counterexample.

## What was established and what remains

New production leaf: Foundation/RiemannStochasticBridge.lean. ALL29 public types,
22 public proofs,7 public definitions and2 private proofs are reviewed. The
strongest viable bridge proved is the all-j ACTUAL Xi Gaussian-domain/Stein
identity and its actual bilinear covariance correction. Full Hermite/Fock
coefficient identification, a quantitative nonzero vacuum share, actual Jensen
hyperbolicity and the alternating covariance estimates remain OPEN.

Do not describe this as three novel RH advances, an IBM representation of Xi,
a higher-order signed process probability law, full Clark–Ocone for Xi, or a new
threshold bound. The next mathematically substantive task is to test a concrete
Xi-specific energy/total-positivity estimate, not to assume that completion of
classical Gaussian infrastructure would supply it. Existing1947-1949 kernel
curvature work is preserved and its fifth sign remains unproved.

Verification/timings/source-integrity/exact-commit evidence are recorded in
STARDUST_A2_STOCHASTIC_BRIDGE_VERIFICATION.json, PROJECT_STARDUST_REPORT.md and
local.lake/stardust-1950-* receipts. Guarded BOTH-branch synchronization and
independent PUBLIC visibility checks remain mandatory; visibility is never changed.
