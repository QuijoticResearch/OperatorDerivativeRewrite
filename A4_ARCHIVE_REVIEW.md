# A(4) archive review and theorem reuse audit

Review completed October 19, 2026, after the frozen IBM checkpoint
`89460761948de953f47da4564c38c255749f06f3` was verified on the private remote.
All eleven files recursively present in `ResearchSources/a4` were read in full
before any new A(4) proof was started. Original manuscripts are unchanged and
remain untracked. Their claims are research inputs, not Lean assumptions.

**A(4) remains unresolved in both directions.** The archive contains competing
finite and infinite threshold conjectures. In particular, one manuscript
explicitly retracts the numerical persistence argument used by another. None
of the local collision calculations, generic polynomial counterexamples,
finite-frequency covariance calculations, or finite-window numerical tests
settles the eventual global zero configuration of the Riemann kernel.

The manuscript notation is generally `Lambda(4)`, defined as the infimum of
times T for which every subsequent transform belongs to the Laguerre–Polya
class. This is the eventual threshold meant here by the user's A(4) question;
membership at one time and eventual membership must be distinguished. A(2)
and the final multichannel campaign remain queued, with October 31 the stop.

## Complete inventory

SHA256 values are over original bytes. Eleven filenames have eleven distinct
hashes. The specifically requested `even_pseudoprocess_bridge(1).tex` is absent;
the available unnumbered version below was read without assuming version identity.

| File under ResearchSources/a4 | Lines | Bytes | SHA256 |
|---|---:|---:|---|
| bakry_emery_revised_v8 (2) (2).tex | 1628 | 65987 | 53B29C9365C037FEE4F9367C7EFDC4F1C2F30076F8085EFB4DAECFA694B9006D |
| compression_study.tex | 306 | 15307 | F74994C68255DCE5894430FBC2AA937085231A1744482C8F9FE5CE954F25DB24 |
| compression_study_IBM.tex | 576 | 29127 | 955A72CF5E61B358771AE23C384A8300972B87CF8C832A840E5AC28F2E721380 |
| derivation_zero_odes.tex | 180 | 6577 | 3F5AAC7B2FDF67FA9C4D7CE01F7CEBFC90F406D0F9ECED4C6CAFD1FEC607CE5F |
| even_pseudoprocess_bridge.tex | 1377 | 74795 | 1AD0711512416FFB0F028045494CB4CEADA7447EC2F1F1A4C280FEB21DD06CB9 |
| gershgorin_bounds.tex | 158 | 5584 | E9BAD53123A9FD0E517A80555167DF22294CCB9FDF04E51A62117F03FF4D3CAB |
| hurst_line_signed_curvature.tex | 878 | 47733 | FC3D61873CC3533BA301F9A4FD74A9509CFED31CA0AE972DAE2E231AB18AD899 |
| ibm_laguerre_polya.tex | 1035 | 55609 | EAF31754F5F993EF8EB33A1917484D70F6B62F5B37A907AD85F097C3C5589D96 |
| iterated_gamma_curvature_tower.tex | 569 | 27245 | 77B41BF5E45AF82EFE02EA7BC326DB745E37F2A82EBEEEC2796742B177263940 |
| large_N_formal_limit.tex | 142 | 5420 | 309C212A02CC503919CDA30BB0A851D065A758B7E9108C91C83084000ABE2CBA |
| quartic_decoherence_scaling.tex | 208 | 9575 | 49AD986D74FF87FA24B159C585D5637FD821455D99A9943A72F635B001DA4BCB |

## Competing threshold arguments and their status

`ibm_laguerre_polya.tex`, especially lines191–240 and601–850, favors
**eventual finite threshold**. It claims a certified Laguerre violation at
t=8, x=63.2083; a large-time expanding-window theorem; and conjectures a
uniform far-field estimate giving eventual global membership. It explicitly
states that coarse quadrature missed a narrow saddle and falsely kept an
initial nonreal pair alive through t=300. Its corrected numerical narrative
says that pair returns by about t=30. These are the manuscript's assertions:
the stated Arb enclosures have not been independently reproduced here, and
the referenced computation repository is not part of this folder.

`even_pseudoprocess_bridge.tex`, especially lines1076–1160, instead favors
**infinite threshold**, using persistence of that pair through t=300 and a
comparison of a supposed t^(1/4) real-rooting window with high-zero gap
compression. This is the very persistence claim explicitly retracted in the
other manuscript. Filename/version chronology is not established by dates;
the mathematical conflict and explicit retraction are sufficient to reject
this numerical persistence argument as present evidence. Earlier lift-off at
arbitrarily high heights also does not imply a surviving nonreal pair at
each fixed later time. A persistence/no-return estimate would be needed.

`quartic_decoherence_scaling.tex` supplies an additional local compression
heuristic, not a global persistence theorem. Neither conjecture is adopted.

## Heat signs, domains, and the actual stochastic bridge

For the archive transform integral exp(t*u^4)*Phi(u)*cos(x*u), the spatial
generator is **+D^4**. The verified real signed biharmonic heat kernel in this
repository has the **decaying** Fourier symbol exp(-t*(2*pi*xi)^4) and
generator **-D^4**. A growing Fourier multiplier cannot be the Fourier
transform of a finite signed measure on the real line: such a transform is
bounded by total variation. The manuscripts' growing flow may be defined on
suitable analytic domains or through complex random variables; calling it
the same real signed-kernel semigroup is incorrect.

The Gaussian identity E[exp(S*u^2)]=exp(t*u^4), S~N(0,2t), is a genuine
scalar identity. On polynomials the corresponding two-sided quadratic heat
average is finite and gives exp(t*D^4). Extending it to the Xi transform
requires the actual integrability/Fubini estimates. Its positive clock does
not turn the complex displacement into a real positive pseudoprocess law,
nor does it make real-rootedness commute with averaging. The archive itself
gives a convex average of two real-rooted quadratic polynomials that is not
real-rooted. This blocks a generic inference from quartic membership to
membership of its quadratic mixands, in either time direction.

The quadratic de Bruijn direction is **-D^2**, multiplier exp(t*u^2).
Forward Gaussian heat **+D^2** is not a real-rootedness preserver: it sends
x^2-1 to x^2-1+2t. The dictionary theorem in
`hurst_line_signed_curvature.tex` lines300–350 incorrectly asserts the
opposite. This is a direct counterexample to that theorem as written,
including its claimed m=1 implication. The sign distinction is correctly
explained in `ibm_laguerre_polya.tex` and `derivation_zero_odes.tex`.

## File-by-file mathematical audit

### ibm_laguerre_polya.tex — all lines1–1035

The finite polynomial identity exp(t*D^4)[(x^2-1)(x^2-4)]
=x^4-5x^2+4+24t is correct. The substitution y=x^2 gives collision time
3/32 and no real zeros afterward. This proves a **generic preservation
failure**, not the Xi-specific eventual threshold. The general growing
even-order polynomial counterexamples likewise have meaningful algebraic
content after the appropriate sign (-1)^m is included in the generator.

The signed real-kernel interpretation fails as explained above. The stated
one-time weighted Fourier L1 hypothesis alone does not ensure an entire
extension or differentiation in time: extra exponential-in-frequency moments
and a time neighborhood are required. The actual Xi kernel's double
exponential decay is promising for those obligations, but must be established
in the formal development rather than assumed from a generic proposition.

The claimed uniform two-saddle theorem needs repair before use. Its proof
deforms a contour for log(Phi) without proving a zero-free analytic logarithm
on the required region, or constructing and bounding all connecting contour
segments. The endpoint estimate divides by |g'(0)+i*z| while including z=0;
evenness gives g'(0)=0. The real-axis Gaussian tail estimate does not by
itself justify exponentially small errors relative to a highly canceled
Fourier transform on an expanding complex disk. The displayed bound
Phi(u)<=exp(-pi*exp(4u)) drops a growing prefactor. A stated fixed power for
K_t*w is not implied for every allowed K_t. The window proof also invokes
K_t->infinity when gamma<=1/2, for which its chosen K_t does not diverge;
smaller windows could follow from a larger valid one, if first proved.
Its last assertion identifies actual zeros with leading cosine zeros,
where Rouche gives nearby zeros, not equality of their locations.

These gaps do not disprove the expanding-window conclusion; they prevent
treating this proof as established. Even a repaired expanding-window theorem
leaves an unbounded far field and does not prove finite A(4). The t=8 interval
certificate remains a separate reproducibility obligation with exact kernel,
normalization, differentiation and truncation bounds. A certificate at one
positive time cannot prove infinite eventual threshold.

### even_pseudoprocess_bridge.tex — all lines1–1377

The nondegenerate collision calculation has a concrete reuse target:
for G(x,s,epsilon)=0 and G_x=0 with G_xx nonzero and G_s=-G_xx,
the implicit Jacobian is G_xx^2, and T'_m=-M_m/M_1. This is conditional on
existence of the collision and the analytic map; the cited compact-criticality
theorem in an unavailable companion is not adopted as an established premise.
The text switches between perturbing an additive exponent epsilon*sigma and
perturbing a time-multiplied symbol; these differ by a factor Lambda in the
response formula. Keep the two parameterizations explicit.

The vertical contour segment identity -integral Im[w(i*y)]*g(i*y)*exp(-x*y)
is algebraically sound with its analytic/decay hypotheses. Even powers give
zero segment real part; the logarithmic direction gives density pi*y^2/2.
This alone does not imply oscillation, nor does a positive numerator imply
a positive normalized ratio without the sign of its denominator. The paper
claims R'(1)>0 from positivity of N while only assuming M_1!=0; that sign
requires another argument.

The moment-oscillation route is promising but not yet a verified theorem.
It replaces the exact logarithmic derivative of Phi by its leading n=1
asymptotic and then states exact saddle equations. Tail derivative bounds,
unique concentration and uniform error must be supplied. Concentration with
an **additive** o(1) error in the normalized cosine is enough for subsequences
bounded away from cosine zeros; a relative error after taking real parts is
not automatic near those zeros. Convergence theta_m->0 gives increments
o(1), not the displayed stronger asymptotic theta increment=o(1/m).
The first-passage arc-visitation lemma is true but its written proof can
choose m_0 already beyond the interval it purportedly first crosses, giving
k=m_0 and losing the previous-index assertion. Choose a later target above
the starting value to repair it. This is visitation, not equidistribution.

Several later deductions require separate rejection or repair. Positive
derivatives of a one-sided-zero factor h give **alternating** M_m via the
paper's own (-1)^m formula, contrary to its asserted constant-sign cone.
An asymptotic log-moment expansion for each fixed order cannot be summed
into an exact analytic germ without uniform bounds. The Carlson argument
calls a meromorphic Mellin function of rapidly growing real moments an
entire exponential-type-zero function; its hypotheses are not justified.
Generic even-jet blindness is not an impossibility theorem on the restricted
Xi-kernel family. The claimed discrete-scale zero ratio needs more than an
O(1) error in log beta_k and requires zero uniqueness/phase control. Claims
of a Clark–Ocone pairing do not identify an actual derivative domain,
causal representer or signed integration theorem for this collision map.
Loss of positivity of one measure never by itself proves sign oscillation
for a different arithmetic response measure.

The infinite-A(4) argument is superseded as discussed above. Neither its
numerical >300 bound nor its claimed universal no-go for deformation
methods is established by the supplied mathematics.

### quartic_decoherence_scaling.tex — all lines1–208

Writing H_0(x)=((x-x*)^2-h^2)q(x), the jets at x* are
H_0=-h^2*q, H_0'= -h^2*q', H_0''=2q-h^2*q'', and
H_0''''=12q''-h^2*q''''. Thus the midpoint is generally **not** a critical
point. The ratio -H_0/H_0'''' is a first-order estimate at a fixed point,
not an exact moving collision time. Neglected higher time terms, critical
point movement, nonvanishing q'' and uniform remainders require proof.
The inverse-gap q''/q identity is finite-polynomial algebra; entire canonical
products may have extra exponential terms and convergence obligations.
Random-matrix edge and compressed-gap estimates do not supply those controls
for a fixed Xi kernel, and early lift-off supplies no later-time persistence.

### derivation_zero_odes.tex — all lines1–180

On a finite polynomial simple-zero branch, the chain-rule velocity
-p^(m)/p'=-m!*e_(m-1)(inverse gaps) is valid. Quartic velocity is
-4*(P1^3-3P1*P2+2P3). The standalone quotient identity requires q(z)!=0;
its use at a selected simple zero has that property. The proof should
separate m>N, where the derivative and symmetric sum vanish. The formula
does not continue through collisions without further analysis and does not
itself extend to an entire Xi product.

### gershgorin_bounds.tex — all lines1–158

The finite-polynomial absolute bound m!*e_(m-1)(positive inverse distances)
<=m*S^(m-1) has a direct counting proof. Separation-based confinement is
conditional on a separation lower bound and cannot establish that lower
bound or prevent collisions. Nearest-neighbor quantities need another zero;
the m=1 case needs e_0 handled separately. The claimed characterization of
saturation as a spectral-edge regime cites absent `edge_gershgorin.tex`
and is unsupported here. No entire-function or uniform degree limit follows.

### large_N_formal_limit.tex — all lines1–142

The logarithmic-derivative Bell-polynomial PDE is a valid finite-polynomial
candidate away from zeros, requiring only local logarithms or rational
identities. The rescaled inviscid equation has quartic flux G^4 and cubic
characteristic speed, not cubic flux. The note expressly leaves measure
convergence, derivative scale bounds, well-posedness and shocks unproved.
Stieltjes inversion also needs real-support measure hypotheses. These
limitations should be preserved, not converted into an A(4) theorem.

### hurst_line_signed_curvature.tex — all lines1–878

The polynomial kernel's anti-diagonal coefficient matrix gives the proposed
even-station inertia by paired opposite-sign eigenvalues and one central
entry. The full rank requires enough distinct sampled frequencies; small
truncations cannot have rank 2m-1. Degenerate finite sampled forms must be
quotiented before being called nondegenerate Krein spaces. Tensor-product
Gram matrices are Kronecker products; Hadamard powers occur only on the
diagonal tensor lifts. A real trigonometric function involves the blocks
A+B and A-B after a cosine/sine change of coordinates, not two copies of A
when cross-sign coupling B is nonzero.

The exact biharmonic two-frequency matrices R=[[1,8],[8,16]] and
R∘R=[[1,64],[64,256]] yield determinant -48 for R, trace47/3 and determinant80
for R^-1(R∘R), and discriminant -671/9. The local matrix inequality
R∘R-kappa*R>=0 therefore fails on this block for every real kappa. These
are concrete algebraic targets, independent of any Xi implication. The
repository already verifies a negative quadratic form for the same R.

The real-rootedness dictionary fails its heat sign test. Its later
energy-cone comparison uses positive-frequency functions which are not real
entire functions on the real axis; calling them members of the real
Laguerre–Polya class from unit-circle root locations changes the definition.
Thus it does not prove the claimed inclusion LP⊂C for the actual LP class.

Failure of the positivity step in one interpolation proof does not prove
that every log-Sobolev or hypercontractivity inequality is impossible.
The universal 'pencil spectrum can never equal a decay rate' assertion
also does not follow from coefficients versus exponents: numerical coincidence
must be excluded by a separate statement with quantifiers. Real spectrum
of a general indefinite pencil is not sufficient for a positive-semidefinite
matrix lower bound. The negative-dimension discussion asserts growing
negative inertia without proof; at fixed polynomial order the kernel
matrices have a bounded feature rank, so unbounded growth is not available.
Its N=1 lower-eigenvalue wall test also needs the N>=2 restriction.

The finite-dimensional real invariant-block decomposition of a nonreal
pencil pair is potentially reusable after field/basis/area hypotheses are
made explicit. It is static matrix geometry, not zero control for Xi.

### iterated_gamma_curvature_tower.tex — all lines1–569

The exact min(n,m)^k factorization L*diag(j^k-(j-1)^k)*L^T gives successive
pencil eigenvalues (j^k-(j-1)^k)/(j^(k-1)-(j-1)^(k-1)). The abstract/intro
omit the denominator, conflicting with the body: at j=2,k=3 it is7/3,
not7. The Hadamard normalization conjugates by diag(n^(H*k)), depending
on k, rather than one fixed diagonal. Claimed uniform regularization rates
require denominator and small-level bounds. First-chaos extraction is not
the full Malliavin derivative; complex positive-frequency coefficients need
the corresponding complexification and Hermitian form.

The secular polynomial z^k-(z-1)^k has a useful vertical-line modulus
argument, but its zeros are not 'real-rooted in Re z' in the usual meaning.
That elementary identity and odd-zeta sums provide no RH theorem.
Integrated energy dissipation concerns generator weights, not convergence
of stochastic laws to a Gaussian. The N=1 correlation maximum needs its
own convention. No quartic threshold is proved.

### bakry_emery_revised_v8 (2) (2).tex — all lines1–1628

The stable kernel/fBM covariance equality is a genuine identity on same-sign
frequencies, with signed frequency coordinates supplying the full covariance
kernel. Correctly symmetrized iterated Gamma kernels are Hadamard powers.
The displayed sesquilinear Gamma2 definition using 2*Gamma(f,Lf) needs a
real part or the two distinct conjugate terms; silently Hermitianizing it
changes the definition for complex inputs. The Brownian min-kernel factorization
and odd-integer first pencil are promising exact finite algebra, while
conditional Z-matrix numerics do not prove the general positive-curvature
claim. Multiplying an inverse Stieltjes matrix by a nonnegative matrix does
not automatically preserve off-diagonal signs. Anti-persistent increments
are not the same thing as the positive correlations of fBM values.

The cosine-drift scalar-shift claim passes the elementary one-mode check:
for f=e^(i*n*x), Gamma=n and the real part of Gamma(f,b*f') is
-omega^2*n*cos(x)/2, so the drift correction is the claimed
omega^2*n*cos(x)/2. Likewise for f=cos(x), Gamma=1/2 and
Gamma(cos(x),cos(2x))=cos(x)/2 give correction omega^2*cos(x)/4.
These hand calculations are consistency tests, not a verified proof of the
all-mode identity or new Lean declarations. The finite-frequency calculation
should be kept distinct from its functional-inequality consequences.
Uniform Lebesgue measure is not invariant under the nonconstant drift:
integral Lf includes -integral b'*f. The claimed invariant-measure Poincare
consequence cannot be obtained by treating that measure as stationary.
Diffusion-chain-rule log-Sobolev implications also require a valid jump
calculus argument. The original Gaussian LSI replacement audit already
warns against confusing this with a general curvature theorem.

The refined decay claim identifies covariance-pencil eigenvectors with
generator decay directions without a commutation theorem. The complex
coefficient ellipsoid has real dimension2N; its volume determinant exponent
differs from the stated real N-dimensional formula unless the coefficient
space is restricted. None of this supplies Xi zero estimates.

### compression_study.tex and compression_study_IBM.tex — all lines1–306 and1–576

These are empirical coding studies, not quartic zero-control manuscripts.
The ECG paper reports actual tuned FLAC comparisons, qualifying the IBM
paper's surrogate FLAC-class results and a purported fractional-only gain.
No benchmark scripts/data are in the eleven-file archive; numerical tables
remain unverified. No coding campaign is opened.

The IBM note's half-normal Gaussian mixture is a one-point law. Actual
increments on fixed reflected scenery have conditional variance
abs(abs(Y_t)-abs(Y_s)), not automatically abs(Y_t-Y_s). A fitted fractional
model, or finite ACF/FFT study, does not prove a long-memory law. Finite-window
Airy kernel L1 numerics are not a global integrability theorem. Signed
kernels cannot directly be positive coding densities, but this observation
has no implication for A(4).

## Exact reuse and missing bridges

The following declarations were read or their source statements inspected
in the unchanged verified Foundation library. Existing proof certification
is the frozen full-build/root-axiom audit; this review adds no Lean theorem.

| Verified declarations | Actual reusable content | Missing connection |
|---|---|---|
| `FractionalCovarianceMatrices.covarianceMatrix_posSemidef`, `covariancePower_posSemidef`, `brownian_covariance` | fBM covariance PSD for 0<H<1, Schur powers, min kernel | Does not identify a nonlocal Gamma2 definition or a Xi flow |
| `FractionalCovarianceMatrices.hurst_two_negative_energy` | Explicit two-frequency H=2 energy equals -12 | Already handles this positivity obstruction; do not reprove it |
| `FractionalWickCovariance.cylinder_inner`, `finite_sum_norm_sq` | Genuine Gaussian Wick realization of covariance powers | A Gram identity does not identify heat generators, curvature decay, or real-rootedness |
| `GaussianSchwartzKernel.evenKernel_fourier`, `HigherHeatL2.symbol`, `symbol_norm_le` | Actual signed kernel with exp(-t*(2*pi*xi)^(2m)) | Growing quartic flow has the opposite sign at m=2 |
| `PureOrderPolynomialTransport.transport_eval`, `transport_add`, `actual_kernel_transport` | Exact polynomial transport for arbitrary real algebraic parameter; actual kernel only at sign (-1)^(m+1)*t | Positive quartic polynomial transport is usable algebraically, but its identification with a real signed heat law is false |
| `FactorialAnalyticHeat.evolution_polynomial`, `series_coordinate`, `evolution_hasDerivAt`, `actual_mean` | Complete factorial coefficient domain, exact transport and generator | Xi membership in this restrictive coefficient domain is not established and must not be presumed |
| `BandLimitedEntireCalculus.iterated_derivative_formula`, `fourth_derivative_formula` | Actual compact-frequency Fourier integrals and complex derivatives | Xi has unbounded frequency support; truncation limits need exponential weights and derivative control |
| `HigherHeatBackwardFourier.transition_test`, `transition_spectral_bound` | Actual decaying signed-kernel Fourier transport | 'Backward' here means a terminal backward solution, not reversing the generator into the growing Xi flow |
| `DifferentiableZeroSet.transverse_zeros_countable` | Countability of transverse real zeros and AE cancellation | Not a collision ODE or global real-rootedness theorem |

Searches of executable Foundation sources found no existing Laguerre–Polya,
de Bruijn–Newman, or Xi global zero-control declaration. Mathematical
connections asserted in manuscripts or comments must not be reported as
already verified zero-dynamics theorems. The audited IBM source/clock
reconstruction does not supply a replacement for this missing entire-function
analysis, and IBM remains frozen.

## Next focused obligations

1. Independently reconstruct the quartic flow on the actual Xi kernel with
   correct sign, Fourier convention, analytic domain and parameter derivatives.
   Reuse compact-frequency differentiation and direct weighted integral
   estimates rather than force Xi into the factorial coefficient completion.
2. Audit the one-point Laguerre certificate by reproducible rigorous enclosures
   if its computation source can be recovered. It would prove a finite-time
   nonmembership statement only. Do not promote decimal tables to axioms.
3. For a finite-threshold proof, establish complex contour/saddle bounds
   uniformly into the far field. A local cosine approximation or increasing
   bounded disk leaves the decisive universal-height quantifier open.
4. For an infinite-threshold proof, exhibit a nonreal zero or negative
   Laguerre certificate at arbitrarily large times, with rigorous error
   control. Compressed initial gaps and generic LP-preservation failure do
   not provide that result.

Prioritize these global alternatives and concrete obstructions over a new
curvature tower or unrelated coding branch. Transfer to A(2) is deferred to
its queued campaign; no relationship of thresholds, and no RH progress, is
claimed by this archive review.
