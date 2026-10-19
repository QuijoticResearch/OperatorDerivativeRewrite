# A(4) archive review and theorem reuse audit

Review completed October 19, 2026, after the frozen IBM checkpoint
`89460761948de953f47da4564c38c255749f06f3` was verified on the private remote.
All eleven files recursively present in `ResearchSources/a4` were read in full
before any new A(4) proof was started. Original manuscripts are unchanged and
remain untracked. Their claims are research inputs, not Lean assumptions.

**Current verified status, checkpoint1128 (October19):** Actual LOCAL arithmetic integrals now have a proved full-complex-Gaussian comparison and norm-relative convergence at radius x^(-7/16), using leading-model curvature evaluated at ACTUAL saddles. Nonzero normalization, explicit error budgets and coverage of every sufficiently large real frequency for each fixed t>=1 are verified. Actual saddles/contours, growing-window real/simple zeros and the finite t8 negative Laguerre witness remain closed. Complementary ACTUAL contour pieces, opposite-frequency pairing, joint uniform-time/frequency control and global re-entry remain OPEN. Neither finite/infinite eventual A(4), nor an RH/A2 consequence, is established. See latest1127/1128 entries for exact domains and evidence.

**A(4) remains unresolved in both directions.** The archive contains competing
finite and infinite threshold conjectures. In particular, one manuscript
explicitly retracts the numerical persistence argument used by another. None
of the local collision calculations, generic polynomial counterexamples,
finite-frequency covariance calculations, or finite-window numerical tests
settles the eventual global zero configuration of the Riemann kernel.

The manuscript notation is generally `Lambda(4)`, defined as the infimum of
times T for which every subsequent transform belongs to the Laguerre–Polya
class. This is the eventual threshold meant here by the user's A(4) question;
membership at one time and eventual membership must be distinguished. The current
queue is A(4) ACTIVE, then integer A(2k), k >= 2 (verified A(4) results as
base; first generalization A(6)), with a real k > 1 / uniform k -> 1+ branch
conditional on a coherent, reusable integer theorem providing a justified
foundation, then A(2), then the final multichannel campaign. October 31, 2026
remains the hard stop. No limit preservation of real-rootedness or RH implication
is assumed.
See STARDUST_CAMPAIGN_QUEUE.md; this October 19 instruction supersedes older
successor-order statements in the historical entries below.

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

## Verified extension after the archive review: checkpoint1109

The five `RiemannQuartic*` Foundation modules now construct the literal
arithmetic-kernel transform, rather than a generic polynomial substitute.
`RiemannQuarticKernel.kernel_eq_series` identifies the definition with the
actual series in the manuscripts, with summation index n+1. Its summability
comes from Mathlib's `HurwitzKernelBounds.summable_f_nat`; no manuscript
theorem or numerical enclosure is assumed. `kernel_pos` proves positivity
for every u>=0. `kernel_decay` gives the explicit envelope

    |Phi(u)| <= C*exp(9*u - pi*exp(4*u)/2),  u>=0,

where C=2*pi^2*thetaMoment(4,1/2)+3*pi*thetaMoment(2,1/2) is a fixed finite
constant. `RiemannQuarticDomain.weighted_integrable` proves integrability
of u^k*exp(T*u^4+B*u)*Phi(u) on [0,infinity) for **every** natural k and
real T,B. Polynomial-exponential comparison is used only after this actual
kernel bound, without an assumed decay hypothesis on an arbitrary function.

`RiemannQuarticFlow` constructs actual complex half-line integrals and all
their spatial jets. `flow_differentiable` proves that the symmetrized
transform is entire in z for each real time. Dominated differentiation in
`RiemannQuarticEvolution.jet_time_hasDerivAt` uses the same all-tilt moment
domain and proves the time derivative of jet k is jet k+4. The theorem
`fourth_order_heat_equation` gives the correct **positive** fourth spatial
derivative for the growing arithmetic flow. `flow_eq_cosine_integral`
identifies it with the literal absolutely integrable cosine transform.

`RiemannQuarticReality.flow_real` identifies real-axis values with the
actual real cosine integral; `flow_even` proves evenness. Finally,
`flow_ne_zero_on_imaginary_axis` excludes every imaginary-axis zero for
every real time, using the strictly positive cosh integral. This is a
global axis exclusion, not exclusion of all off-axis zeros.

The identification at t=0 with Mathlib's completed zeta function is still
open in this development. It needs the precise normalization, theta/Mellin
identity and integrations by parts. No theorem above is asserted to close
that bridge, establish real-rootedness, certify the t=8 decimal intervals,
or decide A(4). The existing compact-frequency derivative mechanism was
reused for the spatial integral proof; the unbounded arithmetic domain was
proved separately instead of assuming compact support or factorial-domain
membership for Xi.

## Verified Xi identification: checkpoint1110

The completed-zeta identification left open in1109 is now proved, including
the normalization and every complex spatial point. Seven new modules
`RiemannThetaDifferentiation`, `RiemannThetaModularity`, `RiemannThetaDecay`,
`RiemannThetaCosine`, `RiemannThetaMellin`, `RiemannXiNormalization` and
`RiemannXiBridge` reuse the same literal kernel and Mathlib's actual theta
and completed-zeta definitions.

The argument establishes the following identities, with genuine integrals:

    Psi(u) = exp(u)*thetaMoment(0, exp(4u))
    Phi(u) = (Psi''(u)-Psi(u))/8
    Psi(u)-Psi(-u) = (exp(-u)-exp(u))/2
    Psi'(0) = -1/2
    J(x) = integral_0^infinity Psi(u)*cos(x*u) du
    H_0(x) = 1/16-(1+x^2)*J(x)/8
    completedRiemannZeta_0(1/2+i*x/2) = 8*J(x).

The actual theta-series derivatives are justified by summable local bounds
on their derivatives. The modular identity comes from Mathlib's theta
functional equation. The improper boundary term uses proved integrability
and decay of Psi and Psi'; it is not supplied as an assumption.
The Mellin identity reuses `hurwitzEvenFEPair 0`, its `f_modif`, its public
`IsStrongFEPair.hasMellin`, and the defining completed-zeta Mellin transform.
The exponential substitution, reflection of the negative logarithmic ray,
and the factor-four scaling are all proved.

The entire function is defined with poles already canceled:

    entireXi(s) = (s*(s-1)*completedRiemannZeta_0(s)+1)/2.

`entireXi_eq_completed` proves that away from s=0,1 this is
s*(s-1)*completedRiemannZeta(s)/2. It is not an identification of the
pole-removed completed zeta function itself with xi. Both the arithmetic
transform and this normalized entire function are proved holomorphic;
their agreement on the real spatial axis extends by the identity theorem.
The final declaration is

    RiemannXiBridge.flow_zero_complex (z : Complex):
      flow 0 z = entireXi(1/2+i*z/2)/8.

Thus the verified growing quartic integral now has the actual normalized
Xi function as its initial datum. This is a classical representation
formalized for the A(4) campaign, not a new result about RH or a proof of
an eventual real-rooting threshold. The global zero-control alternatives
and the rigorous t=8 certificate remain open.

An independent, explicitly **nonrigorous** standard-library Decimal probe
is saved as `tools/stardust_quartic_laguerre_probe.py`. At70-digit precision,
15 theta terms, cutoff1.6, and trapezoidal spacings0.002 and0.001, it gives

    H       ~= -1.641482419874955227552069264822e-10
    H'      ~=  3.656317925334409839674695900428e-13
    H''     ~= -1.460002952462137043575094865066e-10
    H'^2-HH'' ~= -2.396555810771356813972349899970e-20

at t=8, x=63.2083. Both grids agree well and reproduce the manuscript's
reported sign. No interval arithmetic, proved truncation error or proved
quadrature error is supplied by this script. Its output is evidence for
selecting the next rigorous calculation, never a Lean hypothesis.

## Verified finite-integral reduction, 2026-10-19 (1111)

Five new root-imported modules close the frequency-cutoff and theta-tail
parts of that calculation for the actual arithmetic Xi quartic flow.
They do not certify the script's quadrature values.

`RiemannThetaEffective.kernel_effective_bound` proves, for u >= 0,

    Phi(u) <= 64*exp(9*u-pi*exp(4*u)).

The proof bounds successive theta terms by a geometric ratio no greater
than one half, retaining the full negative pi*exp(4u) exponent. At t=8,
`RiemannQuarticCutoff.weighted_tail_bound` bounds the k-th weighted tail
by 64*k!*exp(-63*u) for u >= 8/5. Its integral is at most 10^-28 for
k=0,1,2. `RiemannQuarticJetCutoff` transfers the bound to actual complex
Fourier jets and spatial flow derivatives, uniformly for every real x.

`RiemannThetaTruncation` defines the finite kernel from precisely the
first N theta terms, proves its exact difference from Phi, and bounds
the weighted difference on [0,8/5]. With N=15 this pointwise error is
at most 10^-100 for k=0,1,2; no computed manuscript value is a hypothesis.

`RiemannQuarticFiniteApproximation.derivative_finite_error` proves

    ||D^k H_8(x)-finiteDerivative(15,k,8,x,8/5)|| <= 10^-27

for every real x and k <= 2. `finiteDerivative` is the actual symmetric
complex Bochner integral of that finite kernel on [0,8/5], retaining the
correct (i*u)^k and (-1)^k factors. Continuity, interval integrability,
the exact integrand difference and both tail transfers are proved.

The remaining certificate obligation is a rigorously evaluated enclosure
of these finite elementary integrals at x=63.2083, with both quadrature
and transcendental-evaluation errors justified. The Decimal values remain
nonrigorous. Mathlib already supplies `Real.exp_bound`, `exp_approx_end`
and `intervalIntegral.trapezoidal_error_le_of_c2`; their hypotheses and
effective bounds still need an application to these integrands. A coarse
second-derivative trapezoid estimate may require an impractical grid;
high-order local Taylor bounds or analytic quadrature are possible routes,
not established replacements. Even a verified t=8 negative Laguerre value
would only establish finite-time nonmembership, not A(4)=infinity.
Both threshold alternatives remain open. A(2) retains its successor gate.

## Actual real channels and Taylor certificate route, 2026-10-19 (1112)

`RiemannQuarticRealCertificate` proves the exact real quadrature channels
for derivative orders0,1,2: cos(u*x), -u*sin(u*x), -u^2*cos(u*x), respectively,
multiplied by exp(8*u^4)*partialKernel(N,u). Its `finiteDerivative_real`
identifies the symmetric complex integrals with these real integrals on
[0,8/5]. `realIntegrand_eq_sum` gives the precise finite sum of elementary
exponentials used by the numerical prototype, including the two different
linear exponents9u and5u, all arithmetic powers, and their signs.

Four terms already suffice for a coarse sign certificate: the proved
pointwise weighted theta error is <=10^-17 and the total actual complex
derivative error is <=10^-16, for all real x and k<=2. Here `actualJet` is
defined explicitly as the real part of the actual iterated complex
derivative. The theorem `negative_Laguerre_of_enclosures` retains three
EXPLICIT hypotheses on the actual four-term real integrals Q_k(x):

    Q_0(x) <= -163/10^12
    |Q_1(x)| <= 4/10^13
    Q_2(x) <= -145/10^12.

It concludes that actualJet(1,x)^2-actualJet(0,x)*actualJet(2,x) is less
than -2/10^20, after all proved tail errors. No concrete x is proved to
satisfy these three hypotheses yet; this is a conditional certificate
transfer theorem, not the missing negative-sign theorem.

`RiemannQuarticTaylorJets` proves genuine normalized derivative identities
with a_n(f,c)=D^n f(c)/n!: multiplication is convolution, and

    a_(n+1)(exp(f),c) =
      sum_(i=0)^n (i+1)*a_(i+1)(f,c)*a_(n-i)(exp(f),c)/(n+1).

The finite arithmetic kernels and real channel integrands are proved
C-infinity. The centered local Taylor polynomial is exactly the sum of
these coefficients; its integral on [c-h,c+h] has the exact monomial
formula. If |a_(n+1)(f,v)|<=M throughout that cell, with h>0 and M>=0,
`local_integral_error` proves an error <=2*M*h^(n+2). The coefficient
bound is an explicit obligation, not a presumed numerical fact.

The new standard-library exact-dyadic prototype is
`tools/stardust_quartic_interval_probe.py`. All interval arithmetic rounds
outwards with integer floor/ceiling; exp and sin/cos use finite series
plus remainder bounds and range reduction; pi uses Mathlib's existing
`Real.pi_gt_d20` / `Real.pi_lt_d20`. Floating-point numbers occur only in
display fields. At160 panels, order16,160-bit interval precision, four
theta terms, the reported widths are approximately2.52e-15,2.68e-15 and
6.39e-15, and all three endpoint box tests pass. This prototype's interval
propagation and complete calculation are NOT Lean-verified, so its
printed intervals are not admitted as hypotheses of the Lean theorem.

A higher-order test exposed a concrete numerical obstruction: order20
at the same160-bit precision gives widths around10^-9 and fails every
box test. The interval floor used for tiny exponentials gets amplified
by high derivatives. Keeping the failed output, then raising precision
to256 bits at order20, gives widths about1.64e-21,1.52e-22 and2.04e-23;
all endpoint tests pass again. Thus increasing Taylor order alone is not
an established convergence mechanism for the rounded implementation.
The next central obligation is a small kernel-checked interval evaluator
and proof that its exponential/convolution/trigonometric coefficient
bounds cover actual normalized derivatives on each cell, followed by
the finite-cell integral assembly and the three concrete box proofs.
The analytic recurrence and local Taylor integration portions are now
proved; the remaining interval calculation is not. A(4) remains active
and unresolved, with no transition to A(2) or claim about RH.

## Verified rounded arithmetic and exponential evaluator, 2026-10-19 (1113)

`RiemannQuarticDyadic` reuses Mathlib's `Inclusion.Interval Dyadic`, its
arithmetic membership theorems and rational-to-dyadic approximation. The
new outward-rounding operation preserves membership and handles unbounded
endpoints explicitly. Rounded addition, subtraction, multiplication,
division by a natural number, powers, finite sums and Horner evaluation
all have real-valued enclosure proofs. The scalar divisions use the actual
total real/rational division conventions, including at zero; no accidental
positive-denominator assumption is hidden in those general statements.

`RiemannQuarticIntervalExp` proves the actual exponential Taylor error
<=2/n! for n>0 and |x|<=1. Both a direct power-sum evaluator and a Horner
evaluator include that error with outward rounding. Range reduction by
2^s and s repeated squarings has a proved real exponential enclosure,
with the reduced-argument bound stated explicitly. For x<=-p, the tiny
exponential bound exp(x)<=2^-p is proved from exp(1)>=2, validating the
form of the precision-dependent tiny-exponential enclosure. This does
not assert convergence of the full rounded derivative calculation.

`RiemannQuarticIntervalChecks` provides a computable endpoint checker
with a theorem transferring a successful check to real inequalities.
Its pi box uses Mathlib's existing20-digit proved bounds. A complete
160-bit,65-term,16-fold range-reduced Horner calculation is checked by
`decide +kernel`, proving the concrete real enclosure

    601845037/10^6 <= exp(32/5) <= 601845039/10^6.

This is the exponential exp(4R) at the selected cutoff R=8/5. Both the
arithmetic check and its connection to the actual exponential are Lean
theorems. Native-code admission is not used. The earlier direct-series
version also passed before the checked definition was switched to the
proved Horner evaluator; no quantitative speedup is claimed here.

The Python prototype remains a separate unverified full computation.
The new Lean evaluator need not produce bit-identical intervals to it;
soundness and successful concrete checks, rather than external endpoint
agreement, are required. Outstanding: a similarly verified sine/cosine
evaluator, coefficient/derivative interval propagation, and finite-panel
assembly proving the three actual integral inequalities. The conditional
negative-Laguerre theorem has not become unconditional. Global A(4)
remains unresolved in both directions and A(2) remains gated.

## Verified trigonometric evaluator and derivative propagation, 2026-10-19 (1114)

`RiemannQuarticIntervalTrig` proves the four-period rational coefficients
of powers of i, then the actual cosine/sine polynomial coefficients and
remainder bounds <=2/n! for n>0 and |x|<=1. It reuses Mathlib's bound of
the complex exponential remainder by the real remainder at its norm,
followed by the already verified scalar exponential error. Rounded Horner
evaluation includes that error. The paired doubling operation is proved
from the actual addition formulas. `scaledTrig_mem` proves the cosine and
sine enclosures after division by2^s and s doublings, with the reduced
argument bound explicit; no approximate pi-based range reduction is used.

`RiemannQuarticTrigChecks` performs an actual kernel computation at
632083/6250=(632083/10000)*(8/5), the chosen spatial point times cutoff.
Using96-bit arithmetic,24 series terms and eight doublings, the
`decide +kernel` check and its real interpretation prove

    4/5 <= cos(632083/6250) <= 9/10
    1/2 <= sin(632083/6250) <= 3/5.

These broad inequalities test the complete evaluated procedure. They
are not the required integral enclosures or a numerical zero theorem.

`RiemannQuarticIntervalJets.convolution_mem` propagates actual normalized
product derivatives from input enclosures through order n. Its
`expPrefix_mem` / `expJet_mem` propagate actual derivatives of exp(f),
for C-infinity f, from an actual exp(f(x)) enclosure and coefficient
enclosures through n. Prefix correctness is asserted only for k<=n;
the total function's values outside its computed prefix have no derivative
interpretation. The implementation uses finite structural recursion,
with no assumption of external coefficient output. Its large-grid
computational cost has not yet been measured.

`RiemannQuarticTrigJets` proves the derivative sign cycle and the exact
normalized coefficients of cos(a*u), sin(a*u), for every natural order
and every real a,u. The frequency factor is a^n/n!, including at negative
a. With c_n=Re(i^n), s_n=Im(i^n), their remaining factors are respectively
c_n*cos(a*u)-s_n*sin(a*u) and s_n*cos(a*u)+c_n*sin(a*u). The corresponding
rounded jet evaluators have membership proofs from actual frequency and
phase enclosures. Thus product, exponential and trigonometric propagation
are now verified for actual derivatives, rather than only formal arrays.

The next concrete application is the literal four-term weighted kernel:
enclose its polynomial/exponential phase jets on each cell, combine them
with the proved trigonometric jets, and assemble the centered Taylor
integrals using the1112 remainder theorem. These concrete source and cell
bounds, the finite-panel assembly and the three integral box hypotheses
remain open. The Python prototype's full output is still unverified.
No unconditional negative-Laguerre, nonreal-zero, LP nonmembership,
eventual-threshold or RH theorem is claimed. A(4) remains active; A(2)
retains its gate.

## Literal arithmetic phase and channel jets, 2026-10-19 (1115)

`RiemannQuarticPhaseJets` now supplies the actual source-specific phase

    g_(m,a)(u)=8*u^4+a*u-pi*m^2*exp(4*u)

and proves its normalized derivative at EVERY natural order n:

    D^n g(u)/n! =
      [8*(4 falling n)*u^(4-n)+a*(1 falling n)*u^(1-n)
       -pi*m^2*4^n*exp(4*u)]/n!.

The falling factorials correctly vanish beyond the polynomial degrees.
All real u,a and natural m,n are covered; the actual theta sum uses
m=1,...,N and a=9 or5. `phaseJet_mem` proves the rounded enclosure from
actual u, exp(4u), pi and slope enclosures. `phaseExpJet_mem` connects
these input jets to actual derivatives of exp(g), with an enclosure of
the actual exp(g(u)) still required explicitly.

`RiemannQuarticArithmeticJets` defines the two-phase theta weight with
the exact coefficients2*pi^2*m^4 and -3*pi*m^2, proves its normalized
derivative formula and finite-sum formula, and supplies rounded theta
and finite-weight jet enclosures. `realIntegrand_eq_weight` proves that
the resulting weight times the existing real channel is exactly the
earlier finite arithmetic integrand. `realIntegrandJet_mem` transfers
weight/channel coefficient bounds to derivatives of that actual integrand.

`RiemannQuarticChannelJets` proves normalized monomial bounds and uses
them to account for the factors-u and-u^2 in channels1 and2. Its complete
channel evaluator represents cos(xu), -u*sin(xu), -u^2*cos(xu), with scope
k<=2. `integrandJet_mem` combines these proved channels with actual
weight coefficient bounds. No supplied abstract channel array replaces
the literal Fourier factors.

`RiemannQuarticPhaseChecks` is a concrete kernel computation using96-bit
arithmetic and a proved range-reduced enclosure of exp(2), plus the
proved pi box. At m=1,a=9,u=1/2 it proves

    -19 <= g(u) <= -18
    -81 <= Dg(u) <= -79
    -1/100 <= D^16 g(u)/16! <= -1/1000.

The last check concerns the PHASE coefficient at ONE point. It is not
a bound for D^16 exp(g), the full kernel, or a whole Taylor cell. The
check is reduced by `decide +kernel` and transferred to actual real
derivatives by the phase membership theorem; no external endpoints
are accepted as assumptions.

Next, evaluate genuine whole-cell phase/exponential and integrand bounds
using these source-specific functions, then assemble the centered Taylor
integrals and prove the three required real integral inequalities.
Producing only further all-order identities would not close this gap.
The full Python calculation remains unverified; the negative-Laguerre
theorem remains conditional. Both global A(4) alternatives are open,
and no threshold relation or RH implication is claimed.

## A genuine whole-cell Taylor bound, 2026-10-19 (1116)

For the actual four-term integrands at t=8 and x=632083/10000, Lean now
proves, simultaneously for k=0,1,2 and EVERY u in[1/2,51/100],

    |D_u^16 realIntegrand(4,k,x,u)/16!| <= 10^22.

`RiemannQuarticFullCellChecks.cell_taylor_error` consequently proves an
actual integral error below10^-16 on that cell, replacing each integrand
by its degree15 Taylor polynomial centered at101/200. This is cell50
of the160 equal cells on[0,8/5]. The sixteenth derivative is with respect
to the integration variable u; k labels the original spatial derivative
channels0,1,2. This does not assert a sixteenth spatial-flow theorem.
It is the finite FOUR-term integrand, with the infinite theta/cutoff
errors handled separately by the earlier verified reduction.

`RiemannQuarticCellPhase` first verifies an analogous uniform bound and
actual cell integral error for the first slope9 phase exponential alone.
`RiemannQuarticCellDomain` then proves exp(4u)<=603 on the whole cutoff
interval and -40000<=g_(m,a)(u)<=100 for m<=4,0<=a<=9. These give actual
range-reduction domains for every required phase, not supplied numerical
hypotheses. The full-cell evaluator encloses exp(4u), every exponential
phase base, all eight phase coefficient sequences, their exact theta
weights, and the three signed real Fourier channels uniformly in u.
The final order16 bounds are checked by `decide +kernel` and transferred
to the actual derivatives by `uniform_I`.

This calculation exposed a substantive computational obstruction. The
original prefix evaluator repeatedly recalculates earlier coefficients;
its full-cell exploratory run was stopped after759.34375 observed CPU
seconds with no Boolean output, after verifying the executable/start time.
`RiemannQuarticStoredJets` stores each prefix in a finite list, proves its
length and prefix agreement, and proves `expJetStored_eq`: its returned
intervals are EXACTLY the original evaluator's intervals. The full-cell
proof uses this implementation via `G_eq_original`, so neither domains
nor rounding guarantees are weakened. The stored implementation returned
all three feasibility checks in about36 seconds, and the full kernel
module check then passed in67 seconds. Runs overlapped and are not a
controlled benchmark. A kernel-process memory snapshot was about8.0 GB,
so further sharing may matter before scaling to160 cells. The stopped
exploratory run is not recorded as a successful proof or completed test.

This closes the first actual whole-cell derivative/remainder calculation.
The other159 cells, numerical enclosures of the centered Taylor polynomial
integrals, finite-cell assembly, and the three full real-integral box
inequalities are still open. Those inequalities must be proved before
the conditional Laguerre conclusion can be instantiated. The Python
prototype remains unverified as a whole. No unconditional negative
Laguerre, nonreal zero, LP nonmembership, A(4) threshold or RH implication
is claimed. A(4) stays active and A(2) remains gated.


## Verified derivative grid and actual saddle foundations, 2026-10-19 (1117)

The original160-cell whole-interval derivative proof finished uninterrupted in10134 seconds. The full repository build then passed5799 jobs; the full-root axiom audit passed32973 Foundation declarations with only propext, Classical.choice, Quot.sound, and all349 newly printed public types were read. The source manifest covers1727 Foundation/root files and17 new modules. The107 archive hashes,43 Incoming files/42 distinct hashes, and11 fully reviewed A4 manuscripts are unchanged. ResearchSources stays outside Git staging.

RiemannQuarticGridChecks.all_cells now proves every actual rounded whole-cell check. CertifiedGrid.uniform_sixteenth gives |D_u^16 realIntegrand/16!|<=10^22 for all160 closed cells and channels k<=2 at t=8,x=63.2083. quadrature_error proves actual four-term integral-vs-centered-Taylor-sum error<=1.6e-14; actual_derivative_error proves complex norm error<=1.61e-14 against the infinite arithmetic flow's actual spatial derivatives. Stored-prefix equivalence, exact integral partitioning, and the eight-even-term Taylor integral formula are proved. InitialValues checks only15 point-value memberships, cells0–4/channels0–2. The remaining465 value memberships are OPEN. Exact candidate endpoint arithmetic and the conditional negative-Laguerre connectors do NOT establish those memberships or an unconditional t=8 exit certificate.

The actual cosine transform's ordinary real derivatives and +D4 time equation now agree with its holomorphic derivatives without cutoff. Complex theta moments are holomorphic on Rev>0 with M_k'=-pi*M_(k+2); the literal complex arithmetic kernel is analytic on Re(exp4u)>0. Its leading-prefactor remainder and sixth-moment estimates give actual/model logarithmic-derivative error bounds on explicit domains. Kernel nonvanishing is proved for Reu>=0,Re(exp4u)>=1. This is nonvanishing of the INTEGRATION KERNEL Phi, not its Fourier transform or Xi.

Actual global positive-amplitude maxima exist for every real t and ALL maxima eventually escape every fixed radius as t increases. Each positive maximum is an exact frequency-zero real/complex phase saddle. The real analytic nonconstant saddle-time map has countably many critical values. Outside that exceptional-time set, these actual saddles are nondegenerate and admit analytic complex-frequency local continuation via the verified analytic inverse theorem, with the exact stationary equation, branch derivative and convergence/nonvanishing domain. There is no uniform continuation radius, no assertion that exceptional times are bounded, and no global Fourier remainder estimate.

A separate checked curvature prototype remains in .lake/RiemannQuarticCurvatureProbe.lean, not in the root/commit. It now contains actual normalized theta-moment and coefficient bounds, the literal common-scale derivative dictionary, and a logarithmic-curvature comparison within1 for u>=1. Its printed theorem axiom lists are standard-three only, but it has NOT undergone root integration/full-checkpoint verification. The saddle-time sign proof and resulting removal of exceptional times remain OPEN. This is the next analytical route, alongside bounded batches for the465 missing value checks.

The central source discussion remains ibm_laguerre_polya.tex lines713–793: expanding-window recovery leaves a possible outward-migrating nonreal pair uncontrolled. Neither A(4)<infinity nor A(4)=infinity is established. No RH or threshold-transfer conclusion is inferred; A4 stays active before the queued A2 and final multichannel campaigns, with October31 as the stopping date.

## Verified actual quartic saddles and complex neighborhoods, 2026-10-19 (1118)

Continued A(4) from audited/private-backed ec0b3c8a7e7d0149f92128eb8f7e326fecaa8b10. IBM remains frozen at8946076; A(2), then the final multichannel campaign, remain queued. October31 remains the stopping date. The objective is eventual GLOBAL real-rooting of the actual quartic Xi flow, tested in both directions. Expanding clean windows do not exclude an outward-migrating nonreal pair. The previous question-answer turn was read-only confirmation of this objective, not a proof checkpoint. Current terminal clock: October19,14:19 EDT. ResearchSources is unchanged.

RiemannQuarticValueCells005To024 proves all60 exact point-value checks for cells5 through24 and channels0 through2. Together with the prior firstfive cells,75 of480 required memberships are proved;405 remain. The previous whole-cell derivative grid, Taylor quadrature and infinite-flow derivative error bounds are reused. No unconditional negative Laguerre certificate at t=8 follows yet. Endpoint totals alone cannot discharge actual value memberships.

RiemannQuarticCurvature establishes the literal first and second derivative dictionaries for Phi using theta moments through order8. The eighth-moment tail is dominated by the existing fourth-moment tail at half argument. With v=exp(4u), actual normalized coefficients A0,A1,A2 differ from their leading coefficients by at most352*v*exp(-pi*v),20704*v^2*exp(-pi*v),568928*v^3*exp(-pi*v), respectively, for v>=1; denominator positivity is proved. Actual logarithmic slope and curvature comparisons have error at most1 for u>=1, with all moment assumptions discharged.

For every t>=0,u>=1 satisfying the ACTUAL stationary equation F_t(u)=4*t*u^3+Phi'(u)/Phi(u)=0, F'_t(u)<=-4*pi*exp(4u)-23<0. Existing escape-of-all-maxima results imply nondegeneracy of EVERY global positive-half-line amplitude maximum at EVERY sufficiently large time, without excluding exceptional times. The exact saddle-time map is positive with positive derivative and strictly increasing on[1,infinity). There is at most one stationary point there at each time, and eventually a unique global amplitude maximum on[0,infinity). This is not uniqueness on the full real line or uniqueness of a Fourier zero.

At actual stationary points u>=1, pi*exp(4u)-3<=t*u^3<=pi*exp(4u)-2. With M=4*t*u^2*(4*u-3), t>=0 gives M+31<=abs(F'_t(u))<=M+52. For t>0, M>0 and abs(abs(F'_t(u))/M-1)<=13/t. The bare leading model at its own exact stationary point has curvature 4*t*u^2*(3-4*u)-36. Thus the exact curvature equality displayed in ibm_laguerre_polya.tex lines626-632 requires correction; its leading asymptotic interpretation is rigorously supported. The manuscript is preserved, and its window conclusion is not thereby disproved.

RiemannQuarticSaddleBranch now exposes its existing nonzero-derivative constructor, preserving all six old public interfaces. Combining it with actual curvature gives analytic complex-frequency local continuation at ALL sufficiently large times and ALL actual maxima: branch(0)=u, G_t(branch(z))=-i*z, branch'(0)=-i/G'_t(u), with Re(exp(4*branch(z)))>0 and PhiComplex(branch(z))!=0 nearby. The older exceptionalTimes set is not claimed bounded or empty. The inverse neighborhood is still local and has no effective uniform frequency radius.

RiemannQuarticSaddleNeighborhood proves quantitative integration-variable geometry on closedBall((u:C),1/16), for every realu>=1. Throughout it, Re(w)>=0, Re(exp(4w))>=exp(4u)/2>=8, and norm(exp(4w))<=4*exp(4u)/3. The actual kernel is analytic and nonzero and the actual slope analytic there. Explicit leading, derivative and residual envelope bounds imply norm(G_t(w)-modelDerivative(t,w))<=1 throughout this closed ball, for every realt. Complex Cauchy estimates then give ALL n: norm(iteratedDeriv n (G_t-modelDerivative) u)<=n!*16^n. This bounds the actual-model error jets, not the full slope jets independently of t and u.

These are integration-variable neighborhoods, NOT inverse frequency radii. The next central analytic obligations are quantitative inverse/continuation bounds, control through the expanding frequency window and far field, and connecting contour/endpoint geometry with signed integrated remainder bounds. There is no Gaussian integral approximation or global zero-control theorem yet. Neither A(4)<infinity nor A(4)=infinity nor any RH implication is established. A finite-time exit certificate, even when completed, cannot decide eventual re-entry.

Verification: full pinned root build passed5802 jobs, terminal exit0. Full transitive root axiom audit passed33260 Foundation declarations with only propext, Classical.choice and Quot.sound. ALL160 affected public types were actually read, including154 new and6 retained Branch API types, across648 audit-log lines. Manifest covers1730 Foundation/root Lean files; prior files are unchanged except the reviewed Branch refactor and root imports. All107 archived manuscript hashes,43 Incoming files/42 distinct hashes and all11 fully read A4 hashes match their baselines. No sorry/admit/new axiom, native admission, manuscript modification/staging or unrelated draft edits. Evidence: .lake/stardust-1118-full-build.log, stardust-1118-audit.log, stardust-1118-working-checkpoint.json, stardust-1118-source-integrity.json and stardust-1118-verification.json. Exact seven-path audited Git checkpoint and private synchronization follow this entry; the persistent research goal remains active.

## Verified quantitative quartic saddles and actual phase remainder, 2026-10-19 (1119)

Continued A(4) from audited/private-backed b7926c745c2561dbbe0128b0f93db2f848fa8882. The preceding goal turns made progress: checked actual inverse-disk, analytic branch and normalized-phase constructions, while preserving the sole live bounded value proof. That original value job46593/PID46108 is now TERMINAL0,4342 jobs, observed by14:56 EDT; no proof was restarted on silent polling. Full-root38567 and root-audit39830 are also terminal0. Terminal clock checkpoints include14:47:53,14:50:41,14:53:30,14:56:10,14:56:48 and14:57:33 America/New_York. IBM remains frozen8946076, A4 ACTIVE, A2 then final multichannel queued; October31 remains the stopping date. The objective is eventual GLOBAL re-entry or a rigorous obstruction, without assuming either alternative.

RiemannQuarticValueCells025To044 proves all60 actual exact rounded point-value checks for cells25 through44 and channels0 through2, plus their universally quantified range theorem. With prior cells0 through24,135 of480 memberships are proved;345 remain, cells45 through159. Existing derivative-grid, Taylor-quadrature and infinite-flow error theorems are reused. The t=8 negative-Laguerre certificate remains conditional on unfinished value checks; no finite-time exit certificate or infinite-threshold conclusion is inferred from endpoint totals.

RiemannQuarticQuantitativeSaddle bounds the actual-model slope-error derivatives throughout closedBall(u,1/32) by n!*32^n. Error and first-error-derivative Lipschitz constants32 and2048 are proved. For t>=0,u>=1 satisfying the ACTUAL real stationary equation, let Q=t*u^3+1. The actual complex slope G_t has norm<=100Q on radius1/16. Cauchy gives norm(D^n G)<=n!*100Q*32^n on radius1/32; G' is Lipschitz with constant204800Q there, while norm(G'(u))>=4Q.

On radius1/102400, norm(G'(w)-G'(u))<=norm(G'(u))/2. Reusing mathlib ApproximatesLinearOn.surjOn_closedBall_of_nonlinearRightInverse for complex scalar multiplication and proving injectivity, EVERY complex frequency norm(z)<=Q/51200 has EXACTLY ONE w in that small closed ball with G_t(w)=-i*z. Uniqueness is within that ball, not among all complex saddles. Kernel and slope derivative are nonzero there, with Re(exp(4w))>0. Existing escape of maxima makes this apply to ALL actual positive-half-line global amplitude maxima at EVERY sufficiently large time, with frequency radius at least(t+1)/51200. This is an effective growing frequency disk, beyond the fixed integration-variable ball of1118.

RiemannQuarticFrequencyBranch glues these unique saddles into a single branch b on the closed frequency disk, continuous there and analytic throughout its interior. It proves b(0)=u and b'(z)=-i/G'_t(b(z)). The quantitative scale is 2Q*norm(b(z)-b(y))<=norm(z-y), hence norm(b(z)-u)<=norm(z)/(2Q). In the small spatial ball, norm(G'_t(w))>=2Q; norm(b'(z))<=1/(2Q) on the open frequency disk. Local inverse theorems are glued using uniqueness and continuity, rather than assuming a global spatial logarithm.

Define the ACTUAL saddle weight W_t(z,w)=exp(t*w^4+i*z*w)*PhiComplex(w), and A(z)=W_t(z,b(z)). It is nonzero on the closed disk. The exact stationary equation and actual kernel derivatives give A'=i*b*A, A'/A=i*b, and (A'/A)'=1/G'_t(b(z)). Differentiating inverse curvature gives i*G''_t(b(z))/(G'_t(b(z)))^3, with norm<=25600/Q^2. A is the actual exponential kernel evaluated at the saddle; it is not the Fourier integral or its Gaussian-prefactor approximation.

Reusing mathlib DifferentiableOn.isExactOn_ball and Complex.IsExactOn.with_val_at constructs P with P(0)=0 and P'=i*b on the entire OPEN frequency disk. A zero-derivative argument proves A(z)=W_t(0,u)*exp(P(z)). Thus an actual normalized saddle phase exists, without assuming log(Phi) on a deformed spatial contour. It satisfies P''=1/G'_t(b(z)) and norm(D^3 P)<=25600/Q^2 throughout that disk.

RiemannQuarticPhaseRemainder proves a complex cubic Taylor bound by three mean-value estimates on closed disks. Applied to P it gives
  norm(P(z)-i*u*z-z^2/(2*G'_t(u)))<=25600*norm(z)^3/Q^2.
The curvature is ACTUAL, not the bare-model quantity whose exact manuscript equality needed correction in1118. The absolute constant is coarse; no optimal factorial constant is claimed. The nonzero quadraticSaddleWeight is W_t(0,u)*exp(i*u*z+z^2/(2*G'_t(u))). If delta=25600*norm(z)^3/Q^2<=1, the actual saddle weight divided by this approximation differs from1 in norm by at most2*delta. This is a complex relative-error bound, not only a modulus comparison. It supplies the cubic phase scale relevant to the manuscript's sub-two-thirds window; it does NOT establish an integrated two-saddle approximation or a zero-count theorem.

A separate checked cache .lake/RiemannQuarticContourProbe.lean (83537 terminal0, standard-three axiom print) proves actual integrand analyticity for abs(Im w)<=1/16 and an exact FOUR-segment finite rectangle identity, retaining both vertical endpoints. It is not promoted, root integrated or included in this checkpoint's107-type scope. It supplies no infinite contour shift. A proposed next target is uniform vertical-strip endpoint decay using existing relative_bound, leading_norm_upper and quartic_exponent_dominated; a candidate coarse bound5676*exp(-x) remains UNVERIFIED. The left endpoint must remain explicit until independently controlled or canceled.

Central remaining analysis: actual Gaussian prefactor and its branches, contour geometry, connecting segments and endpoints, and a SIGNED INTEGRATED remainder controlled relative to the dominant saddle through the window and far field. Neither local analytic saddles nor pointwise complex weight errors exclude outward-migrating nonreal zeros. The manuscript expanding-window theorem still needs a repaired integrated proof. Neither A(4)<infinity nor A(4)=infinity nor an RH or A2-threshold implication is proved. No switch to the queued campaigns is justified.

Verification: pinned full root build PASSED5807 jobs, terminal0. Fresh FULL root transitive axiom audit PASSED33443 Foundation declarations with only propext, Classical.choice, Quot.sound. ALL107 public types were printed and actually read across the complete audit log:61 value,15 quantitative saddle,25 branch/phase,6 remainder. Manifest covers1734 Foundation/root Lean files; every previously manifested Foundation source is unchanged, with root imports the sole prior Lean-source change. All107 archive hashes,43 Incoming files/42 distinct hashes and11 fully read A4 manuscript hashes match their baselines. No sorry/admit/new axiom/native admission, manuscript staging or unrelated draft edits. Evidence: .lake/stardust-1119-full-build.log, stardust-1119-audit.log, stardust-1119-working-checkpoint.json, stardust-1119-source-integrity.json and stardust-1119-verification.json. Exact seven-path audited Git checkpoint, exact-commit approval and private synchronization follow this entry. The indefinite research goal remains active.

## Verified signed saddle contour, endpoint budgets and local Gaussian integral error, 2026-10-19 (1120)

Continued A(4) from audited/private-backed8232c3c76a245815b46e687d77c686db28fc4464. Prior goal turns made progress by proving actual signed contour and endpoint/geometry results while preserving the sole bounded value proof. This turn constructs the actual spatial saddle phase and SIGNED local Gaussian integral error, and closes the full checkpoint. Original value26427/PID29604 is TERMINAL0,4342 jobs, observed by15:35 EDT; it was never duplicated or restarted on silent polling. Fullroot58463 and root-audit24291 are terminal0. Terminal clock checks include14:59:56,15:12:48,15:19:58,15:26:12,15:32:47,15:35:08,15:35:54 and15:36:57 America/New_York. IBM remains frozen8946076, A4 ACTIVE, A2 then final multichannel queued; October31 stop. The target remains eventual GLOBAL reentry or its rigorous obstruction, without assuming either alternative.

RiemannQuarticValueCells045To064 proves all60 exact actual value checks for cells45 through64/channels0 through2, plus the range theorem. With prior cells0 through44,195 of480 memberships are proved;285 remain, cells65 through159. Existing interval evaluator, derivative grid, Taylor quadrature and infinite-flow error bounds are reused. The t=8 negative-Laguerre certificate remains conditional; exact endpoint totals do not replace missing memberships and no unconditional exit certificate is claimed here.

RiemannQuarticContour proves analyticity of W_t(z,w)=exp(t*w^4+i*z*w)*PhiComplex(w) in abs(Imw)<=1/16. For Rew>=0 its kernel norm is<=5676*exp(9*Rew)*exp(-(pi/2)*exp(4*Rew)); for Rew>=1 the actual integrand norm is<=5676*exp(16*abs(t)*(Rew)^4+(2*norm(z)+9)*Rew-(pi/2)*exp(4*Rew)). Reusing relative_bound, leading_norm_upper and quartic_exponent_dominated establishes a uniform vertical-strip tail<=5676*exp(-x), eventually in x for each FIXED t,z. The cutoff may depend on t,z; joint uniformity for unbounded parameters is not asserted. Actual shifted half-line weights are genuinely Bochner integrable.

The exact four-segment rectangle identity, its right-endpoint norm bound5676*h*exp(-L), and the limit of that endpoint prove, for all realt, complexz and0<=h<=1/16, the ACTUAL SIGNED identity
  integral_(0,infinity) W_t(z,x)dx = integral_(0,infinity) W_t(z,x+i*h)dx + i*integral_0^h W_t(z,i*y)dy.
Both finite endpoints were retained until the right one was proved to vanish. The left term remains with its sign; no cancellation or spatial parity is assumed.

For Rez>=0, norm(W_t(z,i*y))<=5676*exp(abs(t)*h^4) on0<=y<=h<=1/16, giving left-endpoint norm<=5676*h*exp(abs(t)*h^4), INCLUDING z=0 and uniformly in frequency in that half-plane. This repairs the endpoint-control route without the manuscript's division by abs(g'(0)+i*z), which vanishes at zero. Any actual global positive-half-line amplitude maximum has value M_t>=exp(t)*Phi(1)>0. For t>=0, the retained endpoint/M_t is<=[5676/(16*Phi(1))]*exp(-t/2).

RiemannQuarticEndpointSaddle compares this to the actual frequency-dependent saddle weight A(z)=W_t(z,b(z)). Let Q=t*u^3+1 at t>=0,u>=1 satisfying the actual stationary equation. If Imz<=0, norm(z)<Q/51200, delta=25600*norm(z)^3/Q^2<=1 and norm(z)^2<=tQ, then norm(A(z))>=M_t*exp(-t/8-1). For an actual global maximum and ALSO Rez>=0, endpoint/norm(A(z)) is<=[5676/(16*Phi(1))]*exp(1-3t/8). These disk, lower-right-quadrant, delta and region assumptions are explicit. Automatic inclusion of the manuscript's entire asymptotic window is not proved. This ratio is not yet normalized by the Gaussian prefactor.

RiemannQuarticSaddleGeometry proves the FULL complex real-center identity G'_t(u)=ofReal(F'_t(u)), including zero imaginary part. Scalar linearization and negative real curvature show that a nearby actual saddle G_t(w)=-i*z has Imw>=0 whenever Rez>=0. The coherent branch has positive real part and0<=Im(b(z))<=1/102400 on the closed frequency disk. The actual signed contour identity is therefore instantiated at that saddle height: its shifted horizontal half-line passes through the saddle, retaining the left vertical integral. This closes the previously open height/sign choice in this domain.

Throughout the small spatial ball Re(G'_t(w))<=F'_t(u)/2<0. Thus a=-G'_t(w)/2 has positive real part. Reusing mathlib integrable_cexp_neg_mul_sq and integral_gaussian_complex proves integrability and the exact NONZERO principal-power normalization
  integral_(real s) exp((G'_t(w)/2)*s^2)ds = [pi/(-G'_t(w)/2)]^(1/2).
It uses the ACTUAL curvature and applies at b(z). This is the normalization of the quadratic Gaussian MODEL, not an identification of the full shifted integrand or its Fourier integral with that model.

RiemannQuarticSpatialPhase constructs a normalized SPATIAL phase P(v) on norm(v)<1/102400 around any w in closedBall(u,1/102400), with P(0)=0 and P'=G_t(w+v)+i*z. The derivative identity for the actual kernel and a zero-derivative argument prove W_t(z,w+v)=W_t(z,w)*exp(P(v)). A log(Phi) branch on a deformed contour is not assumed. Existing actual Cauchy estimates give norm(D^3 P)<=204800Q. At an actual saddle, P'(0)=0 and P''(0)=G'_t(w), giving norm(P(v)-G'_t(w)*v^2/2)<=204800Q*norm(v)^3.

Under204800Q*norm(v)^3<=1, the actual weight divided by W_t(z,w)*exp(G'_t(w)*v^2/2) differs from1 in norm by at most409600Q*norm(v)^3. On real displacements the negative real curvature bounds the Gaussian modulus by1, giving the corresponding absolute weight error. All functions on the finite integration interval are actually continuous and interval-integrable.

The resulting SIGNED local integral theorem is, for0<=r<1/102400 and204800Q*r^3<=1,
  norm(integral_(-r)^r W_t(z,w+s)ds - W_t(z,w)*integral_(-r)^r exp(G'_t(w)*s^2/2)ds)
    <=819200Q*r^4*norm(W_t(z,w)).
This is an actual kernel-integral comparison at the actual saddle, not an expectation-level heat formula. It is a coarse bound and compares to the TRUNCATED quadratic Gaussian integral. It does not replace that integral by the full normalization or discard the complementary actual horizontal tails.

Central remaining work: quantify the Gaussian model tail and complementary ACTUAL shifted-integrand tails relative to the nonzero normalized saddle; connect the local interval with an exact split of the shifted half-line; control the opposite-frequency contribution/symmetry needed for the cosine transform; establish valid joint large-time/frequency estimates and any Rouche zero-count conclusion. The old spatial-phase and local SIGNED integral obligations are now proved, but a full integrated two-saddle theorem is not. Far-field exclusion and the possibility of outward-migrating nonreal zeros remain uncontrolled. Neither finite nor infinite A4, an expanding-window real-rooting theorem, A2-threshold transfer or RH is proved. No campaign transition is justified.

A selective theorem-reuse check located mathlib integral_mul_cexp_neg_mul_sq, whose Ioi0 first moment may supply a conservative Gaussian-tail bound; no new tail inequality has yet been proved. Reuse the existing Gaussian normalization and integral machinery rather than start an unrelated probability campaign. Incoming manuscripts remain research inputs, not assumptions.

Verification: pinned FULL root build PASSED5812 jobs, terminal0. Fresh FULL root transitive axiom audit PASSED33631 Foundation declarations with only propext, Classical.choice, Quot.sound. ALL105 public types were printed and actually read across the complete root audit log:61 value,17 contour,4 endpoint,11 geometry,12 spatial phase. Manifest covers1739 Foundation/root Lean files; all prior Foundation hashes unchanged and root imports the sole prior Lean-source change. All107 archive hashes,43 Incoming/42 distinct and11 fully read A4 hashes match baselines. No sorry/admit/new axiom/native admission, manuscript modification/staging or unrelated draft edits. Evidence: .lake/stardust-1120-full-build.log, stardust-1120-audit.log, stardust-1120-working-checkpoint.json, stardust-1120-source-integrity.json and stardust-1120-verification.json. Exact EIGHT-path audited Git checkpoint, exact-commit approval and private synchronization follow this entry. The indefinite goal remains active.

## Verified actual shifted tails and fixed-window Gaussian comparison, 2026-10-19 (1121)

Continued A4 from audited/private-backed b55d03339d5ecaa05e4f4b6c8c15202f6eed2402. The intervening user-question turn was a read-only source/objective confirmation, not a proof checkpoint. This turn advances the actual distant-tail analysis, preserves the original bounded value proof until terminal success, and integrates six new modules. Terminal clock checks include16:02:12,16:03:25,16:06:02,16:09:06,16:10:16,16:11:31,16:12:06,16:13:38,16:14:28,16:15:48,16:16:25 and16:17:03 America/New_York. IBM remains frozen8946076, A4 ACTIVE, A2 then final multichannel queued; October31 stop. The objective remains eventual GLOBAL reentry or a rigorous obstruction, without assuming either.

RiemannQuarticValueCells065To084 proves all60 exact rounded value checks for cells65 through84 and channels0 through2, plus the universally quantified range theorem. Original session68026/PID8936 completed4342 jobs, terminal0 observed16:13; it was never restarted on silence. Values0..84 now give255/480 memberships;225 remain, cells85..159. The t=8 negative-Laguerre certificate remains conditional on the remaining memberships. This finite-time exit question cannot decide eventual reentry.

RiemannQuarticGaussianTail proves the exact real first-moment tail integral integral_(a,infinity) x*exp(-c*x^2)dx=exp(-c*a^2)/(2c) for c>0 and any reala. It derives real and complex Gaussian tail bounds, including the full-minus-truncated complex Gaussian error<=exp(-Re(b)*r^2)/(Re(b)*r) for Reb>0,r>0. Evenness is used ONLY for the quadratic Gaussian model, not assumed for PhiComplex. Actual curvature yields Re(-G'_t(w)/2)>=Q, Q=t*u^3+1, near an actual real stationary u>=1,t>=0. The local SIGNED actual-integral/full-Gaussian error is<=norm(A)*(819200Q*r^4+exp(-Q*r^2)/(Qr)), with0<r<1/102400,204800Q*r^3<=1 and A=W_t(z,w) at an actual complex saddle. The full Gaussian normalization is Gfull=[pi/(-G'_t(w)/2)]^(1/2).

RiemannQuarticLocalTail proves the ACTUAL phase envelope Re(P(s))<=-3Q*s^2/4 for abs(s)<=1/819200, without the central small-error hypothesis at each point. Hence norm(W_t(z,w+s))<=norm(A)*exp(-3Q*s^2/4). Both real annulus sides have actual signed integral norm<=norm(A)*exp(-c*r^2)/(2cr), c=3Q/4. Exact finite-interval splitting gives
  norm(integral_(-R)^R W_t(z,w+s)ds-A*Gfull)
    <=norm(A)*(819200Q*r^4+exp(-Q*r^2)/(Qr)+exp(-c*r^2)/(cr)),
for0<r<=R<=1/819200 and204800Q*r^3<=1. This compares an actual signed kernel integral to the full Gaussian model; it is not an expectation formula.

RiemannQuarticWeightedSlope closes the ACTUAL global-in-x monotonicity connection. For t>0,x>=1,abs(h)<=1/102400,y<=0, put H(x)=Re G_t(x+i*h)-y. The model D-4 cancellation is4*t*[x^2*(3-4x)+h^2*(12x-3)]-36+4y, with bracket<=-x^3/2. Existing actual error<=1 and derivative error<=32 prove H'-4H<0, including the corrected constant budget32+4=36. Thus exp(-4x)*H(x) is strictly decreasing on[1,infinity). If H(a)=0,a>=1, H is positive beforea and negative aftera.

RiemannQuarticShiftedAmplitude proves the exact actual weight derivative and d(norm(W)^2)/dx=2*(Re G_t(x+i*h)-Imz)*norm(W)^2. For Imz<=0 and a shifted stationary point a>=1, norm(W)^2 is monotone on[1,a] and antitone on[a,infinity). If H(b)<=-k at b>=1,k>=0, actual weighted-slope monotonicity gives H(x)<=H(b) for everyx>=b. An exponential integrating factor gives norm(W(x+i*h))<=norm(W(b+i*h))*exp(-k*(x-b)). For k>0 the actual weight is Bochner integrable on(b,infinity), and its SIGNED integral norm is<=norm(W(b+i*h))/k. No assumed saddle-tail negligibility is used.

RiemannQuarticDistantTail discharges that quantitative boundary-slope hypothesis. Actual slope linearization atw obeys norm(G(w+R)-G(w)-G'(w)*R)<=204800Q*R^2 for0<=R<=1/819200. Actual curvature and the stationary equation imply Re G(w+R)-Imz<=-QR. For t>0,u>=2, an ACTUAL real stationaryu, actual complex saddlew within1/102400 ofu, Imz<=0,0<R<=1/819200, let a=Rew,h=Imw. Then
  norm(integral_(a+R,infinity) W_t(z,x+i*h)dx)
    <=norm(A)*exp(-3Q*R^2/4)/(QR).
The complementary actual left segment satisfies
  norm(integral_1^(a-R) W_t(z,x+i*h)dx)
    <=(a-R-1)*norm(A)*exp(-3Q*R^2/4).
The source proves a-R>=1 under these hypotheses. Both bounds are for actual SIGNED complex kernel integrals, not substituted Gaussian tails. Their horizontal estimates do not require Rez>=0; using the previously proved upward contour-through-saddle identity retains its explicit quadrant/frequency assumptions.

Central remaining obligations: control the compact actual segment[0,1] relative to the saddle; assemble an EXACT shifted-half-line decomposition with the proved window and distant tails; prove a useful lower bound for norm(Gfull) and joint parameter/radius limits, so errors are relative to norm(A*Gfull); control opposite-frequency pairing and the cosine transform; then establish valid zero counts and genuinely global FREQUENCY far-field estimates. The infinite integration-variable right tail now has a bound, but that does NOT provide uniform control at arbitrarily large complex frequencies: the current saddle stays within a small verified neighborhood. No full integrated two-saddle asymptotic, expanding-window real-rooting, finite/infinite A4, A2 transfer or RH is established. Outward-migrating nonreal zeros are not excluded. No campaign transition is justified.

Verification1121: pinned FULL root build PASSED5818 jobs, terminal0; fresh FULL transitive root axiom audit PASSED33802 Foundation declarations with only propext, Classical.choice, Quot.sound. ALL95 new public definition/theorem types were printed and actually read across the complete audit log:61value,7Gaussian,4LocalTail,12WeightedSlope,7ShiftedAmplitude,4DistantTail. This includes actual rather than model-tail scope, strict t>0 and u>=2 distant-tail domains, Imz<=0, the explicit nearby-saddle radius, the remaining compact segment and Gaussian normalization. Manifest covers1745 Foundation/root Lean files; all prior Foundation hashes unchanged, root imports the sole prior Lean-source change. All107 archived manuscript hashes,43 Incoming files/42 distinct and11 fully read A4 hashes match saved baselines. No sorry/admit/new axiom/native admission, manuscript modification/staging or unrelated draft edits. Evidence: .lake/stardust-1121-full-build.log, stardust-1121-audit.log, stardust-1121-working-checkpoint.json, stardust-1121-source-integrity.json and stardust-1121-verification.json. Exact NINE-path audited Git checkpoint, exact-commit receipt and private synchronization follow this entry. The indefinite goal remains active.

## Uniform actual half-line saddle asymptotics, 2026-10-19 (1122)

Continued from audited/private-backed fb1233c4c9f6d35154c981a7759fb839e76edee7. The preceding goal turn made substantive progress and closed1121 with full5818-job build,33802-declaration axiom audit,95 public types reviewed, exact nine-path commit and private sync. A4 remains ACTIVE; IBM frozen8946076; A2 then final multichannel queued; October31 stop. Terminal clock checks include16:20:23,16:21:50,16:23:06,16:25:28,16:26:55,16:28:26,16:30:15,16:32:00,16:32:59,16:33:51,16:35:03,16:36:22 and16:37:04 America/New_York. No manuscript changes or campaign transition.

RiemannQuarticGaussianNormalization proves the ACTUAL Gaussian coefficient norm<=1600Q, Q=t*u^3+1, at every actual real stationaryt>=0,u>=1 andw within1/102400 ofu. Reusing mathlib integral_gaussian_sq_complex gives the EXACT identity norm(Gfull)^2=pi/norm(-G'_t(w)/2), Gfull=[pi/(-G'_t(w)/2)]^(1/2). Hence1<=40*sqrt(Q)*norm(Gfull). Production build52055 terminal0,3217jobs; root-plus-module axiom audit58548 terminal0,33805 declarations, standard3 only; ALL3 public types actually read.

RiemannQuarticCompactSegment bounds the ACTUAL integrand onx in[0,1],abs(h)<=1/16 by5676*exp(16*abs(t)+2*norm(z)+9); the SIGNED interval integral has the same bound. At an actual positive-half-line global amplitude maximumu>=1,t>=0, comparison of the maximum with the real point3 and the existing actual branch-phase lower bound give
  norm(integral_0^1 W_t(z,x+i*h)dx)/norm(W_t(z,b(z)))
    <=5676/Phi(3)*exp(10-503*t/8).
Explicit hypotheses remain norm(z)<Q/51200,Imz<=0,norm(z)<=t,25600*norm(z)^3/Q^2<=1,norm(z)^2<=tQ andabs(h)<=1/16. Inclusion of an entire asymptotic frequency window is not assumed. Production build29329 terminal0,3218jobs; root PLUS normalization/compact audit43502 terminal0,33808 declarations, standard3 only; ALL3 compact public types actually read.

RiemannQuarticHalflineApproximation proves the EXACT signed shifted-half-line split into compact0..1, left1..a-R, centered[-R,R] and infinite righta+R..infinity contributions, a=Rew,h=Imw. Every contribution is retained. For an actual saddlew near stationaryu, define
  H(Q,a,r,R)=819200*Q*r^4+exp(-Q*r^2)/(Q*r)
    +exp(-3Q*r^2/4)/((3Q/4)*r)
    +(a-R-1)*exp(-3Q*R^2/4)+exp(-3Q*R^2/4)/(Q*R).
Under t>0,u>=2,Imz<=0,0<r<=R<=1/819200 and204800Q*r^3<=1, a compact bound norm(compact)<=norm(A)*B gives the ACTUAL SIGNED integral comparison norm(Ih-A*Gfull)<=norm(A)*(B+H), A=W_t(z,w). The proved Gaussian lower normalization gives norm(Ih/(A*Gfull)-1)<=40sqrt(Q)*(B+H). Nonvanishing of bothA andGfull is discharged for this actual nearby saddle.

For the actual maximizing branch, the compact hypothesis is fully discharged by Bc=5676/Phi(3)*exp(10-503*t/8) under the explicit frequency conditions above. With ALSO Rez>=0, the previously verified contour-through-saddle identity and endpoint bound give the unshifted positive-half-line theorem
  norm((integral_0^infinity W_t(z,x)dx)/(A*Gfull)-1)
    <=40sqrt(Q)*(Bc+H(Q,Re(b(z)),r,R)+Be),
where Be=5676/(16*Phi(1))*exp(1-3*t/8). This is an ACTUAL signed Fourier-half-line estimate including the vertical endpoint, both actual distant tails, and full Gaussian normalization. It is not solely a pointwise saddle-weight or quadratic-model estimate. Production build87012 terminal0,3220jobs. Root PLUS all three new analytic modules transitive axiom audit15962 terminal0 PASSED33827 declarations, only propext,Classical.choice,Quot.sound; ALL6 HalflineApproximation public types actually read across the entire161-line audit. No parameter-limit or two-saddle conclusion is inferred from this finite error bound.

RiemannQuarticSaddleGrowth reuses stationary_scale_bounds, exponential domination and escape of ALL actual global maxima. For each naturaln, sufficiently large stationaryu satisfiesu^n<=t. For every fixedn, ALL actual positive-half-line global maxima at EVERY sufficiently larget satisfy u^n<=t; the cutoff may depend onn. ConsequentlyQ^n<=2^n*t^(n+1). These are uniform actual-kernel scale estimates supporting the next joint-limit argument; no zero assertion is made. All3 prototype axiom prints passed standard3; production build50825 terminal0 PASSED3203jobs. Root PLUS all four new analytical modules audit76919 terminal0 PASSED33830 declarations, only propext,Classical.choice,Quot.sound. ALL3 growth public types actually read. ALL15 new analytical public types have now been inspected; this combined audit still excludes the pending value module and is NOT the final full1122 root checkpoint.

RiemannQuarticErrorLimits now PROVES the shrinking-radius limits. Put r(Q)=Q^(-7/16). Exact identities are Q*r^2=Q^(1/8), sqrt(Q)*Q*r^4=Q^(-1/4), Q*r^3=Q^(-5/16), and sqrt(Q)/(Q*r)=Q^(-1/16). The radius tends tozero and, for every fixedR>0, eventually0<r<=R and204800Q*r^3<=1. Both normalized local Gaussian tails tend tozero; so do the normalized actual fixed-window left/right envelopes. In particular sqrt(Q)*H(Q,Q+1,r(Q),R)->0, and this envelope dominates every center-coordinatea<=Q+1. The time envelope80*t*(C*exp(10-503*t/8)+D*exp(1-3*t/8)) tends tozero for arbitrary fixedC,D. Production build88609 terminal0 PASSED3222jobs. Root PLUS all five new analytical modules audit19227 terminal0 PASSED33847 declarations, standard3 only; ALL15 ErrorLimits public types actually read. These are limits of the exact error expressions already controlling actual integrals.

RiemannQuarticUniformSaddle connects these limits with actual saddle growth. Every epsilon>0 eventually bounds the TOTAL relative error budget uniformly over ALL global amplitude maxima and ALL pointsw in their verified small complex saddle balls. The proof uses Q>=t, Q<=2t^2, sqrt(Q)<=2t and Rew<=Q+1 at all sufficiently large times; these inequalities are derived for the actual maxima, not assumed as arbitrary parameter growth. It also discharges the central-radius and small-error conditions uniformly.

Consequently uniform_unshifted_relative_error proves: for every fixed0<R<=1/819200 and epsilon>0, at EVERY sufficiently larget, for EVERY actual global maximizing stationaryu>=2 and EVERY frequencyz satisfying norm(z)<Q/51200,Rez>=0,Imz<=0,norm(z)<=t,25600*norm(z)^3/Q^2<=1 andnorm(z)^2<=tQ,
  norm((integral_0^infinity W_t(z,x)dx)/(W_t(z,b(z))*Gfull(b(z)))-1)<epsilon.
This is uniform convergence of an ACTUAL signed unshifted Fourier HALF-LINE integral relative to its ACTUAL frequency-dependent complex saddle and Gaussian factor, retaining all compact, horizontal-tail and vertical-endpoint contributions. The small-radiusr has been chosen and eliminated from this final theorem. The frequency inequalities remain explicit; automatic inclusion of every norm(z)<=curvature^gamma window has NOT been proved. UniformSaddle production build98961 terminal0 PASSED3223jobs. Root PLUS all six new analytical modules audit50731 terminal0 PASSED33858 declarations, only propext,Classical.choice,Quot.sound; ALL3 UniformSaddle public types actually read. ALL33 new analytical public types are inspected. This is not yet the final full1122 root audit including the pending value module.

A targeted manuscript reread of ibm_laguerre_polya.tex lines630-654 identifies the next exact reuse gap. The manuscript adds I_+(z) and I_+(-z) into a fixed-curvature Gaussian-damped cosine profile. The current new theorem is for I_+(z), with Imz<=0,Rez>=0, and an ACTUAL complex-frequency curvature. One cannot apply it automatically to I_+(-z): that frequency has the opposite imaginary sign. The second channel, comparison of its weight/prefactor with a common real-center quadratic model, uniform power-window inclusion, and Rouche zero counts are distinct remaining obligations. In the verified weighted-slope cancellation the scalar term includes+4y, so dropping y<=0 without another quantitative bound is not licensed. A targeted cache .lake/RiemannQuarticSecondChannelBudgetProbe.lean now verifies the quantitative ACTUAL inequality H'-4H<=-t for t>0,x>=1,abs(h)<=1/102400,y<=t/4, using the existing error and Cauchy bounds. Both scalar and actual-kernel axiom prints passed standard3, session44273 terminal0. This is checked evidence for a broader-y route, not a proof of the corresponding shifted-integral approximation; it is excluded from the planned94 public checkpoint types and no upper-half-frequency reconstruction is assumed. No symmetry/evenness of PhiComplex is introduced to hide the sign issue. No full integrated TWO-saddle/cosine theorem, expanding-window real-rooting, unrestricted FREQUENCY far-field control, finite/infinite A4, A2 transfer or RH is established.

RiemannQuarticValueCells085To104 now proves all60 exact rounded value checks for cells85 through104/channels0 through2, plus their universally quantified range theorem. Original value job40236/PID45032, started16:21EDT, was repeatedly directly confirmed live and completed4342 jobs, terminal0 observed16:53:58. It was never duplicated/restarted on silence. Values0..104 now give315/480 memberships;165 remain, cells105..159. The t=8 negative-Laguerre certificate remains conditional until the remaining memberships are proved; no finite-time exit or eventual-threshold conclusion is inferred from this count.

All seven new production modules are integrated into the root. Final1122 scope is1752 Foundation/root sources and94 public types (61value+33analytic), exact10paths in1122-prepare.py. All prior Foundation hashes are unchanged; root imports are the sole prior Lean-source change. ResearchSources and unrelated drafts remain untouched. Full-root checkpoint verification is complete as recorded below; exact Git checkpoint and private backup follow it.

Verification1122: pinned FULL root build PASSED5825 jobs, terminal0. Fresh FULL transitive root axiom audit PASSED33979 Foundation declarations with only propext,Classical.choice,Quot.sound. ALL94 new public definition/theorem types were printed and actually read across the complete audit log:61value,3normalization,3compact,6halfline,3growth,15error-limits,3uniform. This includes the actual Bochner half-line integral, full nonzero Gaussian denominator, every compact/tail/endpoint contribution, uniform epsilon/time/maximizer quantifiers, explicit quadrant/frequency conditions and the absence of a zero-count conclusion. Manifest covers1752 Foundation/root sources; all prior Foundation hashes unchanged, root imports the sole prior Lean-source change. All107 archive hashes,43 Incoming files/42 distinct hashes and11 fully read A4 hashes match their saved baselines. No sorry/admit/new axiom/native admission, manuscript modification/staging, dependency change or unrelated draft edit. Evidence: .lake/stardust-1122-full-build.log, stardust-1122-audit.log, stardust-1122-working-checkpoint.json, stardust-1122-source-integrity.json and stardust-1122-verification.json. Exact TEN-path audited Git checkpoint, exact-commit receipt and private synchronization follow this entry. All proof jobs are terminal0. The indefinite goal remains active; no campaign transition is justified.

## Verified paired saddle approximation on growing complex disks, 2026-10-19 (1123)

Continued from audited/private-backed e1f374e56a140c42155294ca97f68d12bd2250f3. The preceding goal turn made substantive progress: actual uniform one-half-line relative asymptotics, full5825-job build,33979-declaration standard3 axiom audit,94 public types read, exact ten-path Git checkpoint/private sync. No previous proof jobs remained live. A4 stays ACTIVE; IBM frozen8946076; A2 then final multichannel queued; October31 stop. Terminal clock checks include16:57:43,16:58:28,16:59:51,17:00:20,17:01:22,17:03:00,17:04:32,17:05:15,17:06:39,17:07:59,17:09:29,17:10:12,17:11:41 and17:12:24 America/New_York. ResearchSources remains unchanged.

The opposite-frequency domain issue identified in ibm_laguerre_polya.tex630-654 is being repaired directly. WeightedSlope now proves ACTUAL H'-4H<=-t for t>0,x>=1,abs(h)<=1/102400,y<=t/4. It gives strict antitonicity of exp(-4x)*H and the same before/after-zero sign conclusions in that broader domain. ShiftedAmplitude and DistantTail now prove the actual amplitude shape, pointwise exponential decay and signed tails for Imz<=t/4. HalflineApproximation's generic compact-bound and normalized relative-error theorems are correspondingly extended. ALL29 prior public signatures in these four modules, including let-bound conclusions, are unchanged; old theorems are corollaries of the broader proofs. This intentional proof factoring changes four prior Foundation sources and does not assume a previous theorem at a new domain. Source signature evidence: .lake/stardust-1123-yupper-api-compatibility.json.

Broader slope/tail production build92156 terminal0 PASSED3216jobs; root axiom audit23070 terminal0 PASSED33989 declarations, standard3, ALL33 affected types read (23retained+10new). Generic halfline production build42092 terminal0 PASSED3220jobs; root audit19148 terminal0 PASSED33991 declarations, standard3, ALL8 affected halfline types read (6retained+2new). Existing old one-half-line theorem APIs remain intact.

NEW RiemannQuarticSignedContour proves the actual finite-rectangle identity, vanishing right segment and SIGNED half-line contour identity for ANY abs(h)<=1/16, including downward shifts. At an actual nearby saddle, Rez<=0 implies Imw<=0; together with the old nonnegative-height theorem this proves Rez*Imw>=0. The vertical endpoint obeys norm(V)<=5676*exp(abs(t)*h^4)*abs(h) when Rez*h>=0, and its relative-to-real-peak bound is5676/(16*Phi(1))*exp(-t/2). Every signed contribution is retained; no complex-kernel parity or conjugation assumption is introduced. Production build94548 terminal0 PASSED3210jobs; root-plus-module audit73832 terminal0 PASSED34004 declarations, standard3; ALL11 new public types read.

NEW RiemannQuarticSuppressedSaddle keeps the EXACT linear phase term: Req>=-u*Imz-norm(z)^2/(8Q), Q=t*u^3+1. Under u*Imz<=t/8 and the existing disk/cubic-phase/region assumptions, the actual branch amplitude is>=real_peak*exp(-t/4-1). This condition implies Imz<=t/4 for u>=1,t>=0, so the broader actual tails apply. Compact/actual-saddle error is<=5676/Phi(3)*exp(10-251*t/4) when ALSO norm(z)<=t; signed endpoint/actual-saddle error is<=5676/(16*Phi(1))*exp(1-t/4), using the proved sign of Rez*Imw. With t>0,u>=2 and0<r<=R<=1/819200,204800Qr^3<=1, the actual unshifted positive-half-line relative error is<=40sqrt(Q)*(Bc+H(Q,Reb,r,R)+Be) in this domain, with NO quadrant restriction. The horizontal budgetH is the already verified local+left+infinite-right expression. Production build67718 terminal0 PASSED3222jobs; root-plus-module audit33059 terminal0 PASSED34013 declarations, only propext,Classical.choice,Quot.sound; ALL7 public types read. The frequency and suppression conditions remain explicit.

NEW production RiemannQuarticPairedSaddle verifies the slower time envelopes and the eventual uniform ACTUAL one-half-line relative estimate in the broader domain u*Imz<=t/8, with NO real-frequency sign restriction. It also proves the exact bridge jet0(t,z)=integral_(Ioi0) W_t(z,x)dx, reusing the existing actual-flow definition onIci0 and the Lebesgue singleton-null identity. The actual saddle/Gaussian contribution P(t,u,z)=W_t(z,b(z))*[pi/(-G'_t(b(z))/2)]^(1/2) is nonzero throughout the verified frequency disk.

The main new theorem uniform_actual_two_saddle is an ACTUAL two-channel approximation of the existing arithmetic quartic COSINE FLOW: for everyepsilon>0, at EVERY sufficiently larget, for ALL actual global maximizing stationaryu>=2 and EVERYz satisfying norm(z)<Q/51200,u*abs(Imz)<=t/8,norm(z)<=t,cubicphase25600*norm(z)^3/Q^2<=1 andnorm(z)^2<=tQ,
  norm(flow(t,z)-(P(t,u,z)+P(t,u,-z))/2)
    <=epsilon*(norm(P(t,u,z))+norm(P(t,u,-z)))/2.
Both frequency channels use their ACTUAL complex saddle and Gaussian factor; the signed contour endpoints, compact pieces and both infinite/finite horizontal tails have been accounted for. The error is scaled by the sum of MODULI, which is positive; their potentially vanishing complex sum is never a denominator. This is a genuine integrated actual-flow result, not just pointwise saddle weights or a formal expectation identity. Production build71173 terminal0 PASSED4352jobs. Root PLUS all new analytical production modules audit27844 terminal0 PASSED34037 declarations, only propext,Classical.choice,Quot.sound; ALL8 PairedSaddle public types actually read. ALL67 new/affected analytical public types are now inspected (29retained+38new), across the separate audited production logs.

NEW RiemannQuarticFrequencyRegion closes the automatic-domain obligation that was left as a candidate in the preceding turn. From actual maxima u^12<=t and Q<=2*t*u^3, s^3<=Q^2 implies(s*u)^12<=256*t^11. For the coarse explicit lower boundt>=256*8^12=2^44, positivity gives s*u<=t/8. Maxima eventually escape beyond16; this gives s<Q/51200, s<=t ands^2<=tQ. The actual cubic phase inequality25600*s^3/Q^2<=1 implies s^3<=Q^2, so ALL auxiliary paired-saddle frequency conditions are now derived at sufficiently large time. The corresponding uniform_cubic_phase_pair theorem needs only that cubic phase condition.

The scalar limit25600*Q^(3*gamma-2)->0 for everygamma<2/3 proves cubic_phase_power_window. Its actual-flow consequence uniform_power_window_pair states: for EVERYgamma<2/3 andepsilon>0, at EVERY sufficiently larget, ALL actual maximizing stationaryu>=2, EVERY complexz withnorm(z)<=Q^gamma satisfies
  norm(flow(t,z)-(P(t,u,z)+P(t,u,-z))/2)
    <=epsilon*(norm(P(t,u,z))+norm(P(t,u,-z)))/2.
Thus for0<gamma<2/3 this is an ACTUAL integrated paired-saddle estimate on a growing full complex disk, with the auxiliary suppression/disk/region conditions discharged. The window is expressed inQ=t*u^3+1; a curvature-power formulation is not silently substituted. Production FrequencyRegion build25928 terminal0 PASSED4353jobs; root PLUS all new analytical modules audit10228 terminal0 PASSED34045 declarations, only propext,Classical.choice,Quot.sound; ALL7 new public types actually read. ALL74 new/affected analytical public types have now been inspected, including all29 retained public statements.

The manuscript's fixed real-center Gaussian-damped cosine profile and its zero count are STILL NOT established by this actual paired-saddle theorem. The missing connection is quantitative comparison of the ACTUAL Gaussian prefactors and phases with a common real-center quadratic model, followed by Rouche zero counts. Existing branch displacement and phase-quadratic remainder results are reusable; the relative Gaussian-prefactor comparison remains open. No zero exclusion outside the growing window follows, so unrestricted FREQUENCY far-field control and eventual GLOBAL reentry remain open. No finite/infinite A4, RH or A2 transfer is claimed.

RiemannQuarticValueCells105To124 proves all60 exact rounded point-value checks for cells105 through124/channels0 through2, plus their range theorem. Original value job79631/PID45888, started16:58:23EDT, was repeatedly directly confirmed live and completed4342 jobs, terminal0 observed17:31:14. It was never duplicated or restarted on silence. Values0..124 now give375/480 memberships;105 remain, cells125..159. The t=8 negative-Laguerre certificate remains conditional; a finite-time exit would not decide eventual global reentry.

All five new production modules are integrated into the root. Final1123 scope is1757 Foundation/root sources and135 public types (61value+74new/affected analytic), exact12paths. Four intentional prior Foundation proof modules were factored through broader-domain theorems; all29 prior FULL public signatures are retained and checked. All other prior Foundation sources retain their hashes, and root imports are the only other prior Lean-source change. ResearchSources and unrelated drafts remain untouched. Full-root checkpoint verification is complete as recorded below; exact Git checkpoint and private backup follow it.

Verification1123: pinned FULL root build PASSED5830 jobs, terminal0. Fresh FULL transitive root axiom audit PASSED34166 Foundation declarations with only propext,Classical.choice,Quot.sound. ALL135 new/affected public definition/theorem types were printed and actually reviewed from the complete audit log:61value,16WeightedSlope,11ShiftedAmplitude,6DistantTail,8HalflineApproximation,11SignedContour,7SuppressedSaddle,8PairedSaddle,7FrequencyRegion. A faithful whitespace-collapsed display of all135 types, with namespace-only abbreviations and no removed arguments/hypotheses, was reviewed; original full types are retained in .lake/stardust-1123-public-types.json and the raw audit log. The review includes the actual arithmetic cosine flow, both ACTUAL complex saddle/Gaussian channels, the sum-of-moduli error scale, signed endpoints, exact Ici/Ioi bridge, uniform time/maximizer/frequency quantifiers, and the gamma<2/3 Q-power window without hidden auxiliary frequency assumptions. All29 retained FULL public signatures are unchanged. Manifest covers1757 Foundation/root sources; only the four documented broader-domain proof factorizations and root imports change prior Lean sources. All107 archive hashes,43 Incoming/42distinct and11 fully read A4 hashes match saved baselines. No sorry/admit/new axiom/native admission, manuscript modification/staging, dependency change or unrelated draft edit. Evidence: .lake/stardust-1123-full-build.log, stardust-1123-audit.log, stardust-1123-working-checkpoint.json, stardust-1123-source-integrity.json, stardust-1123-yupper-api-compatibility.json and stardust-1123-verification.json. Exact TWELVE-path audited Git checkpoint, exact-commit receipt and private synchronization follow this entry. All proof jobs are terminal0. The indefinite goal remains active; no A4 campaign transition or global-zero conclusion is justified.

## Working common Gaussian-cosine profile and zero strip, 2026-10-19 (1124)

The preceding user-directed turn was a read-only confirmation of the manuscript's exit/apparent-return narrative and the saved GLOBAL eventual-reentry objective; it did not advance proofs. The next safe action was completed:1123 fullbuild5830/rootaudit34166/ALL135publictypes was committed as66ba1648e4249566e7bd92736e4afeada2cae571 and approved with an exact-commit receipt. Independent private synchronization verified BOTH main and codex/stardust-pseudoprocess-calculus at that exact commit, private=true, one new commit secret-scanned. No manuscript, unrelated draft or unfinished proof was committed. A4 remains ACTIVE, IBM frozen8946076, A2 then final multichannel queued; October31 remains the stopping date. Both global finite/infinite alternatives remain open.

NEW RiemannQuarticGaussianPrefactor closes the previously recorded Gaussian-prefactor stability gap. For complexr with nonnegative real part, norm(r-1)<=norm(r^2-1). Applying this to principal square roots relative to a positive real coefficient proves the actual Gaussian relative-center bound102400*norm(w-u) throughout the verified small saddle ball. The principal branch is retained through the square root's nonnegative real part, rather than inferred from squared norms alone. The actual branch displacement gives norm(Gaussian(b(z))/Gaussian(u)-1)<=51200*norm(z)/Q, Q=t*u^3+1. Production build PASSED3218jobs, terminal0.

NEW RiemannQuarticCommonProfile combines that bound with the existing actual saddle-weight quadratic remainder. Its centerContribution C(z)=quadraticSaddleWeight(t,u,z)*Gaussian(t,u) is nonzero at every complexz for an actual stationaryu>=1,t>=0. For the existing disk and cubic-phase assumptions, norm(P(z)/C(z)-1)<=alpha*(1+beta)+beta, alpha=51200*norm(z)^3/Q^2, beta=51200*norm(z)/Q. EXACTLY (C(z)+C(-z))/2=K(z)*cos(u*z), with K(z)=W_t(0,u)*Gaussian(t,u)*exp(z^2/(2G'_t(u))). No assertion identifies actual zeros with cosine zeros. Production build PASSED4354jobs, terminal0.

NEW RiemannQuarticCommonProfileLimit proves the combined relative bound tends tozero uniformly on norm(z)<=Q^gamma for EVERY fixedgamma<2/3, using Q^(3gamma-2)->0 and Q^(gamma-1)->0. It then combines the actual paired-saddle theorem with BOTH channel comparisons. For everyepsilon>0, at EVERY sufficiently larget, ALL actual positive-half-line global maximizing stationaryu>=2 and EVERY complexz in that disk, norm(flow(t,z)-K(z)*cos(u*z))<=epsilon*(norm(C(z))+norm(C(-z)))/2. This is the actual arithmetic quartic cosine flow, with all previously controlled signed endpoints and tails retained. The common real-center profile gap recorded in1123 is now CLOSED at this domain, not merely proposed. Production build PASSED4356jobs, terminal0.

NEW RiemannQuarticCosineNormalization proves K(z) is nonzero and the EXACT norm-envelope identity (norm(C(z))+norm(C(-z)))/2=norm(K(z))*cosh(u*Imz). Consequently norm(flow(t,z)/K(z)-cos(u*z))<=epsilon*cosh(u*Imz), uniformly with the same eventual-time/maximizer/full-complex-window quantifiers. This supplies a precise error topology for zero-control arguments; the possibly cancelling cosine is never a denominator. Production build PASSED4357jobs, terminal0.

NEW RiemannQuarticZeroStrip proves abs(sinh(Imz))<=norm(cos z), then proves a small cosh-weighted cosine bound implies abs(Imz)<=2epsilon for0<=epsilon<=1/2. Its actual uniform_zero_strip theorem says: for EVERYgamma<2/3 anddelta>0, eventuallyALLt,ALLactual maximizing stationaryu>=2,EVERYzeroz of the actual quartic flow withnorm(z)<=Q^gamma satisfies u*abs(Imz)<=delta. This is concrete zero localization; it does NOT establish reality or simplicity. Production build PASSED4359jobs, terminal0.

Root PLUS the first three analytical modules audit41889 PASSED34209 declarations, standard3 only; ALL15 public types actually read. Root PLUS normalized module audit14863 PASSED34224 declarations, standard3; ALL5 additional public types read. Root PLUS all five analytical modules audit6786 PASSED34228 declarations, standard3; ALL3 additional ZeroStrip public types read. ALL23 new analytical public types have been inspected from complete printed types, including every quantified domain, actual arithmetic flow, nonzero envelope, growing full complex window and zero-strip conclusion. Raw evidence: .lake/stardust-1124-analytic-audit.log, stardust-1124-normalized-audit.log and stardust-1124-zero-audit.log. These are COMPONENT/root-plus-module audits, not the final full1124 root checkpoint.

A sole NEW bounded value proof for cells125..144/channels0..2 was started17:37:59EDT, session90914/PID45316. It is directly confirmed LIVE at17:49EDT and must not be duplicated/restarted on silence. Existing certified count remains375/480 until terminal0; if all60pass,435/480 with45remaining cells145..159. t8 negative-Laguerre exit certification remains CONDITIONAL. No new value module or analytical root import has yet been integrated into the root, and there is no1124fullbuild/Gitapproval yet. All1757 prior Foundation/root source hashes remain identical to1123; all107archive,43Incoming/42distinct and11A4 manuscript hashes match baselines. Five analytical modules and the sole value batch are new working sources.

Next: actual zero counts/reality/simplicity in growing windows, then unrestricted FREQUENCY far-field control or an explicit outward-pair obstruction. The existing infinite horizontal integration-variable tails are already controlled and must not be confused with this remaining frequency far field. Inspection found no ready general Rouche theorem in mathlib's Analysis/Complex directory; a direct route via Cauchy derivative estimates, local injectivity near cosine zeros, real-axis sign changes and conjugation may avoid introducing general argument-principle infrastructure. This route is a candidate, not an established result. Thin zero strips alone cannot prove exact real-rooting. Global reentry remains unresolved; no RH or A2 consequence is claimed. Wait for the original live value job before including it in the final fullbuild/axiomaudit/public-type review/integrity/Git/private-backup checkpoint.

### Actual growing-window REAL and SIMPLE zeros, 1124 continuation

The preceding goal turn made concrete proof progress: common-center Gaussian-cosine asymptotics and zero-strip localization were verified. The same bounded value job90914/PID45316 remains directly confirmed LIVE at18:02EDT; it has not been duplicated/restarted. The main zero-reality gap within growing windows has now been CLOSED, while the unrestricted frequency far field remains OPEN.

NEW RiemannQuarticNormalizedAnalytic proves the actual Gaussian envelope is entire, the actual normalized quartic flow is entire under the existing actual-stationary-center assumptions, and both obey conjugation symmetry. The actual Gaussian at a real center equals the positive real sqrt(pi/(-F'_t(u)/2)). The actual flow conjugation identity is proved directly from its signed cosine integral, not assumed from a generic manuscript statement. Production build39032 TERMINAL0 PASSED4359jobs.

NEW RiemannQuarticCosineLocalZeros proves explicit sine/cosine strip bounds and Lipschitz bounds, then uses the EXISTING Cauchy estimate and EXISTING scalar_ball_lower_bound to show: if an entire conjugation-symmetricf is within1/1000 ofcos on the closed unit disk centered at reala, then EVERYzero in the concentric radius1/1000 disk is REAL and has nonzero derivative. The proof bounds the derivative error by1/500, proves the real-center sine slope has norm>=1/2, obtains local injectivity, and compares a zero with its conjugate. It does not require the argument principle or a new general Rouche library. Production build16480 TERMINAL0 PASSED4361jobs. Root PLUS all seven analytical modules audit81740 TERMINAL0 PASSED34247 declarations, standard3 only; ALL14 additional public types actually read,37 analytical public types total.

NEW RiemannQuarticWindowZeros closes the actual growing-window theorem with this local criterion. Its power_window_margin gives Q^gamma+1<=Q^nu eventually when gamma<nu andnu>0. For0<gamma<2/3 choose gamma<nu<2/3, apply the normalized asymptotic on the larger window with epsilon=1/(1000*cosh1), and use the actual zero strip u*abs(Imz)<=1/1000. Rescalingy=u*z, the unit disk centered atRe(y) fits inside the larger verified frequency window. Every putative zero is therefore real; the normalized derivative and nonvanishing envelope also force the actual flow derivative to be nonzero.

Precisely uniform_real_simple_window: for EVERY0<gamma<2/3, at EVERY sufficiently larget, ALL actual maximizing stationaryu>=2 and EVERYcomplexz withnorm(z)<=Q^gamma, flow(t,z)=0 implies Imz=0 AND deriv(flowt)z!=0. No zero is asserted equal to a leading cosine zero. The further eventually_real_simple_zeros corollary ELIMINATES ALL saddle/maximizer assumptions: for EVERY0<gamma<2/3, eventuallyALLt, EVERYcomplexz withnorm(z)<=t^gamma, any actual-flow zero is REAL and SIMPLE. It reuses the proved existence and escape of actual global maxima and t<=Q, without assuming any manuscript saddle equation or RH. Production32055 TERMINAL0 PASSED4364jobs. Root PLUS all eight analytical modules audit57374 TERMINAL0 PASSED34258 declarations, only propext,Classical.choice,Quot.sound; ALL3 additional WindowZeros public types actually read. ALL40 new analytical public types have now been inspected; exact printed types are stored in .lake/stardust-1124-public-types.json.

This establishes the manuscript's widening-window conclusion independently through a repaired actual-kernel proof. It does NOT establish eventual GLOBAL re-entry: a nonreal pair could still migrate beyond every such window. Full1124 checkpoint still awaits the ORIGINAL live bounded value proof, then nine new modules(61value+40analytic=101 public types), root integration, fullbuild/rootaxiomaudit/review/integrity/exact12pathGit/private sync. The final preparation script is .lake/stardust-1124-prepare.py, baseline1757 CLOSED1123 sources; final expected manifest1766. It has NOT yet been run against a fully integrated root.

A targeted .lake/RiemannQuarticKernelReflectionProbe.lean is investigating a far-field connection: use the verified theta modular reflection and kernel=(psiSecond-psi)/8 to prove arithmetic kernel evenness, then analytic complex reflection and cancellation of paired vertical contour endpoints. Real kernel evenness is checked in the current prototype; the complete complex connection is NOT yet established or part of the production/root audit. Separately, existing RiemannQuarticSaddleTheta.saddle_real_lower and saddle_theta_relative already provide frequency-independent theta-tail suppression at CONDITIONAL leading-model saddles. Existing SaddleNeighborhood.logDerivative_coarse_bound is general in complexw withRew>=0 andRe(exp4w)>=1; its second term is30000*exp(4Rew-3piRe(exp4w)). Neither model saddle existence for ALL frequencies, actual far-field saddle continuation nor integrated signed far-field dominance has been proved. These are specific next obligations, not reasons to infer global reentry from the expanding window.

### Exact arithmetic reflection, paired contour cancellation, and completed value batch

RiemannQuarticKernelReflection is now production, promoted from the targeted prototype after terminal0. The verified theta modular reflection is differentiated twice using the existing exact psi/psiPrime/psiSecond derivatives. Together with kernel=(psiSecond-psi)/8 this proves kernel(-u)=kernel(u) on the ENTIRE real line. Complex moments and kernel obey conjugation. The analytic identity theorem on the convex natural strip abs(Imw)<pi/8, using real points1/(n+1) approaching0, proves kernelComplex(-w)=kernelComplex(w) throughout that strip. No symmetry is assumed from manuscript text or extended outside the proved analytic domain.

Combining that arithmetic reflection with the ACTUAL quartic weight gives W_t(-z,-w)=W_t(z,w). Substitution in the SIGNED interval integral proves the two vertical endpoint terms at heights h and-h cancel EXACTLY. Consequently flow_eq_paired_horizontal expresses the ACTUAL cosine flow, for EVERYreal t, EVERYcomplex z and EVERYrealh withabs(h)<=1/16, as ONE HALF the sum of the two horizontal positive-half-line integrals with frequencies z,-z and heights h,-h. There is NO residual vertical endpoint term and NO saddle, quadrant, suppression or frequency-size assumption in this exact identity. The contour-height restriction is inherited from the existing verified contour theorem; reflection alone does not extend that theorem up to pi/8. This is a useful direct far-field connection, not an assertion of far-field dominance. Prototype29573 TERMINAL0 printed standard3 only for paired-flow/reflection/conjugation theorems. Production13226 TERMINAL0 PASSED4365jobs. Its12 public types await the fresh full root audit/review below.

The ORIGINAL bounded value session90914/PID45316, started17:37:59EDT, completed4342jobs TERMINAL0 observed18:10:23EDT. It was preserved through repeated authoritative live observations and was never duplicated/restarted on silence. New ValueCells125To144 proves all60 exact rounded point-value checks for cells125..144/channels0..2 and its universal range theorem. Certified values0..144 now total435/480. Remaining45 are cells145..159. The t8 negative-Laguerre exit certificate remains CONDITIONAL until those actual point-value memberships are verified; no exit/reentry conclusion is inferred from partial totals.

All TEN new production modules, including the completed value batch, are now integrated into the root. Final1124 scope is1767 Foundation/root sources and113public types(61value+52analytic), exactTHIRTEENpaths. All1757 prior Foundation/root hashes match CLOSED1123 except the explicitly reviewed root imports; no old mathematical proof was changed. All107archive,43Incoming/42distinct and11 fully read A4 manuscript hashes remain unchanged. Full-root11909 is now running after originalvalue terminal0. No fresh1124rootaudit/Gitapproval is assumed before completion.

Verification1124: pinned FULL root build PASSED5840 jobs, session11909 TERMINAL0. Fresh FULL transitive root axiom audit PASSED34396 Foundation declarations, session19960 TERMINAL0, with only propext,Classical.choice,Quot.sound. ALL113 new public types were printed and ACTUALLY READ from the complete fresh audit:61value+5GaussianPrefactor+5CommonProfile+5CommonProfileLimit+5CosineNormalization+3ZeroStrip+7NormalizedAnalytic+7CosineLocalZeros+3WindowZeros+12KernelReflection. A faithful whitespace-collapsed display with namespace-only abbreviations, without removing arguments/hypotheses, was reviewed in groups1..61,62..101,102..113. Exact unabridged printed types are saved in .lake/stardust-1124-public-types.json. The review explicitly covers the ACTUAL arithmetic flow, eventual-time/full-complex-disk quantifiers, all0<gamma<2/3, removal of saddle hypotheses in the t^gamma corollary, real AND nonzero derivative conclusions, the natural-strip reflection domain and exact signed paired contour identity with abs(h)<=1/16. Manifest1767 covers every Foundation/root Lean source; prior1757 sources retain hashes except documented root imports. All107archive,43Incoming/42distinct and11fullyreadA4 hashes match baselines. No sorry/admit/new axiom/native admission, manuscript changes/staging, dependency edits or unrelated draft modifications. Originalvalue90914/PID45316 completed4342jobs exit0;435/480 values certified,45 remain. All proof jobs are now terminal0. Evidence: .lake/stardust-1124-full-build.log, stardust-1124-audit.log, stardust-1124-working-checkpoint.json, stardust-1124-source-integrity.json, stardust-1124-public-types.json and stardust-1124-verification.json. Exact THIRTEEN-path audited Git checkpoint, exact-commit receipt and private synchronization follow. A4 and the indefinite research goal remain ACTIVE. Growing-window reality/simplicity is proved; unrestricted frequency far-field/global reentry and the final t8 value checks remain OPEN.

## Working natural-strip contours and representation boundary, 2026-10-19 (1125)

The preceding goal turn made substantive progress: actual growing-window real/simple zeros and exact arithmetic reflection/paired endpoint cancellation were fully verified and privately backed asb1db3e89927b0200b96d6103e7397eef24b14e84 (fullbuild5840/rootaudit34396/ALL113publictypes). The campaign remains A4 ACTIVE, IBM frozen8946076, A2 then final multichannel queued, October31 stop. No global finite/infinite alternative is adopted. Original final value job97399/PID25296, started18:14:09EDT, is authoritatively confirmed LIVE18:27EDT and remains unduplicated. Certified435/480 still; its final45cells145..159 cannot be counted before terminal0.

NEW RiemannQuarticNaturalContour replaces the fixed1/16 contour restriction with EVERY CLOSED SUBSTRIP abs(Imw)<=H<pi/8. The positive margin is cos(4H)>0, and Re(exp4w)>=cos(4H)*exp(4Rew). Existing exact theta remainder and leading estimates give the actual kernel envelope5676*exp(9Rew-piRe(exp4w)) onceRe(exp4w)>=1/2. For ALL realt and complexz, actual shifted weight is eventually<=5676*exp(-x), UNIFORMLY ALL |h|<=H. The cutoff depends onH,t,z; no uniformity asH approachespi/8 is asserted. The proof reuses the existing quartic/exponential domination with coefficients divided bycos(4H), not an unverified far-field asymptotic.

Consequently actual horizontal half-line integrals are absolutely Bochner integrable, the actual signed right vertical segment vanishes, and the exact signed rectangle/half-line contour identities hold for ANY FIXED |h|<pi/8. Combining the ALREADY PROVED arithmetic kernel reflection with signed substitution cancels the two vertical endpoint terms exactly throughout this larger range. The final flow_eq_paired_horizontal theorem: for EVERY realt, EVERYcomplexz, EVERYrealh with|h|<pi/8, the ACTUAL quartic cosine flow equals half the sum of the positive horizontal integrals at frequenciesz,-z and heightsh,-h. No saddle existence, frequency-size restriction, quadrant, dominant-saddle division or logarithm ofPhi is assumed. Production31891 TERMINAL0 PASSED4366jobs. Root PLUS new module audit10447 TERMINAL0 PASSED34411declarations,std3 only; ALL13publictypes printed and ACTUALLY READ.

NEW RiemannQuarticStripBoundary records the precise raw-series obstruction. For EVERY natural moment orderk and EVERY complexv withRev<=0, the actual complexThetaTerm norms are>=1 and the series is NOT summable. In particular Re(exp4(x+i*pi/8))=0 and ALL these raw moment series fail on the top strip boundary at everyrealx. This is a representation-domain obstruction, NOT a proof against analytic continuation by other means or against eventual global quartic real-rooting. It forbids silently replacing |h|<pi/8 by equality in these theta-series contour arguments. Production86696 TERMINAL0 PASSED4367jobs; prototype26719 terminal0 standard3. Root PLUS both new production modules audit22020 TERMINAL0 PASSED34414declarations, only propext,Classical.choice,Quot.sound. ALL3 additional public types ACTUALLY READ,16analytical types total; unabridged printed types in .lake/stardust-1125-public-types.json.

A targeted .lake/RiemannQuarticFarModelProbe.lean now reuses existing scalar_ball_surj/scalar_ball_injective to construct a UNIQUE leading-model saddle in radius1/1024 about an exponential anchorb when4*pi*exp(4b)=i*x andx>=10000*(t+1)*M^3, normb<=M-1,M>=1,t>=0. The anchorb=a+i*pi/8 is proved exact, and the quantitative size condition eventually holds for every fixedt as a grows. Verified prototype9437 TERMINAL0 printed standard3 for this construction and its actual theta-kernel nonvanishing/tail connection. New extensions to EVERY sufficiently large realfrequencyx and the strict-strip/actual-horizontal-contour connection are currently RUNNING under SAME prototype25717; do not assume those newest claims before terminal0 and an audit. The prototype is not yet production/root-integrated and is not part of the16publictype checkpoint scope.

All1767 CLOSED1124 Foundation/root hashes remain unchanged; no new root imports yet. All107archive,43Incoming/42distinct and11A4 manuscripts match baselines. No manuscript, unrelated draft or dependency modification. Full1125 build/Git approval awaits originalvalue job and final proof scope. Main objective remains unrestricted FREQUENCY far-field saddle existence/actual continuation/integrated signed dominance or an outward-pair obstruction. Natural-strip contour access is now verified; it does NOT itself give a saddle approximation or global zero control.

### Constructed far-frequency model saddles and actual phase residual, 1125

The prior far-model prototype93832 TERMINAL0 completed the all-large-frequency/strict-strip/actual-contour extension, and final49458 TERMINAL0 completed the actual phase residual envelope. These results are now production RiemannQuarticFarModelSaddle, build4414 TERMINAL0 PASSED4367jobs. Root PLUS all three new analytical modules audit46524 TERMINAL0 PASSED34434 Foundation declarations, standard3 only. ALL15 FarModelSaddle public types were printed and ACTUALLY READ, including every quantifier and model/actual distinction. Together with13NaturalContour and3Boundary, ALL31new analytical public types have been inspected; exact printed types are in .lake/stardust-1125-public-types.json. The earlier model prototype-running status is superseded.

The new anchored_far_saddle theorem REUSES existing scalar_ball_surj/scalar_ball_injective: ift>=0,M>=1,x>=10000*(t+1)*M^3,normb<=M-1 and4*pi*exp(4b)=i*x, then there is EXACTLY ONE root of modelDerivative(t,w)=-i*x within the radius1/1024 closed ball aboutb. Uniqueness is ONLY within that ball. The proof controls the actual derivative of the explicit leading model near its exponential anchor and the actual center residual; no saddle existence is assumed. Choosingb=a+i*pi/8 gives an exact anchor forx=4*pi*exp(4a), with normb<=a+1. The scale condition eventually holds for every fixedt by the existing verified polynomial/exponential domination.

The constructed roots have Rew>=2 andabs(Imw)<=1/2. The EXACT real stationary identity forces Re(exp4w)>0 and, in this height range, abs(Imw)<pi/8; the anchor is on the boundary but the resulting MODEL SADDLE is STRICTLY inside. For everyfixedt>=1 and EVERY sufficiently large realfrequencyx, eventually_frequency_model_control constructs such aw near log(x/(4*pi))/4+i*pi/8, proves the ACTUAL arithmetic kernel is nonzero there, and supplies the existing exact theta-tail bound for everyk<=4 with factor32*exp(-(3/4)*(t*Rew^3+9)). The frequency threshold may depend ont; this is NOT a uniform-in-time global zero theorem.

Crucially eventually_frequency_model_contour connects the constructed model saddle's height to the ACTUAL flow: for everyfixedt>=1 andALLsufficientlylargex, the actual quartic flow at realx equals the exact sum of its two opposite horizontal integrals at the model saddle height, divided by2. Actual theta kernel, actual signed integrals and all endpoints are retained/cancelled by proved identities. It is NOT asserted that the ACTUAL logarithmic phase is stationary at this model point.

The precise remaining model/actual mismatch is now bounded. actual_slope_residual_at_model proves norm(G_t(w)+i*x)<=5*exp(-4Rew)+30000*exp(4Rew)*exp(-(3/4)*(t*Rew^3+9)) for t>=1,Rew>=2,abs(Imw)<=1/2 and the exact model stationary equation. HereG_t is the ACTUAL phase slope. Its proof uses the existing general actual logarithmic-derivative residual bound onRe(exp4w)>=1, with that domain derived from model stationarity andt*Rew^3>=7. The scalar envelope is<=30005*exp(-Rew) forRew>=4. Hence residual_in_anchor_ball gives the actual phase-slope residual<=30005*exp(-a/2) throughout the stated set of MODEL roots near a+i*pi/8,a>=8,t>=1. This is a pointwise residual theorem at model roots; it DOES NOT prove an actual saddle or an integrated Gaussian asymptotic.

Next exact analytic obligation: control that actual/model residual on a WHOLE shrinking neighborhood of the model saddle, retain a positive Re(exp4w) margin and kernel nonvanishing there, then use Cauchy and the existing scalar inverse machinery to correct to an actual saddle. A promising radius is proportional to1/x: a uniform residual envelope on radius2/x would give a derivative-error bound on radius1/x, and a sufficiently small point residual could then fall inside the verified inverse-image radius. This proposed neighborhood/correction argument is NOT yet proved. Integrated far-field dominance and an eventual-time global zero theorem remain separate. The raw theta-series boundary obstruction forbids assuming Gaussian neighborhoods can crossabs(Imw)=pi/8. Both global A4 alternatives remain OPEN; no RH/A2 result follows.

The original final value session97399/PID25296 remains LIVE at18:37EDT and is not duplicated. A .lake/stardust-1125-laguerre-witness-template.lean is PREPARED but intentionally NOT compiled while its final value dependency is still live. Once terminal0, it will combine the nine exact value ranges and existing grid/quadrature/infinite-flow bounds to prove the explicit actual t8 Laguerre inequality violation. It does not introduce a new Laguerre-Polya class or pretend that generic LP membership/zero-existence infrastructure has already been formalized. Final proposed scope: five new modules,81publictypes(46value+31analytic+4witness),1772Foundation/root sources, exact8commitpaths; fullroot integration/build/audit/Git pending. Baseline remains CLOSED1124's1767sources; original manuscripts unchanged.

### Complete actual t8 Laguerre witness and final checkpoint scope

The ORIGINAL final value job97399/PID25296, started18:14:09EDT, completed4342jobs TERMINAL0 observed18:39:58EDT. It was never duplicated or restarted on silent observations. RiemannQuarticValueCells145To159 proves all45 exact rounded point-value memberships plus its universal range theorem. All160cells/threechannels now give480/480 verified memberships. The previously unresolved finite value-membership obligation is CLOSED.

NEW RiemannQuarticLaguerreWitness combines the verified firstfive cells with the eight verified value ranges using the actual check predicates, then REUSES existing CertifiedGrid negative_of_cell_checks/real_negative_of_cell_checks. The actual infinite-flow Laguerre expression at t8,x=632083/10000 is STRICTLY less than-2/10^20. Its real derivative statement is (d/dx realFlow8(x))^2-realFlow8(x)*(d^2/dx^2 realFlow8(x))<-2e-20 at that point. The theorem laguerre_inequality_fails gives the corresponding failure of the universal nonnegative Laguerre inequality. All cell derivatives, exact interval memberships, Taylor quadrature, arithmetic-kernel truncation and infinite-flow derivative error connectors are the existing verified ones; no external Arb output is trusted. Production24776 TERMINAL0 PASSED4355jobs.

This establishes the manuscript's finite-time NEGATIVE SIGN claim independently. It does not assert the manuscript's narrower [-2.3966,-2.3965]e-20 enclosure. The new Lean theorem states the explicit actual-flow inequality; it does NOT introduce or claim an already formalized LP-membership/entire-function zero-existence criterion. A generic Laguerre-Polya exclusion and a nonreal-zero existence theorem must be distinguished from this exact numerical witness when describing formal scope. In any case a finite-time violation cannot decide eventual global reentry or imply RH.

All FIVE new production modules are integrated into the root. Final1125scope:1772Foundation/root sources,81publictypes(46value+13NaturalContour+3StripBoundary+15FarModelSaddle+4LaguerreWitness), exactEIGHTpaths. All1767 CLOSED1124 source hashes remain unchanged except root imports; all107archive,43Incoming/42distinct and11A4 manuscript hashes match their saved baselines. Full-root51329 is running after the original finalvalue and witness jobs reached terminal0. No fresh root audit or Git approval is assumed before it completes.

A separate checked .lake/RiemannQuarticCorrectionProbe.lean now proves three targeted neighborhood facts: exp4 difference<=8*norm(exp4w)*norm(v-w) when4norm(v-w)<=1; a model saddle with polynomial residual scale<=x hasnorm(exp4w)<=x; and forx>=8,norm(exp4w)<=x,norm(v-w)<=2/x, Re(exp4v)>=Re(exp4w)-16. Prototype42631 TERMINAL0 printed standard3 for the transitive neighbor_real_margin theorem. This is a precise first step toward retaining the actual kernel's domain on shrinking neighborhoods. It is NOT production/root-integrated, has not had full public-type review, and does not yet establish actual saddle correction, analytic residual derivative control or integrated far-field dominance. It is excluded from the81publictype scope and may be reused after checkpoint closure.

Verification1125: pinned FULL root build PASSED5845jobs, session51329 TERMINAL0. Fresh FULL transitive root axiom audit PASSED34537Foundation declarations, session57102 TERMINAL0, with only propext,Classical.choice,Quot.sound. ALL81new public types printed and ACTUALLY READ from the complete fresh audit:46value+13NaturalContour+3StripBoundary+15FarModelSaddle+4LaguerreWitness. A faithful whitespace-collapsed display with namespace-only abbreviations and no removed hypotheses/arguments was reviewed in groups1..46 and47..81; exact unabridged types remain in .lake/stardust-1125-public-types.json. The review covers the natural STRICT contour strip, H-dependent cutoff, actual paired flow, unsummable raw boundary moments, explicit model-saddle existence/local uniqueness, fixed-t/all-large-frequency quantifiers, actual kernel and slope-residual connections, and the UNCONDITIONAL actual t8 derivative inequality. Full model saddles are not confused with actual phase saddles, and no LP-membership or global real-rooting theorem is inferred from the finite witness. Manifest1772 covers every Foundation/root source; all1767prior hashes unchanged except reviewed root imports. All107archive,43Incoming/42distinct and11fullyreadA4 hashes match baselines. No sorry/admit/new axiom/native admission, manuscript changes/staging, dependency changes or unrelated draft edits. All480value memberships verified; final original97399/PID25296 completed4342jobs exit0 and was never duplicated. All production/prototype/root/audit proof jobs are terminal0. Evidence: .lake/stardust-1125-full-build.log, stardust-1125-audit.log, stardust-1125-working-checkpoint.json, stardust-1125-source-integrity.json, stardust-1125-public-types.json and stardust-1125-verification.json. Exact EIGHT-path audited Git checkpoint, exact-commit receipt and private synchronization follow. A4 and the indefinite research goal remain ACTIVE. Actual saddle correction and integrated unrestricted frequency far-field/global reentry remain OPEN; A2 and final multichannel remain queued.


## Stardust1126 — actual far-frequency saddle correction (October 19, 2026)

Resumed the ACTIVE A(4) campaign after the instruction-only queue checkpoint 9d513a0a62bba81a7a7f58331ced0bf395bd030f. That preceding turn made authoritative progress by persisting the revised queue and verifying its private backup; no new campaign was opened. The mathematical baseline remains audited/private-backed 4cf16b70c89385641e0141e75a8363dfe958af68. IBM stays frozen8946076. After the A4 stopping checkpoint: general A(2k), k>=2, start k3/A6; then A2; then final multichannel; October31 hard stop. STARDUST_CAMPAIGN_QUEUE.md is authoritative. Terminal clock checkpoints include18:48:50,18:49:56,18:51:49,18:53:53,18:54:44 and18:55:42 America/New_York. No manuscript, unrelated draft or dependency changes.

Foundation/RiemannQuarticFarCorrection.lean reuses the constructed FarModelSaddle roots, actual arithmetic theta-kernel bounds, complex Cauchy estimates and the existing quantitative scalar inverse theorem. The first three neighborhood lemmas formerly checked only in the ignored correction prototype are now included in production scope, followed by actual-domain, derivative, inverse and contour results. No axiom or external numerical computation replaces a proof.

For t>=1, real frequency x>=10000, a MODEL saddle w with Re(w)>=120020, |Im(w)|<=1/2 and 100*(t*(norm(w)+1)^3+1)<=x, actual_far_frequency_disk constructs a UNIQUE v within distance1/x of w satisfying the ACTUAL phase equation G_t(v)=-i*z for EVERY complex z with norm(z-x)<=1. Uniqueness is only in that stated closed ball, not global. actual_far_saddle is the real-frequency specialization. The deliberately conservative real-part cutoff is finite and not optimized.

The crucial analytic repair is on the WHOLE closed ball of radius2/x, not only its model center: Re(exp(4v))>=t*Re(w)^3/32>=1 and Re(v)>=0, so the arithmetic theta kernel is analytic and nonzero. Actual/model slope error is <=30005*exp(-Re(w)) throughout this ball. Cauchy on the inner radius1/x yields derivative error <=30005*exp(-Re(w))*x. The model derivative differs from -4*i*x by <=x; the inverse theorem's derivative hypothesis follows. actual_far_deriv_norm_lower additionally gives norm(G'_t(v))>=2*x on the inner ball, so corrected saddles are nondegenerate. actual_weight_critical reuses the existing spatial weight derivative theorem to identify actual phase roots as stationary points of the nonzero actual arithmetic weight.

corrected_saddle_geometry proves Re(v)>=1, strict |Im(v)|<pi/8 and actual kernel nonvanishing for every point of the correction ball. eventually_actual_far_saddle discharges all scale/cutoff hypotheses for EACH fixed t>=1 at EVERY sufficiently large logarithmic anchor. eventually_frequency_actual_saddle transfers this to EVERY sufficiently large real frequency x, retaining the explicit model anchor log(x/(4*pi))/4+i*pi/8 and correction distance1/x. eventually_actual_saddle_contour then uses the existing NaturalContour theorem to represent the ACTUAL cosine flow by exactly paired signed horizontal integrals through the ACTUAL saddle heights, with no vertical endpoint remainder.

This resolves the previously OPEN actual far-saddle correction and connects it to the actual contour formula. It does NOT give an integrated far-field asymptotic, signed dominance/error relative to a nonzero Gaussian contribution, uniform-in-time cutoff, zero exclusion, eventual Laguerre-Polya membership, finite/infinite A4 or an RH/A2 implication. The fixed-t/all-large-frequency quantifiers must not be replaced by a uniform eventual-t claim. The shrinking natural-strip margin is respected in the local inverse; it is not a uniform substrip bound.

Next central obligations: obtain sharp actual/model remainder derivatives and signed integrated far-saddle approximations, control the complementary actual horizontal segments and endpoints relative to the dominant oscillatory contributions, handle the intermediate-frequency gap and joint eventual-time quantifiers, and prove valid global zero-control or a counterobstruction. A radius1/x correction ball is narrower than the expected Gaussian scale1/sqrt(x); its existence alone is not an integrated Gaussian theorem. Reuse logDerivative_coarse_bound to retain its sharper exp(-4*Re(w)) scale and cubic-exponential theta remainder when necessary, rather than infer integrated dominance from the weaker correction envelope. Expanding real/simple-zero windows and the completed finite t8 negative Laguerre witness remain verified but do not decide eventual global reentry.

The new module has17 public theorems and is imported by the root. Full-build, fresh complete root axiom audit, actual inspection of all17 public types and source-integrity verification are required before checkpoint acceptance. Verification evidence is recorded below after those jobs terminate; no success is inferred from a running job.

Verification1126: pinned FULL root build PASSED5846jobs, final session94021 TERMINAL0. Fresh FULL transitive root axiom audit PASSED34560Foundation declarations, final session70549 TERMINAL0, only propext,Classical.choice,Quot.sound. ALL17 new public theorem types were printed and ACTUALLY READ in full from the fresh audit log, including all numerical and functional hypotheses, local uniqueness, actual/model equations, fixed-t/all-large-frequency quantifiers and the strict natural strip. No proof jobs remain live. Manifest1773 covers all Foundation/root sources; every prior1772 source hash is unchanged except the reviewed root import. All107archive,43Incoming/42distinct and11fullyreadA4 manuscript hashes match their saved baselines. No sorry/admit/new axiom/native admission, manuscript change/staging, dependency change or unrelated draft edit. Evidence: .lake/stardust-1126-full-build.log, stardust-1126-audit.log, stardust-1126-working-checkpoint.json, stardust-1126-source-integrity.json, stardust-1126-public-types.json and stardust-1126-verification.json. Exact FIVE-path checkpoint includes the new production module, root import, both research ledgers and a queue-file maintenance change directing readers to current mathematical checkpoint reports instead of freezing an obsolete mathematical status; the campaign order is unchanged. Audited Git checkpoint, exact-commit receipt and private synchronization follow. A4 and the indefinite goal remain ACTIVE; integrated signed far-field/global re-entry remains OPEN. No A6 campaign started.


## Stardust1127 — sharp arithmetic remainders and signed local far-saddle transfer (October 19, 2026)

Continued A(4) from audited/private-backed5a74b35f8d42442e18e9ab2a9672458daf046543. The preceding goal turn made substantive progress and closed actual far-saddle correction with full5846-job build,34560-declaration axiom audit,17public types read and verified private backup. A4 remains ACTIVE; IBM frozen8946076; general A(2k),k>=2 startingA6, thenA2, thenfinalmultichannel remain queued; October31hardstop. The queue instructions are unchanged. Terminal clock checkpoints include19:02:33,19:05:09,19:07:11,19:08:15,19:09:47,19:10:16,19:11:05,19:12:38,19:13:23,19:15:14,19:16:18,19:16:38,19:17:46,19:19:20,19:20:12,19:20:51 and19:21:40 America/New_York. No manuscripts or unrelated drafts changed.

Foundation/GaussianOscillatoryTail.lean (9public theorems) proves a cancellation-sensitive COMPLEX Gaussian tail estimate by exact integration by parts. For Re(b)>0,r>0 the one-sided integral has norm <=1/(norm(b)*r), and the full-minus-truncated SIGNED complex integral has norm <=2/(norm(b)*r). Unlike the prior absolute Gaussian estimate with denominator Re(b), this retains the full curvature norm when the curvature is mostly imaginary. The proof establishes inverse-square integrability and its exact integral, weighted Gaussian integrability, boundary decay and an exact Bochner integral identity before taking norms. Re(b)>0 remains essential for the stated full-integral construction; no pure imaginary Fresnel integral or conditional-integral extension is asserted. These are Gaussian-MODEL estimates, not actual Xi nonlocal-tail estimates.

Foundation/RiemannQuarticFarRemainder.lean (5public) strengthens the previous inverse-theorem envelope to actual/model slope error <=30005*exp(-4*Re(w)+4) on the WHOLE radius2/x neighborhood of a constructed model saddle w under t>=1,x>=8,Re(w)>=32,|Im(w)|<=1/2 and4*t*norm(w)^3+9<=x. All n-th Cauchy derivatives on the inner radius1/x ball are bounded by n!*30005*exp(-4*Re(w)+4)*x^n. Crucially, horizontal_neighbor_domain/error retain the SAME sharp envelope at v+s for EVERY real |s|<=1/16 whenever norm(v-w)<=1/x. The fixed horizontal interval is wider than the shrinking correction ball at large x. Its proof uses the exact positive real factor exp(4s), preserving the actual theta-kernel domain without assuming a complex disk of Gaussian width fits under the natural strip boundary. Re(exp(4*(v+s)))>=t*Re(w)^3/64 and Re(v+s)>=0 are proved.

Foundation/RiemannQuarticFarSignedIntegral.lean (12public definitions/theorems) constructs an exact normalized REAL-horizontal phase for the ACTUAL arithmetic weight using FTC and the existing spatial weight derivative identity. Supporting real ODE lemmas are private in the same module; no new process/functional infrastructure is introduced. The explicit entire leadingPhase is t*((v+u)^4-v^4)+9*u-pi*(exp(4*(v+u))-exp(4*v))+i*z*u. Its derivative is D_t(v+u)+i*z and its zero value is proved. The actual horizontal phase differs from leadingPhase by norm <=epsilon*|s|, epsilon=30005*exp(-4*Re(w)+4). With epsilon*|s|<=1 this gives a relative actual/leading-weight error <=2*epsilon*|s|.

For Re(w)>=64 the model curvature satisfies Re(D'_t(v+s))<=-t*Re(w)^3/4 throughout the same fixed horizontal interval. At an ACTUAL phase saddle G_t(v)=-i*z, real concavity of leadingPhase and the actual/model slope error yield Re(leadingPhase(s))<=epsilon*|s|, so its exponential has norm <=3 whenever epsilon*|s|<=1. This is proved from the actual saddle relation rather than assumed as a model damping condition.

The substantive signed_local_leading_error theorem compares ACTUAL complex Bochner integrals, not integrals of moduli or an expectation-level identity: for0<=r<1/16 andepsilon*r<=1, norm(integral[-r,r]W_t(z,v+s)-W_t(z,v)*integral[-r,r]exp(leadingPhase(t,z,v,s))) <=360060*exp(-4*Re(w)+4)*r^2*norm(W_t(z,v)). All model-saddle, corrected-point, scale and actual-stationarity hypotheses are explicit; the earlier actual far-saddle construction supplies actual points for fixed t>=1 and all sufficiently large real frequencies, including its unit complex-frequency inverse disks. The estimate removes the arithmetic theta remainder on a fixed horizontal integration interval; it does not identify the remaining model integral with a Gaussian or with the entire half-line integral.

Remaining central obligations: quantify the leading model phase's cubic remainder and match its SIGNED local integral to the complex Gaussian with valid relative normalization; combine the new norm-curvature Gaussian tail bound; control complementary ACTUAL shifted horizontal segments and endpoints relative to the oscillatory saddle contributions; close the intermediate-frequency gap and obtain joint uniform eventual-time/complex-frequency zero control or a rigorous counterobstruction. Neither the exact phase identity, local signed transfer, model Gaussian cancellation bound nor the prior actual saddle existence supplies global dominance. A shrinking strip margin is a domain restriction, not a proof that separate analytic continuation is impossible. Neither finite/infinite A4, global Laguerre-Polya re-entry nor RH/A2 transfer is established. Do not switch campaigns.

All26public declarations across the THREE new modules are in full checkpoint scope; root imports are added. Full build, fresh complete root axiom audit, actual public-type inspection and manuscript/source-integrity verification are required before acceptance. Verification is recorded below only after terminal success.

Verification1127: pinned FULL root build PASSED5849jobs, session83143 TERMINAL0. Fresh FULL transitive root axiom audit PASSED34604Foundation declarations, session10645 TERMINAL0, only propext,Classical.choice,Quot.sound. ALL26public definition/theorem types were printed and ACTUALLY READ in full from the fresh audit log (9GaussianOscillatoryTail+5FarRemainder+12FarSignedIntegral), with every hypothesis and quantifier retained. Review includes Re(b)>0 for the full Gaussian, nonnegative real curvature only for weighted integrals, exact actual/model phase equations, actual stationarity, fixed horizontal interval and shrinking neighborhood distinction, epsilon/radius smallness, and the actual complex Bochner signed-integral conclusion. Manifest1776 covers all Foundation/root sources; prior1773 hashes unchanged except root imports. All107archive,43Incoming/42distinct and11fullyreadA4 manuscript hashes match saved baselines. No sorry/admit/new axiom/native admission, manuscript change/staging, dependency change or unrelated draft edit. All proof jobs terminal0. Evidence: .lake/stardust-1127-full-build.log, stardust-1127-audit.log, stardust-1127-working-checkpoint.json, stardust-1127-source-integrity.json, stardust-1127-public-types.json and stardust-1127-verification.json. Exact SIX-path audited Git checkpoint, exact-commit receipt and private synchronization follow. A4 and the indefinite goal remainACTIVE. Local Gaussian matching, complementary actual signed tails and global re-entry remainOPEN; no campaign transition.


## Stardust1128 — local actual Xi/full-Gaussian comparison and relative convergence (October 19, 2026)

Continued A(4) from audited/private-backed a3e5b9ec67b3c1a370760b922c338fb3298036d3. The preceding instruction-only turn made authoritative progress by persisting the conditional real-exponent queue and verifying private backup fc2116bd810dd1d77188abc754920ee7c3745a55. A4 proof priorities were unchanged. IBM remains frozen8946076. After A4's verified stopping checkpoint: integer A(2k), verified A4 base/startA6, with realk>1/uniformk->1+ investigation conditional on a coherent reusable integer foundation; thenA2; thenfinalmultichannel; October31hardstop. No queued campaign opened. Terminal clock checkpoints include19:28:14,19:29:44,19:31:44,19:33:21,19:34:28,19:35:07,19:35:41,19:36:29,19:38:02,19:39:28,19:39:38,19:40:47 and19:42:11 America/New_York. No manuscripts, unrelated drafts or pinned dependencies changed.

Foundation/RiemannQuarticFarGaussianLocal.lean (12public theorems) closes the previous OPEN local actual/full-Gaussian comparison. An explicit complex exponential cubic remainder, derived from Mathlib's norm_exp_sub_sum_le_norm_mul_exp, bounds norm(exp(4u)-1-4u-8u^2)<=128*norm(u)^3 fornorm(u)<=1/16. Existing constructed model roots and quantitative correction give norm(exp4v)<=2x and the requisite polynomial scale. Exact algebra and these estimates prove norm(leadingPhase(u)-(D_t(v)+iz)*u-D'_t(v)*u^2/2)<=2048*x*norm(u)^3.

The center v is an ACTUAL phase saddle G_t(v)=-iz, not an exact model saddle. Accordingly the NONZERO linear mismatch D_t(v)+iz is retained and bounded byepsilon=30005*exp(-4*Re(w)+4) from the verified horizontal arithmetic remainder. The phase/quadratic error is <=epsilon*|s|+2048*x*|s|^3. The previously verified horizontal model curvature gives Re(b)>0 for b=-D'_t(v)/2 and norm(exp(-b*s^2))<=1 on real s. All domains and inequalities are explicit; no wide actual complex disk through the natural theta boundary is presumed.

Combining the prior SIGNED actual/leading-integral transfer with the signed leading/quadratic comparison proves actual_local_quadratic_error: actual local integral minus W_t(z,v) times the truncated Gaussian has norm <=norm(W_t(z,v))*(16*epsilon*r^2+8192*x*r^4). For0<r<1/16 andepsilon*r+2048*x*r^3<=1, actual_local_full_gaussian_error adds the proved cancellation-sensitive Gaussian tail, giving the rigorous bound norm(W_t(z,v))*(16*epsilon*r^2+8192*x*r^4+2/(norm(b)*r)) against the FULL complex Gaussian integral. full_gaussian_formula identifies that integral with (pi/b)^(1/2) using Mathlib's verified formula under Re(b)>0, preserving its principal complex-power convention.

IMPORTANT curvature distinction: this is the ACTUAL arithmetic local integral at an ACTUAL saddle, approximated using the LEADING-MODEL curvature D'_t(v). It is not silently identified with the actual Hessian G'_t(v), and is not the whole half-line or full cosine-flow integral.

Foundation/RiemannQuarticFarGaussianLimit.lean (15public definitions/theorems) proves actual norm-relative convergence. Under the existing stronger scale hypothesis100*(t*(norm(w)+1)^3+1)<=x, x>=10000,t>=1, it provesepsilon<=100000000/x, x<=norm(b)<=4x and1<=2*sqrt(x)*norm(Gfull). Actual kernel-domain bounds and this lower normalization prove BOTH factors in the normalized denominator W_t(z,v)*Gfull are nonzero. The relative error is bounded by2*sqrt(x)*(16*epsilon*r^2+8192*x*r^4+2/(x*r)). No division by a potentially zero model contribution is assumed.

Instead of introducing the prospective x^(-2/5) radius or duplicating scalar infrastructure, the proof reuses RiemannQuarticErrorLimits.centralRadius(x)=x^(-7/16), its exact power identities, central_scaled_error, gaussian_scaled_prefactor and centralRadius_tendsto_zero. The verified relativeBudget is3200000000*x^(-11/8)+16384*x^(-1/4)+4*x^(-1/16), and relativeBudget_tendsto_zero proves its limit0. The small phase budget also tends0. eventually_uniform_local_gaussian_error gives epsilon-norm accuracy for ALL admissible saddle data above one scalar frequency threshold. Its uniformity remains CONDITIONAL on the explicit model/correction/scale hypotheses; it does not establish a uniform-in-time cutoff for existence of those data.

The earlier actual far-saddle existence theorem is reused and its quantitative scale information recovered from the logarithmic anchor, rather than assuming a saddle branch. eventually_controlled_far_saddles supplies that complete data for EACH fixedt>=1 and EVERY sufficiently large realfrequencyx. eventually_actual_local_gaussian therefore obtains the actual local relative Gaussian approximation at EVERY such realfrequency, not merely a subsequence. Finally relative_limit_for_saddle_family proves ordinary complex norm-topology Tendsto of the normalized actual local integral to1 for ANY saddle family eventually satisfying the displayed hypotheses, including complex frequency families satisfying the actual phase equation. No continuity, analytic branch or samplewise process property of an arbitrary saddle family is inferred.

Remaining central obligations: control ACTUAL complementary horizontal contour intervals/endpoints relative to the nonzero saddle/Gaussian scale; pair the opposite-frequency contribution; handle the intermediate-frequency gap, complex-frequency localization and joint eventual-time quantifiers; prove global real-rooting or a rigorous counterobstruction. The new theorem closes LOCAL Gaussian matching and relative normalization only. Neither finite/infinite A4, eventual global Laguerre-Polya re-entry, nor any RH/A2 implication follows. A4 remains ACTIVE.

Both new modules (27public definitions/theorems total) are imported by the root and in full checkpoint scope. Full build, fresh complete root axiom audit, actual public-type inspection and manuscript/source-integrity verification are required before acceptance. Verification is recorded below only after terminal success.

Verification1128: pinned FULL root build PASSED5851jobs, session94633 TERMINAL0. Fresh FULL transitive root axiom audit PASSED34649Foundation declarations, session55470 TERMINAL0, only propext,Classical.choice,Quot.sound. ALL27public definition/theorem types were printed and ACTUALLY READ in full from the complete fresh log (12FarGaussianLocal+15FarGaussianLimit); both scalar-budget definition bodies were also read from the final sources. No hypotheses/quantifiers were elided. Review explicitly checked MODEL curvature evaluated at ACTUAL saddles, retained nonzero linear mismatch, principal complex Gaussian identity under positive real curvature, both nonzero denominator factors, radius/scale/smallness hypotheses, conditional-in-data uniformity versus fixed-t existence thresholds, all-large-real-frequency coverage and genuine complex norm Tendsto. Manifest1778 covers every Foundation/root source; all prior1776 hashes unchanged except reviewed root imports. All107archive,43Incoming/42distinct and11fullyreadA4 hashes match saved baselines. No sorry/admit/new axiom/native admission, manuscript modification/staging, dependency change or unrelated draft edit. All proof jobs terminal0. Evidence: .lake/stardust-1128-full-build.log, stardust-1128-audit.log, stardust-1128-working-checkpoint.json, stardust-1128-source-integrity.json, stardust-1128-public-types.json and stardust-1128-verification.json. Exact FIVE-path audited Git checkpoint, exact-commit receipt and private synchronization follow. A4 and the indefinite goal remainACTIVE; complementary actual contour pieces, uniform eventual-time/global zero control and both A4 alternatives remainOPEN. No campaign transition.
