# A(4) archive review and theorem reuse audit

> Current queue update (October 19, 2026): [STARDUST_CAMPAIGN_QUEUE.md](STARDUST_CAMPAIGN_QUEUE.md) is authoritative. A(4) remains active -> integer A(2k), first A(6) -> real k > 1 only on a coherent integer theorem -> rigorously justified k -> 1+ interpolation/zero-escape study and the independent classical A(2) investigation -> final multichannel campaign -> stop by October 31. Prove local uniform convergence and every Hurwitz hypothesis for the actual family; identify interpolation failures. No real-rootedness or RH implication is assumed. No queued investigation has started. Older queue statements below are historical.

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

## Stardust1129 — signed actual far-saddle annuli (October 19, 2026)

A4 remains ACTIVE from audited/private-backed8aedb8e62850231ce623cf4df1dc1dc6aa19669f. Both remote main and research branch were independently verified at that exact commit, with privacy true, before new proof edits. The authoritative STARDUST_CAMPAIGN_QUEUE.md is unchanged: A4 stopping checkpoint before integerA2k/A6, conditional real-exponent branch only on a coherent reusable integer foundation, then A2 and final multichannel; October31 hardstop. No queued campaign opened. Terminal clocks during this continuation include19:53:53,19:55:23,19:56:49,19:57:54,19:59:47,20:00:41,20:02:43 and20:03:35 America/New_York.

Foundation/RiemannQuarticFarAnnulus.lean reuses the actual far-saddle correction, horizontal theta arithmetic transfer, leadingPhase and nonzero Gaussian normalization. Eleven public definitions/theorems close the complementary annuli between centralRadius(x)=x^(-7/16) and any fixed0<R<=1/8192, in either horizontal direction. They do not bound the remainder of the half-line.

A complex exponential quadratic remainder gives norm(exp4u-1-4u)<=32*norm(u)^2 onnorm(u)<=1/16. Exact model algebra then gives norm(D(v+u)-D(v)-Dprime(v)*u)<=2048*x*norm(u)^2. At an ACTUAL saddle G(v)=-iz, the NONZERO model mismatch D(v)+iz remains bounded byepsilon=30005exp(-4Rew+4). Under t>=1,x>=10000,Rew>=64,|Imw|<=1/2,modelD(w)=-ix,strongscale100*(t*(normw+1)^3+1)<=x andnorm(v-w)<=1/x, annulus_slope_lower proves norm(D(v+s)+iz)>=x*|s| whenever|s|<=1/8192 andepsilon<=x*|s|/2. annulus_slope_derivative_upper independently bounds norm(Dprime(v+s))<=512x. No model stationarity at v is assumed.

finite_nonstationary_bound proves a signed complex integration-by-parts estimate from explicit derivative, continuity and nonzero-denominator hypotheses. For Eprime=H*E,Hprime=K,normE<=3,normH>=x*s,normK<=512x on0<a<=s<=b, it obtains norm(integral_a^b E)<=1542/(x*a). The proof establishes quotient differentiability, integrability, exact finite FTC identity and inverse-square remainder integration before taking norms. It uses signed cancellation, rather than bounding integral norms by the interval length.

signed_model_annulus_bound applies this to E(s)=exp(leadingPhase(t,z,v,sigma*s)) for every realsigma with|sigma|=1. Both directions are treated with the correct derivative factors sigma andsigma^2. signed_actual_annulus_bound transfers to the ACTUAL arithmetic weight W_t(z,v+sigma*s). For0<r<=R<=1/8192,epsilon<=xr/2 andepsilonR<=1, the actual signed Bochner integral has norm <=normW(v)*(1542/(xr)+6*epsilon*R^2). The added term is the rigorously integrated actual/model error, not an omitted arithmetic contribution.

relative_actual_annulus_bound divides by W(v)*Gfull, where Gfull is the full complex Gaussian with MODEL curvature Dprime(v) evaluated at the ACTUAL saddle. Both denominator factors are proved nonzero using existing kernel-domain and Gaussian normalization theorems. The relative norm is <=2sqrtx*(1542/(xr)+6*epsilon*R^2). The explicit annulusBudget(R,x)=3084*x^(-1/16)+1200000000*R^2*x^(-1/2) tends0. eventually_uniform_relative_annulus proves that for every fixed0<R<=1/8192 andeta>0, ALL sufficiently large realx give normalized actual-annulus norm<=eta for EVERY admissible t,w,v,z and BOTH directions. The eventual proof discharges the smallness and nonstationarity conditions; it reuses the established centralRadius power limits andepsilon<=1e8/x. Uniformity is conditional on the displayed scale/saddle data. It does not manufacture uniform-in-time saddle existence or a coherent analytic saddle branch.

Thus the previously OPEN shrinking-to-fixed-neighborhood actual signed annuli are now controlled relative to the genuine nonzero saddle/Gaussian scale. The whole positive half-line, signed opposite-frequency pairing, complex-frequency zero localization, intermediate-frequency gap and joint eventual-time/global estimates remain OPEN. No full-contour asymptotic, finite/infinite A4, eventual Laguerre-Polya reentry, RH or A2 implication is asserted. A useful next step is to combine the existing central Gaussian theorem with these two annuli by exact interval identities, then control the actual contour beyond fixedR; near-boundary theta envelopes must meet their actual hypotheses.

The new module is imported by the root. Full build, fresh complete root axiom audit, actual public-type inspection, source-integrity verification, ledger and exact-commit private backup are required for checkpoint acceptance. Verification results follow only after terminal success. ResearchSources, pinned dependencies and unrelated drafts are preserved.

Verification1129: pinned FULL root build PASSED5852jobs, session77068 TERMINAL0. Fresh FULL root transitive axiom audit PASSED34671Foundation declarations, session28630 TERMINAL0, only propext,Classical.choice,Quot.sound. ALL11 public definition/theorem types were printed and ACTUALLY READ in full from the fresh complete log; annulusBudget definition body was reviewed in the final source. Review checked actual signed integration, retained model mismatch, two direction derivative factors, exact radius/scale/error hypotheses, nonzero normalization at model curvature evaluated at the actual saddle, discharged eventual smallness and conditional-in-data uniformity. Manifest1779 covers every Foundation/root source, all prior1778 hashes unchanged except reviewed root import. All107archive,43Incoming/42distinct and11fullyreadA4 hashes match saved baselines. No sorry/admit/new axiom/native admission, manuscript/dependency change or unrelated draft modification. All proof jobs terminal0. Evidence: .lake/stardust-1129-full-build.log, stardust-1129-audit.log, stardust-1129-working-checkpoint.json, stardust-1129-source-integrity.json, stardust-1129-public-types.json and stardust-1129-verification.json. Exact FOUR-path audited Git checkpoint, exact-commit receipt and verified private backup follow. A4 remainsACTIVE and farther actual contours/global zero control remainOPEN. No campaign transition.

## Stardust1130 — actual fixed-neighborhood asymptotics and entire right-tail control (October 19, 2026)

Continued A4 from audited/private-backed e8cbbae1353f542dd1d829604aca8a66375d6403. The preceding goal turn made substantive progress: all11 signed-annulus declarations were built/audited, reviewed and committed, and private main/research refs independently verified. Current HEAD and clean tracked tree were inspected before new proof edits. A4 remains ACTIVE; the authoritative STARDUST_CAMPAIGN_QUEUE.md and all transition gates remain unchanged. IntegerA2k/startA6, conditional real exponents, A2 and final multichannel remain queued; October31hardstop. Terminal system times include20:31:06,20:32:52,20:35:40,20:36:31,20:38:39,20:39:23,20:40:50,20:41:08 and20:42:14 America/New_York. Manuscripts and unrelated drafts were preserved.

Foundation/RiemannQuarticFarGaussianFixed.lean (4public theorems) directly reuses the previous central Gaussian and signed-annulus results. actual_neighborhood_split first proves continuity and interval integrability of the ACTUAL arithmetic integrand on the entire fixed interval, then uses exact adjacent-interval identities and negative-variable substitution. It identifies the signed integral on[-R,R] with its central[-r,r] integral plus BOTH annuli parametrized on[r,R]. No implicit sign change or integral-of-norm replacement is used.

eventually_uniform_fixed_gaussian_error obtains normalized complex error<=eta for every fixed0<R<=1/8192, all sufficiently large realx and ALL admissible t,w,v,z. The assumptions remain t>=1,Rew>=64,|Imw|<=1/2,strongscale100*(t*(normw+1)^3+1)<=x, modelD(w)=-ix,norm(v-w)<=1/x and ACTUAL G(v)=-iz. The denominator is W_t(z,v) times the full Gaussian at MODEL curvature Dprime(v), not the actual Hessian. eventually_actual_fixed_gaussian reuses the constructed saddles for EACH fixedt>=1 and EVERY sufficiently large realx, retaining strict natural-strip membership and nonzero arithmetic kernel. fixed_relative_limit_for_saddle_family proves ordinary complex norm Tendsto to1 for any family eventually satisfying the displayed data, without assuming continuity or an analytic branch. The small fixed neighborhood is now closed as a signed actual asymptotic; it is not the whole contour.

Foundation/RiemannQuarticFarRightTail.lean (10public definitions/theorems) makes a direct advance beyond that neighborhood. A read-only reuse audit found RiemannThetaDerivativeBounds.kernel_norm_lower (under Reu>=0,Reexp4u>=1) and NaturalContour.kernel_norm_bound (under Reu>=0,Reexp4u>=1/2). These existing genuine arithmetic bounds yield actual_weight_model_envelope: normW(v+u)<=1000*normW(v)*exp(Re leadingPhase(u)), provided both displayed kernel domains hold. The proof uses exact exponential phase algebra and two-sided actual kernel estimates, not a wide actual analytic disk, global logarithm or a model-only amplitude.

right_model_curvature extends the real model-curvature inequality ReDprime(v+s)<=-t*(Rew)^3/4 to EVERY real s>=0. The proof retains the actual corrected v, uses Reexp4(v+s)=exp4s*Reexp4v, and compares polynomial growth with exp2s and exp4s. right_phase_quadratic_bound applies real concavity to the augmented entire phase to prove Re leadingPhase(s)<=epsilon*s-(t*(Rew)^3/8)*s^2 for every s>=0, with epsilon=30005exp(-4Rew+4). The NONZERO model linear mismatch at the ACTUAL saddle is explicitly retained and bounded. No model stationarity at v is assumed.

For c=t*(Rew)^3/16, fixedR>0 andepsilon<=cR, actual_right_gaussian_envelope gives normW(v+s)<=1000*normW(v)*exp(-c*s^2) for EVERY s>=R. The actual theta domain is proved along the entire right ray. actual_right_tail_bound proves Bochner integrability onIoiR using actual analyticity and the Gaussian majorant, then bounds the signed complex tail integral by1000*normW(v)*exp(-cR^2)/(2cR), reusing the verified real Gaussian tail integral. This controls the ENTIRE right tail, not just a finite interval or an expectation-level/model integral.

relative_actual_right_tail_bound divides by the proven nonzero W(v)*Gfull and obtains2000*sqrtx*exp(-cR^2)/(2cR). An explicit model-root frequency bound x<=32exp(4Rew) gives sqrtx<=8exp(2Rew). Since c>=1 and c>=(Rew)^3/16, relative_right_tail_budget bounds the normalized actual tail by rightBudget(R,Rew)=(16000/R)*exp(2Rew-(R^2/16)*(Rew)^3). rightBudget_tendsto_zero proves its limit0 for every fixedR>0. eventually_uniform_relative_right_tail discharges epsilon<=cR and proves normalized actual right-tail norm<=eta for ALL sufficiently large realx and ALL admissible saddle data. The same frequency bound forces Rew above any required scalar threshold. Its uniformity remains CONDITIONAL on the explicit scale/root/correction data, and it does not establish a uniform-in-time existence cutoff or a coherent frequency branch.

Remaining central obligations are now principally LEFT of the fixed neighborhood, including the near-boundary compact/intermediate actual theta pieces. The exact opposite-frequency/end-point bookkeeping, complex-frequency zero localization, intermediate-frequency gap and joint eventual-time global estimates remain OPEN. The fixed-neighborhood and entire-right-tail theorems must still be combined with those missing pieces to control the actual half-line/full cosine flow. Both A4 threshold alternatives, eventual global Laguerre-Polya reentry and RH/A2 consequences remain unresolved. No campaign transition or claim of global reentry is made.

Both new modules (14public declarations total) are imported by the root. Full build, fresh complete transitive root axiom audit, actual public-type inspection, source integrity, ledger, exact Git checkpoint and verified private backup are required before acceptance. Verification follows only after terminal success. No manuscript/dependency modifications or unrelated edits were made.

Verification1130: pinned FULL root build PASSED5854jobs, session68296 TERMINAL0. Fresh FULL root transitive axiom audit PASSED34688Foundation declarations, session57054 TERMINAL0, only propext,Classical.choice,Quot.sound. ALL14 public definition/theorem types were printed and ACTUALLY READ in full from the complete fresh log (4FarGaussianFixed+10FarRightTail); the rightBudget definition body was reviewed in the final source. Review checked exact signed interval identities, actual kernel envelope domains, the retained model linear mismatch, all-positive-displacement curvature, actual entire-right-ray Bochner integrability and quantitative bound, MODEL Gaussian curvature/nonzero denominator, discharged eventual conditions and precise quantifier order. The normalized tail result is conditional on admissible data and does not prove uniform eventual-time saddle existence. Manifest1781 covers all Foundation/root sources; prior1779 hashes unchanged except reviewed root imports. All107archive,43Incoming/42distinct and11fullyreadA4 hashes match saved baselines. No sorry/admit/new axiom/native admission, manuscript/dependency change or unrelated draft modification. All proof jobs terminal0. Evidence: .lake/stardust-1130-full-build.log, stardust-1130-audit.log, stardust-1130-working-checkpoint.json, stardust-1130-source-integrity.json, stardust-1130-public-types.json and stardust-1130-verification.json. Exact FIVE-path audited Git checkpoint, exact-commit receipt and verified private backup follow. A4/goal remainACTIVE, left contour and global zero control remainOPEN; no campaign transition.

## Stardust1131 — actual near-boundary theta bounds and negligible compact-left contour (October 19, 2026)

Continued A4 from audited/private-backed60d13a538314bb8de739cdd0d6c4add32bd52c78. The previous goal turn made substantive progress by proving the actual fixed-neighborhood asymptotic and entire actual right-tail negligibility, completing full build/axiom/type/source audits and verifying exact private remote refs. Current HEAD and clean tracked tree were rechecked before new work. A4 remains ACTIVE under STARDUST_CAMPAIGN_QUEUE.md; no queued integerA2k/A6, conditional real-exponent, A2 or final multichannel campaign opened. October31hardstop remains unchanged. Terminal system-time checks include20:47:06,20:49:30,20:50:06,20:53:07,20:53:54,20:55:04,20:55:49,20:56:34 and20:57:16 America/New_York. No ResearchSources, pinned dependencies or unrelated drafts changed.

The main obstruction addressed here was an actual domain gap: NaturalContour.kernel_norm_bound requires Reexp4q>=1/2, while the leftmost horizontal contour can have arbitrarily small POSITIVE Reexp4q as its height approaches the natural boundary. Holomorphy and the real-u theta modular reflection do not supply a uniform estimate there. Rather than applying those bounds outside their domains or introducing a complex modularity foundation, the proof constructs a direct coarse arithmetic-series majorant.

Foundation/RiemannThetaSmallParameter.lean (5public theorems) uses the pinned Mathlib Real.pow_div_factorial_le_exp with degree3 to bound the fourth theta summand by6/(pi^3*v^3)*(n+1)^(-2) for EVERY realv>0. A private elementary inequality bounds m^(-2) by2*(1/m-1/(m+1)) for m>=1. Exact finite telescoping and Real.tsum_le_of_sum_range_le prove thetaMoment(k,v)<=12/(pi^3*v^3) for allk<=4 andv>0. This verifies summation/positivity rather than treating a termwise bound as an infinite-sum identity. moment_norm_polynomial_bound passes to the actual complex theta series on Re(v)>0 through absolute summability and the exact term norm identity.

kernel_positive_parameter_bound proves norm(kernelComplex(q))<=528*exp(9Req)/(Reexp4q)^3 for Req>=0 and EVERY Reexp4q>0. kernel_horizontal_margin_bound then gives norm(kernelComplex(a+ih))<=528*cos(4h)^(-3)*exp(-3a) for a>=0 andcos4h>0. The polynomial blowup is explicit and coarse, not asserted optimal. No estimate at cos4h=0, global analytic continuation across the boundary, or limiting real-rootedness is claimed. The finite telescoping route avoids new lattice-sum or modular infrastructure while using existing theta definitions and summability.

Foundation/RiemannQuarticFarLeftCompact.lean (10public definitions/theorems) applies that genuine arithmetic bound to the actual signed contour. compact_weight_bound retains the common frequency attenuation -Re(z)*h and the full cosine-margin factor. compact_signed_bound proves actual Bochner interval integrability and norm(integral_0^L W_t(z,s+ih)) <=(528L/cos4h^3)*exp(t*(L^4+h^4)-Re(z)*h+|Im(z)|L) for t>=0,L>=0,cos4h>0. Actual analyticity is established along that whole horizontal line using the positive real theta parameter.

actual_left_compact_bound sets L=a-1 at a corrected far-saddle center v=a+ih. Under t>=1,a>=64,|h|<=1,|Im(z)|<=1,Reexp4v>=1 andpi*Reexp4v<=t*a^3+3, it proves the ACTUAL signed compact-left norm <=528*(a-1)*norm(W_t(z,v))*exp(5a+3-2t*a^3). The proof absorbs cos4h^(-3) using the CENTER inequality Reexp4v=exp4a*cos4h>=1, retaining its positive margin. The common -Re(z)*h factor cancels against the actual saddle normalization. The quartic drop between a-1 and a beats the resulting exp12a margin loss; the actual arithmetic center lower bound is reused from RiemannThetaDerivativeBounds.kernel_norm_lower. This is not a model-only or expectation-level heat estimate.

actual_center_theta_upper derives the required pi*Reexp4v<=t*(Rev)^3+3 from the ACTUAL equation G_t(v)=-iz, |Im(z)|<=1,Rev>=0,t>=0 andnorm(G_t(v)-D_t(v))<=1. In particular, the sign G_t(v).re=Im(z) and the nonzero actual/model mismatch are handled explicitly. relative_actual_left_compact_bound obtains the center geometry and sharp arithmetic error from the existing corrected-root data, discharges that norm-error condition, and divides by the PROVEN nonzero W_t(z,v)*Gfull. Gfull still uses MODEL curvature Dprime(v) evaluated at the ACTUAL saddle, not the actual Hessian. The resulting normalized bound is1056*sqrtx*(Rev-1)*exp(5Rev+3-2t*(Rev)^3).

frequency_exp_bound directly reuses the prior epsilon<=1e8/x result to give the conservative public bound x<=1e8*exp4Rew. It is deliberately looser than the previous module's private32-constant proof and is exported for direct reuse by the remaining left-annulus estimate. It gives sqrtx<=10000*exp2Rew. Using norm(v-w)<=1/x andt>=1, relative_left_compact_budget bounds the actual normalized compact-left integral by compactBudget(Rev)=10560000*exp(8Rev+5-2*(Rev)^3). compactBudget_tendsto_zero proves its ordinary real limit0. eventually_uniform_relative_left_compact forces Rew andRev above each needed scalar threshold via the frequency estimate, giving normalized ACTUAL compact-left norm<=eta for all sufficiently large realx and ALL admissible data with |Im(z)|<=1. The data include t>=1,Rew>=120020,|Imw|<=1/2,strongscale100*(t*(normw+1)^3+1)<=x, modelD(w)=-ix,norm(v-w)<=1/x andACTUAL G(v)=-iz.

Uniformity is CONDITIONAL on that explicit saddle/scale data. The additional frequency-strip restriction |Im(z)|<=1 is essential to the displayed compact bound; it includes real frequencies and the earlier constructed unit complex-frequency disks but is not silently discarded. No coherent analytic branch, uniform-in-time saddle-existence cutoff or whole-flow zero estimate is inferred.

This closes the previously missing actual compact-left piece from coordinate0 toRev-1, including the near-boundary small-positive theta-parameter regime. Remaining before a full horizontal half-line asymptotic: the finite LEFT interval from displacement-1 to-R, exact assembly with the fixed[-R,R] neighborhood and entire right tail, opposite-frequency/end-point pairing, complex-frequency zero localization, intermediate-frequency gap and joint eventual-time global estimates. The intervening left interval has NOT been bounded by the new compact theorem. Both A4 alternatives, eventual global Laguerre-Polya reentry and RH/A2 consequences remain OPEN. A4 stays active.

Both new modules (15public declarations total) are imported by the root. Full build, fresh complete root axiom audit, actual public-type inspection, source integrity, ledger, exact Git checkpoint and verified private backup are required before checkpoint acceptance. Verification follows only after terminal success.

Verification1131: pinned FULL root build PASSED5856jobs, session84937 TERMINAL0. Fresh FULL root transitive axiom audit PASSED34707Foundation declarations, session11844 TERMINAL0, only propext,Classical.choice,Quot.sound. ALL15 public definition/theorem types were printed and ACTUALLY READ unabridged from the complete fresh log (5ThetaSmallParameter+10FarLeftCompact); compactBudget definition body was reviewed in the final source. Type/proof review checked strictly positive theta parameters, finite telescoping and absolute summation, explicit cosine-margin domains, actual signed integration/integrability, same-height frequency attenuation cancellation, actual phase sign/nonzero model mismatch, nonzero Gaussian denominator at MODEL curvature, the retained |Im(z)|<=1 restriction, conditional data uniformity and the exact remaining finite left interval. Manifest1783 covers every Foundation/root source; all prior1781 hashes unchanged except reviewed root imports. All107archive,43Incoming/42distinct and11fullyreadA4 hashes match saved baselines. No sorry/admit/new axiom/native admission, manuscript/dependency change or unrelated draft modification. All proof jobs terminal0. Evidence: .lake/stardust-1131-full-build.log, stardust-1131-audit.log, stardust-1131-working-checkpoint.json, stardust-1131-source-integrity.json, stardust-1131-public-types.json and stardust-1131-verification.json. Exact FIVE-path audited Git checkpoint, exact-commit receipt and verified private synchronization follow. A4/goal remainACTIVE; remaining left interval/full contour assembly and global zero control stayOPEN. No campaign transition.

## Interpolation and zero-escape queue update — October 19, 2026 (instructions only)

At the user's explicit request, STARDUST_CAMPAIGN_QUEUE.md now makes the preserved order explicit: finish active A(4), integer A(2k) startingA6, realk>1 only after a coherent reusable integer theorem, justifiedk->1+ limiting study and independent classicalA(2), then the final multichannel campaign and October31hardstop. The real-exponent objective now explicitly asks whether a natural F_k(z), or F_{k,t}(z) with its flow parameter retained, interpolates the integer constructions and converges locally uniformly to the correctly normalized classical target. It requires branch/analyticity/parameter-domain and uniform-majorant proofs, explicit study of nonreal zeros escaping compact sets versus approaching real zeros, and all hypotheses before invoking Hurwitz-type arguments. Interpolation failure must be documented by an exact obstruction, failed hypothesis or counterexample. Neither real-rootedness nor an RH/threshold implication is assumed.

This instruction update starts none of those investigations. A4 remains on its next finite-left-interval proof target after audited/private-backed13e0a85c36842fffb691f27ed27b39ddf7989c82. AGENTS.md, the recovery priority header and both research-ledger headers point to the exact authoritative gate. No mathematical result or manuscript changed. Instruction-only verification compares all1783 Foundation/root sources with the audited1131 manifest and rechecks manuscript inventories. The existing full5856-job build,34707-declaration standard-three-axiom audit and15 reviewed public types apply to the identical mathematical source tree; no fresh mathematical build or audit is claimed. Exact documentation commit, audit receipt for the unchanged mathematics and verified private backup follow, then A4 resumes.
Instruction-only verification PASSED: all1783 Foundation/root source hashes equal audited1131, all107archive/43Incoming(42distinct)/11A4 manuscript hashes unchanged; no mathematical sources or dependencies changed. Evidence: .lake/stardust-interpolation-queue-20261019-verification.json. The prior full5856-job build,34707-declaration axiom audit and15 reviewed types apply to this identical Lean tree.

## Stardust1132 — actual whole horizontal half-line Gaussian asymptotics (October 19, 2026)

A4 remains ACTIVE after instruction-only private checkpoint 1e3e104a712f227979dd5fdcf166f4394ab204f4 and mathematical checkpoint 13e0a85c36842fffb691f27ed27b39ddf7989c82. The revised queue and conditional interpolation/Hurwitz/zero-escape instructions remain saved and unopened. October31hardstop is unchanged. Terminal system-time checks include21:18:14 America/New_York. No ResearchSources, dependencies or unrelated drafts were changed.

Foundation/RiemannQuarticFarLeftAnnulus.lean adds six public theorems closing the remaining displacement interval[-1,-R]. left_unit_domain_curvature proves actual theta-domain membership Re(v+s)>=0,Reexp4(v+s)>=1 and ReDprime(v+s)<=-t*(Rew)^3/1024 for EVERY -1<=s<=0 under the explicit corrected far-saddle data. The proof uses exp(4s)>=1/81, the verified center Reexp4v lower bound and polynomial curvature comparison. left_phase_quadratic_bound applies concavity on[-1,0] to obtain Re leadingPhase(s)<=epsilon*|s|-(t*(Rew)^3/2048)*s^2. The small NONZERO model slope mismatch at the ACTUAL saddle G(v)=-iz is retained as epsilon=30005exp(-4Rew+4); model stationarity at v is never assumed.

For0<R<=1 andepsilon<=(t*(Rew)^3/4096)*R, actual_left_annulus_bound proves Bochner interval integrability and the ACTUAL signed norm bound <=1000*normW(v)*exp(-(t*(Rew)^3/4096)*R^2). It establishes actual arithmetic analyticity/domain along the entire interval before using the bound. relative_actual_left_annulus_bound divides by PROVEN nonzero W(v)*Gfull and gives2000sqrtx exp(-(t*(Rew)^3/4096)*R^2). relative_left_annulus_budget reuses the existing rightBudget(R/16,Rew) with prefactor100; no new scalar limit infrastructure is introduced. eventually_uniform_relative_left_annulus discharges epsilon-smallness and obtains relative error<=eta for ALL sufficiently large realx and ALL admissible t,w,v,z. Its uniformity is conditional on the explicit scale/root/correction data, not a uniform-in-time saddle-existence assertion.

Foundation/RiemannQuarticFarHalfline.lean adds four public theorems. horizontal_decomposition proves the exact signed identity splitting the literal integral over coordinates(0,infinity) at fixed height Im(v) into compact0..Rev-1, left displacement-1..-R, central-R..R and the entire right rayIoiR. It uses Lebesgue translation of indicator integrals and exact adjacent-interval/improper-integral identities. It requires the strict natural strip and actual right-ray integrability, and is valid for general realR as a signed identity.

eventually_uniform_horizontal_gaussian_error combines the four genuinely actual estimates at the internal fixed radiusR=1/8192. For everyeta>0, ALL sufficiently large realx and ALL admissible data t>=1,Rew>=120020,|Imw|<=1/2,strongscale100*(t*(normw+1)^3+1)<=x,modelD(w)=-ix,norm(v-w)<=1/x,ACTUAL G(v)=-iz and|Imz|<=1, it proves integrability of the literal positive horizontal contour and norm(H/(W(v)*Gfull)-1)<=eta. It proves the right-ray smallness conditions explicitly and gets the strict natural strip from corrected_saddle_geometry. Gfull is the full Gaussian at MODEL curvature Dprime(v) evaluated at the ACTUAL corrected saddle; it is not silently replaced by the actual Hessian. The nonzero normalization is inherited from the previously proved arithmetic kernel and complex Gaussian bounds.

eventually_actual_horizontal_gaussian reuses the already constructed saddles: for EACH fixedt>=1 and EVERY sufficiently large realx, there exist model/actual roots w,v with strict natural-strip membership, nonzero kernel, actual horizontal integrability and the stated normalized error<=eta. horizontal_relative_limit_for_saddle_family proves ordinary complex norm Tendsto to1 for ANY family eventually satisfying the explicit data, including|Imz|<=1. No continuity, analytic saddle branch or joint time/frequency existence cutoff is assumed. Thus the actual entire POSITIVE HORIZONTAL contribution, including near-boundary compact-left arithmetic and both tails, is now asymptotically Gaussian on this precise domain.

This single horizontal contribution is not the full cosine Xi-flow. The EXISTING NaturalContour.flow_eq_paired_horizontal and vertical_pair_cancel already give the exact opposite-frequency identity and vertical-endpoint cancellation on the natural strip; these are reusable proved results, not new open foundational obligations. What remains OPEN is to combine the two opposite-frequency horizontal asymptotics and their relative phase into a full-flow zero estimate, together with a coherent analytic-frequency branch and complex-frequency zero localization, intermediate-frequency matching and uniform eventual-time/global zero estimates. Both finite/infinite A4 alternatives and eventual global Laguerre-Polya reentry remain unresolved. No RH/A2 implication or future campaign transition is claimed. The next direct target is to reuse the exact arithmetic paired-contour and vertical-cancellation identities, prove the required conjugacy or two-frequency relative estimates, and control the resulting phase for zero localization.

Both modules (10public theorems total) are root-imported. Full repository build, fresh complete transitive root axiom audit, actual unabridged public-type inspection, integrity, Git checkpoint and private backup are required for acceptance; verification results follow only after terminal success.

Verification1132: pinned FULL root build PASSED5858jobs, session87253 TERMINAL0. Fresh FULL root transitive axiom audit PASSED34718Foundation declarations, session26227 TERMINAL0, only propext,Classical.choice,Quot.sound. ALL10 new public theorem types were printed and ACTUALLY READ unabridged from the complete fresh log (6FarLeftAnnulus+4FarHalfline). Type/proof review checked actual theta-domain membership on[-1,0], retained nonzero model mismatch, signed Bochner integrability/translation/adjacent interval identities, nonzero normalization with MODEL curvature at the ACTUAL saddle, exact |Imz|<=1 restriction, conditional uniformity and fixed-time existence quantifiers. Manifest1785 covers every Foundation/root source; all prior1783 hashes unchanged except reviewed root imports. All107archive,43Incoming/42distinct and11fullyreadA4 hashes match saved baselines. No sorry/admit/new axiom/native admission, manuscript/dependency change or unrelated draft modification. All proof jobs terminal0. Evidence: .lake/stardust-1132-full-build.log, stardust-1132-audit.log, stardust-1132-working-checkpoint.json, stardust-1132-source-integrity.json, stardust-1132-public-types.json and stardust-1132-verification.json. Exact FIVE-path audited Git checkpoint, exact-commit receipt and verified private backup follow. A4 remainsACTIVE; pairing-to-zero estimates and global reentry remainOPEN. No campaign transition.

## Stardust1133 — actual real-axis full-flow pairing and saddle-phase error (October 19, 2026)

The previous turn made verified progress: checkpoint3a37ab752b42b58cd70efdba17f874cf2aeb8428 proved the actual whole positive horizontal Gaussian asymptotic, passed the full5858-job build and34718-declaration root axiom audit, reviewed all10public types and verified exact PRIVATE main/research refs. Current HEAD, clean tracked state, saved queue and the closed1132evidence were rechecked before this proof. A4 remainsACTIVE; no integerA6, conditionalreal-k/limit, A2 or finalmultichannel campaign opened. October31hardstop and all verification gates remain unchanged. Terminal system-time observations include21:22:56,21:24:30,21:25:39 and21:26:23 America/New_York. No manuscripts, pinned dependencies or unrelated drafts were changed.

A theorem-level reuse audit found NaturalContour.flow_eq_paired_horizontal and vertical_pair_cancel already prove the actual paired contour identity and exact cancellation of signed vertical endpoints for |h|<pi/8. KernelReflection.kernel_conj and moment_conj already prove actual series conjugacy. These foundations are reused rather than reproved. The old GaussianPrefactor.gaussianFactor uses ACTUAL curvature; the far-frequency asymptotic uses MODEL curvature at the corrected ACTUAL saddle. They are not silently identified.

Foundation/RiemannQuarticFarPairing.lean introduces two explicit expression definitions, horizontalIntegral(t,z,h) for the genuine positive horizontal Bochner integral and modelGaussianAmplitude(t,z,v)=W_t(z,v)*integral_R exp(Dprime_t(v)*s^2/2), and12public theorems. weight_conj proves W_t(-conj(z),conj(q))=conj(W_t(z,q)) directly from the existing kernel conjugacy, with the correct frequency sign. horizontal_conj passes this to the ACTUAL integral and opposite height by Bochner integral_conj. flow_real_horizontal then reuses the exact paired contour theorem: for EVERY realt,x and strict-natural-strip heighth, the ACTUAL full quartic flow at realx equals the real part of horizontalIntegral(t,x,h). This is not an expectation-level or model-only heat formula, and the1/2 paired normalization is retained correctly.

real_pair_error gives norm(flow(t,x)-Re(A))<=eta*norm(A) whenever A!=0 andnorm(H/A-1)<=eta. It deliberately normalizes by the magnitude of the COMPLEX amplitude, never its potentially vanishing real part. real_pair_cosine_error gives |Re(flow(t,x))/norm(A)-cos(arg(A))|<=eta using Mathlib Complex.cos_arg. This requires no continuous global argument branch, but also proves no phase-derivative estimate. real_pair_zero_phase proves the NECESSARY zero condition |cos(arg(A))|<=eta; real_pair_nonzero proves nonvanishing when |cos(arg(A))|>eta. These are conditional on the displayed actual horizontal error and do not assert nonvanishing at all frequencies. modelGaussianAmplitude_ne_zero independently proves both normalization factors nonzero from the existing corrected-saddle geometry and full complex Gaussian lower bound, retaining MODEL curvature Dprime(v).

eventually_uniform_real_flow_error combines the1132actual entire-horizontal theorem with this exact pairing. For everyeta>0 and ALL sufficiently large real centerx, ALL admissible t>=1,Rew>=120020,|Imw|<=1/2,strongscale100*(t*(normw+1)^3+1)<=x, D(w)=-ix,norm(v-w)<=1/x, and ANY real frequencyy for which G(v)=-iy, it proves A(t,y,v)!=0, the actual full-flow norm error<=eta*norm(A), and the normalized cosine error<=eta. The realfrequencyy may differ from the model-centerx; this stronger quantifier is useful on the constructed unit frequency disks. Uniformity remains conditional on the explicit saddle data and does not supply a uniform-in-time existence cutoff.

eventually_actual_real_flow_cosine uses the previously constructed saddles: for EACH fixedt>=1, EVERY sufficiently large realx has actual/model saddles in the strict natural strip and the nonzero amplitude/cosine approximation. real_flow_cosine_limit_for_saddle_family proves the normalized REAL full-flow-minus-cosine error tends0 in the ordinary real topology along ANY admissible eventually defined family. No continuity or analytic branch is assumed for that limit theorem.

eventually_real_disk_flow_cosine strengthens the existence formulation using the EXISTING actual_far_frequency_disk theorem. For EACH fixedt>=1,eta>0 and EVERY sufficiently large real centerx, there exists a model rootw such that EVERY realy with|y-x|<=1 has a UNIQUE corrected actualrootv in closedBall(w,1/x), nonzero modelGaussianAmplitude and the normalized ACTUAL full-flow cosine error<=eta. Uniqueness is inherited from the actual root problem, not asserted because the error happened to be small. This is a simultaneous pointwise statement on the disk's real diameter; holomorphic/continuous dependence and a controlled derivative of an unwrapped saddle phase are not yet claimed.

Remaining substantive A4 obligations: control saddle-amplitude phase variation and its derivative, justify coherent far-frequency analytic branches on the domains needed, turn paired complex-frequency estimates into zero localization/simplicity, match the intermediate-frequency region, and obtain global all-complex-frequency bounds with an eventual-time cutoff. For nonrealz, frequency -z is NOT -conj(z); the real-axis conjugate pairing cannot be silently used to infer complex zero control. Phase cancellation at real frequencies is genuine and is retained by the cosine/necessary-phase theorem, not removed by an invalid division by Re(A). Both finite/infiniteA4, eventual global Laguerre-Polya reentry and RH/A2 consequences remain OPEN. No novelty assertion or future campaign transition is made.

The new module (14public definitions/theorems) is imported by the root. Full build, fresh complete root transitive axiom audit, unabridged public-type inspection, source integrity, research ledger, exact Git checkpoint and verified PRIVATE backup remain required before acceptance. Verification results follow only after terminal success.

Verification1133: pinned FULL root build PASSED5859jobs, session9072 TERMINAL0. Fresh FULL root transitive axiom audit PASSED34746Foundation declarations, session47604 TERMINAL0, only propext,Classical.choice,Quot.sound. ALL14 public definition/theorem types were printed and ACTUALLY READ unabridged from the complete fresh log; both expression-definition bodies were reviewed in the final source. Review checked -conj(z) and opposite-height signs, actual paired contour/endpoints, full real-axis flow and one-half normalization, nonzero MODEL Gaussian amplitude, norm(A) rather than Re(A) as error scale, necessary zero phase/conditional exclusion, realfrequencyy distinct from modelcenterx, unit-disk real-diameter UNIQUE actual roots, and exact eventual/time/regularity quantifiers. Manifest1786 covers every Foundation/root source; prior1785 hashes unchanged except reviewed root import. All107archive,43Incoming/42distinct and11fullyreadA4 manuscript hashes unchanged. No sorry/admit/new axiom/native admission, manuscript/dependency change or unrelated draft modification. All proof jobs terminal0. Evidence: .lake/stardust-1133-full-build.log, stardust-1133-audit.log, stardust-1133-working-checkpoint.json, stardust-1133-source-integrity.json, stardust-1133-public-types.json and stardust-1133-verification.json. Exact FOUR-path audited Git checkpoint, receipt and verified PRIVATE backup follow. A4 remainsACTIVE; phase variation, nonreal zeros and eventual global reentry remainOPEN. No queued campaign opened.

## Stardust1134 — coherent analytic far saddles and genuine saddle-weight phase growth (October 19, 2026)

The previous goal turn made verified progress:25807125000b3466b3683626118b84a4701e4045 connected the actual horizontal integral to the full real-axis flow, passed full5859-job build/34746-declaration axiom audit and14type reviews, and verified exact PRIVATE main/research refs. Current HEAD, clean tracked state, AGENTS.md, the authoritative saved queue and closed1133evidence were rechecked before proof edits. A4 remainsACTIVE with no future stage opened; October31hardstop is unchanged. Terminal system-time observations include21:30:42,21:32:41,21:33:27,21:34:52,21:35:43,21:36:26 and21:37:15 America/New_York. Manuscripts, dependencies and unrelated drafts remain preserved.

The productive gap was that unique actual saddles at every frequency do not by themselves justify differentiating a saddle amplitude. A direct reuse audit identified FarCorrection.actual_far_frequency_disk, neighbor_slope_analytic, actual_far_deriv_norm_lower, neighbor_error_deriv_bound and model_deriv_near_far_saddle, together with the GENERAL FrequencyBranch.scalar_ball_lower_bound and its existing local-inverse/primitive proof pattern. The older near-real maximizing-saddle branch is parameter-specific and was not assumed to cover the far field.

Foundation/RiemannQuarticFarAnalyticBranch.lean adds18public definitions/theorems. All far-data parameters are explicit: t>=1,x>=10000,Rew>=120020,|Imw|<=1/2,strongscale100*(t*(normw+1)^3+1)<=x and modelD_t(w)=-ix. derivative_affine_bound proves norm(Gprime_t(v)-(-4ix))<=2x on closedBall(w,1/x), using the previously verified actual/model derivative errors. inverse_distance_bound applies the existing convex scalar lower-bound theorem to obtain2x*norm(v-q)<=norm(G_t(v)-G_t(q)) on that entire ball. These control actual arithmetic G, not only modelD.

branch selects the EXISTING unique actualroot for EVERY complexz withnorm(z-x)<=1 and uses a harmless defaultw elsewhere; no regularity outside that disk is asserted. branch_spec records corrected-ball membership and the ACTUAL equation G_t(branch(z))=-iz. branch_distance proves the SHARP inverse bound norm(branch(z)-branch(y))<=norm(z-y)/(2x) on the closed disk. branch_lipschitz supplies continuity there (a conservative Lipschitz constant1 suffices), and branch_continuousAt gives ordinary continuity at all interior points. branch_analyticAt uses the actual analytic slope, actual nonzero inverse derivative and Mathlib's analytic local inverse, together with the proved continuous root selection. Thus the branch is coherent and holomorphic throughout the OPEN unit complex frequency disk; no merely pointwise choice is treated as analytic.

branch_hasStrictDerivAt proves branch'(z)=-i/Gprime_t(branch(z)) from the differentiated actual root identity. branch_deriv_norm_bound gives norm(branch'(z))<=1/(2x). branch_domain retains realpart>=1, strict natural-strip membership|Imbranch|<pi/8 and nonzero ACTUAL theta kernel for the entire closed frequency disk. These hypotheses are derived from corrected_saddle_geometry, not added as unsupported assumptions. The construction remains local to a model-center disk; gluing every far disk into a global branch is not claimed.

actual_weight_hasDerivAt proves the genuine differentiated arithmetic saddle weight W_t(z,branch(z)) has derivative i*branch(z)*W_t(z,branch(z)). It uses the actual theta-series derivative, chain/product rules, and exact cancellation from ACTUAL stationarity. actual_weight_ne_zero and actual_weight_logDerivative then give nonzero weight and W'/W=i*branch(z) on their explicit domains. This closes the actual-weight calculus prerequisite in the far field, without identifying model and actual curvature.

exists_normalized_weight_phase constructs a holomorphic primitive P with P(x)=0 and P'(z)=i*branch(z) on the OPEN unit disk, using the existing Mathlib exactness-on-a-ball theorem. actual_weight_eq_exp_phase proves the exact identity W_t(z,branch(z))=W_t(x,branch(x))*exp(P(z)); the center factor is the weight at the ACTUAL corrected center branch, not the model rootw. weight_phase_real_derivative proves that for EVERY realy with|y-x|<1, d/dy ImP(y)=Rebranch(y)>=120019. The conservative lower bound follows from Rew>=120020 andnorm(branch(y)-w)<=1/x<=1. weight_phase_real_growth applies the existing real mean-value theorem on(x-1,x+1) to prove120019*(b-a)<=ImP(b)-ImP(a) for a<=b in that interval. This is actual unwrapped WEIGHT-phase growth, not a derivative of the discontinuous principal argument.

The important remaining distinction is the Gaussian prefactor. The actual full-flow approximation1133 uses A(z)=W_t(z,branch(z))*integral_R exp(Dprime_t(branch(z))*s^2/2), with MODEL curvature at the actual branch. The present P controls W alone. Neither the Gaussian's analytic dependence/logarithmic derivative nor the full amplitude phase derivative is silently inferred. The proposed identity A'/A=i*branch-(Dsecond(branch)/(2*Dprime(branch)))*branch' remains a target requiring proof. Its correction should be bounded using actual branch' and model-curvature estimates, but no unverified O(1/x) statement is accepted as a theorem here. Existing GaussianPrefactor.gaussianFactor uses ACTUAL curvature and cannot be substituted without an exact bridge.

Next direct A4 target: prove the analytic MODEL-Gaussian factor and its logarithmic derivative on these actual frequency disks, then bound the prefactor phase correction and combine it with the verified1133actual full-flow cosine error. Control of nonreal zeros, simplicity, intermediate frequencies, uniform eventual-time cutoffs and frequencies outside controlled sectors remainsOPEN. Real-axis phase growth alone does not establish all-real zeros or global Laguerre-Polya reentry. Both finite/infiniteA4 alternatives and RH/A2 consequences remain unresolved. No novelty claim or future campaign transition is made.

The module (18public declarations:1definition+17theorems) is root-imported. Full root build, fresh complete transitive axiom audit, actual unabridged public-type review, source integrity, ledger, exact Git checkpoint and verified PRIVATE backup remain required before acceptance. Verification results follow only after terminal success.

Verification1134: pinned FULL root build PASSED5860jobs, session69422 TERMINAL0. Fresh FULL root transitive axiom audit PASSED34781Foundation declarations, session17733 TERMINAL0, only propext,Classical.choice,Quot.sound. ALL18 public definition/theorem types ACTUALLY READ unabridged from the complete fresh log; branch definition body reviewed in final source. Review checked explicit far data, actual affine derivative/inverse bounds, canonical unique-root selection, continuity before local-inverse analyticity, OPEN versus closed disk domains, sharp1/(2x) derivative estimate, actual strip/kernel nonvanishing, genuine arithmetic stationary-weight differentiation, normalized primitive/exponential identity and the real weight-phase derivative/growth domain. The Gaussian-prefactor/full-amplitude phase gap remains explicit. Manifest1787 covers every Foundation/root source; prior1786 hashes unchanged except reviewed root import. All107archive,43Incoming/42distinct and11fullyreadA4 hashes unchanged. No sorry/admit/new axiom/native admission, manuscript/dependency or unrelated draft change. All proof jobs terminal0. Evidence: .lake/stardust-1134-full-build.log, stardust-1134-audit.log, stardust-1134-working-checkpoint.json, stardust-1134-source-integrity.json, stardust-1134-public-types.json and stardust-1134-verification.json. Exact FOUR-path audited Git checkpoint, receipt and verified PRIVATE backup follow. A4 remainsACTIVE; full-amplitude phase, nonreal zeros and global reentry remainOPEN. No queued stage opened.

## Stardust1135 — genuine model-Gaussian calculus and full saddle-amplitude phase growth (October 19, 2026)

Previous goal turn classified as verified progress:54b6ec882b5334943ae3cba0aeaf6baa208176ff constructed the coherent actual analytic far branch and actual-weight phase growth, passed full5860-job build/34781-declaration root audit/18type reviews, and verified exact PRIVATE main/research refs. Current HEAD, clean tracked state, saved instructions/queue and closed1134evidence were rechecked before new proofs. A4 remainsACTIVE and all later stages remain queued. October31hardstop is unchanged. Terminal times include21:41:37,21:43:29,21:44:21,21:45:40 and21:48:01 America/New_York. No manuscripts, dependencies or unrelated drafts changed.

The prior exact gap was the MODEL-Gaussian prefactor in the already proved actual horizontal/full-real-flow approximation. The older GaussianPrefactor.gaussianFactor uses ACTUAL curvature and was not substituted. A direct local-library audit identified Mathlib integral_gaussian_complex, integral_gaussian_sq_complex, HasDerivAt.cpow_const, complex differentiable-on-open-set analyticity, FarGaussianLocal.model_gaussian_coefficient_pos, FarGaussianLimit.gaussian_coefficient_norm_bounds and the newly verified actual far branch. These suffice without differentiating an improper integral under an unproved majorant or introducing new foundational integration infrastructure.

Foundation/RiemannQuarticFarGaussianPhase.lean adds18public declarations (2definitions+16theorems). gaussian_integral_hasDerivAt proves the derivative of the GENUINE full Bochner Gaussian integral G(b)=integral_R exp(-b*s^2): G'(b)=-G(b)/(2b), for Reb>0. The proof first identifies the integral locally with the PRINCIPAL (pi/b)^(1/2), explicitly proves Re(pi/b)>0/slit-plane membership and obtains differentiability. It then differentiates the EXISTING exact squared identity G(b)^2*b=pi and cancels proved nonzero factors. Thus branch choice, local equality, nonzero denominators and the actual integral are justified; no formal interchange of derivative and improper integral is assumed.

model_curvature_hasDerivAt proves the entire model-curvature derivative Dsecond_t(v)=24t*v-64pi*exp(4v). Under the explicit far data t>=1,x>=10000,Rew>=120020,|Imw|<=1/2,strongscale100*(t*(normw+1)^3+1)<=x,modelD(w)=-ix andnorm(v-w)<=1/x, model_curvature_norm_bound proves norm(Dsecond_t(v))<=4096x. It reuses the exact8-constant exp4_difference_bound and model_exp_norm_le_frequency, giving the conservative norm(exp4v)<=9x, and uses the strong polynomial scale to bound24t*normv<=x. The coefficient4096 is deliberately coarse, not claimed optimal.

gaussian(z) is the ACTUAL full Gaussian integral with MODEL curvature Dprime_t(branch(z)), where branch is the verified actual far-saddle branch on the unit complex frequency disk. A private coefficient_pos transfers the already proved positive real part of -Dprime/2. gaussian_hasDerivAt applies the genuine Gaussian derivative and the actual branch chain rule to obtain Gm'(z)=-(Dsecond(branch)/(2Dprime(branch)))*branch'(z)*Gm(z). gaussian_ne_zero reuses the proved actual-amplitude nonzero factors. gaussian_logDerivative records the exact quotient formula, and gaussian_logDerivative_norm_bound proves norm(Gm'/Gm)<=512/x. The denominator estimate normDprime>=2x and ACTUAL inverse derivative bound normbranch'<=1/(2x) are both retained. The actual/model curvatures are not conflated.

gaussian_analyticAt proves holomorphy on the OPEN unit frequency disk from the proved complex derivative at every point and the existing Mathlib analytic-on-open-set theorem. phaseSlope(z)=i*branch(z)+Gm'(z)/Gm(z) is an explicit definition of the FULL model-Gaussian saddle-amplitude logarithmic slope. phaseSlope_analyticAt proves its analytic domain; phaseSlope_error_bound proves norm(phaseSlope-i*branch)<=512/x. amplitude_hasDerivAt and amplitude_logDerivative identify it with A'/A for the EXISTING FarPairing.modelGaussianAmplitude(t,z,branch(z))=ACTUAL W_t(z,branch(z))*Gm(z). This closes the previously unresolved prefactor logarithmic-derivative identity on the actual branch, with the correct minus sign and factor2.

exists_normalized_amplitude_phase constructs P(x)=0,P'=phaseSlope on the OPEN unit complex disk using the existing exactness theorem. amplitude_eq_exp_phase proves EXACTLY A(z)=A(x)*exp(P(z)), normalized by the ACTUAL corrected center amplitude including the MODEL Gaussian. amplitude_phase_real_derivative proves d/dy ImP(y)=ImphaseSlope(y)>=120018 for EVERY real|y-x|<1. It reuses actual weight-phase growth Rebranch>=120019, the rigorous512/x<=1 bound and the imaginary-part norm estimate. amplitude_phase_real_growth proves120018*(b-a)<=ImP(b)-ImP(a) for a<=b in(x-1,x+1) by the real mean-value theorem. This is unwrapped FULL AMPLITUDE phase growth, rather than differentiation of a discontinuous principal argument. The Gaussian phase gap from1134is now closed on these explicit local far disks.

The next substantive step is to connect this unwrapped full-amplitude phase to the actual1133full real-flow cosine error throughout the constructed unit frequency diameter. The bridge cos(argA(z))=cos(argA(center)+ImP(z)) must be proved from the exact exponential representation and nonzero normalization. Then a justified intermediate-value sign argument may produce actual real zeros in sufficiently far real intervals. No such zero-existence, simplicity, or nonreal-zero theorem is claimed in this checkpoint merely from phase growth. The real-center versus varying real-frequency quantifiers remain distinct; simultaneous estimates are available from eventually_uniform_real_flow_error, conditional on actual branch data.

Nonreal-frequency paired-contour estimates, simplicity, intermediate-frequency matching, uniform eventual-time cutoffs and global zero control outside constructed sectors remainOPEN. For nonrealz, -z differs from-conj(z); the real-axis exact conjugate pair is not silently extended there. Both finite/infiniteA4 and eventual global Laguerre-Polya reentry remain unresolved; no RH/A2 or threshold implication is asserted. No future campaign started and no novelty claim is made.

The module (18public declarations) is root-imported. Full build, fresh complete root transitive axiom audit, unabridged public-type inspection, source integrity, ledger, exact Git checkpoint and verified PRIVATE backup remain required before acceptance. Verification results follow only after terminal success.

Verification1135: pinned FULL root build PASSED5861jobs, session54031 TERMINAL0. Fresh FULL root transitive axiom audit PASSED34821Foundation declarations, session31715 TERMINAL0, only propext,Classical.choice,Quot.sound. ALL18 public definition/theorem types ACTUALLY READ unabridged from the complete fresh log; both definition bodies reviewed in final source. Review checked genuine Gaussian integral/principal branch domains, local equality and squared-identity differentiation, nonzero denominators, MODEL second curvature4096x bound, composition with ACTUAL branch, correct Gaussian logarithmic minus sign/factor2, explicit512/x correction, OPEN-disk analyticity, actual existing amplitude normalization/derivative, normalized full-amplitude primitive and exact exponential identity, real120018 derivative/growth domain, and all unresolved zero obligations. Manifest1788 covers every Foundation/root source; prior1787 hashes unchanged except reviewed root import. All107archive,43Incoming/42distinct and11fullyreadA4 hashes unchanged. No sorry/admit/new axiom/native admission, manuscript/dependency or unrelated draft change. All proof jobs terminal0. Evidence: .lake/stardust-1135-full-build.log, stardust-1135-audit.log, stardust-1135-working-checkpoint.json, stardust-1135-source-integrity.json, stardust-1135-public-types.json and stardust-1135-verification.json. Exact FOUR-path audited Git checkpoint, receipt and verified PRIVATE backup follow. A4 remainsACTIVE; actual-flow sign/zero existence in far unit intervals, nonreal-zero localization and eventual global reentry remainOPEN. No queued stage opened.

## Stardust1136 — actual far-frequency sign changes and infinitely many real zeros (October 19, 2026)

Previous goal turn classified as verified progress:462c9117c7fe215c608ce20ab650da5e7573a1c4 closed the genuine MODEL-Gaussian prefactor/full-amplitude phase gap, passed full5861-job build/34821-declaration axiom audit/18type reviews and verified exact PRIVATE main/research refs. Current HEAD, clean tracked state, AGENTS.md, the authoritative queue and closed1135evidence were rechecked before proof edits. A4 remainsACTIVE with no queued stage opened. October31hardstop is unchanged. Terminal system times include21:52:48,21:54:58,21:56:07 and21:57:36 America/New_York. Manuscripts, pinned dependencies and unrelated drafts were preserved.

Foundation/RiemannQuarticFarRealZeros.lean adds7public theorems that directly combine the proved actual arithmetic contour asymptotic, coherent far branch, full MODEL-Gaussian amplitude phase and real intermediate-value machinery. A read-only reuse audit identified FarPairing.eventually_uniform_real_flow_error, FarGaussianLimit.eventually_controlled_far_saddles, FarGaussianPhase.amplitude_eq_exp_phase/amplitude_phase_real_growth, Mathlib intermediate_value_Icc/Icc', RiemannQuarticFlow.flow_differentiable and the EXISTING Reality.flow_im_zero. No new contour approximation, saddle construction or foundational integration infrastructure was introduced.

cos_arg_mul_exp proves the exact general identity cos(arg(a*exp(p)))=cos(arg(a)+Im(p)) for EVERY nonzero complexa and complexp. It uses the actual cosine/sine argument identities, complex exponential real/imaginary parts and nonzero norms. No principal-argument continuity or differentiation is assumed. This supplies the previously missing bridge from the verified unwrapped full-amplitude phase to the actual real-flow cosine estimate.

actual_real_sign_change works under the explicit far data t>=1,x>=10000,Rew>=120020,|Imw|<=1/2,strongscale100*(t*(normw+1)^3+1)<=x andmodelD(w)=-ix, together with the actual normalized full-flow cosine error<=1/4 onIcc(x,x+1/2). It constructs the already verified actual branch B and normalized FULL amplitude phase P. For theta(y)=arg(Acenter)+ImP(y), exact P(x)=0 and principal center-argument bounds give theta(x)<=pi; the VERIFIED120018-phase-growth bound gives theta(x+1/2)>=3pi. Complex differentiability of P gives actual continuity on that real interval. The real IVT produces points with theta=2pi and3pi. Phase growth orders these points strictly. At them the amplitude cosine is respectively1 and-1; the actual error<=1/4 and PROVEN positive amplitude norm give STRICT positive and negative values of the actual flow's real part. Thus it proves x<=a<b<=x+1/2 with actual opposite signs. The amplitude includes the MODEL Gaussian at the ACTUAL saddle, so its phase correction is not omitted.

eventually_actual_real_sign_change discharges all of that theorem's saddle/error hypotheses from EXISTING verified results. For EACH fixed realt>=1, ALL sufficiently large real frequency centersx have such actual sign-change points. The error theorem is applied correctly with model-centerx and varying REALfrequencyy, using the actual branch root at eachy andnorm(B(y)-w)<=1/x throughout the half-unit interval. No uniform-in-time cutoff or unspecified saddle-family existence is assumed.

eventually_actual_real_zero then applies the real IVT to the ACTUAL flow's real part, whose continuity follows from the proved entire flow. Strict endpoint signs place the zero in the OPEN interval(x,x+1/2). The EXISTING actual cosine-transform reality theorem Reality.flow_im_zero then proves the COMPLEX flow itself is zero there; a zero of the real part is not silently identified with a complex zero. The final precise statement is: for EACH fixedt>=1, EVERY sufficiently large realx admits realy with x<y<x+1/2 and RiemannQuarticFlow.flow(t,y)=0.

arbitrarily_large_actual_real_zero proves that for every realR there is an ACTUAL real quartic-flow zero y>R at each fixedt>=1. real_zeros_not_bddAbove and infinitely_many_actual_real_zeros record that the actual real zero set is unbounded above and infinite. These conclusions concern the arithmetic Xi-kernel quartic flow itself, not a generic entire-function example, a model saddle, or numerical approximations. The eventual parameter is FREQUENCYx at FIXEDt; it is not an eventual-time global real-rootedness theorem.

This closes the specific1135open sign-change/real-zero existence target in sufficiently far half-unit intervals. It does NOT prove simplicity of these zeros, uniqueness or a zero count in those intervals, exclusion of additional nonreal zeros, a global Laguerre-Polya theorem or either A4 threshold alternative. Infinitely many real zeros can coexist with nonreal zeros. No RH/A2 implication or novelty claim is asserted.

Next direct A4 priority is the complex-frequency paired-contour estimate and real/simple zero localization, using the already verified analytic actual branch/amplitude. For nonrealz, -z differs from-conj(z), so real-axis conjugate pairing cannot be applied unchanged. Independently adapted saddle heights may leave a signed vertical endpoint difference; preserve it and prove its actual arithmetic bound before using a complex cosine approximation. Existing NaturalContour halfline_contour_shift_signed/vertical_pair_cancel and WindowZeros/CosineLocalZeros/ZeroStrip methods are reusable once their actual domains and approximation hypotheses are proved. Intermediate-frequency matching, uniform eventual-time cutoffs and global zero control outside controlled sectors remainOPEN. A4 staysACTIVE, and all later campaigns remain gated.

The module (7public theorems) is root-imported. Full build, fresh complete root transitive axiom audit, actual unabridged public-type inspection, source integrity, ledger, exact Git checkpoint and verified PRIVATE backup remain required before acceptance. Verification results follow only after terminal success.

Verification1136: pinned FULL root build PASSED5862jobs, session7892 TERMINAL0. Fresh FULL root transitive axiom audit PASSED34838Foundation declarations, session81651 TERMINAL0, only propext,Classical.choice,Quot.sound. ALL7 new public theorem types ACTUALLY READ unabridged from the complete fresh log. Review checked the exact exponential cosine bridge, full MODEL-Gaussian amplitude/actual branch, discharged conditional quarter-error, ordered STRICT actual signs, fixed-time/eventual-frequency quantifiers, OPEN half-unit zero interval, actual-flow continuity and actual reality before claiming a complex-flow zero, and unbounded/infinite real zero-set consequences. Simplicity/nonreal exclusion/global reentry remain explicit open obligations. Manifest1789 covers every Foundation/root source; prior1788 hashes unchanged except reviewed root import. All107archive,43Incoming/42distinct and11fullyreadA4 hashes unchanged. No sorry/admit/new axiom/native admission, manuscript/dependency or unrelated draft change. All proof jobs terminal0. Evidence: .lake/stardust-1136-full-build.log, stardust-1136-audit.log, stardust-1136-working-checkpoint.json, stardust-1136-source-integrity.json, stardust-1136-public-types.json and stardust-1136-verification.json. Exact FOUR-path audited Git checkpoint, receipt and verified PRIVATE backup follow. A4 remainsACTIVE; no queued stage opened.

## Stardust1137 — actual complex-frequency saddle pair with controlled signed endpoint residual (October 19, 2026)

Previous goal turn classified as verified progress:7bc91fadaf6526987e7a04572728f67201ec5e16 proved actual real-flow sign changes and zeros in every sufficiently far OPEN half-unit real interval, passed full5862-job build/34838-declaration audit/7type reviews, and verified exact PRIVATE main/research refs. Current HEAD, clean tracked state, AGENTS.md, authoritative queue and closed1136notes were rechecked before proof edits. A4 remainsACTIVE; no queued stage opened and October31hardstop is unchanged. Terminal times include22:01:41,22:05:12,22:06:32,22:08:02,22:09:33,22:11:01,22:12:33 and22:13:29 America/New_York. Manuscripts, pinned dependencies and unrelated drafts remain preserved.

The mathematical obstruction addressed here is specific: for NONREAL frequencyz, the actual positive-frequency saddle B(z) and the reflected negative-frequency saddle conj(B(conj(z))) need not have opposite heights. The already proved real-axis conjugate pair cannot simply be reused with the endpoint term deleted. A direct theorem-level reuse audit identified NaturalContour.halfline_contour_shift_signed/vertical_pair_cancel/weight_analyticAt, FarPairing.horizontal_conj, the coherent FarAnalyticBranch.branch and sharp inverse bound, ThetaSmallParameter's positive-parameter arithmetic bounds, existing kernel_norm_lower, actual_center_theta_upper, full Gaussian normalization and compactBudget limit. These proved tools suffice to keep and estimate the actual signed residual.

Foundation/RiemannQuarticFarComplexPairing.lean adds12public theorems. vertical_interval_integrable proves actual Bochner interval integrability on ANY vertical segment between strict-natural-strip heights. flow_unequal_heights gives the EXACT identity flow(t,z)=(H(t,z,h)+conj(H(t,conj(z),k))+i*integral_k^h W_t(z,iy)dy)/2 for |h|,|k|<pi/8. The proof reuses both signed half-line shifts, exact vertical pair cancellation and an adjacent-interval identity. The residual has the displayed orientation k..h; it vanishes at coincident heights, not at arbitrary complex-frequency saddles.

cosine_margin_between uses the existing concavity/minimum principle for cos on[-pi/2,pi/2] to retain a COMMON positive lower bound c for cos(4y) throughout the segment from the two endpoint margins. vertical_segment_bound proves the ACTUAL signed norm bound <=(528*|h-k|/c^3)*exp(t+|Re(z)|*|h-k|-Re(z)*h) for t>=0 and those explicit strict-strip/positive-margin hypotheses. It uses the existing arithmetic compact_weight_bound at horizontal coordinate0, quartic vertical height |y|<1, the actual frequency attenuation and a genuine finite interval-integral norm estimate. No bound at c=0 or outside the natural strip is asserted.

vertical_center_bound compares that residual with the actual arithmetic saddle weight at v=a+ih, under a>=64,t>=1,|Imz|<=1,|h-k|<=1,|Rez|*|h-k|<=2,Reexp4v>=1,pi*Reexp4v<=t*a^3+3 and cos(4k)>=exp(-4(a+2)). It proves norm(integral_k^h W(z,iy))<=528*normW(z,v)*exp(5a+3-2t*a^3). The shrinking cosine margin is retained as c=exp(-4(a+2)), with explicit c^(-3)=exp(12(a+2)). The center lower bound is derived from the EXISTING arithmetic kernel_norm_lower. The actual negative quartic gap beats that margin loss; the source proves the polynomial inequality and frequency-factor comparison instead of assuming uniform boundedness near the boundary.

Under the SAME explicit far data t>=1,x>=10000,Rew>=120020,|Imw|<=1/2,strongscale100*(t*(normw+1)^3+1)<=x,modelD(w)=-ix, let B be the EXISTING coherent actual branch on the unit complex frequency disk. branch_height_gap proves the SHARP bound |ImB(z)-ImB(conj(z))|<=|Imz|/x. flow_actual_branch_pair applies the exact unequal-height identity with these two actual heights, retaining the genuine arithmetic signed vertical residual.

actual_branch_endpoint_bound discharges ALL vertical_center_bound hypotheses on the CLOSED unit frequency disk norm(z-x)<=1. Both actual theta parameters are>=1 by the existing corrected-neighborhood domain theorem. Their comparable real parts yield the common positive cosine margin. The sharp height difference gives the frequency-attenuation cost<=2; |Imz|<=1 and |Rez|<=x+1 are derived from the disk. The existing actual slope error bound and ACTUAL stationarity G(B(z))=-iz give the center upper bound pi*Reexp4B<=t*(ReB)^3+3 via actual_center_theta_upper. No model stationarity at the corrected saddle is assumed.

relative_actual_branch_endpoint_bound divides by the PROVEN nonzero existing modelGaussianAmplitude A(z)=W_t(z,B(z))*fullGaussian(Dprime_t(B(z))) and obtains1056*sqrtx*exp(5ReB+3-2t*(ReB)^3). The Gaussian retains MODEL curvature at the ACTUAL saddle. relative_endpoint_budget bounds this by the EXISTING compactBudget(ReB)=10560000exp(8ReB+5-2*(ReB)^3), reusing frequency_exp_bound and the proved Gaussian lower bound. eventually_uniform_relative_endpoint reuses compactBudget_tendsto_zero: for everyeta>0, ALL sufficiently large real centerx and ALL admissible t,w and complexz in the unit disk have normalized signed endpoint norm<=eta. It introduces no new scalar-limit infrastructure.

eventually_uniform_complex_pair_error now proves the ACTUAL COMPLEX-FREQUENCY two-amplitude approximation: for everyeta>0, ALL sufficiently large real centerx and ALL admissible far data and norm(z-x)<=1,
  norm(flow(t,z)-(A(z)+conj(A(conj(z))))/2) <= eta*(normA(z)+normA(conj(z))).
Here both A terms use the same verified model-centerw and actual analytic branch, each with its MODEL-curvature Gaussian. The proof combines the genuine1132entire-horizontal errors atz andconj(z), the EXACT residual identity and the newly proved residual negligibility before taking the final norm. Reflection preserves the frequency disk and all imaginary-part restrictions are proved. The error scale is the SUM OF AMPLITUDE MAGNITUDES, not the potentially vanishing magnitude of their sum. Conditional uniformity in t,data is not a uniform-in-time existence cutoff; fixed-time nonvacuity follows from the already constructed far saddles for every sufficiently large real center.

Thus the signed unequal-height endpoint obstruction and the actual complex paired approximation are closed on this precise local far-disk domain. The next direct target is an analytic balanced envelope and real-compatible nonlinear cosine phase for (A+A-reflected)/2, with explicit derivative control, followed by reuse of existing CosineLocalZeros/ZeroStrip/WindowZeros local-injectivity methods. The current norm approximation does NOT itself prove simplicity, absence of nonreal zeros or global Laguerre-Polya membership. Intermediate-frequency matching, global complex sectors outside these disks, and uniform eventual-time/global estimates remainOPEN. Both finite/infiniteA4 and eventual global reentry remain unresolved. No RH/A2 or novelty claim is made, and all later campaigns stay gated.

The new module (12public theorems) is root-imported. Full build, fresh complete root transitive axiom audit, actual unabridged public-type review, source integrity, ledger, exact Git checkpoint and verified PRIVATE backup remain required before acceptance. Verification results follow only after terminal success.

Verification1137: pinned FULL root build PASSED5863jobs, session67977 TERMINAL0. Fresh FULL root transitive axiom audit PASSED34862Foundation declarations, session26132 TERMINAL0, only propext,Classical.choice,Quot.sound. ALL12 public theorem types ACTUALLY READ unabridged from the complete fresh log. Review checked signed Bochner integrability, reflected-frequency/opposite-height signs and residual orientation, explicit positive cosine margins/natural-strip domains, genuine arithmetic endpoint norm and negative quartic gap, sharp |Imz|/x height difference, discharged actual branch hypotheses and center theta upper bound from ACTUAL stationarity, nonzero MODEL Gaussian amplitude normalization, reused compactBudget limit, exact conditional uniformity, closed complex/reflected disk domains, and actual full-flow two-amplitude error scaled by the SUM OF MAGNITUDES. No zero/simplicity/global conclusion is inferred from that error alone. Manifest1790 covers every Foundation/root source; prior1789 hashes unchanged except reviewed root import. All107archive,43Incoming/42distinct and11fullyreadA4 hashes unchanged. No sorry/admit/new axiom/native admission, manuscript/dependency or unrelated draft change. All proof jobs terminal0. Evidence: .lake/stardust-1137-full-build.log, stardust-1137-audit.log, stardust-1137-working-checkpoint.json, stardust-1137-source-integrity.json, stardust-1137-public-types.json and stardust-1137-verification.json. Exact FOUR-path audited Git checkpoint, receipt and verified PRIVATE backup follow. A4 remainsACTIVE; balanced cosine normalization, nonreal-zero localization and eventual global reentry remainOPEN. No queued stage opened.

## Stardust1138 — analytic far-field cosine normalization and actual zero-strip control (October 19, 2026)

Previous goal turn classified as verified progress:a59c7de6f99bddd3ab515f38fd9726eadbdbac2c proved the actual complex saddle-pair approximation with the signed unequal-height endpoint residual controlled, passed full5863-job build/34862-declaration audit/12type reviews and verified exact PRIVATE main/research refs. Current HEAD, clean tracked state, AGENTS.md, authoritative queue and closed1137evidence were rechecked before proof edits. A4 remainsACTIVE; later campaigns remain queued, and October31hardstop is unchanged. Terminal times include22:18:50,22:21:11,22:23:29,22:25:38 and22:26:37 America/New_York. Manuscripts, pinned dependencies and unrelated drafts were preserved.

The direct target was to put the ACTUAL complex pair into a usable cosine-perturbation framework, without differentiating principal arguments or assuming an analytic phase inverse. A theorem-level reuse audit found the exact polar identity Complex.norm_mul_exp_arg_mul_I, Complex.two_cos, Mathlib HasDerivAt.conj_conj, the1135actual full-amplitude primitive/derivative, the1137actual paired error and the EXISTING ZeroStrip.small_cos_im and GENERAL scalar_ball_lower_bound. These supply a direct construction and an actual zero-localization theorem.

Foundation/RiemannQuarticFarCosinePhase.lean adds20public declarations (2definitions+18theorems). For a fixed center amplitudea and a phase functionP, envelope(a,P,z)=norm(a)*exp((P(z)+conj(P(conj(z))))/2) and phase(a,P,z)=arg(a)+(P(z)-conj(P(conj(z))))/(2i). Only the FIXED real center argumentarg(a) is used; no varying principal argument is assumed continuous or differentiated.

split_exponentials proves the exact two exponential factors. pair_identity gives (a*exp(P(z))+conj(a)*exp(conj(P(conj(z)))))/2=envelope*cos(phase). pair_norm_identity proves the exact magnitude identity norm(left amplitude)+norm(right amplitude)=2*norm(envelope)*cosh(Imphase). envelope_ne_zero proves the normalization nonzero whena!=0. envelope_conj, phase_conj and phase_real establish the real-compatible reflection identities, and normalized_flow_conj reuses the ACTUAL flow's proved conjugacy. These are exact algebraic/exponential statements, not asymptotic analogies.

Under the same explicit far data t>=1,x>=10000,Rew>=120020,|Imw|<=1/2,strongscale100*(t*(normw+1)^3+1)<=x andmodelD(w)=-ix, let B be the verified coherent ACTUAL branch and a=A(x)=modelGaussianAmplitude(t,x,B(x)). LetP be ANY normalized actual full-amplitude primitive P(x)=0,P'=S=A'/A on the OPEN unit complex frequency disk; existence was already proved in1135. actual_pair_identity and actual_pair_norm_identity identify the generic formulas with the ACTUAL arithmetic saddle amplitudes A(z),conj(A(conj(z))), including their MODEL-curvature Gaussian factors. Both frequency arguments remain in the correct conjugation-stable domain.

phase_hasDerivAt proves Phi'(z)=(S(z)-conj(S(conj(z))))/(2i), explicitly deriving the reflected derivative by HasDerivAt.conj_conj atconj(z). envelope_analyticAt, phase_analyticAt and normalized_flow_analyticAt prove holomorphy on the OPEN unit disk. The normalized actual flow is divided by a PROVEN nonzero envelope; it is not assumed entire outside this local domain. phase_deriv_model_bound proves norm(Phi'(z)-Rew)<=513/x: the actual amplitude correction contributes512/x and the actual branch displacement contributes1/x. Both model imaginary parts cancel correctly under reflection, leaving the positive REAL model scaleRew.

phase_im_lower_bound applies the existing convex scalar-ball lower theorem on a strictly smaller closed disk containingz andconj(z), preserving the OPEN-disk analytic hypotheses. It proves Rew*|Imz|<=2*|ImPhi(z)|. The closed-disk radius is explicitly buffered between norm(z-x) and1; no differentiability on the unit boundary is asserted. Exact Phi(conjz)=conjPhi(z) supplies the conversion from complex inverse separation to imaginary parts.

eventually_uniform_normalized_cosine_error combines the1137actual paired error with the exact normalization and magnitude identity. For everyepsilon>0, ALL sufficiently large real centersx, ALL admissible far data, ALL normalized primitivesP and ALL complexz withnorm(z-x)<1,
  norm(flow(t,z)/E(z)-cos(Phi(z)))<=epsilon*cosh(ImPhi(z)).
The factor2 from the two amplitude norms is handled by using the previous paired theorem with eta=epsilon/2. The approximation concerns the ACTUAL full arithmetic flow; the signed endpoint residual was already controlled, not discarded. The envelope remains nonzero even at cancellation zeros of the pair.

eventually_uniform_zero_strip directly reuses the EXISTING ZeroStrip.small_cos_im. For every0<epsilon<=1/2, ALL sufficiently large real centersx and admissible far data, every ACTUAL flow zeroz in the OPEN unit frequency disk satisfies BOTH |ImPhi(z)|<=2epsilon and |Imz|<=4epsilon/Rew. This is a genuine complex-zero localization theorem for the arithmetic quartic flow on the displayed far-disk domain. It is conditional-uniform in the explicit model/branch data; fixed-time nonvacuity follows from the already constructed far saddles. The eventual center cutoff depends on epsilon. Letting epsilon approach0 does NOT establish exact reality at a fixed center without controlling those cutoffs.

A precise reuse obstruction was also identified: CosineLocalZeros.real_simple_zero and perturbation_deriv_bound assume a GLOBALLY complex-differentiable functionf, whereas the new normalized far-phase maps have only a proved LOCAL holomorphic domain. An arbitrary local holomorphic function need not have the needed entire extension. Before invoking that criterion, prove a local-hypothesis version by reusing its actual Cauchy/scalar lower proof on explicitly contained closed disks, or supply another justified local argument. Do not silently promote local analyticity to global differentiability. The generic normalization already gives global conjugation compatibility as an identity of defined functions, so the regularity/domain requirement is the specific remaining mismatch.

Next A4 priority is local reality and simplicity from the now verified weighted cosine approximation, conjugacy and phase derivative control, using a rigorously localized version of existing injectivity machinery. An affine real phase scale on small disks may avoid unnecessary nonlinear inverse infrastructure; either route must prove its actual containment and Cauchy estimates. Current thin-strip localization does NOT prove exact reality, simplicity, a zero count, or global Laguerre-Polya membership. Intermediate-frequency matching, global sectors outside these disks and uniform eventual-time/global estimates remainOPEN. Both finite/infiniteA4 and eventual global reentry remain unresolved. No RH/A2 or novelty claim is made; no queued campaign started.

The module (20public declarations) is root-imported. Full build, fresh complete root transitive axiom audit, actual unabridged public-type review, source integrity, ledger, exact Git checkpoint and verified PRIVATE backup remain required before acceptance. Verification results follow only after terminal success.

Verification1138: pinned FULL root build PASSED5866jobs, session61607 TERMINAL0. Fresh FULL root transitive axiom audit PASSED34921Foundation declarations, session58903 TERMINAL0, only propext,Classical.choice,Quot.sound. ALL20 public definition/theorem types ACTUALLY READ unabridged from the complete fresh log; both definition bodies reviewed in final source. Review checked fixed-center argument/exponential factorization, exact magnitude/cosh identity/nonzero envelope, reflection and actual-flow conjugacy, actual branch/MODEL-Gaussian amplitudes, normalized primitive and reflected derivative with2i denominator, OPEN-disk analyticity,513/x REAL model derivative bound, buffered closed-disk inverse lower estimate, actual weighted cosine error/factor2 calibration, and necessary phase/frequency zero bounds for0<epsilon<=1/2. The epsilon-dependent cutoff is retained; no epsilon-limit exact reality is inferred. The old zero criterion's global-regularity mismatch remains explicit. Manifest1791 covers every Foundation/root source; prior1790 hashes unchanged except reviewed root import. All107archive,43Incoming/42distinct and11fullyreadA4 hashes unchanged. No sorry/admit/new axiom/native admission, manuscript/dependency or unrelated draft change. All proof jobs terminal0. Evidence: .lake/stardust-1138-full-build.log, stardust-1138-audit.log, stardust-1138-working-checkpoint.json, stardust-1138-source-integrity.json, stardust-1138-public-types.json and stardust-1138-verification.json. Exact FOUR-path audited Git checkpoint, receipt and verified PRIVATE backup follow. A4 remainsACTIVE; exact reality/simplicity on far disks and eventual global reentry remainOPEN. No queued stage opened.

## Stardust1139 — locally justified real and simple actual zeros in the far horizontal half-strip (October 19, 2026)

Previous goal turn classified as verified progress:2901fddddf392dcf17b58ad823c0a3c6b52a05a0 proved actual analytic cosine normalization and necessary phase/frequency zero-strip bounds, passed full5866-job build/34921-declaration root audit/20type reviews and verified exact PRIVATE main/research refs. Current HEAD, clean tracked state, AGENTS.md, authoritative queue and closed1138evidence were rechecked before proof edits. A4 remainsACTIVE with no queued stage opened. October31hardstop is unchanged. Terminal times include22:33:11,22:35:04,22:39:58,22:41:32 and22:43:03 America/New_York. Manuscripts, dependencies and unrelated drafts were preserved.

The exact reuse obstruction from1138was addressed first. The existing CosineLocalZeros.real_simple_zero is valid for GLOBALLY complex-differentiable functions, but the actual far normalization is only proved holomorphic on a local disk. Foundation/RiemannQuarticLocalCosineZeros.lean adds2public theorems extending the SAME proved Cauchy/scalar-injectivity method to local hypotheses, preserving the older valid declarations unchanged. perturbation_deriv_bound now requires pointwise complex differentiability only on closedBall(a,1), plus the same1/1000 cosine-error bound. Its Cauchy disk closedBall(w,1/2) is explicitly contained in that domain; DiffContOnCl is obtained from the local differentiability/continuity on that actual containing set. real_simple_zero uses the same local hypothesis and global conjugation identity to prove reality and nonzero derivative for a zero within1/1000ofa. No entire extension is assumed or constructed. The center a is ANY real number; the proof does not require an exact cosine zero or an integer lattice search.

Foundation/RiemannQuarticFarSimpleZeros.lean adds4public theorems applying that local criterion to the ACTUAL arithmetic quartic flow. actual_real_simple_zero uses the standard explicit far data t>=1,x>=10000,Rew>=120020,|Imw|<=1/2,strongscale100*(t*(normw+1)^3+1)<=x,modelD(w)=-ix, the existing actual branch B and FULL model-Gaussian amplitude normalization. It assumes the already verified weighted actual normalized-flow cosine error<=1/1000000 throughout the OPEN unit frequency disk and proves every actual flow zeroz in the buffered OPEN half-unit disk norm(z-x)<1/2 is real and has deriv(flow t)(z)!=0.

The proof uses a REAL affine phase scale rather than introducing an unnecessary nonlinear inverse. Set p=Rez,s=Rew>0,a=RePhi(p), and L(q)=p+(q-a)/s. phase_real proves Phi(p)=a as a complex equality. For q in closedBall(a,1), L(q) lies in closedBall(p,1/s), whose containment in the ORIGINAL open unit disk is explicitly proved from norm(p-x)<1/2 and1/s<=1/1000. Thus all pointwise complex differentiability required by the localized Cauchy criterion, including its closed-disk boundary, comes from a genuinely proved analytic neighborhood.

The existing actual phase derivative estimate norm(Phi'-s)<=513/x, applied through the convex mean-value bound, gives norm(Phi(L(q))-q)<=513/(x*s)<=1/1000000. The numerical inequality is proved from x>=10000 ands>=120020. The actual normalized flow F=flow/E is therefore within1/1000ofcos(q) on that entire LOCAL phase disk: the weighted error is controlled by the proved cosh bound<=9, and the cosine variation by a proved radius2 Lipschitz bound9. No fixed-radius1 trigonometric bound is applied outside its domain. All estimates are exact Lean inequalities, not floating-point tests.

For an actual zeroz, q0=a+s*(z-p) maps back EXACTLY toz. The1138necessary zero-strip/phase inverse lower bounds with FIXED epsilon=1/1000000 place q0 within1/1000of the real center a. This uses a single verified error tolerance, not an invalid epsilon->0 argument at fixedx. The affine map has real coefficients and the actual normalized flow has the proved conjugation identity. The localized Cauchy/injectivity theorem therefore gives q0.im=0 and nonzero derivative of F composed withL. Since q0.im=s*z.im withs>0, z.im=0. Finally, at the actual flow zero, the proved nonzero envelope, quotient rule and nonzero affine derivative transfer simplicity back to deriv(RiemannQuarticFlow.flow t)(z). A derivative of only the model amplitude or normalized auxiliary function is not substituted for the actual flow derivative.

eventually_uniform_real_simple_zeros DISCHARGES the weighted-error and normalized-phase hypotheses using the EXISTING1135phase existence and1138eventually_uniform_normalized_cosine_error at the fixed rational tolerance. For ALL sufficiently large real centersx and ALL admissible far data, every actual zero in the OPEN half-unit frequency disk is real and simple. The explicit data-uniformity is retained; no uniform-in-time model-root existence cutoff is inferred.

eventually_fixed_time_far_disks then reuses eventually_controlled_far_saddles to eliminate all model-root/branch data for EACH fixedt>=1. far_strip_real_simple is the final nonvacuous theorem:
  for every fixed realt>=1 there exists realX such that, for every complexz,
  Re(z)>=X and |Im(z)|<1/2 and flow(t,z)=0 imply Im(z)=0 and deriv(flow t)(z)!=0.
It takes the real frequency centerx=Rez and uses the exact norm(z-Rez)=|Imz| identity. The result concerns the ACTUAL arithmetic quartic flow. Its half-strip width is explicit and OPEN, and its right-hand cutoff may depend on t.

This closes the specific local exact-reality/simplicity target left open in1138, complementing1136actual far real-zero existence. It does NOT prove absence of nonreal zeros with|Imz|>=1/2, a classical critical-strip confinement theorem for the quartic deformation, a uniform late-time/global cutoff, intermediate-frequency matching or eventual Laguerre-Polya membership. Neither finite nor infiniteA4 is decided. No RH/A2 or novelty claim is made. The next A4 priority is a precise global-coverage audit and productive estimates or obstructions beyond this proved half-strip; avoid replacing the global objective with more easy real-zero corollaries. All later campaigns remain gated.

Both new modules (6public theorems total) are root-imported. Full build, fresh complete root transitive axiom audit, actual unabridged public-type review, source integrity, ledger, exact Git checkpoint and verified PRIVATE backup remain required before acceptance. Verification results follow only after terminal success.

Verification1139: pinned FULL root build PASSED5868jobs, session42089 TERMINAL0. Fresh FULL root transitive axiom audit PASSED34930Foundation declarations, session40420 TERMINAL0, only propext,Classical.choice,Quot.sound. ALL6 public theorem types ACTUALLY READ unabridged from the complete fresh log (2LocalCosineZeros+4FarSimpleZeros). Review checked local closed-disk regularity/Cauchy containment, arbitrary real cosine center, actual affine-map containment in the original OPEN disk, exact phase linearization/constants, radius2 trigonometric bounds, fixed-epsilon conjugate-root injectivity, nonzero actual envelope/affine derivative in the chain/quotient simplicity transfer, discharged phase/error/model-root existence, and the final fixed-time positive-real half-strip quantifiers. The derivative is that of the ACTUAL quartic flow. No global analytic extension, epsilon-limit reality inference, outside-strip exclusion or uniform eventual-time conclusion is assumed. Manifest1793 covers every Foundation/root source; prior1791 hashes unchanged except reviewed root imports, including the unchanged older globally differentiable cosine criterion. All107archive,43Incoming/42distinct and11fullyreadA4 hashes unchanged. No sorry/admit/new axiom/native admission, manuscript/dependency or unrelated draft change. All proof jobs terminal0. Evidence: .lake/stardust-1139-full-build.log, stardust-1139-audit.log, stardust-1139-working-checkpoint.json, stardust-1139-source-integrity.json, stardust-1139-public-types.json and stardust-1139-verification.json. Exact FIVE-path audited Git checkpoint, receipt and verified PRIVATE backup follow. A4 remainsACTIVE; outside-half-strip/global coverage and eventual global reentry remainOPEN. No queued stage opened.


## Stardust 1140 — complex-frequency quartic model saddles throughout the far lower half-plane (October 19, 2026)

A4 remains ACTIVE. Previous goal turn classification: verified progress, closing1139recovery evidence, checking all1793source hashes and the exact PRIVATE backup; its local actual-flow reality/simplicity proof is closed. This checkpoint follows the required global-coverage audit rather than extending a bounded-width real strip. Existing anchored_far_saddle only constructs roots at real frequencies. New Foundation/RiemannQuarticComplexModelSaddle.lean reuses its quantitative scalar inverse machinery for arbitrary complex frequencies, then constructs the principal-log anchor and discharges the anchor existence/geometry hypotheses uniformly over the entire closed lower frequency half-plane.

anchored_complex_saddle: for t>=0, M>=1, norm(z)>=10000*(t+1)*M^3 and an anchor b with norm(b)<=M-1 and4*pi*exp(4*b)=i*z, there exists a UNIQUE leading-model root in closedBall(b,1/1024), D_t(w)=-i*z. Uniqueness is LOCAL to that ball. The inverse linearization is -4*i*z with norm4*norm(z); the polynomial residual and derivative error are bounded using norm(z), with no real-frequency cast or sign shortcut. The older real-frequency theorem and all prior modules are unchanged.

The exact real stationary equation is
4*pi*Re(exp(4*w))=4*t*(Re(w)^3-3*Re(w)*Im(w)^2)+9-Im(z).
For Re(w)>=1 and abs(Im(w))<=1/2, real_margin proves the stronger lower bound t*Re(w)^3+9-Im(z). No sign on Im(z) is required for that identity/bound. If Im(z)<=0, the theta margin improves, rather than weakens, as the frequency moves deeper into the lower half-plane. The positive real exponential parameter implies abs(Im(w))<pi/8, using the stated abs(Im(w))<=1/2 preliminary geometry. The actual arithmetic theta kernel is nonzero whenever t*Re(w)^3-Im(z)>=7. For each k<=4, the relative arithmetic theta tail is bounded by32*exp(-(3/4)*(t*Re(w)^3+9-Im(z))) times its leading term. These are estimates for the literal arithmetic kernel, not a replacement kernel.

complexAnchor(z)=log(i*z/(4*pi))/4 uses the principal complex logarithm. Its exact exponential identity is proved for z!=0. On the lower half-plane, i*z/(4*pi) has nonnegative real part, so abs(arg)<=pi/2 and abs(Im(anchor))<=pi/8; no global holomorphic logarithm is assumed. On norm(z)=4*pi*exp(4*a), a>=0, Re(anchor)=a and norm(anchor)<=a+1. The same radial scale dominates the polynomial inverse budget uniformly in angle. eventually_lower_half_circles constructs roots on EVERY sufficiently large lower half-circle, not merely selected rays or sampled frequencies. far_lower_half_plane converts this to: for EACH fixed t>=1, there exists R(t)>0 such that EVERY z with norm(z)>=R(t) and Im(z)<=0 has a constructed model root w with Re(w)>=2, abs(Im(w))<pi/8, the strengthened real margin, a nonzero actual arithmetic kernel, and all four-order relative theta-tail estimates. No seed-root or anchor assumption remains in this final theorem.

Selective source comparison: ResearchSources/a4/ibm_laguerre_polya.tex lines760-777 discuss the approaching theta-strip edge and uncontrolled far-field remainder; lines786-797 explicitly leave outward nonreal migration versus eventual extinction open. Its hash remains EAF31754F5F993EF8EB33A1917484D70F6B62F5B37A907AD85F097C3C5589D96. This verified complex-frequency construction gives quantitative theta control at far lower-half-plane MODEL saddles despite approach to the strip edge. It does not by itself justify or refute the manuscript's proposed reduction of full far-field zero exclusion to Xi-tail/RH information. In particular, pointwise arithmetic control at a model saddle is not a signed Fourier remainder bound. Both competing A4 alternatives remain OPEN. No novelty claim is made.

Next direct obligation: correct these complex-frequency roots to ACTUAL logarithmic-slope saddles, retaining the growing theta margin and inverse scale norm(z), then prove the signed contour and dominance estimates for the full transform. Existing FarCorrection is restricted to real center frequency, though it allows a unit disk about that real center; it cannot already be applied at arbitrary complex center. Reuse its actual/model derivative-error and scalar inverse arguments with the new real margin before attempting off-axis dominance. Do not discard vertical endpoint cancellation or identify a model root with an actual root. Global/intermediate matching and a joint eventual-time cutoff remain separate. Neither A4<infinity nor A4=infinity, eventual global LP reentry, or any RH/A2 implication is established. No queued campaign opened.

Verification1140: pinned FULL root build PASSED5869jobs, session31652 TERMINAL0. Fresh COMPLETE root transitive axiom audit PASSED34953Foundation declarations, session30454 TERMINAL0; only propext,Classical.choice,Quot.sound. ALL12 public definition/theorem types ACTUALLY READ UNABRIDGED from the fresh complete log; the principal-log definition body reviewed. Review checked complex norm scaling and local uniqueness, exact stationary sign, principal-branch domain and uniform angular geometry, actual kernel versus model stationarity, improved theta exponent, eventual-radius conversion to ALL sufficiently large frequencies, and fixed-time quantifiers. Manifest1794covers every Foundation/root source; prior1793hashes unchanged except reviewed root import. All107archive,43Incoming/42distinct,11fullyreadA4 hashes unchanged. No sorry/admit/new axiom/native admission, manuscript/dependency or unrelated draft change. Standalone final probe41939 TERMINAL0; full build/audit supersede earlier failed exploratory probes. Evidence: .lake/stardust-1140-full-build.log, stardust-1140-audit.log, stardust-1140-working-checkpoint.json, stardust-1140-source-integrity.json, stardust-1140-public-types.json and stardust-1140-verification.json. Exact FOUR-path audited Git checkpoint, receipt and verified PRIVATE backup follow. A4 ACTIVE; later stages remain gated; October31hard stop unchanged.


## Stardust 1141 — actual arithmetic saddles at all far lower-half-plane frequencies and exact signed contours (October 19, 2026)

A4 remains ACTIVE. Previous goal turn classification: verified progress, audited/private-backed1140complex model construction, commit cebcc326d0f727245207afeb37cd645584c247cf. This checkpoint closes its stated MODEL-to-ACTUAL correction obligation. Foundation/RiemannQuarticComplexCorrection.lean adds12theorems reusing the earlier FarCorrection's scalar inverse, theta logarithmic error and Cauchy arguments with genuinely complex center z. All earlier verified sources are unchanged except the reviewed root import.

The model exponential norm estimate uses norm(z). The neighbor_domain theorem keeps the improved actual theta-parameter bound
(t*Re(w)^3-Im(z))/32 <= Re(exp(4*v))
on norm(v-w)<=2/norm(z), under Im(z)<=0, t>=1, norm(z)>=8, Re(w)>=32, abs(Im(w))<=1/2, model stationarity D_t(w)=-i*z and the stated polynomial budget. It also proves Re(v)>=0 and Re(exp(4*v))>=1. Thus actual arithmetic kernel analyticity and nonvanishing are justified BEFORE differentiating the logarithmic slope. The actual/model slope error is <=30005*exp(-Re(w)); the Cauchy derivative error on the half-radius disk is <=30005*exp(-Re(w))*norm(z). No logarithmic-kernel division at an unproved nonzero point is used.

For norm(z)>=10000, Re(w)>=120020 and norm(z)>=100*(t*(norm(w)+1)^3+1), actual_far_frequency_disk constructs a UNIQUE actual root in closedBall(w,1/norm(z)) for EVERY q with norm(q-z)<=1:
complexSlope(t,v)=-i*q.
The lower-half-plane restriction is on the CENTER z; the target q need not stay there. Uniqueness is LOCAL to this ball. The model derivative is compared with -4*i*z of norm4*norm(z), and the actual derivative error is controlled by the existing exp(-Re(w)) budget. corrected_saddle_geometry proves Re(v)>=1, abs(Im(v))<pi/8 and a nonzero ACTUAL arithmetic kernel. actual_far_deriv_norm_lower proves norm(deriv(complexSlope t)(v))>=2*norm(z) throughout the correction ball, for the actual logarithmic slope, not merely the model derivative.

The final theorem far_lower_half_plane_actual has NO seed-root, anchor or polynomial-budget hypotheses: for EACH fixed real t>=1 there exists R(t)>0 such that EVERY complex z with norm(z)>=R(t) and Im(z)<=0 has an actual root v with all the geometry above, Re(exp(4*v))>=1 and the actual derivative lower bound. The proof first works uniformly over all angles on every sufficiently large half-circle, preserving1140principal-anchor closeness to prove the large-Re(w) and polynomial budgets, then converts the radial parameter to ALL sufficiently large norms by a=log(norm(z)/(4*pi))/4. It does not merely select a sequence of frequencies. The original real-frequency actual-saddle theorem could not be invoked at arbitrary complex center; that reuse gap is now closed.

The same final theorem proves that the GENUINE arithmetic saddleWeight(t,z) has HasDerivAt(...,0,v) and a nonzero value at v, by direct reuse of actual_weight_critical. It also includes the exact identity for the FULL quartic transform:
flow(t,z) = (integral over s>0 of saddleWeight(t,z,s+i*Im(v)) + integral over s>0 of saddleWeight(t,-z,s-i*Im(v)))/2.
This is the existing signed paired-contour theorem at the CONSTRUCTED ACTUAL saddle height; its vertical endpoints cancel exactly. The second, opposite-height contour is not silently declared stationary at its own saddle for nonreal z. The two complex integrals have not been bounded away from cancellation, and pointwise nonzero weight is not treated as full-flow nonvanishing.

Next A4 priority: Gaussian-relative actual signed integral estimates and complementary-tail/competing-channel dominance at these complex centers, then global/intermediate matching and eventual-time uniformity. Existing FarGaussianLocal/Limit/Fixed and FarAnnulus still assume a real center x in model stationarity; their pure exponential, scalar integration-by-parts and generic Gaussian estimates can be reused, but the real-center hypotheses must be discharged or rigorously generalized. Reuse GaussianOscillatoryTail.tail_norm_bound and full_minus_truncated_bound: these are already valid for ANY b with Re(b)>0, with norm(b)-based bounds; no new generic oscillatory-Gaussian foundation or assumed angular sector is needed. The actual/model mismatch at the corrected saddle must remain explicit. Off-axis dominant versus reflected channel geometry and exact endpoint cancellation remain essential. Model/actual saddle existence by itself proves neither absence of nonreal zeros nor eventual global Laguerre-Polya membership. Both A4<infinity and A4=infinity remain OPEN. No RH/A2 or novelty claim is made; no queued stage opened.

Verification1141: pinned FULL root build PASSED5870jobs, session26835 TERMINAL0. Fresh COMPLETE root transitive axiom audit PASSED34971Foundation declarations, session31859 TERMINAL0, only propext,Classical.choice,Quot.sound. ALL12 public theorem types ACTUALLY READ UNABRIDGED from the complete fresh log. Review checked center/target distinction, complex norm inverse scale, retained -Im(z) theta margin, actual kernel domain before division/differentiation, Cauchy disk containment, actual local uniqueness/derivative estimate, all-angle large-radius construction and discharged root/budget hypotheses, genuine stationary arithmetic weight, signed full-flow identity and its exact scope. Manifest1795covers all Foundation/root sources; prior1794hashes unchanged except reviewed root import. All107archive,43Incoming/42distinct,11fullyreadA4 manuscript hashes unchanged. No sorry/admit/new axiom/native admission, manuscript/dependency or unrelated draft change. Final standalone probe51738 TERMINAL0; full build/audit supersede earlier failed variable-shadowing probes. Evidence: .lake/stardust-1141-full-build.log, stardust-1141-audit.log, stardust-1141-working-checkpoint.json, stardust-1141-source-integrity.json, stardust-1141-public-types.json and stardust-1141-verification.json. Exact FOUR-path audited Git checkpoint, receipt and verified PRIVATE backup follow. A4 ACTIVE; global reentry OPEN; all later campaigns and October31hard stop preserved.


## Stardust 1142 — signed complex-saddle central Gaussian reconstruction and nonvanishing (October 19, 2026)

A4 remains ACTIVE. Previous goal turn classification: verified progress, actual complex-frequency saddle construction, exact signed contours and audited/private-backed checkpoint df8074a639b63eca402bb22ffe8bb2cf2a4172b0. The present checkpoint advances from saddle existence to a genuine signed integral approximation. It does not replace the global A4 objective with a parameter estimate or an expectation-level formula.

Foundation/RiemannQuarticComplexGaussian.lean adds30public theorems extending the arithmetic phase and local Gaussian chain to complex lower-half-plane centers. Existing generic exponential remainder, Gaussian integration, oscillatory tail, interval integration and power-limit results are reused. The only change to an older mathematical module is making the ALREADY PROVED generic FarSignedIntegral.normalized_real_ode public; its proof body and statement are unchanged, and the older actual_horizontal_phase statement is unchanged. The exact one-word visibility diff was independently checked against HEAD. This permits direct reuse of the real-horizontal ODE proof, without assuming a holomorphic logarithm on a disk crossing the theta boundary or duplicating the ODE proof.

Write N=norm(c), Im(c)<=0, D_t=modelDerivative, G_t=complexSlope (the actual arithmetic logarithmic slope), W=saddleWeight. Conditional estimates state all domains explicitly: t>=1, N>=8 or10000 as appropriate, Re(w)>=32 or64, abs(Im(w))<=1/2, D_t(w)=-i*c, the appropriate polynomial budget, norm(v-w)<=1/N, and G_t(v)=-i*z for the actual target z. The target z is not silently identified with the model center c; equality is discharged in the constructed-family application. Horizontal theta-domain control extends across abs(s)<=1/16 along v+s, rather than assuming a complex disk of that radius stays inside the theta strip. The retained actual/model logarithmic error is sharpened to E=30005*exp(-4*Re(w)+4). arithmetic_error_frequency_bound proves E<=100000000/N under the strong polynomial budget, using the complex norm of model stationarity, without a real-frequency cast.

actual_horizontal_phase reconstructs the GENUINE arithmetic weight as W(t,z,v+s)=W(t,z,v)*exp(integral_0^s(G_t(v+a)+i*z) da). actual_phase_model_error bounds its difference from the existing leading model phase by E*abs(s). The model phase retains the linear mismatch (D_t(v)+i*z)*s at an ACTUAL saddle; actual stationarity is never substituted into D_t. This mismatch and the actual/model phase error are both bounded before estimating exponentials and signed integrals. The horizontal model curvature bound proves positive real part of b=-D_t'(v)/2. The full complex Gaussian integral is nonzero, satisfies its existing principal-power formula, and obeys the proved lower normalization1<=2*sqrt(N)*norm(Gfull). This branch condition is established for the actual coefficient before invoking the Gaussian formula.

For 0<r<1/16 and E*r+2048*N*r^3<=1, actual_local_full_gaussian_error proves the absolute signed estimate
norm(integral_{-r}^r W(t,z,v+s) ds - W(t,z,v)*Gfull) <= norm(W(t,z,v))*(16*E*r^2+8192*N*r^4+2/(norm(b)*r)).
Here Gfull is the integral over ALL real s of exp(D_t'(v)*s^2/2). The final term uses the ALREADY VERIFIED GaussianOscillatoryTail.full_minus_truncated_bound for arbitrary Re(b)>0. It does not replace the complex Gaussian by an unsigned real Gaussian. The denominator W(t,z,v)*Gfull is proved nonzero from the actual arithmetic kernel domain and Gaussian normalization before division.

The established radius rho(N)=centralRadius(N)=N^(-7/16) is reused. central_relative_error_bound proves the relative signed norm error is at most the existing budget
B(N)=3200000000*N^(-11/8)+16384*N^(-1/4)+4*N^(-1/16),
which already has a verified limit0. The accompanying smallness budget and rho(N)->0 are also reused. uniform_local_gaussian_error supplies a SINGLE cutoff for a given eta>0, uniform over every complex lower-half-plane center and all t,w,v,z satisfying its stated admissibility budgets. This is a relative-norm topology for the ACTUAL complex integral; no convergence of unsigned measures or of a full Fourier transform is inferred.

The constructed-family application uses1141eventually_actual_half_circles, retains its principal-anchor closeness, and proves the needed large real part and strong polynomial budget uniformly over all angles. far_actual_local_gaussian has NO assumed model root, actual root, anchor or polynomial-budget hypothesis: for EACH fixed t>=1 and0<eta<1 there exists R(t,eta)>0 such that EVERY lower-half-plane c with norm(c)>=R has an ACTUAL saddle v with Re(v)>=1, abs(Im(v))<pi/8, nonzero arithmetic kernel, and relative signed central error<=eta. The integral over[-rho(N),rho(N)] of the actual arithmetic weight along v+s is itself NONZERO. This follows rigorously from error<1; it is not inferred merely from pointwise nonzero weight. The radius, denominator and dependence of cutoffs on eta and t remain explicit.

Selective manuscript comparison at this proof break: ResearchSources/a4/ibm_laguerre_polya.tex lines760-777 again discusses the moving saddle, theta-strip edge and uncontrolled far remainder; hash EAF31754F5F993EF8EB33A1917484D70F6B62F5B37A907AD85F097C3C5589D96 was independently rechecked unchanged. The new theorem controls the actual SIGNED CENTRAL saddle integral, including the arithmetic error, at all sufficiently large lower-half-plane frequencies for fixed t. It does not control the complementary half-line pieces or the reflected channel, and therefore neither proves nor refutes the manuscript's proposed reduction of FULL far-field exclusion to Xi-tail/RH information. Numerical statements in that paragraph remain manuscript evidence only. No novelty claim is made.

Next direct target: signed annular estimates, then a fixed-neighborhood/full-half-line Gaussian asymptotic and competing-channel dominance at complex centers. Directly reuse FarAnnulus.finite_nonstationary_bound, which is already generic for complex E,H,K and a positive REAL scale; do not duplicate its integration-by-parts proof. Its annulusBudget and annulusBudget_tendsto_zero are also generic/reusable; the private algebraic budget identity may need a local proof, but no new power-limit foundation. ComplexGaussian now provides the required norm-based coefficient, sharp arithmetic error, signed phase and normalization estimates. Existing real-center FarAnnulus and FarGaussianFixed hypotheses still cannot be silently applied at arbitrary complex center. Preserve actual/model mismatch and exact endpoint cancellation. The opposite-height second contour is not automatically stationary, and no sign of Im(v) has been proved here. The new local nonvanishing DOES NOT prove full half-line or full-transform nonvanishing. Global off-axis dominance, intermediate-frequency matching and a joint eventual-time cutoff remain OPEN. Both A4<infinity and A4=infinity and eventual global LP reentry remain OPEN. No RH/A2 or threshold implication is asserted; no queued campaign opened.

Verification1142: pinned FULL root build PASSED5871jobs, session31959 TERMINAL0, including all downstream rebuilds after the one-word ODE visibility change. Fresh COMPLETE root transitive axiom audit PASSED35017Foundation declarations, session25282 TERMINAL0, only propext,Classical.choice,Quot.sound. ALL32 new/affected public theorem types ACTUALLY READ UNABRIDGED:30new module theorems,1existing proved generic helper made public,1unchanged older actual_horizontal_phase type rechecked. The initial tool-output truncation was resolved by explicitly rereading both missing complete theorem types before attesting review. Review checked complex center/target domains, actual horizontal phase reconstruction, retained linear mismatch, positive-real-part Gaussian branch, nonzero relative denominator, actual signed integral bounds and power-limit topology, all-angle constructed-saddle application, discharged seed-root budgets, precise fixed-time/eta cutoff quantifiers and local-versus-full nonvanishing. Manifest1796covers every Foundation/root source; prior1795hashes unchanged except reviewed root import and the EXACT private-to-public normalized_real_ode visibility change, whose statement and proof body are unchanged. All107archive,43Incoming/42distinct,11fullyreadA4 manuscript hashes unchanged; the relevant LP manuscript hash was independently rechecked at the proof break. No sorry/admit/new axiom/native admission, manuscript/dependency or unrelated draft change. Final standalone probe27650 TERMINAL0; supporting reuse build75457 TERMINAL0,4374jobs; full build/audit supersede exploratory37992private-helper/shadowing failures and78599intermediate success. Evidence: .lake/stardust-1142-full-build.log, stardust-1142-audit.log, stardust-1142-working-checkpoint.json, stardust-1142-source-integrity.json, stardust-1142-public-types.json and stardust-1142-verification.json. Exact FIVE-path audited Git checkpoint, receipt and verified PRIVATE backup follow. A4 ACTIVE; eventual global reentry OPEN; all later campaign gates and October31hard stop preserved.


## Stardust 1143 — both signed complex-saddle annuli and fixed-neighborhood Gaussian reconstruction (October 19, 2026)

A4 remains ACTIVE. Previous goal turn classification: verified progress,1142signed central Gaussian reconstruction/nonvanishing, audited/private-backed fe72966ac649b275692cdb54640d121e5cba914c. Foundation/RiemannQuarticComplexAnnulus.lean adds11public theorems extending the signed annular and fixed-neighborhood integral estimates to complex lower-half-plane centers. All earlier mathematical sources are unchanged; only the new module and root import are added. The proven generic finite_nonstationary_bound, complex Gaussian normalization, sharp arithmetic phase error, annulusBudget and its limiting theorem are reused directly.

Write N=norm(c), Im(c)<=0. Under the explicit far model/actual data, model_slope_quadratic_remainder bounds the quadratic slope Taylor remainder by2048*N*norm(u)^2. annulus_slope_lower gives norm(D_t(v+s)+i*z)>=N*abs(s) for abs(s)<=1/8192 when the retained actual/model mismatch E=30005*exp(-4*Re(w)+4) satisfies E<=N*abs(s)/2. It uses the norm of the full complex derivative, not an unproved imaginary-component sign or an angular restriction. annulus_slope_derivative_upper bounds the model derivative by512*N over the same interval.

For0<r<=R<=1/8192 and abs(sigma)=1, signed_model_annulus_bound applies the EXISTING generic complex integration-by-parts theorem to E(s)=exp(leadingPhase(t,z,v,sigma*s)), its actual complex multiplier H and derivative K. It proves norm(integral_r^R E)<=1542/(N*r). The inverse multiplier is nonzero on the actual interval by the slope lower bound. The proof retains model linear mismatch at the ACTUAL saddle, and bounds the real part of the model phase before estimating its exponential. No absolute integral estimate is substituted for signed cancellation.

signed_actual_annulus_bound transfers this estimate to the literal arithmetic weight:
norm(integral_r^R W(t,z,v+sigma*s) ds) <= norm(W(t,z,v))*(1542/(N*r)+180030*exp(-4*Re(w)+4)*R^2),
under the stated mismatch/smallness conditions. relative_actual_annulus_bound divides by the SAME nonzero normalization W(t,z,v)*Gfull as1142, using the proved actual kernel domain and complex Gaussian lower bound. Both sigma=-1 and sigma=1 are covered; the sign is not dropped from the integration path.

At rho(N)=N^(-7/16), uniform_relative_annulus proves these relative signed annular norms tend uniformly to0 over all lower-half-plane centers and all t,w,v,z satisfying the explicit admissibility data. The existing scalar budget3084*N^(-1/16)+1200000000*R^2*N^(-1/2) and its proved zero limit are reused. Only its private elementary algebraic identity is reproduced locally; the integration-by-parts and power-limit proofs are not duplicated.

actual_neighborhood_split proves an EXACT identity for the arithmetic integral over[-R,R] as the sum of the central integral over[-rho,rho] and BOTH signed annuli. Its continuity and integrability are justified using the actual horizontal theta-domain estimates, without assuming a complex disk as wide as the interval lies inside the theta strip. Negative-side orientation follows the real interval substitution, not an unsigned replacement.

uniform_fixed_gaussian_error combines the1142central relative estimate and both annular estimates at a common maximum cutoff. For each0<R<=1/8192 and eta>0 it supplies a cutoff N0(R,eta), uniform over every complex lower-half-plane center and every admissible t,w,v,z, such that
norm((integral_{-R}^R W(t,z,v+s) ds)/(W(t,z,v)*Gfull)-1)<=eta.
The integration neighborhood is now FIXED as N grows. The normalization remains the full complex Gaussian with MODEL curvature at the ACTUAL saddle; no actual/model curvature identity is assumed. This is convergence in relative complex norm of the ACTUAL signed integral.

The constructed-family theorem far_actual_fixed_gaussian has NO seed-root, anchor or polynomial-budget hypothesis: for EACH fixed t>=1,0<R<=1/8192 and0<eta<1 there exists X(t,R,eta)>0 such that EVERY lower-half-plane frequency c with norm(c)>=X has an ACTUAL saddle v, Re(v)>=1, abs(Im(v))<pi/8 and nonzero arithmetic kernel, satisfying the fixed-neighborhood relative estimate. The ACTUAL SIGNED integral over[-R,R] at v is nonzero, proved from error<1. The all-angle half-circle construction is converted to all sufficiently large frequency norms with its hypotheses proved explicitly. The same root construction is reused, rather than postulated anew.

This closes the complex-center signed-annulus and fixed-neighborhood gap. It does NOT prove nonvanishing of the whole positive half-line contour, the full quartic transform, or the reflected Fourier channel. Off-axis channel cancellation, global/intermediate matching and a joint eventual-time cutoff remain open. Both A4<infinity and A4=infinity and eventual global Laguerre-Polya reentry remain OPEN. No RH/A2 or novelty claim is made, and no queued campaign starts.

The next precise reuse obstruction is visible in FarLeftCompact.actual_left_compact_bound and actual_center_theta_upper: their hypotheses include abs(Im(z))<=1, which is NOT available over the whole lower half-plane, and the latter upper bound lacks the frequency-dependent term. It cannot be silently invoked for these complex frequencies. Investigate a corrected upper estimate retaining -Im(z)/4 from actual real stationarity, then combine it with the compact phase gap before asserting a tail bound. FarRightTail.actual_weight_model_envelope is already generic in the complex target and can be reused directly; its real-center curvature/normalization theorems need the proved complex-center replacements. Preserve the actual stationary linear term and exact vertical endpoint cancellation throughout. The next target remains actual complementary-contour bounds leading to a whole-half-line Gaussian asymptotic and competing-channel dominance, not more local zero corollaries.

Verification1143: pinned FULL root build PASSED5872jobs, session13746 TERMINAL0. Fresh COMPLETE root transitive axiom audit PASSED35029Foundation declarations, session40839 TERMINAL0; only propext,Classical.choice,Quot.sound. ALL11 public theorem types ACTUALLY READ UNABRIDGED from the complete fresh log. Review checked complex norm Taylor/inverse-slope scales, both signs, direct generic signed integration-by-parts reuse, retained actual/model mismatch, nonzero normalization before division, exact actual interval splitting and orientation, uniform common cutoffs and scalar budget limits, constructed all-angle actual saddles with discharged seed budgets, fixed R and eta/time quantifiers, and local-versus-full nonvanishing. Manifest1797covers all Foundation/root sources; prior1796hashes unchanged except reviewed root import. All107archive,43Incoming/42distinct,11fullyreadA4 manuscript hashes unchanged. No sorry/admit/new axiom/native admission, manuscript/dependency or unrelated draft change. Standalone probes29495 and7956 TERMINAL0; final7956includes uniform/family theorems. No live jobs. Evidence: .lake/stardust-1143-full-build.log, stardust-1143-audit.log, stardust-1143-working-checkpoint.json, stardust-1143-source-integrity.json, stardust-1143-public-types.json and stardust-1143-verification.json. Exact FOUR-path audited Git checkpoint, receipt and verified PRIVATE backup follow. A4 ACTIVE; global reentry OPEN; later gates and October31hard stop unchanged.


## Stardust 1144 — corrected complex theta upper, actual counterexample, and compact left-contour decay (October 19, 2026)

A4 remains ACTIVE. Previous goal turn classification: verified progress,1143both signed annuli and fixed-neighborhood Gaussian reconstruction, audited/private-backed0cf5d03b34b8948620b8df4a5ca46489f5e3ca7d. Foundation/RiemannQuarticComplexCompactTail.lean adds9public theorems resolving the compact-tail scope obstruction recorded there. All previous mathematical sources are unchanged except the root import. Generic compact signed-integral bounds, arithmetic kernel norm estimates, Gaussian normalization and the existing compactBudget limit are reused.

actual_center_theta_upper proves the corrected estimate
pi*Re(exp(4*v)) <= t*Re(v)^3+3-Im(z)/4
from t>=0, Re(v)>=0, ACTUAL logarithmic stationarity G_t(v)=-i*z and norm(G_t(v)-D_t(v))<=1. This lemma allows ANY complex target z; it does not assume Im(z)<=0 or abs(Im(z))<=1. The real stationary identity and the actual/model residual give the frequency term with its precise sign. The older valid FarLeftCompact.actual_center_theta_upper retains its original abs(Im(z))<=1 hypothesis unchanged.

missing_frequency_term_counterexample verifies that the restriction cannot simply be dropped while keeping the old conclusion. It constructs a complex z with Im(z)<=0 at t=1,v=1, for which the ACTUAL arithmetic slope satisfies G_1(1)=-i*z, the actual/model slope error is<=1, and the literal arithmetic kernel at1 is nonzero, but
1*1^3+3 < pi*Re(exp(4*1)).
The witness is z=i*phaseSlope(1,1), using the actual real logarithmic slope. Realness comes from complexSlope_real; the neighborhood theorem proves the error bound, and exact inequalities exp(4)>=5,pi>3 prove the violation. No quadrature, numerical approximation, model-only stationary point or assumed Millennium claim enters the counterexample. This refutes the naive UNRESTRICTED extension of a theta upper estimate, not the original theorem, A4 finiteness, or eventual global reentry.

actual_left_compact_bound uses the corrected theta upper and Im(z)<=0 to prove
norm(integral_0^{a-1} W(t,z,s+i*h) ds) <=528*(a-1)*norm(W(t,z,a+i*h))*exp(5*a+3-2*t*a^3+3*Im(z)/4),
for the stated a>=64, abs(h)<=1 and actual positive theta-parameter hypotheses. The generic compact_signed_bound already handles arbitrary complex z and the cosine margin, so it is reused. The new phase comparison uses abs(Im(z))=-Im(z) EXACTLY in the lower half-plane. The earlier crude abs(Im(z))<=1 bound is not substituted. This retains the extra factor exp(3*Im(z)/4), giving stronger decay deeper in the lower half-plane. The endpoint and actual arithmetic kernel domain remain justified up to the natural strip boundary by the positive theta parameter.

relative_actual_left_compact_bound applies this estimate at a corrected ACTUAL saddle v, with complex model center c and N=norm(c). All center/target domains are explicit: Im(c)<=0, t>=1, N>=10000, Re(w)>=120020, abs(Im(w))<=1/2, D_t(w)=-i*c, the strong polynomial budget, norm(v-w)<=1/N, ACTUAL G_t(v)=-i*z and Im(z)<=0. The corrected theta upper is discharged from the actual stationarity and the proved sharp arithmetic error; no abs(Im(z))<=1 hypothesis remains. The denominator is the SAME nonzero actual weight times the full complex Gaussian used by the fixed-neighborhood theorem. The relative compact integral is bounded by
1056*sqrt(N)*(Re(v)-1)*exp(5*Re(v)+3-2*t*Re(v)^3+3*Im(z)/4).
The Gaussian curvature remains the model derivative at the actual saddle, with its positive-real-part branch and actual/model mismatch handled by earlier verified results.

frequency_exp_bound proves N<=100000000*exp(4*Re(w)) from complex norm stationarity. relative_left_compact_budget drops exp(3*Im(z)/4)<=1 only after proving the multiplying factor nonnegative, then reuses the existing compactBudget(Re(v))=10560000*exp(8*Re(v)+5-2*Re(v)^3) and its proved limit0. uniform_relative_left_compact supplies a single cutoff for eta>0, uniform over every lower-half-plane center and all admissible data. This is an actual signed contour integral norm relative to the nonzero complex Gaussian, not merely a pointwise weight or expectation estimate.

far_actual_left_compact has NO seed-root, actual-root, anchor, polynomial-budget or bounded-imaginary-frequency hypothesis: for EACH fixed t>=1 and eta>0 there exists X(t,eta)>0 such that EVERY lower-half-plane frequency c with norm(c)>=X has a constructed ACTUAL saddle v, Re(v)>=1, abs(Im(v))<pi/8 and nonzero arithmetic kernel, at which the Gaussian-relative compact integral from0toRe(v)-1 has norm<=eta. The proof reuses the all-angle actual half-circle family and principal-anchor closeness to discharge the data, then converts to every sufficiently large norm. It does not infer that the compact integral is nonzero; this is a negligible complementary contribution.

This closes the precise1143compact-domain obstruction and adds an actual counterexample to the invalid shortcut. The intervening left interval[-1,-R] in saddle coordinates and the right tail[R,infinity) still need complex-center bounds before a WHOLE horizontal half-line asymptotic can be asserted. Generic FarRightTail.actual_weight_model_envelope is already valid for arbitrary complex targets and should be reused directly. Existing FarLeftAnnulus curvature and phase arguments require complex-center adaptation but retain the ACTUAL stationary linear mismatch. To combine all pieces, apply their CONDITIONAL uniform estimates to one common constructed w,v family; do not silently identify existential saddles from separate final theorems. The reflected channel still requires its own estimate and exact vertical endpoint cancellation. Full-transform zero exclusion, intermediate-frequency matching and joint eventual-time control remain OPEN. Both A4<infinity and A4=infinity and eventual global LP reentry remain OPEN. No RH/A2, threshold or novelty claim is made; no queued stage starts.

Verification1144: pinned FULL root build PASSED5873jobs, session96866 TERMINAL0. Fresh COMPLETE root transitive axiom audit PASSED35039Foundation declarations, session50927 TERMINAL0; only propext,Classical.choice,Quot.sound. ALL9 public theorem types ACTUALLY READ UNABRIDGED from the complete fresh log. Review checked the exact -Im(z)/4 sign and unrestricted target domain of the corrected upper, actual rather than model counterexample and kernel nonvanishing, preserved validity of older restricted theorems, retained lower-half-plane phase gain, signed compact interval/domain, actual/model stationary distinction, nonzero Gaussian denominator, coefficient nonnegativity before dropping the gain, common admissibility hypotheses, all-angle construction and fixed-time/eta cutoff quantifiers, and compact-versus-whole-contour scope. Manifest1798covers all Foundation/root sources; prior1797hashes unchanged except reviewed root import. All107archive,43Incoming/42distinct,11fullyreadA4 manuscript hashes unchanged. No sorry/admit/new axiom/native admission, manuscript/dependency or unrelated draft change. Final standalone82661 TERMINAL0 supersedes13151namespace/coercion and83647coefficient-nonnegativity failures;74397verified the corrected upper/counterexample/core compact bound. Evidence: .lake/stardust-1144-full-build.log, stardust-1144-audit.log, stardust-1144-working-checkpoint.json, stardust-1144-source-integrity.json, stardust-1144-public-types.json and stardust-1144-verification.json. Exact FOUR-path audited Git checkpoint, receipt and verified PRIVATE backup follow. A4 ACTIVE; all later gates and October31hard stop unchanged.


## Stardust 1145 — whole actual complex horizontal Gaussian asymptotics and reflected-weight identity (October 19, 2026)

A4 remains ACTIVE. Previous goal turn classification: verified progress,1144corrected actual theta upper, explicit actual counterexample and compact lower-half-plane contour decay, audited/private-backed7b9e0e6e028566f4882ae55e1a8ebe3337c9ef13. Foundation/RiemannQuarticComplexContour.lean adds17public theorems closing the remaining left-intervening and right-tail gaps and assembling the ENTIRE actual horizontal half-line integral. All previous mathematical sources are unchanged except the root import. The new result is a genuine signed integral asymptotic for the literal arithmetic kernel, not an expectation formula or a pointwise model estimate.

For lower complex model center c0, N=norm(c0), all conditional theorems retain the actual target z separately and state the model root, actual stationarity, correction distance and polynomial budgets explicitly. right_model_curvature proves Re(D_t'(v+s))<=-t*Re(w)^3/4 for ALL s>=0. right_phase_quadratic_bound retains the ACTUAL-saddle mismatch E=30005*exp(-4*Re(w)+4), giving Re(leadingPhase(t,z,v,s))<=E*s-(t*Re(w)^3/8)*s^2. The existing GENERIC actual_weight_model_envelope is reused directly. actual_right_tail_bound proves integrability on(R,infinity) and an actual Gaussian-tail norm estimate, with its error-smallness hypothesis discharged at a sufficiently large frequency cutoff in the uniform theorem.

left_unit_domain_curvature proves actual theta-domain control on EVERY s in[-1,0] and Re(D_t'(v+s))<=-t*Re(w)^3/1024. left_phase_quadratic_bound gives Re(leadingPhase)<=E*abs(s)-(t*Re(w)^3/2048)*s^2. actual_left_annulus_bound therefore controls the actual signed integral from-1to-R by1000*norm(W(v))*exp(-(t*Re(w)^3/4096)*R^2), for the stated0<R<=1 and mismatch condition. No imaginary-frequency bound abs(Im(z))<=1 is imposed in these complementary estimates. The actual kernel and phase domains are proved before the envelope is used.

Both complementary contours are normalized by the SAME nonzero W(t,z,v)*Gfull as the fixed central neighborhood, where Gfull is the full complex Gaussian with coefficient -D_t'(v)/2. The right relative budget reuses rightBudget(R,Re(w)); the left relative budget reuses100*rightBudget(R/16,Re(w)). Their existing zero limits are reused; no generic Gaussian, integration-by-parts or power-limit theory is duplicated. uniform_relative_right_tail and uniform_relative_left_annulus supply cutoffs uniform over complex lower-half-plane centers and all explicitly admissible data. Constants and model-versus-actual curvature remain explicit.

uniform_horizontal_gaussian_error takes a common maximum cutoff and applies the compact, intervening-left, fixed-neighborhood and right-tail estimates to ONE COMMON pair w,v. It does not identify unrelated existential witnesses. With fixed split radius R=1/8192, the ALREADY VERIFIED GENERIC horizontal_decomposition splits the ACTUAL whole horizontal integral exactly into these four pieces, retaining their signed orientations. NaturalContour.shifted_weight_integrable proves full horizontal integrability, and the actual right-tail theorem supplies the integrability needed by the split. For each eta>0 there is a cutoff uniform over all admissible data, at which the relative COMPLEX NORM error of the whole horizontal integral is<=eta.

The final theorem far_actual_horizontal_gaussian has NO assumed model root, actual root, anchor or polynomial-budget hypothesis. For EACH fixed t>=1 and0<eta<1 there exists X(t,eta)>0 such that EVERY lower-half-plane frequency c with norm(c)>=X has a constructed ACTUAL saddle v with Re(v)>=1, abs(Im(v))<pi/8, nonzero arithmetic kernel and an integrable actual horizontal half-line contribution
H(t,c,Im(v))=integral_{s>0} W(t,c,s+i*Im(v)) ds,
satisfying norm(H/(W(t,c,v)*Gfull)-1)<=eta and H!=0. The all-angle actual half-circle family and anchor closeness discharge all data, then the radial logarithm passes to EVERY sufficiently large norm. The earlier fixed-neighborhood theorem is now extended to the WHOLE horizontal half-line. This is NOT the original unshifted half-line integral and NOT yet the full paired quartic transform.

A useful exact connection was independently proved as reflected_weight_norm:
norm(W(t,-z,conj(q))) = norm(W(t,z,q))*exp(2*Im(z)*Re(q)),
for ALL real t and ALL complex z,q, with no saddle, height-sign or branch assumption. The proof reuses the verified actual arithmetic weight conjugation identity and compares the real parts of the two phase exponents. At q=s+i*h, it relates the opposite-height channel at -z directly to the controlled channel at z, with pointwise factor exp(2*Im(z)*s). This is a genuine identity for the literal arithmetic weight; it is not a claimed integral dominance estimate.

Next focused target: use this reflection identity, the new Gaussian phase envelopes and compact theta bounds to bound the opposite-height integral for Im(z)<=-1. A possible route is to split at Re(v)-1: compact absolute pointwise control on the first interval, then a real Gaussian mass bound around the saddle on the rest. The suppression exp(-2*(Re(v)-1)) at that height may compensate for the sqrt(norm(z)) normalization loss, leaving a decaying curvature factor. This remains a PROPOSAL: no reflected integral bound or zero exclusion is asserted from the identity alone. In particular, a bound on norm(integral W) cannot be reused as a bound on integral(norm W); the needed pointwise/absolute estimates must be proved. Do not substitute an unsigned bound on the ORIGINAL unshifted opposite half-line, which would lose the exact vertical endpoint cancellation. The full flow remains the signed sum of two horizontal channels, and one nonzero contribution does not prevent cancellation.

The prior manuscript discussion of uncontrolled far remainders is narrowed by the verified WHOLE contribution theorem, but the proposed RH reduction of full far-field zero exclusion remains unaudited as a complete implication. No new literature or novelty claim is made. Competing-channel dominance, intermediate-frequency matching and a joint eventual-time cutoff remain OPEN. Both A4<infinity and A4=infinity and eventual global LP reentry remain OPEN. No RH/A2 or threshold implication is asserted, and no queued campaign starts.

Verification1145: pinned FULL root build PASSED5874jobs, session92189 TERMINAL0. Fresh COMPLETE root transitive axiom audit PASSED35058Foundation declarations, session30667 TERMINAL0; only propext,Classical.choice,Quot.sound. ALL17 public theorem types ACTUALLY READ UNABRIDGED in two complete nontruncated groups9+8. Review checked whole right domain/left unit domain and actual integrability, retained stationary mismatch, direct generic kernel-envelope/budget reuse, common nonzero normalization, ONE shared constructed saddle for all four pieces, exact signed horizontal decomposition, actual whole-H versus unshifted-I versus full-flow distinction, discharged seed budgets and all-angle cutoff quantifiers, and the unconditional reflected norm identity with its exact sign. Manifest1799covers all Foundation/root sources; prior1798hashes unchanged except reviewed root import. All107archive,43Incoming/42distinct,11fullyreadA4 manuscript hashes unchanged. No sorry/admit/new axiom/native admission, manuscript/dependency or unrelated draft change. Standalone53293(base complements),75329(uniform whole assembly),94027(actual family),20948(final including reflected identity) all TERMINAL0. No live jobs. Evidence: .lake/stardust-1145-full-build.log, stardust-1145-audit.log, stardust-1145-working-checkpoint.json, stardust-1145-source-integrity.json, stardust-1145-public-types.json and stardust-1145-verification.json. Exact FOUR-path audited Git checkpoint, receipt and verified PRIVATE backup follow. A4 ACTIVE; all future gates and October31hard stop unchanged.


## Stardust 1146 — reflected-channel dominance and all far zeros real at each fixed positive quartic time (October 20, 2026)

A4 remains ACTIVE. Previous goal turn classification: verified progress,1145whole complex horizontal Gaussian asymptotics and exact reflected-weight identity, audited/private-backed7d8d5855dd2d5de1fe66ef63c7c68640a683075a. Foundation/RiemannQuarticReflectedDominance.lean adds15theorems and1scalar budget definition, proving actual reflected integral dominance, nonvanishing of the FULL signed pair outside the unit strip, and fixed-time far-field reality in the WHOLE complex plane. This closes the fixed-time far-frequency sector gap left open in earlier checkpoints; it does not decide eventual global reentry. The only older mathematical-source change makes the already proved ComplexCompactTail.center_weight_lower public, with EXACTLY the same statement and proof body, independently checked against HEAD. This permits direct reuse instead of duplicating its proof; the older compact theorem's type is unchanged and rechecked.

reflected_left_compact_bound controls the OPPOSITE-height compact integral at(-z,-h), normalized against the MAIN actual saddle W(t,z,a+i*h). It applies the existing GENERIC compact_signed_bound directly to(-z,-h), whose numerical bound is the same as at(z,h): cosine and quartic height are even, the real-frequency/height product is unchanged, and abs(Im(-z))=abs(Im(z)). The main saddle's corrected theta upper supplies the phase comparison. Thus, for Im(z)<=0, it proves the same528*(a-1)*norm(Wmain)*exp(5*a+3-2*t*a^3+3*Im(z)/4) bound without applying the lower-half-plane compact theorem to an upper-half-plane target. Gaussian-relative and uniform compact estimates follow using the existing scalar compactBudget limit. No inequality between norm(signed integral) and integral(norm) is assumed.

actual_gaussian_mass_envelope combines the verified right and left-unit phase estimates at ONE ACTUAL saddle. With Q=t*Re(w)^3 and C=Q/4096>=1, the retained actual/model error E<=1 gives Re(leadingPhase)<=E*abs(s)-2*C*s^2<=1-C*s^2 for EVERY s>=-1. The generic actual arithmetic kernel envelope therefore yields
norm(W(t,z,v+s)) <=3000*norm(W(t,z,v))*exp(-C*s^2).
Both actual theta-domain cases are proved, including the entire right ray; a large complex disk crossing the theta boundary is not assumed. The private Gaussian-majorant wrapper reuses the existing REAL Gaussian integral and Bochner norm domination to prove actual integrability and a full real Gaussian mass bound.

The1145exact reflected-weight identity then gives, for Im(z)<=-1, the pointwise suppression exp(2*Im(z)*(Re(v)+s))<=exp(-2*(Re(v)-1)) on s>=-1. reflected_outer_mass_bound proves ACTUAL opposite-height tail integrability and
norm(integral_{s>-1} W(t,-z,conj(v)+s) ds) <=3000*norm(Wmain)*exp(-2*(Re(v)-1))*sqrt(pi/C).
No sign of Im(v) and no stationary point for the opposite frequency are required. The denominator for every relative bound remains the SAME nonzero main actual weight times its full COMPLEX Gaussian. Real Gaussian mass and complex Gaussian normalization are not identified with each other.

The complex normalization contributes at most2*sqrt(N), N=norm(model center). The verified N<=100000000*exp(4*Re(w)) and norm(v-w)<=1/N imply sqrt(N)*exp(-2*(Re(v)-1))<=10000*exp(4). Also C>=Re(w). relative_reflected_outer_budget therefore bounds the reflected outer ratio by
reflectionBudget(Re(w))=60000000*exp(4)*sqrt(pi/Re(w)),
whose zero limit is proved. This rigorously compensates the complex Gaussian normalization loss at the UNIT imaginary-height threshold. It avoids constructing an unproved upper-frequency saddle or imposing an angular sector.

uniform_reflected_horizontal_bound assembles the compact and outer bounds at common cutoffs and one common saddle. A direct theorem-level reuse is important: the existing GENERIC horizontal_decomposition is evaluated at split radius R=-1. Its finite intervals[-1,1] and[1,-1] cancel EXACTLY, leaving the reflected compact piece and the integrable outer tail. No new translation or integration foundation is introduced. The resulting Gaussian-relative norm of the ENTIRE opposite-height horizontal contribution tends uniformly to0 for Im(z)<=-1 under the explicit admissibility data.

uniform_nonzero_below_unit_strip combines a main ratio error<=1/4 with reflected ratio norm<=1/4. If the FULL actual quartic flow vanished, the exact signed paired-horizontal identity, including its vertical endpoint cancellation, would give main+reflected=0. Dividing by the common main normalization and applying the triangle inequality would force1<=1/2. This proves full-flow nonvanishing, not merely a nonzero individual contribution. far_nonzero_below_unit_strip discharges all assumed roots, anchors and polynomial budgets: for EACH fixed t>=1 there is a positive norm cutoff beyond which EVERY frequency with Im(z)<=-1 is a nonzero of the ACTUAL quartic transform.

The remaining near-real matching is also proved. The verified fixed-epsilon necessary zero bound from1138is used with epsilon=1/4 in the OPEN unit disk about the REAL center Re(z), giving abs(Im(z))<=1/Re(w)<1/2 at an actual zero. The1139real/simple half-disk theorem then applies. Together with lower off-strip exclusion and actual flow conjugacy, far_right_half_plane_real_simple proves: for EACH fixed t>=1 there exists X>=1 such that EVERY actual zero with Re(z)>=X is REAL and SIMPLE, with NO imaginary-height restriction. Finally, conjugacy, evenness and norm(z)<=abs(Re(z))+abs(Im(z)) give the principal theorem far_all_zeros_real:
FOR EVERY fixed real t>=1, THERE EXISTS R(t)>0 such that FOR EVERY complex z,
R(t)<=norm(z) AND flow(t,z)=0 IMPLY Im(z)=0.
This is an actual arithmetic quartic-flow theorem on the WHOLE complex plane. It assumes neither RH nor a classical undeformed-Xi strip bound. Nonreal zeros at that fixed time are confined inside a disk. No finite count is claimed here without a separate compact zero-isolation argument.

Selective source review at this completed proof break: ResearchSources/a4/ibm_laguerre_polya.tex lines760-777discuss the approaching strip edge and far remainder; lines822-858(Proposition prop:rh and its proof) explicitly distinguish eventual upper-time reentry from a sequence of GLOBAL LP times tending to0. The manuscript hash was rechecked unchanged: EAF31754F5F993EF8EB33A1917484D70F6B62F5B37A907AD85F097C3C5589D96. The new proof supplies FIXED-t>=1far-field reality without an RH hypothesis. It supplies neither the manuscript's upper-edge global-in-z eventual-time conclusion nor its lower-edge t_n->0 global LP hypothesis. No RH/A2, threshold or novelty claim is made. The sentence proposing a reduction of full far-field exclusion to RH information is not used as a premise; the exact scope distinctions above must be retained.

A4 remains unresolved: the radius depends on t, and nonreal zeros may still occupy or migrate through the intermediate region as t grows. The expanding verified bulk windows do not yet overlap the norm-dominant far regime uniformly in late time. The NEXT proof priority is that TRANSITION REGION, rather than additional easy fixed-time far-zero corollaries: audit reuse for a moving-saddle construction at bounded frequency/real-saddle-curvature ratios and test whether a common scale comparable to curvature plus frequency closes the gap. Any proposed interpolation or scaled anchor must be constructed and its domains and errors proved; no new campaign is authorized. Both A4<infinity and A4=infinity and eventual global LP reentry remain OPEN. Queued integer A(2k)/A(6), conditional real exponents, independent A(2) and final multichannel stages remain unopened; October31is unchanged.

Verification1146: pinned FULL root build PASSED5875jobs, session7153 TERMINAL0. Fresh COMPLETE root transitive axiom audit PASSED35082Foundation declarations, session78967 TERMINAL0; only propext,Classical.choice,Quot.sound. ALL18 new/affected public types ACTUALLY READ UNABRIDGED in complete groups9+9:15new module theorems,1budget definition with body reviewed,1existing lower-weight helper exported unchanged,1older compact theorem type rechecked unchanged. Review checked actual reflected versus main normalization, absolute Gaussian domination and Bochner integrability, retained stationary mismatch, exact unit-height compensation and scalar budget limit, signed reversal at R=-1, exact endpoint-cancelling paired identity, common actual saddle, seedless all-angle lower nonvanishing, fixed-epsilon unit-strip matching, actual conjugacy/evenness, right-half-plane simplicity without an imaginary restriction, and the final fixed-t forall-complex-z cutoff. Manifest1800covers all Foundation/root sources; prior1799hashes unchanged except reviewed root import and EXACT private-to-public center_weight_lower visibility word; its proof body and statement match the earlier commit. All107archive,43Incoming/42distinct,11fullyreadA4 manuscript hashes unchanged. No sorry/admit/new axiom/native admission, manuscript/dependency or unrelated draft change. Final standalone28252 TERMINAL0includes all global matching;77280proved lower off-strip exclusion; supporting reuse build89545 TERMINAL0,4388jobs. Earlier negated-fourth-power, real-variable continuity, budget-unfolding and interval-endpoint probe failures are superseded. No live jobs. Evidence: .lake/stardust-1146-full-build.log, stardust-1146-audit.log, stardust-1146-working-checkpoint.json, stardust-1146-source-integrity.json, stardust-1146-public-types.json and stardust-1146-verification.json. Exact FIVE-path audited Git checkpoint, receipt and verified PRIVATE backup follow. A4 ACTIVE; fixed-time far-field reality CLOSED, uniform late-time/global reentry OPEN.

## Stardust checkpoint 1147 — moving model saddles across bounded transition ratios (October 20, 2026)

A(4) remains active. Checkpoint 1146 established whole-plane far-zero reality for each fixed t >= 1, with a cutoff that can depend on t. This does not close the uniform late-time intermediate-frequency gap. This checkpoint constructs the moving leading-model saddles needed to address that gap; it does not substitute model saddles for actual arithmetic saddles or transform zeros.

The theorem-level reuse audit found that RiemannQuarticQuantitativeSaddle.existsUnique_frequency_saddle already constructs ACTUAL saddles in the disk norm(z) <= (t*u^3+1)/51200, and RiemannQuarticFrequencyBranch already supplies analytic continuation, derivative and displacement bounds on that disk. RiemannQuarticUniformSaddle.uniform_unshifted_relative_error additionally assumes norm(z) <= t, a cubic phase-error restriction and a quadratic region restriction. Thus existence on a disk proportional to curvature was already available; the full signed Gaussian approximation has additional restrictions. No duplicate actual inverse or Gaussian foundation was introduced. The new construction addresses arbitrary FIXED bounded ratios rather than re-proving the existing small disk.

New root-imported module: Foundation/RiemannQuarticTransitionSaddle.lean. Define B(u) = 4*pi*exp(4*u) and b(u,z) = u + log(1+i*z/B(u))/4, using the principal complex logarithm. The actual real stationary hypothesis is phaseSlope(t,u)=0, not the false assertion that the leading-model derivative vanishes there. Existing arithmetic neighborhood control gives norm(D_t(u)) <= 1. Existing stationary scale bounds give B(u) >= 4*t*u^3+8. These are reused without changing their proofs.

For B >= 2 and Im(z) <= 1, the logarithm argument has real part at least 1/2. movingAnchor_analyticAt proves local complex analyticity on an actual open neighborhood, including at the boundary Im(z)=1; the branch cut is excluded by this positive margin. anchor_exponential proves EXACTLY 4*pi*exp(4*b)=B+i*z. anchor_residual_identity retains the actual/model discrepancy D_t(u): D_t(b)+i*z = 4*t*(b^3-u^3)+D_t(u). No stationary mismatch is discarded.

The elementary log_norm_half_plane bound follows directly from the existing real logarithm inequalities, complex log real/imaginary identities and argument bound; it does not require a new integration or path foundation. For M >= 0 and norm(z) <= M*B, anchor_displacement gives norm(b-u) <= M+6, and anchor_imaginary_bound gives abs(Im(b)) <= pi/8. The constants are deliberately conservative and are not optimal estimates.

anchor_residual_bound proves norm(D_t(b)+i*z) <= 28*L*t*u^2+1 when norm(b-u) <= L and norm(b) <= 2*u. model_saddle_near_moving_anchor then reuses the VERIFIED scalar_ball_surj and scalar_ball_injective for a radius 1/1024 ball about any such exponential anchor. With A = -4*(B+i*z), Im(z) <= 1 and t >= 1, its proof keeps the nonzero REAL scale: norm(A) >= 2*B. The polynomial derivative error and relative exponential variation are bounded against this scale. The explicit large-u hypothesis 65536*(L+1) <= u puts the residual inside the inverse image radius. No division by norm(z), positive-frequency hypothesis, or far-frequency domination of t*norm(b)^3 is used; z=0 is included.

existsUnique_transition_model_saddle specializes this construction: t >= 1, M >= 0, u >= 65536*(M+7), ACTUAL real stationarity, Im(z) <= 1 and norm(z) <= M*B(u) imply a unique MODEL root of D_t(w)=-i*z in closedBall(b(u,z),1/1024). Uniqueness is LOCAL to this stated ball, not global. transition_model_geometry proves norm(w-u) <= M+7, Re(w) >= 1, abs(Im(w)) <= 1/2 and the quantitative positive theta margin t*Re(w)^3+8 <= 4*pi*Re(exp(4*w)). This uses the existing general model real_margin theorem, whose identity retains -Im(z), and the proved numerical pi bound. No kernel branch or positivity assumption is silently added.

eventually_all_maxima_transition_model_saddle proves the construction uniformly over ALL actual global real amplitude maxima at sufficiently large times for each fixed M. eventually_exists_transition_family additionally uses the existing global maximum existence theorem, so the statement supplies an actual real stationary center at every sufficiently late time and is not a conditional statement about possibly absent maxima. Quantifier order is FOR EVERY fixed M >= 0, EVENTUALLY in t, THERE EXISTS u, FOR EVERY z in that bounded-ratio region, THERE EXISTS a locally unique model w. The time threshold may depend on M. No uniformity for unbounded M or global analytic root branch is claimed.

Selective manuscript check: ibm_laguerre_polya.tex lines 759-777 explicitly identify saddle movement beyond the old Gaussian range and an uncontrolled remainder near the strip edge; lines 936-944 request a signed remainder bound uniform in large t. These passages were read again without modification. Hash remains EAF31754F5F993EF8EB33A1917484D70F6B62F5B37A907AD85F097C3C5589D96. The new bounded-ratio construction is a rigorous step toward that moving-saddle obligation; it proves neither the requested integrated remainder nor any reduction to RH. No novelty claim is made.

Exact remaining obligations: correct these transition MODEL roots to ACTUAL arithmetic roots on a common curvature-plus-frequency scale; prove the actual analytic root dependence and nondegenerate curvature needed for phase estimates; control the complete SIGNED horizontal integrals, vertical endpoint cancellation, compact pieces and both tails uniformly for fixed bounded ratio; match those estimates with the large-ratio far regime uniformly in t. The previous fixed-t far theorem cannot supply the last uniformity by quantifier exchange. The existing ComplexCorrection far estimates require 4*t*norm(w)^3+9 <= norm(z) and use radii inverse in norm(z), so they cannot be applied unchanged at zero or bounded small ratio. Reuse their generic exp4_difference_bound and neighbor_real_margin with a proved positive common scale instead; prove all new theta-domain and Cauchy bounds before applying an inverse. Both A(4)<infinity and A(4)=infinity remain open. Global eventual Laguerre-Polya re-entry, A(2), RH and any threshold relation remain unproved. No queued campaign has started.

Verification 1147: pinned FULL root build PASSED 5876 jobs (session 79284, terminal exit 0). Fresh COMPLETE root transitive axiom audit PASSED 35120 Foundation declarations (session 51277, terminal exit 0), only propext, Classical.choice and Quot.sound. ALL 19 public types ACTUALLY READ UNABRIDGED from the audit output, with overlap at the long residual statement: 17 theorems and 2 definitions; both definition bodies were reviewed from source. The entire new proof source was read. Manifest 1801 covers all Foundation/root sources, and all previous 1800 sources match checkpoint 1146 except the reviewed root import. All 107 archive, 43 Incoming / 42 distinct, and 11 fully read A4 manuscript hashes are unchanged. No sorry/admit/new axiom/native admission, dependency, manuscript or unrelated draft change. Earlier branch-analytic proof elaboration failure and build 46471 are superseded by the successful frozen-source full build 79284; all jobs are terminal. Evidence: .lake/stardust-1147-full-build.log, stardust-1147-audit.log, stardust-1147-working-checkpoint.json, stardust-1147-source-integrity.json, stardust-1147-public-types.json and stardust-1147-verification.json. Exact four-path audited Git checkpoint, receipt and verified PRIVATE backup follow. A4 remains ACTIVE; no queued stage or October 31 stopping-date change.

## Stardust checkpoint 1148 — actual arithmetic transition saddles and analytic local branches (October 20, 2026)

A(4) remains active. The preceding moving MODEL saddle construction is now connected to the ACTUAL arithmetic logarithmic phase slope, with its denominator, theta domain, derivative and real curvature controlled. This is a construction of actual saddle objects across bounded transition ratios. It is not yet a theorem about the complete signed Fourier integral, its zeros, global Laguerre-Polya re-entry, or the finiteness of A(4).

New root-imported module: Foundation/RiemannQuarticTransitionCorrection.lean. The main actual_transition_saddle theorem assumes t >= 1, M >= 0, u >= 65536*(M+7), the ACTUAL real stationary equation phaseSlope(t,u)=0, Im(z) <= 1 and norm(z) <= M*B(u), where B(u)=4*pi*exp(4*u). It CONSTRUCTS an actual complex v satisfying 0 <= Re(v), Re(exp(4*v)) >= 1, kernelComplex(v) != 0, complexSlope(t,v) = -i*z, deriv(complexSlope t)(v) != 0, Re(deriv(complexSlope t)(v)) <= -t*u^3/4, and norm(v-u) <= M+8. The arithmetic slope is the existing 4*t*v^3 + deriv(kernelComplex)(v)/kernelComplex(v), with no replacement by the leading model. Both frequency zero and the upper frequency-height interval up to Im(z)=1 are included.

The construction reuses the existing scalar inverse, analytic theta kernel, coarse arithmetic logarithmic derivative error, complex Cauchy estimate and generic exponential perturbation bound. It retains two scales: the real curvature Q=t*Re(w)^3 at a MODEL saddle w provides a lower invertibility bound, while a positive K bounding norm(exp(4*w)) controls a neighborhood. Unlike old far-frequency correction, neither scale is norm(z), and no hypothesis 4*t*norm(w)^3+9 <= norm(z) is imposed.

scaled_neighbor_domain reuses FarCorrection.neighbor_real_margin at the positive scale K. For t >= 1, K >= 8, Re(w) >= 1000, abs(Im(w)) <= 1/2, Im(z) <= 1, D_t(w)=-i*z, norm(exp(4*w)) <= K and norm(v-w) <= 2/K, it proves nonnegative Re(v), Re(exp(4*v)) >= 1 and the lower bound Q/32 for that theta real part. The model identity's -Im(z) term is retained; Im(z)<=1 gives the required positive margin even above the real frequency axis. scaled_neighbor_error then proves the ACTUAL/model slope error <= 30005*exp(-Re(w)) on that complete DOUBLE ball. scaled_neighbor_analytic explicitly uses the nonvanishing actual kernel there. scaled_neighbor_deriv_error applies the existing Cauchy estimate on a 1/K ball around each inner-ball point to obtain the derivative error <= 30005*exp(-Re(w))*K. The nested ball inclusion and every arithmetic domain hypothesis are proved.

The inverse is centered on A=-16*pi*exp(4*w), retaining its negative REAL part. scaled_curvature_lower proves norm(A) >= 4*Q. scaled_model_deriv_bound controls the model derivative error by Q on the inner ball, assuming norm(w) <= 2*Re(w). With the explicit smallness hypothesis 30005*exp(-Re(w))*K <= Q/4, scaled_actual_deriv_bound proves the inverse approximation bound norm(G_t'(v)-A) <= norm(A)/2. scaled_actual_deriv_lower gives norm(G_t'(v)) >= 2*Q. Crucially, scaled_actual_real_curvature separately uses the SHARPER absolute Q-based errors and the model real identity to prove Re(G_t'(v)) <= -2*Q. Nonzero complex curvature alone would not justify a decaying horizontal Gaussian; the sign is independently established.

actual_scaled_frequency_disk constructs a UNIQUE actual root G_t(v)=-i*q in closedBall(w,1/K) for EVERY q with norm(q-z) <= Q/K. Uniqueness is local to that stated integration-variable ball. The frequency neighborhood has positive radius Q/K and is not silently called a unit disk. The actual slope residual and all inverse-image radius budgets are proved. No global choice of a root or global uniqueness is asserted.

transition_scale_data discharges ALL of these analytic and inverse admissibility hypotheses for the existing moving model root, using K=(M+8)*B(u). The prior model geometry gives Re(w) >= 50000*(M+8), Re(w) >= 1000, norm(w) <= 2*Re(w), and norm(w) <= 2*u. Existing real stationary scale bounds give B(u) <= 16*t*u^3 <= 128*Q. Exact model stationarity and the triangle inequality prove norm(exp(4*w)) <= K. transition_error_small uses the existing quadratic lower bound for exp(a) to prove 30005*exp(-a)*(M+8) <= 1/512 on this explicit domain. Combining it with B<=128*Q proves 30005*exp(-Re(w))*K <= Q/4. No assumed asymptotic smallness, new axiom, frequency division or unproved numerical extrapolation enters the construction.

The final real-curvature estimate -t*u^3/4 follows from Re(w) >= u/2 and the proved inner-ball bound -2*Q. The actual kernel is proved nonzero at the returned root, so the logarithmic quotient is an arithmetic saddle on its intended domain rather than an artifact of Lean's totalized division. eventually_exists_actual_transition_family combines this construction with the existing real maximum existence and escape theorems: FOR EACH fixed M>=0, at EVERY sufficiently late t there EXISTS a single actual real stationary u, and EVERY z in its bounded-ratio region has such an actual nondegenerate complex saddle. The threshold may depend on M. No time threshold uniform for unbounded M is inferred.

local_actual_saddle_branch directly reuses Mathlib's analytic local inverse theorem at any constructed nonreal actual saddle with proved positive theta real part, nonzero kernel and nonzero slope derivative. It proves a branch through that exact saddle, complex analyticity, strict derivative -i/G_t'(v), and the actual stationary equation together with positive theta domain and kernel nonvanishing throughout an actual open neighborhood. actual_transition_local_branch discharges its hypotheses for every bounded-ratio transition point and retains the center distance, nondegeneracy and negative real-curvature estimate. These are LOCAL analytic branches; no globally coherent branch across the whole transition region or quantitative common analytic radius is claimed.

Selective source review at this proof break: ibm_laguerre_polya.tex lines 760-770 describe the moving saddle, the approaching strip edge and the uncontrolled remainder beyond the old Gaussian region. The file was read again without changes; hash EAF31754F5F993EF8EB33A1917484D70F6B62F5B37A907AD85F097C3C5589D96 is unchanged. The present construction resolves actual saddle existence and local analyticity at every fixed bounded ratio for sufficiently late time. It does not discharge the manuscript's uniform integrated-remainder assertion or justify its proposed RH-related far-field reduction. No novelty claim is made.

Next A(4) obligation: use the ACTUAL saddles and negative real curvature to prove a complete signed Gaussian approximation uniformly for fixed bounded ratio, including the exact paired-contour endpoint cancellation, compact pieces and horizontal tails. Audit existing pure leading-phase, Gaussian, contour and reflected-dominance theorems before generalizing their norm(z)-dominant hypotheses. Actual saddle existence by itself does not extend the old restricted UniformSaddle integral theorem. The local frequency radius Q/K is positive; any uniform lower bound, coherent branch selection, phase-derivative estimate or replacement of a unit disk by a smaller disk must be proved. Matching to arbitrarily large ratios still requires explicit uniform-in-t estimates; checkpoint 1146's fixed-t far cutoff cannot be used with exchanged quantifiers. Both A(4)<infinity and A(4)=infinity remain open, along with eventual global re-entry. The queued integer, conditional real-exponent, A(2) and final multichannel campaigns remain unopened; October 31 is unchanged.

Verification 1148: pinned FULL root build PASSED 5877 jobs (session 41949, terminal exit 0). Fresh COMPLETE root transitive axiom audit PASSED 35141 Foundation declarations (session 99995, terminal exit 0), only propext, Classical.choice and Quot.sound. ALL 16 public theorem types ACTUALLY READ UNABRIDGED in complete groups 5+5+6; no new definitions. The complete new proof source was read in overlapping segments. Manifest 1802 covers every Foundation/root source, and all previous 1801 sources match checkpoint 1147 except the reviewed root import. All 107 archive, 43 Incoming / 42 distinct, and 11 fully read A4 manuscript hashes remain unchanged. No sorry/admit/new axiom/native admission, manuscript, dependency or unrelated draft change. Final standalone probe 58426 passed; earlier nested-ball parsing and endpoint positivity probes were repaired and are superseded by the frozen-source full build. All jobs are terminal. Evidence: .lake/stardust-1148-full-build.log, stardust-1148-audit.log, stardust-1148-working-checkpoint.json, stardust-1148-source-integrity.json, stardust-1148-public-types.json and stardust-1148-verification.json. Exact four-path audited Git checkpoint, receipt and verified PRIVATE backup follow. A4 remains ACTIVE; actual transition saddle construction and local analyticity are established, uniform signed integral control and global re-entry remain OPEN.

## Stardust checkpoint 1149 — uniform signed CENTRAL Gaussian approximation in the transition region (October 20, 2026)

A(4) remains active. Building on the constructed ACTUAL arithmetic saddles, this checkpoint proves a signed central-integral approximation with a rigorously nonzero full complex Gaussian normalization, and proves its relative error tends to zero uniformly at each fixed bounded frequency-to-scale ratio. The word CENTRAL is essential: the actual integral is over a shrinking horizontal neighborhood of the actual saddle. The Gaussian comparison is over the whole real line. This is not yet a bound for the complete actual horizontal integral, the paired transform, its zeros, or global re-entry.

New root-imported module: Foundation/RiemannQuarticTransitionGaussian.lean. It reuses TransitionCorrection, the generic real ODE identity normalized_real_ode, the existing leadingPhase and its exact primitive identity, the existing exponential cubic remainder, the complex Gaussian integral and oscillatory tail estimate, and the already verified centralRadius(Q)=Q^(-7/16) and its power limits. No new integration, Gaussian, or analytic-inverse foundation is introduced. Some common section hypotheses are deliberately retained even on a few auxiliary estimates that need fewer of them; actual public types were reviewed with those hypotheses present.

The common data are t>=1, K>=8, a=Re(w)>=1000, abs(Im(w))<=1/2, norm(w)<=2*a, Im(c)<=1, the MODEL equation D_t(w)=-i*c, norm(exp(4*w))<=K, and an ACTUAL integration center v with norm(v-w)<=1/K. Set Q=t*a^3 and E=30005*exp(-4*a+4). The actual frequency z need not equal c in the intermediate estimates; the actual stationarity equation G_t(v)=-i*z is explicitly required for the Gaussian approximation.

horizontal_neighbor_domain proves the arithmetic kernel domain on the FIXED real interval abs(s)<=1/16 about v, with Re(exp(4*(v+s)))>=Q/64 and Re(v+s)>=0. It reuses the corrected double-ball domain and the generic positive real exponential translation bound. horizontal_neighbor_error strengthens the arithmetic/model slope error there to E. The proof directly bounds the theta remainder on the interval. It does not take high-order Cauchy derivatives on the tiny radius-1/K correction ball, which could introduce unnecessary powers of K.

horizontal_slope_continuousOn and horizontal_weight_hasDerivAt prove the actual slope continuity and actual arithmetic weight ODE, including the nonzero denominator. actual_horizontal_phase then applies the existing generic normalized real ODE to obtain EXACTLY W(v+s)=W(v)*exp(integral_0^s(G_t(v+r)+i*z)dr). actual_phase_model_error proves the complex phase integral differs from leadingPhase by at most E*abs(s). All phase and weight identities are actual signed complex identities, not expectation-level heat formulas or absolute-value replacements of the integral.

corrected_exp_norm gives norm(exp(4*v))<=2*K. corrected_polynomial_scale gives t*(4*norm(v)+1)<=K. model_real_curvature separately proves Re(D_t'(v))<=-3*Q. Thus the model Gaussian has positive real decay coefficient b=-D_t'(v)/2, and its exponential has norm at most one on the entire real displacement line. No claim of decay is inferred merely from nonzero complex curvature.

The existing explicit exponential cubic remainder gives leadingPhase_cubic_bound with error 2048*K*norm(s)^3 after subtracting both its LINEAR and quadratic terms. At an actual saddle the model linear term is NOT zero: D_t(v)+i*z=-(G_t(v)-D_t(v)), and its norm is bounded by E. leadingPhase_quadratic_bound retains this term. Combining it with the actual/model phase error yields actual_phase_quadratic_bound: the ACTUAL integrated phase differs from D_t'(v)*s^2/2 by at most 2*E*abs(s)+2048*K*abs(s)^3.

If 0<=r<1/16 and 2*E*r+2048*K*r^3<=1, actual_quadratic_weight_error and actual_local_quadratic_error rigorously compare the SIGNED actual integral over [-r,r] with the signed truncated complex Gaussian times W(v). The bound is (8*E*r^2+8192*K*r^4)*norm(W(v)). The proof first obtains a pointwise complex exponential difference bound, then integrates the signed difference; it never infers cancellation bounds from an expectation or replaces the signed target by an integral of absolute values.

actual_local_full_gaussian_error adds the existing complex Gaussian tail bound 2/(norm(b)*r). gaussian_coefficient_norm_bounds proves Q<=norm(b)<=64*K. gaussian_normalization_lower uses the existing squared complex Gaussian identity to prove 1<=8*sqrt(K)*norm(G), where G is the FULL complex Gaussian integral. Both G and the actual W(v) are proved nonzero before dividing. relative_local_error_bound therefore gives the explicit actual signed relative error
norm(L/(W(v)*G)-1) <= 8*sqrt(K)*(8*E*r^2+8192*K*r^4+2/(Q*r)),
where L is the ACTUAL central integral. No normalization is assumed or silently canceled at a possible zero.

The completed convergence statement uses the EXISTING centralRadius(Q)=Q^(-7/16), not a new radius hierarchy. For each fixed positive C with K<=C*Q, E<=30005 and the local smallness condition holds at sufficiently large Q. The normalized error is bounded by
8*sqrt(C)*sqrt(Q)*(240040*r^2+8192*C*Q*r^4+2/(Q*r)).
central_budget_tendsto_zero proves this expression tends to zero, using the verified exponents sqrt(Q)*r^2=Q^(-3/8), sqrt(Q)*Q*r^4=Q^(-1/4), and sqrt(Q)/(Q*r)=Q^(-1/16). eventually_uniform_relative_central_error proves the resulting epsilon bound UNIFORMLY over all actual saddle data satisfying Q=t*Re(w)^3 and K<=C*Q. Local smallness, positivity of r, the cap r<1/16, and every limit hypothesis are discharged, rather than added to the final asymptotic assertion.

moving_scale_ratio_bound proves the missing transition-scale comparison explicitly: for the constructed moving model center, K=(M+8)*B(u)<=128*(M+8)*Q. Its proof reuses the ACTUAL real stationary scale bounds B(u)<=16*t*u^3, the constructed center distance and u<=2*Re(w). This is a fixed-M comparison, not a bound uniform in unbounded M.

MAIN theorem eventually_actual_relative_central_error: for every fixed M>=0 and epsilon>0, at every sufficiently late time t there exists an actual real stationary u>=65536*(M+7) such that EVERY z with Im(z)<=1 and norm(z)<=M*B(u) has the constructed model w and ACTUAL corrected v, satisfying their exact stationary equations and correction-ball constraints, for which the SIGNED central relative error at radius centralRadius(t*Re(w)^3) is less than epsilon. This includes z=0. The same time threshold works for every z in that fixed bounded-ratio region; it may depend on M and epsilon. The central radius follows each moving saddle's Q, and no fixed global analytic selector is asserted. The existence and all common-scale hypotheses are discharged with the verified saddle constructors; this is not just a conditional scalar budget theorem.

Selective read-only manuscript review: ibm_laguerre_polya.tex lines 694-710 separately assert endpoint and complementary-neighborhood bounds before summing a Gaussian approximation. These passages were read again; hash EAF31754F5F993EF8EB33A1917484D70F6B62F5B37A907AD85F097C3C5589D96 is unchanged. The new theorem supplies a rigorously normalized actual central comparison for moving transition saddles, not those asserted endpoint or off-neighborhood estimates. Those estimates must be proved independently, including any zero-frequency denominator issue; they are not imported from the manuscript as facts. No counterexample to that passage or novelty/RH claim is asserted here.

Exact remaining A(4) obligations: extend the central estimate to the ENTIRE actual horizontal contour by proving complementary annular/outer tails and the compact part uniformly for fixed bounded ratio; retain exact vertical endpoint cancellation when pairing channels; establish the reflected-channel dominance and near-real zero localization with proved analytic hypotheses; then match to arbitrarily large ratios uniformly in t. The prior fixed-t whole-plane far-zero theorem cannot supply a uniform late-time matching by quantifier exchange. The central convergence theorem alone supplies no nonvanishing or real-zero statement for the FULL quartic flow. Both A(4)<infinity and A(4)=infinity and eventual global Laguerre-Polya re-entry remain open. The queued integer A(2k)/A(6), conditional real-exponent, independent A(2) and final multichannel campaigns remain unopened; October 31, 2026 is unchanged.

Verification 1149: pinned FULL root build PASSED 5878 jobs (session 5090, terminal exit 0). Fresh COMPLETE root transitive axiom audit PASSED 35176 Foundation declarations (session 68577, terminal exit 0), only propext, Classical.choice and Quot.sound. ALL 26 public theorem types ACTUALLY READ UNABRIDGED in complete groups 6+7+7+6; no new definitions. Proof source was reviewed through its complete construction patches and the final assembled convergence/constructor section. Manifest 1803 covers every Foundation/root source, and all previous 1802 sources match checkpoint 1148 except the reviewed root import. All 107 archive, 43 Incoming / 42 distinct, and 11 fully read A4 manuscript hashes remain unchanged. No sorry/admit/new axiom/native admission, manuscript, dependency or unrelated draft change. Final standalone probe 51194 passed; earlier missing namespace, coefficient-norm rewriting and tactic indentation probes are repaired and superseded by the frozen-source full build. Existing-style section-variable and tactic-search linter warnings do not introduce admissions. All jobs are terminal. Evidence: .lake/stardust-1149-full-build.log, stardust-1149-audit.log, stardust-1149-working-checkpoint.json, stardust-1149-source-integrity.json, stardust-1149-public-types.json and stardust-1149-verification.json. Exact four-path audited Git checkpoint, receipt and verified PRIVATE backup follow. A4 remains ACTIVE; CENTRAL signed Gaussian convergence is established, actual complementary contour estimates and global re-entry remain OPEN.

## Stardust checkpoint 1150 — COMPLETE positive horizontal Gaussian asymptotics at bounded transition ratios (October 20, 2026)

A(4) remains active. The signed central approximation is now extended to the ENTIRE actual positive horizontal contribution through a constructed actual saddle. Both complementary outer tails and the compact segment are controlled. The resulting relative error tends to zero uniformly at every fixed bounded frequency-to-scale ratio. This is a complete ONE-CHANNEL horizontal theorem. It is not yet a theorem for the opposite-frequency pair or the zeros of the full quartic flow.

New root-imported modules: Foundation/RiemannQuarticTransitionContour.lean (12 theorems) and Foundation/RiemannQuarticTransitionCompact.lean (8 theorems). The proof reuses the existing explicit model curvature arguments, actual arithmetic weight/model envelope, Gaussian integration, set-integral difference, corrected compact-contour estimates, natural-strip integrability and exact horizontal decomposition. No new analytic or integration foundation is introduced. Every old proof source remains unchanged.

The common scaled hypotheses are t>=1, K>=8, a=Re(w)>=120020, abs(Im(w))<=1/2, norm(w)<=2*a, Im(c0)<=1, the MODEL equation D_t(w)=-i*c0, norm(exp(4*w))<=K, and norm(v-w)<=1/K. The actual frequency z satisfies G_t(v)=-i*z; the compact comparison additionally needs Im(z)<=1. Set Q=t*a^3 and E=30005*exp(-4*a+4). These conditions do NOT require nonzero frequency, division by norm(z), or domination of the polynomial saddle terms by norm(z). The constructed moving transition roots discharge all of them at sufficiently late time for each fixed M.

TransitionContour.right_model_curvature and left_unit_domain_curvature adapt the existing complex-frequency curvature proofs using the verified transition theta domain. They prove Re(D_t'(v+s))<=-Q/4 for every s>=0, and <=-Q/1024 for -1<=s<=0, with the actual theta parameter positive on the full left unit interval. right_phase_quadratic_bound and left_phase_quadratic_bound apply the existing second-derivative concavity method to the model phase PLUS its quadratic compensator. They retain the small model-stationarity mismatch at the ACTUAL saddle, giving Re(leadingPhase)<=E*s-Q*s^2/8 on the right and <=E*abs(s)-Q*s^2/2048 on the left. The arithmetic error is not set to zero.

The key reuse audit found that FarRightTail.actual_weight_model_envelope was already a GENERIC actual arithmetic inequality with no far-frequency hypothesis. It is reused directly after the new global-horizontal domain estimates. actual_gaussian_mass_envelope proves, for EVERY s>=-1,
norm(W_t(z,v+s)) <= 3000*norm(W_t(z,v))*exp(-(Q/4096)*s^2).
The proof absorbs E*abs(s) with the proved E<=1 and Q/4096>=1. It controls the ACTUAL weight, not just the leading model. No wide complex neighborhood, arithmetic positivity assumption, or integration-by-parts surrogate is used for the outer tails.

horizontal_weight_continuous proves continuity on the whole real displacement line from the positive real exponential factor and the existing analytic theta kernel. actual_outer_integrable proves actual Bochner integrability on s>-1 using Gaussian domination. actual_outer_central_difference proves the signed difference between that outer half-line integral and the central interval [-r,r], 0<r<1, is bounded by
3000*norm(W(v))*sqrt(8192*pi/Q)*exp(-Q*r^2/8192).
The proof uses the exact measurable-set difference Ioi(-1) minus Ioc(-r,r), and a pointwise Gaussian bound on that set where abs(s)>=r. It does not infer a bound for an integral of absolute values from a signed integral estimate.

The existing nonzero arithmetic center and full Gaussian normalization justify relative_outer_central_difference, bounded by 24000*sqrt(K)*sqrt(8192*pi)*exp(-Q*r^2/8192). At the existing centralRadius(Q)=Q^(-7/16), Q*r^2=Q^(1/8). With K<=C*Q, a fixed C>0, the resulting bound tends to zero by Mathlib's proved polynomial-times-exponential limit. eventually_uniform_relative_outer_error combines this with checkpoint 1149's SIGNED central theorem. eventually_actual_relative_outer_error discharges the actual moving-saddle constructors and fixed-M scale comparison, giving uniform actual Gaussian convergence on the whole displacement half-line s>-1. All three pieces are actual signed integrals with a proved nonzero common denominator.

TransitionCompact.corrected_geometry proves Re(v)>=64, abs(Im(v))<pi/8 and the actual kernel nonzero at v from the scaled domain, closeness and positive cosine. horizontal_integrable then directly reuses NaturalContour.shifted_weight_integrable for the COMPLETE horizontal line parametrized by x>0 at height Im(v). The required strict strip condition is proved, not assumed from an approaching model anchor.

actual_compact_bound controls x in [0,Re(v)-1] by
528*(Re(v)-1)*norm(W(v))*exp(5*Re(v)+3-2*t*Re(v)^3).
This is mostly direct theorem reuse. For Im(z)<=0 it applies ComplexCompactTail.actual_left_compact_bound, KEEPING the corrected theta upper bound pi*Re(exp(4*v))<=t*Re(v)^3+3-Im(z)/4 and its additional favorable 3*Im(z)/4 term. For 0<Im(z)<=1 it applies the existing unit-height FarLeftCompact.actual_left_compact_bound; the same corrected theta upper bound implies the required weaker bound in that sign range. The library's missing_frequency_term_counterexample is respected. No invalid omission of -Im(z)/4 or manuscript endpoint denominator is used.

relative_compact_bound proves its ratio to the common Gaussian amplitude is at most 4224*sqrt(K)*Q*exp(-Q/8). This follows from Re(v)>=a/2, Re(v)-1<=Q and 5*Re(v)+3<=t*Re(v)^3. Under K<=C*Q and Q>=1, it is bounded by 4224*sqrt(C)*Q^2*exp(-Q/8), whose zero limit is proved in compact_budget_tendsto_zero. No time-dependent cutoff is silently made uniform.

horizontal_compact_outer_identity is EXACT. It evaluates the already verified generic FarHalfline.horizontal_decomposition at R=-1, and proves the finite horizontal intervals [-1,1] and [1,-1] cancel. The complete positive horizontal integral is precisely compact+outer. This finite-horizontal cancellation must not be confused with the VERTICAL endpoint cancellation required later when pairing opposite frequencies.

eventually_uniform_horizontal_error proves that for each fixed C>0 and epsilon>0, all sufficiently large Q give
norm(H_t(z,Im(v))/(W_t(z,v)*G_model(t,v))-1) < epsilon,
uniformly over every scaled actual saddle datum with K<=C*Q and Im(z)<=1. Here H_t is the ENTIRE actual signed integral over x>0 on the horizontal line x+i*Im(v), and G_model is the FULL real-displacement complex Gaussian integral with coefficient D_t'(v)/2 evaluated at the ACTUAL saddle v. Its positive decay, nonzero normalization and arithmetic phase mismatch were proved in checkpoint 1149. The Gaussian coefficient is explicitly the leading-model derivative at v, not mislabeled as the actual logarithmic derivative G_t'(v).

MAIN theorem TransitionCompact.eventually_actual_horizontal_error: for every fixed M>=0 and epsilon>0, at every sufficiently late real t there exists an ACTUAL real stationary u>=65536*(M+7) such that EVERY z with Im(z)<=1 and norm(z)<=M*B(u) has a constructed model w and ACTUAL corrected v, with their exact stationary equations, correction-ball bound, strict natural-strip membership and integrability, for which the COMPLETE positive horizontal relative error is less than epsilon. B(u)=4*pi*exp(4*u), K=(M+8)*B(u), and K<=128*(M+8)*Q are already proved and reused. The same threshold works for every frequency in that fixed bounded-ratio region; it may depend on M and epsilon. Frequency zero is included. No unproved global analytic root choice or unbounded-M uniformity is claimed.

Selective manuscript review: ibm_laguerre_polya.tex lines 760-771 were read again, describing the moving saddle and the uncontrolled remainder beyond the old Gaussian window. Hash EAF31754F5F993EF8EB33A1917484D70F6B62F5B37A907AD85F097C3C5589D96 remains unchanged. The new theorem addresses actual one-channel integrated steepest descent in bounded transition ratios. It does not establish that manuscript's global eventual re-entry conjecture or any proposed reduction to RH. No novelty or RH claim is made.

The next obligations are now more specific: apply the existing exact paired-contour identity with VERTICAL endpoint cancellation; control the reflected contribution and prove near-real zero localization/real-simple-zero conclusions using analytic amplitude branches and their actual functional domains; then prove uniform late-time matching to arbitrarily large frequency-to-scale ratios. The fixed-t far-zero theorem from checkpoint 1146 cannot be used by exchanging quantifiers. A complete one-channel horizontal asymptotic alone does not decide zeros of the sum of channels, A(4)<infinity versus A(4)=infinity, or eventual global Laguerre-Polya re-entry. These remain OPEN. A(4) stays active, all queued campaigns remain unopened, and October 31, 2026 is unchanged.

Verification 1150: pinned FULL root build PASSED 5880 jobs (session 56286, terminal exit 0). Fresh COMPLETE root transitive axiom audit PASSED 35198 Foundation declarations (session 86483, terminal exit 0), only propext, Classical.choice and Quot.sound. ALL 20 public theorem types ACTUALLY READ UNABRIDGED in complete groups 5+5+5+5: 12 TransitionContour and 8 TransitionCompact; no new definitions. Both proof sources were reviewed, including explicit adaptations of the existing phase proofs and the final constructor/assembly statements. Manifest 1805 covers every Foundation/root source; all previous 1803 sources match checkpoint 1149 except the reviewed two root imports. All 107 archive, 43 Incoming / 42 distinct, and 11 fully read A4 manuscript hashes remain unchanged. No sorry/admit/new axiom/native admission, manuscript, dependency or unrelated draft change. Final contour probe 89061 and compact probe 87143 passed; support build 96813 passed 4412 jobs. Earlier namespace, coefficient positivity, interval-measure inference and scalar exponent probes are repaired and superseded by the frozen-source full build. All jobs are terminal. Evidence: .lake/stardust-1150-full-build.log, stardust-1150-audit.log, stardust-1150-working-checkpoint.json, stardust-1150-source-integrity.json, stardust-1150-public-types.json and stardust-1150-verification.json. Exact five-path audited Git checkpoint, receipt and verified PRIVATE backup follow. A4 remains ACTIVE; complete ONE-CHANNEL horizontal asymptotics are proved at fixed bounded ratios, paired-flow zero control and global re-entry remain OPEN.
