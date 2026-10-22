# Actual bounded predictable steps and square-energy series

Checkpoint1334 identifies the completed integral1333 with EVERY existing
bounded raw-past coefficient step for the actual G^F right-germ terminal
martingale. It also proves exact finite sums and genuine ordered countable
G-step series on their summable-square-energy domain. The ACTIVE IBM calculus
campaign continues. Raw terminal projections are not identified with G^F.

## Exact bounded-step theorem

For every actual JointL2 terminal F, ordered s<=t, and EVERY existing
IBMIntrinsicMartingaleStep.Coefficient s, define

    H(r,omega) = 1_(s,t](r) a.function(omega).

The coefficient is strongly measurable in the ENTIRE actual raw observed past
at s. Its norm bound is only required ALMOST EVERYWHERE under the ORIGINAL
joint sample law, exactly as in the original Coefficient structure. It need
not have finite range or a pointwise bound at every sample.

IBMPredictableCoefficientLift.coefficientLp is the actual mu_F L2 equivalence
class of H. The new theorem
IBMPredictableBoundedApproximation.integral_identification proves

    IBMFullPredictableIntegral.integral F (coefficientLp F hst a)
      = IBMGermPredictableStep.stepClass F s t a.

The right side is the EXISTING actual stochastic step, constructed as the
difference of the conditional projections of a*F, with its verified scalar
representative a(omega)*(G^F_t(omega)-G^F_s(omega)). It is not a new prescribed
law or a formal operator substituted for that random variable.

The actual weighted energy is also identified:

    integral H^2 dmu_F
      = E_original[a^2 * (G^F_t-G^F_s)^2].

The squared coefficient, original sample law, raw-past adaptation, ordered
endpoints and actual energy-L2 topology all appear explicitly in Lean.

## Null sets and measurable realization

Strong predictability of the actual step function is REUSED DIRECTLY from
IBMIntrinsicPredictableProcess.timeStep_predictable; it is not rebuilt.
The new lift is just its uncurried time/sample function.

If A is a RAW F_s measurable original-law null event, the exact rectangle
measure from1332 equals incrementMeasure F s t A. That measure is withDensity
of the original joint law, hence absolutely continuous. Therefore the entire
predictable rectangle (s,t] times A is energy-null. This transfers any raw
F_s measurable original almost-sure property to mu_F almost every time/sample
point inside the step interval. It does not assert a global product-measure
identity or measurability of arbitrary sample projections.

Apply this to the coefficient bound. With C=max(a.bound,0), H is bounded by C
mu_F-almost everywhere, including outside the interval where it is zero.
The already proved global finiteness of mu_F then gives genuine MemLp 2 and
the actual coefficientLp class, with an explicit scalar representative bridge.

## Finite simple coefficients and original stochastic sums

For a raw F_s simple function f, its finite range fibers are raw measurable
events. The finite sum of value times rectangle indicator is pointwise
EXACTLY the lifted step H. Thus H belongs to the actual finite process range
from1331; no assertion that general bounded functions have finite range.

For ANY finite presentation representing such a lifted coefficient step,
IBMFiniteIntervalIdentification.interval_equal_ae identifies its actual
stochastic sum with the existing G^F step. This reuses the verified endpoint
charge relation and the original scalar almost-everywhere finite-sum bridge.
Equality is independent of which finite representation of the same H is used.
The completed integral agrees on the finite dictionary by1333, proving exact
simple-coefficient agreement before taking any approximation limit.

## Bounded approximation in BOTH actual L2 spaces

Use Mathlib StronglyMeasurable.approxBounded with cap C. These are raw F_s
simple functions, bounded by C EVERYWHERE and converging to a almost surely
under the original law. Each is packaged in the UNCHANGED Coefficient domain.

The cap event is raw measurable, so the null-transfer lemma gives its energy
almost-sure validity. At points in the interval, the pointwise bounded-simple
convergence theorem applies; outside, all lifted functions are zero. Actual
Lp representatives are handled with their countably many almost-everywhere
identities. Existing BochnerL2Approximation.tendsto_of_dominated, with constant
C in the finite energy L2 space, proves STRONG mu_F L2 convergence.

For the original random variables, the verified scalar step identities and
original bounded-simple convergence apply under the ORIGINAL joint law. The
L2 majorant is C times the actual G increment, represented by the existing
channelClass difference. The SAME verified Bochner L2 dominated-convergence
theorem proves convergence to the original stepClass F s t a.

Continuity of the completed isometry, exact simple agreement and uniqueness
of limits identify the two actual random variables. This explicitly closes
the bounded-coefficient gap; finite-event density alone was not substituted
for the two required convergence/identification proofs.

## Finite grids and countable square-energy domain

Finite linearity now identifies the full integral of ANY finite sum of lifted
bounded steps with the existing IBMGermIndicatorSupport.sumClass. No time
disjointness is needed for this finite identification.

On a nondecreasing countable time grid tau, the genuine G-step random variables
lie in rightPast(tau(i+1)) intersect orthogonal(rightPast(tau(i))). These actual
increment subspaces are orthogonal by the already verified rightPast monotonicity
and step orthogonality. The existing Hilbert OrthogonalFamily theorem proves
summability from SUMMABLE SQUARED stochastic norms; absolute norm summability
is not required.

The exact isometry transfers the Cauchy criterion for finite sums back to the
actual integrand L2 space, proving integrand summability on that SAME energy
domain. Continuity/linearity then gives

    integral F (sum_i coefficientLp_i) = sum_i actual_G_step_i.

Both the integrand and original stochastic partial sums converge STRONGLY in
their respective L2 spaces. The energy-domain assumption is retained in every
relevant theorem; a default tsum value is never asserted to be a convergent
stochastic integral outside the proved summability domain.

## Important surviving distinction and next obligations

The older IBMTerminalPredictableSeries uses IBMTerminalPredictableStep and
RAW conditional projections N^F. It is NOT silently identified with these G^F
right-germ series. The unchanged IBMIntrinsicMartingaleSeries integrates the
specific actual quadratic martingale M, which is also not replaced by an
arbitrary terminal channel. Proving further identifications requires actual
raw/G comparison or a separate exact M-channel theorem. Existing raw/germ
comparison and F1–F3 results must be reused with their exact domains.

This checkpoint DISCHARGES full bounded G-step identification, actual weighted
energy agreement, finite sums and ordered G-series integration on the genuine
square-energy domain. It does not complete native IBM calculus, establish a
universal driving noise, integrate directly against nonmartingale IBM Z, or
prove arbitrary derivative-adjoint domain/Clark–Ocone/Itô identifications.
Positive-time raw/G comparison and regular scalar versions/pathwise bracket
remain open. Focused F1–F3 exact1107 results, actual closed densely defined
intrinsic derivative and Hilbert adjoint, initial-coordinate zero1329, every
original M/F/Z definition, earlier domain and campaign priority are preserved.

## Verification and preservation

Four modules363lines/29 public declarations. Complete sources/proofs and all
actual unabridged public types are reviewed. Fresh full root build, COMPLETE
transitive safe Foundation axiom audit and five independent Lean checks with
terminal times are recorded in
STARDUST_IBM_BOUNDED_PREDICTABLE_IDENTIFICATION_VERIFICATION.json.
All2140 prior sources except EXACTLY4 appended root imports, all3 configs and
all113 archive paths/hashes must remain unchanged. All source material remains
read-only and untracked. Explicit-path Git, exact-commit receipt and verified
PRIVATE main/research synchronization follow full verification. The indefinite
research goal and IBM remain ACTIVE; no later campaign begins early.
