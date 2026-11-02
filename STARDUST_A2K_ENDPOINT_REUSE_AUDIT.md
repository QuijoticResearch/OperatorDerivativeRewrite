# A(2k) to A(2): endpoint reuse and stopping recommendation

Checkpoint1951, November2,2026. A(2) is audited as the k=1 ENDPOINT of the
existing higher-order program. The Gaussian audit1950 is preserved as supporting
work, not substituted for that strategy. This is a research ledger, not manuscript
or public-exposition maintenance. No research-queue transition is made here.

## Actual family and audited scope

Let Phi=RiemannQuarticKernel.kernel and
 F(k,t,z)=integral_(u>=0) exp(t*|u|^(2k))*Phi(u)*cos(u*z)du.
This is the EXISTING RiemannRealOrderFlow.flow, not a new interpolation.
RiemannRealOrderFlow.flow_nat identifies every natural order with RiemannEvenFlow.
k=2 is A4; k=3 is A6; k=1 is H_t=RiemannEvenFlow.flow 1 t. The Fourier jets and
positive origin mass belong to these literal arithmetic functions.

Read the saved A4_CAMPAIGN_STOPPING_AUDIT.md, A2K_INTEGER_CAMPAIGN.md,
A2K_REAL_ORDER_STOPPING_AUDIT.md and prior A2 stopping/method audits, then checked
relevant source proofs, definitions and authenticated declaration signatures.
Historical October31/private/final-campaign labels in those records are preserved,
not reactivated. Current no-expiration, user-controlled PUBLIC-repository and
all verification/source-integrity requirements remain unchanged.

## 1. Structures which genuinely survive at k=1

- RiemannRealOrderFlow.weighted_integrable and integrand_integrable: actual
  domains for all k>=0, all real t, all complex z and natural polynomial moments.
  The SAME arithmetic Phi is used throughout. Spatial entireness and actual
  derivative identities are proved; no complex |u| power branch is required for
  the real integration variable.
- flow_nat and RiemannEvenEvolution.even_order_heat_equation specialize DIRECTLY
  at integer m=1, giving d_t H=-d_z^2 H. A sequence of integers k>=2 cannot tend
  to1. Natural-order formulas must be specialized, not assigned a fictional
  integer-order limiting parameter. k>=4 global eventual reality remains open;
  A4/A6 do not supply a universal all-integer global-zero theorem.
- RiemannRealOrderLimit.jet_order_tendsto_uniformly_on_ball and
  locally_uniform_quadratic_limit_from_above: for every FIXED real time t,
  genuine compact-complex convergence to H_t as k approaches1 from above.
  A common actual integrable Fourier envelope is proved before the limit.
- RiemannRealOrderRealUniform.uniform_quadratic_limit_from_above: genuine
  convergence on the WHOLE REAL frequency axis at fixed t. It does not control
  nonreal zeros or give uniform relative errors near zeros.
- flow_zero_time and RiemannQuadraticXiTransfer.real_order_zero_time:
  F(k,0,z)=H_0(z)=entireXi(1/2+I*z/2)/8 for EVERY k. No order limit is needed at
  time0. At fixed nonzero t the limit is H_t, NOT undeformed Xi.
- The universal integer expanding-window theorem ALSO applies at m=1:
  RiemannEvenWindowZeros.eventually_real_simple_on_each_disk. It gives
  forallR existsT_R forallt>=T_R, real/simple quadratic zeros in that disk.
  It does not exchange these quantifiers into existsT forallR. Existing
  RiemannQuadraticGlobalStrip/FiniteThreshold already prove global quadratic
  reality for t>=1/2, stronger for reality than this reused local conclusion.
- RiemannEvenRealityClosed and the canonical/divisor/growth machinery survive
  direct m=1 specialization with their original nonzero/analytic hypotheses.
  Those transfers were already used in the verified quadratic threshold work.
- HigherHeatL2/HigherHeatSchwartzSemigroup/HigherHeatTemperedSemigroup specialize
  at m=1 on their original L2(R), Schwartz and tempered domains. The genuine
  Brownian realization is constructed at this endpoint by
  HigherHeatRealizationClassification.probability_realizable_iff. It is not
  obtained by assuming a limit of higher-order path probability measures.

## 2. Limits which fail, and hypotheses that cannot be erased

### Global zero control and threshold interpolation

A4's frozen result is a finite attained PERMANENT split-polynomial starting time
A>8, global reality for EVERY t>=A, plus eventual global simplicity and the
recorded threshold collision/nonreal pre-threshold witnesses. This does NOT
assert initial LP membership, nor that the all-real time set itself is that ray.
In particular, A4>8 is not evidence against RH: upward preservation from ANY
all-real time is a QUADRATIC theorem, not established for the quartic flow.
A6 has verified eventual global real/simple zeros; no numerical/optimal A6
threshold or comparison with A2 follows.

The real interpolation has a decisive, ACTUAL obstruction:
 RiemannRealOrderQuarticLimitZeros.between_one_two_nonreal_zeros_infinite:
 EVERY 1<k<2, EVERY t!=0, infinitely many nonreal zeros.
 between_one_two_real_zeros_finite gives finitely many real zeros there.
 between_one_two_no_eventual_real_zeros excludes any finite eventual starting
 time. between_one_two_no_split_polynomial_limit excludes the corresponding
 locally uniform real-split polynomial approximation. The exception t=0 is
 ESSENTIAL and is never discarded.

NEW, by direct theorem reuse in RiemannOrderEndpointAudit:
 fractional_all_real_iff proves for1<k<2
  [all zeros of F(k,t) are real] iff [t=0 AND all zeros of H_0 are real].
 fractional_all_real_time_set identifies the exact set as {0} if H_0 is all-real,
 and as EMPTY otherwise. Neither branch is asserted unconditionally. Its
 eventual-start set is empty in both cases. Calling its threshold+infinity is
 justified only with an explicitly EXTENDED-real convention. Real sInf(empty)=0
 in Lean is independently checked and must not be reported as a finite threshold.

A concrete endpoint check is UNCONDITIONAL: H_(1/2) has only real zeros, while
EVERY1<k<2 has infinitely many nonreal zeros at that SAME time1/2. At the quartic
endpoint, the previously proved eventually_quartic_real_simple_with_escaping_fractional_zeros
supplies another ACTUAL example: late F(2,t) is real/simple while neighboring
fractional orders have nonreal zeros escaping every compact.

Therefore neither global real-rootedness nor finite eventual-start thresholds
extend continuously through this interpolation. Infinite nonreal-zero sets
nearby do NOT disprove real-rootedness of the limit; the actual quartic example
already demonstrates why that inference is false.

### Correct zero-limit and Hurwitz logic

The actual compact convergence hypotheses are proved, not assumed.
RiemannRealOrderZeroLimits.zero_of_order_and_zero_limits transfers convergent
zeros. quadratic_nonreal_zero_escape and quadratic_compact_zero_stability KEEP
BOTH all-real and simple-zero hypotheses for H_t. Using them at t=0 to prove RH
would assume the central missing all-real conclusion, plus simplicity.
RiemannRealOrderFractionalZeros.exists_approaching_escaping_nonreal_zeros only
selects SOME escaping zeros at each fixed nonzero time, not EVERY zero.
No fixed-nonzero-time theorem is silently promoted to a joint t(k)->0 theorem.
If an all-real approximating family converged locally uniformly to a nonzero
entire limit, appropriate Hurwitz/vertical-limit arguments could transfer
reality. That premise is FALSE for the actual1<k<2 family at nonzero time.
No general impossibility of a future different bridge is claimed.

### Absolute convergence survives; relative normalization degenerates

The actual fractional leading coefficient is
 L(k,t)=t*Phi(0)*Gamma(2k+1)*sin(pi*(k-1)).
RiemannRealOrderFractionalCoefficient.leading_div_order_gap_limit proves
 L(k,t)/(k-1) ->2*pi*t*Phi(0).
It vanishes linearly at1 for t!=0. RiemannRealOrderTransitionRate proves uniform
ABSOLUTE scaled error <=C_t*x^(-1/2) for1<k<=5/4,x>=1. Its relative bound is
C/((k-1)*sqrt(x)), only on its stated moving region. The relative-obstruction
theorems prove failure on every full order/frequency tail rectangle touching1.
The real-zero radius bound max(1,(K/(k-1))^2) diverges; this is an upper bound
on REAL zeros, not localization of nonreal zeros or an actual escape rate.

RiemannRealOrderCutoffConcentration.no_common_integrable_majorant concerns the
DERIVATIVE CUTOFF, whose mass concentrates at0 despite pointwise convergence to0.
It does NOT negate the genuinely proved common envelope for the original
weighted Fourier integrand. These are distinct dominated-convergence questions.

RiemannRealOrderBranchObstruction proves a no-holomorphic-germ obstruction at
odd half-integer orders and nonzero time, with positive-half-line continuation
still available. It does NOT prevent spatial entireness of F or every contour
argument. Integer entire-polynomial phases/contours cannot simply be copied
across the origin to a fractional absolute-value power.

### Operator domains, positivity and normalization

The DISSIPATIVE symbol of HigherHeatL2 is exp[-s*(2*pi*xi)^(2m)], s>=0.
The GROWING arithmetic weight is exp[+t*u^(2m)]. Their signs are opposite;
u=2*pi*xi is the frequency normalization. Positive arithmetic deformation is
not automatically a bounded L2 contraction. The actual theta-weighted integrals
exist on their proved special domains, which does not extend that operator to
all of L2, a bounded Fourier-character path space, or the factorial lp-one domain
already excluded for actual Xi by RiemannFactorialObstruction.

The original HigherHeatL2 and higher path evolution have NATURAL order m.
The separate FractionalFourierSemigroup allows real fractional rates but acts
on normalized Haar L2 of the CIRCLE, not the real-line arithmetic transform.
Its source/function algebra, graph domain and normalization must be identified
before claiming any actual-Xi realization. No continuous real-line order family
or operator-norm/graph convergence theorem is silently inferred from time
strong continuity or an abstract Hilbert isometry.

HigherHeatRealizationClassification proves probability AND finite-signed full
path realization iff m=1 for the specified cylinder family. For m>=2 signed
finite-dimensional laws/operator-dual completions remain meaningful; a full
bounded-variation path measure does not. Positivity at the Brownian endpoint
is a new endpoint property, not a property inherited from nonexistent higher
path probability measures. No unverified real-order path-limit claim is made.

Distinguish THREE objects: the positive arithmetic density
exp(t*|u|^(2k))*Phi(u), the dissipative Fourier multiplier, and the signed
higher-heat convolution kernel. The arithmetic density stays positive and
integrable for real k>=0; normalized by its positive mass it defines a positive
Fourier functional. This never implies real-rootedness: the ACTUAL fractional
nonreal-zero theorem already refutes that inference. Signed heat-kernel
nonpositivity is about a different kernel.

RiemannQuadraticGaussian.real_gaussian_average and imaginary_gaussian_average
remain exact at k=1: real noiseN(0,2s) shifts t to t-s; imaginary noise shifts t
to t+s. For k!=1 real Gaussian averaging instead inserts exp(-s*u^2) beside
exp(t*|u|^(2k)); it is a MIXED tilt, not a shift of the higher-order time.
Independent exact checks using u=1,2 exclude reparametrizing u^2 as d*u^4 or
as d*u^6 even on the nonnegative integration half-line. Saddle amplitude/frequency
normalizations with cosine/Gaussian local limits also change the object; those
limits are not the fixed-time actual Xi transform. No threshold sandwich follows.

## 3. A genuine surviving quantitative endpoint corollary

NEW quadratic_scaled_decay is proved by the EXISTING uniform absolute remainder,
the EXISTING actual order continuity at1, the proved leading coefficient limit,
and le_of_tendsto on the nontrivial right-neighborhood filter. It states:
 for EVERY real t there is C_t>=0 such that for EVERY x>=1,
  norm(x^3*H_t(x)) <= C_t*x^(-1/2).
Thus H_t(x)=O_t(x^(-7/2)) on the positive real axis. In particular it applies to
t=0 and hence actual normalized Xi. This is a legitimate new FORMAL REUSE
corollary; no world-novelty claim is made for the classical decay fact. It is
not a pointwise new inequality for the common Phi kernel, not a nonvanishing
lower bound, and not a complex zero-free estimate. The existing no-rate
Riemann–Lebesgue result alone was weaker than this quantified conclusion.

Everything else inherited at1 is already covered by the actual quadratic
integral/evolution/Gaussian/canonical/strip/finite-threshold developments.
The known <=1/2 production bound and pinned conditional7/8-arithmetic ->9/32
consequence are unchanged. No actual zero-time reality, threshold sign or
improved arithmetic bound is established by the endpoint audit.

## Recommendation and preserved obligations

Recommend STOPPING the CURRENT A2/RH campaign at this verified checkpoint,
with the problem explicitly unresolved. The original higher-order strategy has
been revisited; its valid endpoint structures and quantitative corollary survive,
but its global zero-control mechanism does not traverse the actual fractional
family. Generic m=1 positive-time window results do survive, but do not improve
the already verified quadratic real-zero bound or control H_0.

Do not extend the Gaussian audit as a replacement strategy without a specific
new Xi-dependent sign/arithmetic estimate. Preserve1950's verified actual domains,
Stein/covariance identities and counterexamples. Preserve the UNFINISHED1947-1949
kernel fifth-sign certificate and full-Hermite/vacuum/Jensen/covariance obligations
as OPEN, not disproved or completed. No claim of an impossibility theorem for RH.
This is a stopping RECOMMENDATION, not a user-authorized queue transition or
completion of the indefinite research goal. The existing queue is unchanged.

Verification, integrity, exact commit and guarded two-branch backup evidence are
recorded in STARDUST_A2K_ENDPOINT_REUSE_VERIFICATION.json and the research ledger.
ResearchSources and all previous Lean/manuscript histories remain unchanged;
no publication/README/PDF work is performed and repository visibility is untouched.
