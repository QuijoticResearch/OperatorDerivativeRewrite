# Actual IBM strong L2 right germs — checkpoint1313

IBM remains ACTIVE. This constructs canonical right limits of the existing
intrinsic IBM martingale in strong scalar L2 and gives actual random-variable
representatives with precise conditional identities. Equality with the present
process is proved at zero; at positive time it remains an exact jump obligation.

## Reuse and decreasing pasts

IBMDecreasingPastProjection obtains strong convergence of projections on
decreasing actual IBM past spaces by applying Mathlib's existing increasing-
projection convergence theorem to their orthogonal complements. The limit is
projection onto their intersection. Closedness and projection instances come
from existing Hilbert-space and actual closed-past results. No new stochastic
law, completion convention or martingale regularization is assumed.

For every nonincreasing deterministic time sequence bounded by a finite future
horizon T, the actual M_tau_n classes converge strongly in L2 to projection of
the ACTUAL M_T class onto that intersection. This directly uses the previously
verified actual martingale conditioning identity.

## Canonical right germ and independence

IBMIntrinsicRightGerm.rightPast t is the intersection of the actual L2 past
spaces for ALL u>t. It is implemented through orthogonal complements to make
closedness explicit; rightPast_eq_iInf proves the exact intersection identity.
This intersection is not silently identified with L2 of the raw intersection
sigma algebra: that representative/filtration statement is a separate obligation.

Any sequence tau_n>t converging to t has the same intersection of L2 pasts,
by cofinality and filtration monotonicity. rightLimitClass t is projection of
M_(t+1) onto rightPast t. rightLimitClass_horizon proves the same class is
obtained using ANY future horizon T>t. valueClass_tendsto_right proves that
EVERY bounded nonincreasing strictly-from-the-right cofinal sequence converges
strongly to this same class. The result is independent of the sequence and
future horizon under its explicit hypotheses.

IBMIntrinsicRightApproach constructs tau_n=t+(1/2)^n, proves positivity,
monotonicity, finite-horizon bound and convergence, and verifies the actual
martingale classes converge along it. Existence is therefore instantiated by
a concrete sequence rather than left conditional on an unspecified approach.

## Actual realization and precise jump

rightValue t is the actual scalar representative of rightLimitClass t on the
original joint IBM probability space. rightValue_memLp proves L2 membership;
rightValue_future_ae proves it has a measurable version in EVERY strictly
later raw IBM past. rightValue_present_condExp proves

    E[rightValue_t | F_t^IBM] = M_t almost surely.

The past and underlying probability law are unchanged. This does not assert
strong adaptation of rightValue to the present raw filtration, raw intersection
sigma-algebra adaptation, joint time/sample measurability, regular sample paths,
or the full Mathlib Martingale predicate for this new representative family.

jumpClass t=rightLimitClass t-M_t lies in the orthogonal complement of the
ENTIRE actual present L2 past. energy_decomposition proves

    ||rightLimitClass t||^2 = ||M_t||^2 + ||jumpClass t||^2.

rightLimitClass_ne_zero proves the germ nonzero at every positive time, using
the verified actual fourth-power observation test. equals_present_iff_energy
and rightValue_eq_original_iff identify exact equivalent regularity conditions:
actual almost-sure equality to M_t, zero jump, and equality of the two energies.
None is assumed at positive time.

## Bounds and origin

Passing the existing actual squared norm bound along the concrete approach
gives ||rightLimitClass t||^2<=2t^2 and
||jumpClass t||^2<=2t^2-||M_t||^2. rightLimitClass_zero and jumpClass_zero prove
the right germ and jump vanish at zero. The actual representatives therefore
agree with the original martingale at zero almost surely. This preserves and
extends the actual origin result from checkpoint1312.

## Tests and remaining construction obligations

The independent Lean tests check nonzero germ, actual present conditional
expectation and energy at time1; prove an independent cofinal rate
1+(1/4)^n converges to the same class; use a different future horizon3 and
actual conditional recovery at time2; and verify the origin equality while
retaining positive-time modification as an energy equivalence only.

Next investigate the actual right jump, its variance/time behavior and the
representative relationship between these Hilbert intersections and right-germ
sigma algebras. A canonical L2 limit is not yet a right-continuous or cadlag
modification. If a right-continued filtration or another process is constructed,
prove its actual adaptation and martingale identities and state exactly which
original values it preserves. Do not remove the right-jump obligation by
renaming a right limit as a modification.

General common refinements, the correct countably additive energy/null relation,
an independent completed continuum predictable domain, bracket, PRP and native
derivative-adjoint identification remain open. Preserve all existing actual
integration, endpoint, F1/F2 correction and clock-number smoothing domains.
No campaign transition, arbitrary stopping date or manuscript change.

## Verification contract

Three modules260 lines,35 public declarations and two private closed-projection
instances. Full root build, complete transitive safe-Foundation axiom audit,
actual unabridged type/proof review, four independent Lean examples and all113
immutable manuscript paths/hashes remain mandatory. Exact terminal results and
reproducible test code are recorded in
STARDUST_IBM_RIGHT_GERM_VERIFICATION.json after verification succeeds.
Git/exact-receipt/verified PRIVATE main and research synchronization remain
separate final gates. No new toolchain, resource, trust or audit settings.
