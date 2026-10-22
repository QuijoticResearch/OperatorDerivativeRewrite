# Actual IBM cofinal past and stochastic endpoints — checkpoint1310

IBM remains ACTIVE. This checkpoint resolves the terminal identification left
open by checkpoint1309 for retained-coefficient cofinal countable refinements.
It does not complete continuum predictable integration or the IBM calculus.

## Actual raw filtration identity

IBMCofinalPast.natural_eq_iSup proves the exact measurable-space equality

    F_T^IBM = sup_n F_{tau_n}^IBM

for every deterministic sequence tau_n<=T converging to T. Monotonicity is not
needed for this equality. This includes zero horizon and sequences attaining T.
The proof uses the ACTUAL constructed IBM continuous paths pointwise: Z_T is
a pointwise limit of Z_tau_n, hence measurable in the supremum sigma algebra.
Every earlier Z_s with s<T already belongs to one of those pasts by cofinality.
The reverse inclusion is ordinary filtration monotonicity. No null completion,
right continuity, or hypothetical path version is assumed or inserted.

## Strong conditional approximation and martingale endpoints

projection_ae identifies the existing full past Hilbert projection with actual
scalar conditional expectation. projection_tendsto proves, for every monotone
tau_n<=T converging to T and every joint L2 class f,

    P_{F_tau_n} f -> P_{F_T} f in strong scalar L2.

The proof reuses Mathlib's increasing-subspace projection convergence and
Levy upward conditional convergence. Uniqueness of limits in measure identifies
the limiting Hilbert projection using the exact sigma-algebra equality above.
For actual terminal-past observations the limiting projection is the observation
itself. No stronger measurability of arbitrary ambient f is required.

IBMIntrinsicMartingaleEndpoint.projection_value uses the ALREADY verified
martingale identity for M_t=E[Y_t^2-t|F_t^IBM] to identify projection of M_T
at every earlier s with M_s. valueClass_tendsto therefore proves M_tau_n->M_T
strongly in L2 along every such monotone cofinal sequence. This does not require
a new clock-moment continuity estimate, nor does it imply continuous sample
paths or right continuity of the filtration/martingale.

## Genuine countable retained-coefficient refinement

split_stepClass proves the finite subdivision identity for the actual L2
classes. For any bounded actual F_tau_0-measurable coefficient a, the difference
between the step ending at tau_n and the step ending at T is an actual final
tail step with the SAME coefficient transported to F_tau_n. Its norm is bounded
by the coefficient bound times the unit-tail norm. The latter tends to zero
by the newly proved strong L2 convergence of M.

retained_step_tendsto proves the resulting strong L2 convergence of actual
products. integral_retained_endpoint identifies checkpoint1309's convergent
countable stochastic integral with the original single step a*(M_T-M_tau_0).
integral_retained_actual gives the explicit actual-function identity almost
surely under the original IBM joint law. Thus retained-coefficient cofinal
subdivision cannot change this integral, even with infinitely many cells.
All bounded-energy and adaptation premises are discharged in these theorems.

## Independent tests

The reproducible Lean examples construct the explicit grid
tau_n=2-(1/2)^n in NNReal, prove its monotonicity, bound and convergence, then
check the actual raw-filtration equality at time2; strong conditional recovery
of the actual NONLINEAR terminal observation Z_2^4; strong L2 convergence of
M_tau_n to M_2; and the actual countable stochastic endpoint identity for
sin(Z_tau_0), whose starting time is1. The convergence premise is proved for
this strict cofinal example rather than supplied as an untested assumption.

## Exact open obligations

The terminal accumulation obstruction for these RETAINED-coefficient cofinal
refinements is now discharged. This is not arbitrary-grid equivalence for
changing integrands, a completed continuum predictable domain, or density of
unbounded integrands in a separately defined martingale-energy space. No bracket
measure, quadratic variation, continuous/right-continuous martingale version,
predictable representation property or intrinsic native-adjoint identity is
proved. No ordinary Itô formula for raw IBM is inferred from calculus for M.

Next use retained-step consistency and the actual endpoint control to examine
common finite refinements of general bounded simple processes, with equality
of time-dependent actual integrands and their energy null relations. Build a
continuum completion only with those independent domain and convergence
hypotheses proved. Reuse the existing completion machinery. Preserve all F1/F2
correction terms and clock-number smoothing in their existing verified domains.
The campaign queue and manuscript contents are unchanged.

## Verification contract

Two modules159 source lines,9 public declarations plus the reviewed private
past-projection instance. Complete root build, complete transitive safe-Foundation
axiom audit, actual unabridged public-type/proof review, four independent Lean
examples and all113 archive paths/hashes remain required. Exact observations
and reproducible test code are recorded in
STARDUST_IBM_ENDPOINT_CONTINUITY_VERIFICATION.json after those checks pass.
Git/exact-receipt/verified PRIVATE main and research synchronization are separate
final gates. No toolchain, mathematical semantics, trust or resource override.
