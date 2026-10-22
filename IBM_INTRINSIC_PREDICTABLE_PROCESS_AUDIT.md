# Actual IBM predictable processes and common-grid equality — checkpoint1311

IBM remains ACTIVE. This connects the actual stochastic sums to independently
defined predictable time processes and proves common-strict-grid representation
independence. It does not complete arbitrary-grid or continuum integration.

## Actual observation filtration and integrator

IBMIntrinsicPredictableProcess.timeStep is the actual time process
a(omega)*1_(s,t](r), with the previously defined bounded coefficient a strongly
measurable in the full raw IBM past F_s. timeSum is the actual finite sum of
these time functions. These definitions do not involve the stochastic integral
or identify integrands by equality of their outputs.

coefficient_factorization reuses GaussianPredictableStep's verified raw-natural-
filtration factorization. It represents every such actual coefficient as a
measurable function of the entire actual IBM coordinate past. No polynomial,
finite-coordinate or Brownian-law restriction is inserted. The existing
stepProcess_stronglyPredictable theorem then proves timeStep_predictable;
timeSum_predictable follows for every finite grid, without requiring ordering.

Here the process used to GENERATE the filtration and factor the coefficient
is actual IBM Z. The process used for stochastic INTEGRATION remains the
verified martingale M_t=E[Y_t^2-t|F_t]. They are not identified. Only the law-free
predictability/factorization theorems of the Gaussian module are reused. Its
Brownian isometries are not instantiated with either Z or M.

## Refinement of actual time functions

timeStep_split proves the pointwise time-process equality under s<=u<=t while
retaining a's actual coefficient function and transporting its adaptation.
The proof uses disjoint Ioc intervals and their exact union. refined_timeSum
extends this to every finite monotone chain, with repeated times allowed.
Together with checkpoints1309/1310 this proves consistency of both actual
integrand processes and stochastic outputs under retained-coefficient subdivision.

## Equality on an independently specified common grid

For every STRICTLY increasing deterministic grid and every i<n,
timeSum_endpoint proves that evaluating the actual time process at the cell's
right endpoint recovers exactly its coefficient. Strict ordering makes all
other cells inactive. This explicitly verifies the (s,t] endpoint convention.

Consequently equality of two actual time processes on that grid forces equality
of their coefficient functions. integral_eq_of_timeSum_eq proves equality of
the ORIGINAL actual stochastic-sum functions; integralClass_eq_of_timeSum_eq
proves equality of their genuine L2 classes. Coefficient bound values or proof
fields need not agree.

coefficient_ae_of_timeSum_ae and integralClass_eq_of_timeSum_ae strengthen this
to time-process equality almost surely at EVERY fixed deterministic time. No
single simultaneous probability-one event over all times is required: the
proof only uses the finitely many relevant right endpoints. This correctly
identifies different almost-sure coefficient versions in the stochastic integral.

## Independent tests

The Lean tests use the actual bounded random coefficient sin(Z_1) to check
strong predictability and simultaneous consistency of the time process and
actual stochastic integral under subdivision. A two-cell unit grid checks that
the right endpoint at2 recovers sin(Z_1), rather than the initial coefficient.
Finally a coefficient sin(M_0), known to vanish almost surely by the existing
actual martingale theorem, is used in three cells. Its actual time-process
versions agree with zero almost surely, and the two actual L2 stochastic sums
are proved equal despite differing coefficient descriptions and bounds.

## Exact remaining gaps

Common-strict-grid equality is not yet a common-refinement existence theorem
for arbitrary different grids. Repeated times are covered by predictability
and retained-step subdivision, but the endpoint coefficient-recovery theorem
deliberately requires strict ordering. Nor is equality almost surely at every
fixed time equivalent here to equality only almost everywhere for an arbitrary
time-product measure. The latter relation needs a justified energy measure or
a separate continuity/finite-cell argument.

No independently defined completed continuum predictable domain, bracket,
quadratic variation, general Itô/Clark-Ocone formula, predictable representation
or native derivative-adjoint identification is established. A space defined
only by closing stochastic outputs would not resolve these integrand-domain
obligations. Next construct or directly reuse general common-refinement
machinery, remove repeated-point descriptions, and prove the correct energy
null relation before completing time-dependent simple processes. Preserve all
previous actual endpoint theorems, F1/F2 corrections and clock-number smoothing.
No campaign transition or manuscript modification.

## Verification contract

One module136 source lines and13 public declarations. Preserve complete root
build, complete transitive safe-Foundation axiom audit, actual unabridged final
type/proof review, four independent Lean tests and all113 manuscript paths/hashes.
STARDUST_IBM_PREDICTABLE_PROCESS_VERIFICATION.json records exact terminal results
and reproducible tests after verification succeeds. Git/exact-receipt/verified
PRIVATE main and research synchronization remain separate gates. No resource,
toolchain, mathematical semantics, trust or audit configuration change.
