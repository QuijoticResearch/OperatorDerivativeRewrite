# Actual IBM terminal martingales: countable predictable integration

Checkpoint1323 extends checkpoint1322's actual finite random sums. IBM remains
ACTIVE; this is a supporting construction, not completion of intrinsic calculus.

## Exact objects and theorem contracts

Work on the existing joint IBM probability space and its full raw-observation
filtration. For each fixed actual `JointL2` terminal observable F, set
N_t = E[F | raw IBM past at t]. The integrator is this actual martingale,
not the nonmartingale IBM coordinate Z_t. Coefficients use the existing
`IBMIntrinsicMartingaleStep.Coefficient s`: actual bounded, strongly
raw-past-measurable random functions. No independence or Brownian variance law
is introduced.

`IBMTerminalIntegralEnergy` proves the finite uniform estimate

    || sum_{i<n} a_i (N_(tau(i+1)) - N_(tau i)) ||_2^2 <= C^2 ||F||_2^2

for EVERY monotone deterministic grid tau and coefficients bounded by the
SAME nonnegative C. Repeated times are permitted. There is no bounded-horizon
assumption. The proof compares each weighted increment norm to the corresponding
unit increment, uses the verified actual orthogonal finite-sum energy identity,
telescopes unit increments, and applies the conditional-projection contraction
with nested-past orthogonality. Thus the actual weighted squared energies are
summable, even on unbounded time grids.

`IBMTerminalPredictableSeries` directly reuses the existing GENERIC subspaces
`IBMIntrinsicMartingaleSeries.incrementSpace` and their orthogonal family.
Each new actual random increment is placed in past(tau(i+1)) intersect
past(tau i)-orthogonal. The Hilbert orthogonal-series theorem gives strong
L2 convergence precisely when the actual squared norms are summable.
The integral definition REQUIRES monotonicity and this summability certificate;
no stochastic meaning is assigned to a default total sum outside its domain.
Uniformly bounded coefficients discharge the domain automatically by the new
bound, with no time-horizon restriction.

The limiting integral has exact norm-squared equal to the infinite sum of
actual increment norm-squares. By checkpoint1322's step-energy identity these
are E[a_i^2 (Delta N_i)^2], retaining coefficients and increments together.
It obeys the same C^2 ||F||_2^2 bound. For grids bounded by T its L2 class
belongs to the full raw past at T. Conditional expectation at every sampled
time tau(m) is exactly the actual finite scalar sum of the first m increments.
The limit therefore closes the existing actual sampled martingale; both the
L2 projection identity and actual scalar conditional-expectation identity
are proved, using continuity of the existing L2 conditional expectation.

## Cofinal reconstruction and its scope

For monotone tau bounded by T and converging to T from below, unit integration
equals N_T - N_(tau 0). This uses the existing `IBMCofinalPast.projection_tendsto`
for the actual continuous-observation filtration, not an assumed right
continuity or zero right germ. If tau(0)=0 and F is centered and belongs to the
raw past at T, the result equals F. In particular, the actual scalar IBM value
at time one is recovered for F=observed(1), using the proved RAW initial-past
projection theorem. The right-germ initial sigma field remains a separate issue.

This unit identity depends on choosing the terminal-specific integrator N^F.
It is NOT a Clark–Ocone representation using a fixed universal noise, a native
derivative, or the covariance adjoint of the earlier quadratic channel.
It does not contradict the proved deterministic quadratic-range obstruction:
the present odd observed-terminal channel is a different actual integrator.

## Reuse, tests, and remaining obligations

New modules: `Foundation/IBMTerminalIntegralEnergy.lean` (6 declarations) and
`Foundation/IBMTerminalPredictableSeries.lean` (14 declarations). Reuse includes
the existing coefficient/predictable-process definitions, actual conditional
expectations, finite martingale/energy identities, generic orthogonal increment
spaces, and cofinal-past theorem. No new process realization, filtration,
abstract completion, resource override, or trust setting is introduced.

Independent Lean checks cover actual observed-sine random coefficients on ANY
monotone grid; scalar conditional-expectation closure; actual IBM1 cofinal
recovery; and the concrete UNBOUNDED integer time grid with the terminal-norm
energy bound. Complete root build, complete transitive safe-Foundation axiom
audit, all 20 unabridged public types and 228 lines of complete source/proofs,
and independent checks are recorded in
`STARDUST_IBM_TERMINAL_PREDICTABLE_SERIES_VERIFICATION.json`.
Every prior source except the two root imports, all three configurations and
all 113 archive paths/hashes must remain unchanged. Source manuscripts are
never staged. Exact-commit receipt and verified private main/research closure
follow the audited commit; a precommit record does not certify that closure.

Still OPEN: arbitrary common-refinement/presentation consistency for actual
random time processes; a genuine continuum predictable-integrand domain and
its control/closure; random bracket and suitable regular versions; intrinsic
derivative/adjoint identification; full Clark–Ocone; and actual unsmoothed IBM
Itô formulas. Fixed-grid strong convergence does not solve these obligations.
Original M/F/Z, F1/F2 corrections, and all smoothing/domain restrictions remain.
Continue IBM toward these actual-domain questions before the queued campaigns.
