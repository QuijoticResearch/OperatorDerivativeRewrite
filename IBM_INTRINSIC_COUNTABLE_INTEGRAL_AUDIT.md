# Actual IBM-natural refinement and countable integration — checkpoint1309

IBM remains ACTIVE. The construction integrates against the actual martingale
M_t=E[Y_t^2-t|F_t^IBM], retaining the raw full IBM natural filtration. This
checkpoint proves finite interval refinement and countable ordered-grid strong
L2 convergence with exact energy and conditional closure. Full continuum IBM
stochastic calculus is not complete.

## Refinement and uniform control

IBMIntrinsicMartingaleRefinement.later transports a genuine bounded coefficient
from F_s to F_u when s<=u without changing its actual function or bound.
split_step proves pointwise equality of a single step with two subdivisions.
refined_sum proves the same for every finite nondecreasing chain, retaining the
original coefficient throughout; refined_sumClass proves equality of the actual
L2 classes. Repeated times and zero-length intervals are allowed. These are
finite retained-coefficient refinement identities, not a theorem about arbitrary
changing integrands on unrelated grids or arbitrary infinite regrouping.

unit_stepClass identifies the actual unit step with the difference of the
existing actual M classes. Conditional orthogonality to the previous value
gives unit_energy_bound <=2t^2. step_norm_bound compares any bounded coefficient
with the unit step using an actual almost-sure norm bound. grid_energy_bound
therefore proves, for every nondecreasing deterministic grid and common bound
C>=0, that the accumulated sum at tau_n has squared L2 norm <=2C^2 tau_n^2.
For a finite horizon T this is <=2C^2 T^2 uniformly in n and the grid.

## Genuine countable-grid construction

IBMIntrinsicMartingaleSeries.incrementSpace is the intersection of the ending
full IBM past with the orthogonal complement of the starting past. These
subspaces form an actual orthogonal family along every nondecreasing grid.
The previously constructed actual stochastic step belongs to its corresponding
subspace. This discharges the hypotheses of the existing Hilbert orthogonal-
series theorem; no new abstract completion or process is assumed.

The precise general convergence domain is a fixed deterministic nondecreasing
tau:N->NNReal, actual bounded F_tau_i-measurable coefficients a_i (individual
bounds may differ), and

    sum_i ||a_i*(M_{tau_{i+1}}-M_{tau_i})||_2^2 < infinity.

steps_summable proves unconditional Hilbert summability of the actual step
classes. integral is their L2 sum. sumClass_tendsto proves strong scalar L2
convergence of the genuine finite stochastic sums to this integral; their
actual-function identification is already verified at checkpoint1308.
integral_energy proves the exact infinite energy identity, not just a bound.
bounded_energy_summable discharges the summability premise for EVERY bounded
monotone grid in [0,T] and EVERY uniformly bounded coefficient sequence.
bounded_integral_bound proves the limiting squared norm <=2C^2 T^2.
integral_mem_past proves the limit belongs to the full actual IBM past F_T.

The definition uses Lean's total tsum convention, so its convergence/energy
interpretation is asserted only under the explicit monotonicity and summable-
energy hypotheses. No meaning is inferred for divergent inputs.

## Actual martingale closure

sumClass_condExp identifies conditioning of any later finite sum at an earlier
grid time with its earlier partial sum. Continuity of the verified Hilbert
conditional projection passes this identity to the strong L2 limit.
integral_condExp is the exact L2 equality. integral_actual_condExp identifies
the scalar conditional expectation of the limiting actual Lp representative
with the original actual finite stochastic sum, almost surely.

Thus this constructs a terminal variable closing the actual sampled martingale.
It does not claim all IBM observables are representable by this integrator or
that the raw IBM process itself is a martingale.

## Independent tests and exact limitations

The reproducible Lean checks retain the actual coefficient sin(Z_1) through a
two-cell refinement; instantiate countable strong L2 convergence and the energy
bound for the entire family sin(Z_tau_i) on EVERY bounded monotone grid; check
the corresponding actual conditional closure; and verify the zero actual
coefficient sequence produces the zero integral even on an arbitrary grid.

Not proved: a completed continuum predictable integrand space, measure/bracket
identification, arbitrary-grid representation independence, unbounded-coefficient
density in an independently defined weighted space, right-continuous martingale
version, quadratic variation, or a predictable representation theorem. A fixed
countable grid with one accumulation point does not span arbitrary continuum
time observations. No claim identifies the limit at a terminal accumulation
time with M_T itself without proving the necessary temporal continuity.

Next investigate genuine endpoint/filtration continuity and common-refinement
energy consistency to pass from these explicit grids to a justified continuum
domain. Reuse the actual IBM continuous paths and existing past-density and
projection machinery before constructing new foundations. A range closure alone
is not a full predictable calculus. The native intrinsic derivative/adjoint
identification remains open; F1/F2 corrections and clock-number smoothing keep
their existing proved domains. No campaign transition or source modification.

## Verification contract

Two new modules,234 source lines and23 public declarations. Keep the complete
root build, full transitive safe-Foundation axiom audit, all final unabridged
type/proof reviews, four independent Lean examples and all113 immutable
manuscript path/hash checks. Exact observed terminal results and reproducible
tests are recorded in STARDUST_IBM_COUNTABLE_INTEGRAL_VERIFICATION.json after
verification passes. Git/exact-receipt/PRIVATE main and research synchronization
are separate final gates. Toolchain, trust, resource settings and audits are
unchanged. The indefinite goal and IBM campaign remain active.
