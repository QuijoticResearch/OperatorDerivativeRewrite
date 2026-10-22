# Actual common-cell realization and cross-grid stochastic control

Checkpoint1326 advances the ACTIVE actual IBM calculus campaign from1325's
control with a supplied disjoint presentation to a CONSTRUCTED presentation
for the difference of two finite chronological grids.

## Exact construction and contracts

Take any two monotone deterministic grids tau,sigma, existing full-raw-past
bounded random coefficients a_i,b_j, and finite cell counts n,m. Repeated
times are allowed. The grids must have matching initial and final times:
tau(0)=sigma(0), tau(n)=sigma(m). No uniform time-step, nesting, common
partition, strictness, or positive horizon is required.

`IBMGridIntersection.cells` filters the product of the two finite index sets
to retain precisely the POSITIVE intervals

    (L_ij,R_ij] = (max(tau(i),sigma(j)), min(tau(i+1),sigma(j+1))], L_ij<R_ij.

Filtering is part of the actual construction, not an optional optimization:
the previously verified reversed-interval counterexample makes integrating
unfiltered reversed candidates invalid. `cells_positive` proves ordering;
`cells_separated` proves pairwise endpoint separation. This proof uses the
order of one or the other grid index, without sorting a combined endpoint set.

`coefficient` is the ACTUAL random function a_i-b_j in the full raw IBM past
at L_ij, constructed with the existing `later` transports along the two
max inequalities. Its stored bound is the sum of the original bounds.
The actual common-cell process is a finite sum of the existing timeStep
processes. `process_predictable` proves strong predictability for the SAME
raw IBM filtration and nonnegative-real time type; no Gaussian real-time
predictable space or newly assumed filtration is substituted.

`cell_formula` identifies each time indicator with the product of the two
original cell indicators. `process_product` factors the finite double sum
as H_tau U_sigma - U_tau H_sigma, where U denotes unit-coefficient sums.
`unit_cover` reuses the verified `refined_timeSum` and shows U is the indicator
of the whole grid interval. `process_support` proves the original process
vanishes outside that interval. Matching endpoints then give the EXACT
pointwise identity `process_difference`: the common-cell process is
H_tau-H_sigma for every time and sample. Empty horizons/cell families are
included by the same formulas.

## Actual stochastic identity and estimate

For ANY fixed actual terminal F in JointL2, N^F_t is its existing full-raw-past
conditional-expectation martingale. `IBMGridDifferenceControl.integral` is
the genuine finite sum of actual stochastic L2 steps over the constructed
positive cells. `integral_ae` explicitly connects it to the actual scalar
random sum. Coefficient negation respects both the existing time process
and actual stochastic step classes.

`integral_difference` applies1324's finite presentation identification to
the union of the original tau presentation and the negated sigma presentation
and the newly CONSTRUCTED cell presentation. It proves the common-cell integral
equals the original stochastic sum difference in JointL2. `actual_difference`
proves the corresponding actual scalar almost-sure identity. Intermediate
increments remain N^F_R-N^F_L; no nonmartingale IBM coordinate is substituted
for a conditional prediction at an intermediate time.

Finally `difference_bound` applies1325's ACTUAL process bound to these
separated positive cells. If, at EACH deterministic time r,

    ||H_tau(r)-H_sigma(r)|| <= C almost surely, C>=0,

then

    ||I_tau-I_sigma||_2^2 <= C^2 ||F||_2^2.

The disjoint-reference existence hypothesis is discharged for this two-grid
comparison. No independent-increment, elapsed-time variance law, product-time
isometry, random bracket or native derivative is assumed.

## Remaining obligations and verification

This is a genuine finite cross-grid realization and uniform-process control.
It does NOT identify arbitrary countable presentations, construct a continuum
predictable-energy measure/domain, or prove convergence of actual IBM
integrand approximations in this uniform topology. Uniform essential time
control must not be mislabeled the full predictable energy space. Arbitrary
finite interval families without a supplied grid realization still require
an appropriate general refinement theorem. Random control measure/bracket,
regular versions, native derivatives/adjoints, full Clark–Ocone and actual
unsmoothed IBM Itô remain OPEN. N^F depends on F; it is not universal noise
or IBM coordinate Z. Original M/F/Z and all F1/F2 correction/K domains remain.

Two modules257lines,21 public declarations, all actual unabridged types and
complete proofs reviewed. Four independent Lean checks use genuine crossing
half/third grids with actual sine-of-IBM coefficients: predictability and
stochastic class identity; exclusion of a reversed candidate cell; an actual
time-process bound2 giving stochastic energy control; and the explicit scalar
identity retaining every actual prediction increment. The sine bound is
proved pointwise using unit cover, not asserted as an assumption.
Fresh full root build, complete transitive safe-Foundation axiom audit with
the same three allowed standard axioms, and independent checks are recorded
in `STARDUST_IBM_CROSS_GRID_DIFFERENCE_VERIFICATION.json`.
All2115 prior sources except the two root imports, all3 configurations and
all113 immutable archive paths/hashes must remain unchanged. No manuscript is
staged. Exact-commit receipt and verified PRIVATE main/research closure follow
the audited commit; precommit evidence does not claim that closure. IBM and
the indefinite goal remain ACTIVE; the campaign queue is unchanged.
