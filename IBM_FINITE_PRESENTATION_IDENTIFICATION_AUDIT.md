# Actual finite predictable-process presentation independence

Checkpoint1324, IBM ACTIVE. This resolves the arbitrary FINITE presentation
consistency obligation left by checkpoints1322–1323. It does not complete a
continuum predictable-integrand domain or an IBM Clark–Ocone theorem.

## Exact theorem

Fix an actual terminal F in JointL2 and its martingale
N_t = E[F | full raw IBM past at t]. Take ANY two finite families of
ordered deterministic intervals (s_i,t_i] and (u_j,v_j], with s_i <= t_i
and u_j <= v_j. Within each family the intervals may overlap, repeat,
have zero length, or appear in any order. The families may have different
cardinalities and different endpoints. Coefficients are the existing actual
bounded random `IBMIntrinsicMartingaleStep.Coefficient` at each left endpoint.

If the two actual step processes agree almost surely at EACH deterministic
time r, then their finite stochastic sums agree as actual JointL2 classes:

    sum_i a_i (N_(t_i)-N_(s_i)) = sum_j b_j (N_(v_j)-N_(u_j)).

`IBMFiniteIntervalIdentification.stochastic_integral_identification` is the
precise Lean theorem. `grid_sumClass_identification` connects it directly to
the existing `IBMTerminalPredictableGrid.sumClass` for ANY two monotone grids,
possibly with repeated times, and possibly different finite cell counts.
Strict monotonicity and a shared partition are no longer required.

## Proof and reuse

The supporting finite algebra is proved for ANY real path x and ANY measure,
without measurability, continuity or martingale assumptions on x. Collect the
charges at each right endpoint minus those at each left endpoint. Their tail
sums reproduce the interval process at positive endpoint times. Induction on
the largest of finitely many endpoints shows that a zero process pairs to
zero with x(v)-x(0). The contribution at zero is handled explicitly; x(0)
is NOT assumed zero. Finite charge pairing then gives the increment identity.

For timewise almost-sure equality, only the FINITE union of endpoints must
share one full-probability event. `Finset.eventually_all` provides that event.
No uncountable intersection of almost-sure statements occurs. Combining the
two finite families using a sum type and negative coefficients gives equality.
The actual L2 step bridges and `Lp.coeFn_finsetSum` transfer this algebra to
the existing stochastic sum classes. Existing full raw-past coefficient,
predictable timeStep/timeSum, terminal martingale and finite-grid definitions
are reused; no new process realization, filtration, or formal completion.

## Explicit counterexample and precise limits

`reversed_interval_counterexample` proves that ordering cannot simply be
discarded. The actual predictable timeStep on (1,0] with unit coefficient is
identically zero, but its formal stochastic step for F=observed(1) is
-observed(1), which is nonzero. The proof reuses actual raw initial projection,
terminal recovery and the previously verified nonzero actual IBM1 class.
Thus a reversed-interval convention would destroy presentation independence.

The equality hypothesis is timewise almost-sure equality at every deterministic
r. No claim is made here about mere product-Lebesgue almost-sure equality,
arbitrary countable presentations, or convergence of predictable integrands
in a continuum control norm. A quotient map on a completed actual process
domain is not constructed merely by proving finite presentation independence.
The countable-grid construction1323 remains on its certified actual energy
domain. Cross-grid limiting consistency and suitable control/closure are the
next obligations. Bracket/regular versions, intrinsic derivatives and adjoints,
full Clark–Ocone and actual unsmoothed IBM Itô remain OPEN. The terminal-specific
integrator N^F must not be conflated with nonmartingale IBM coordinate Z or a
fixed universal representation noise. Original M/F/Z and F1/F2 domains remain.

## Verification

One new module,185 lines and11 public declarations; all complete proofs and
actual unabridged public types are reviewed. Independent Lean checks exercise
actual observed-sine random-coefficient splitting, actual scalar energy
identification across arbitrary finite families, actual scalar sums across
different non-strict grids, and the actual reversed-interval counterexample.
Full root build, COMPLETE transitive safe-Foundation axiom audit with only the
three permitted standard axioms, independent checks, all2113 prior-source
hashes except the single root import, all3 configurations and all113 immutable
manuscript paths/hashes are recorded in
`STARDUST_IBM_FINITE_PRESENTATION_IDENTIFICATION_VERIFICATION.json`.
Exact-commit receipt and verified PRIVATE main/research closure follow the
audited commit. Precommit evidence does not claim that backup has occurred.
Queue, verification requirements and source-preservation rules are unchanged.
