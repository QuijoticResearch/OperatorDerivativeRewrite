# Actual predictable-process control on disjoint interval families

Checkpoint1325 supports the ACTIVE intrinsic IBM calculus campaign. It gives
an actual time-process estimate and transfers it through the verified finite
presentation identification. It does not construct the continuum domain.

## Theorem and hypotheses

Use the existing joint probability space, full raw IBM past, any fixed
actual terminal F in JointL2 and N_t = E[F | raw past at t]. For a finite
index set I, take existing bounded random Coefficient(s_i), ordered intervals
s_i <= t_i, and the exact separation condition

    for distinct i,j in I: t_i <= s_j OR t_j <= s_i.

No grid, covering property, horizon bound or enumeration in time order is
required. Gaps are allowed. Zero-length intervals are permitted when the
displayed separation hypothesis holds. This hypothesis is not silently
identified with mere disjointness of Ioc sets in every degenerate case.

`finite_energy` proves the exact actual L2 energy identity for these random
steps, using existing full-past orthogonality, not independence. For unit
coefficients, `terminal_pairing` proves

    <F, N_t-N_s> = ||N_t-N_s||_2^2.

Together with finite orthogonality and ||F-sum(unit increments)||_2^2 >= 0,
this gives `unit_energy_bound`: the sum of unit increment energies is at
most ||F||_2^2, even for gapped families. `coefficient_energy_bound` therefore
bounds the stochastic sum energy by C^2 ||F||_2^2 for uniformly C-bounded
coefficients, with no time-horizon restriction or factored variance formula.

The stronger `actual_process_bound` assumes only the bound on the actual
time process H(r,omega) = sum_i 1_(s_i,t_i](r) a_i(omega): at EACH deterministic
r, ||H(r,omega)|| <= C almost surely, with C >= 0. The resulting stochastic
energy is again at most C^2 ||F||_2^2. The numerical bounds stored in coefficient
structures are not used as C. For positive-length cells, `process_endpoint`
recovers a_i by evaluating H at t_i. Zero-length increments vanish exactly
by `stepClass_self` and require no such recovery. Each almost-sure bound is
used only at a single deterministic endpoint; no uncountable intersection.

`bound_of_disjoint_presentation` transfers this ACTUAL process bound to ANY
other ordered finite presentation of the same time process, using1324's
`stochastic_integral_identification`. The alternate presentation may overlap
and be internally unordered. A supplied equal disjoint presentation with
the stated separation is an explicit hypothesis. No general disjoint
refinement-existence theorem is assumed or claimed in this checkpoint.

## Reuse and relevance to the remaining construction

The proof reuses actual terminal steps, projections, raw-past orthogonality,
bounded multiplier control, full finite presentation identification and the
original predictable timeStep. No Brownian independence, product Lebesgue
isometry, random bracket or new measure is inserted. The inspected Gaussian
`GaussianTimeStepIntegral` uses its genuine pre-Brownian elapsed-time isometry;
`GaussianPredictableHorizon` uses the corresponding actual product-time measure.
Those specific hypotheses have not been proved for IBM terminal martingales
and are not transported merely by changing process names.

A concrete next route is intersecting cells from two chronological grids,
retaining positive intersections (max(lefts),min(rights)]. Existing coefficients
can be transported to max(lefts) with the old `later`; their differences are
then measurable in that actual past. Such cells are separated and the present
estimate would control cross-grid integral differences by an actual difference
process bound. The common-cell process identity and suitable convergence of
actual integrands still need proofs. This route is not declared successful
here, and a restrictive uniform topology must not be mislabeled the full
predictable energy domain. In particular, merely completing output norms
would not prove a continuum stochastic process realization.

Still OPEN: general disjoint refinement of arbitrary finite interval
presentations, cross-grid limiting control, actual continuum integrand domain
and closure, suitable control measure/bracket, regular versions, intrinsic
derivatives/adjoints, full Clark–Ocone and actual unsmoothed IBM Itô. Fixed
terminal N^F depends on F; it is not nonmartingale IBM coordinate Z or a fixed
universal representation noise. Original M/F/Z, F1/F2 corrections and smoothing
domains remain unchanged. The finite and countable results1322–1324 remain.

## Verification contract

`Foundation/IBMDisjointProcessControl.lean`:155 lines,8 public declarations.
All actual unabridged types and full proofs are reviewed. Four independent
Lean checks cover a gapped reverse-order family with actual observed-sine
coefficients; unit energies for actual observed(4); an actual sine coefficient
whose stored bound is intentionally1000 while the process bound1 controls
the result; and actual scalar energy transfer through a different disjoint
presentation. Fresh full root build, complete transitive safe-Foundation
axiom audit with the same three allowed standard axioms, and independent
checks are recorded in
`STARDUST_IBM_DISJOINT_PROCESS_CONTROL_VERIFICATION.json`.
All2114 prior sources except the single root import, all3 configurations and
all113 archive paths/hashes must remain unchanged. Manuscripts remain immutable
and unstaged. Exact-commit receipt and verified PRIVATE main/research backup
follow the audited commit; precommit evidence does not claim that closure.
Campaign queue, verification gates and the indefinite goal remain unchanged.
