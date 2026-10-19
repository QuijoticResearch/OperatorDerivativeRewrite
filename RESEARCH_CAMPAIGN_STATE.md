> Current priority override (October 19, 2026): see [STARDUST_CAMPAIGN_QUEUE.md](STARDUST_CAMPAIGN_QUEUE.md). A(4) is active; its successor is general A(2k), k >= 2, beginning with A(6), followed by A(2) and the final multichannel campaign. October 31 remains the hard stop. The older recovery entries below are historical, not the current queue.

# Research recovery campaign state — 2026-10-13

Initial HEAD: 953e958c2d6ba5ed21deaca4d3a36f813a0c5f95.
Authoritative state: actual Lean declarations and Git; manuscript claims remain unverified unless identified with a proved declaration.

## Completed verified milestones (not whole manuscript campaigns)
- Brownian integration, restricted smooth Ito and polynomial calculus: see PAPER1_BROWNIAN_ITO_REPAIR.md and BROWNIAN_ENDGAME_REPORT.md.
- Volterra power kernels and concrete positive random volatility/representer: through d09656e; 4187 build jobs, 2951 audit checks.
- Fractional spectral integrability, exact covariance, genuine Gaussian finite-dimensional laws, observable closed derivative/adjoint, prediction obstruction and mean-square Taylor control: through fc5d9fb; 4193 jobs, 3057 checks. See FRACTIONAL_GAUSSIAN_REPORT.md.
- Gaussian OU polynomial Gamma/Gamma2, finite covariance powers, generalized eigenpairs, actual Wick realization: through f61a34e, report c48387e; 4197 jobs, 3102 checks.
- Zero-generator fractional forcing exact L2 threshold and Gaussian response: 953e958; 4198 jobs, 3113 checks.

## Active
- Recover and independently verify uncommitted StochasticKernelConvolution.lean, root import and audit entries. Existing finite energy statement must compile and its elaborated type must be checked.
- Actual bounded predictable kernel-transform adjoint/normal/nullspace and finite-rank energy. This is not yet a Hilbert-valued semigroup stochastic convolution or a mild solution theorem.

## Blocked analytic obligations (not assumed)
- Causal standard-fBM Volterra kernel, filtration transfer, intrinsic field range and fractional Clark-Ocone.
- Fractional continuous sample modification/pathwise controlled estimates.
- Full closed OU generator domain, higher Gamma tower domain extensions and eigenbasis completeness.
- Nonzero-generator Mittag-Leffler summability, Caputo identities, Hilbert-valued convolution, trace/summability and Galerkin convergence.
- Whole-space cylindrical-noise HS claim is invalid; preserve SPDE_SOURCE_AUDIT.md corrections.
- IBM random-time composition, independent sources, local time, observable-domain density, singular first-chaos estimates and negative-Sobolev limit.
- Signed higher-order kernels cannot be treated as probability transitions without a valid construction.

## Pending ordered campaigns
1. Finish recovered convolution operator milestone; investigate legitimate independent extensions.
2. Fractional evolution and finite-rank Hilbert energy with actual domains.
3. IBM foundations and singular calculus from original archive sources; do not skip difficult obligations.
4. Higher-order heat pseudoprocess restricted analytic foundations.
5. Consolidated readiness/backlog audit.

## Preservation and verification policy
No reset, push, dependency change, source manuscript edit, cleanup, black-noise or RH campaign. Preserve twelve unrelated untracked documents. Before each mathematical commit: exact statements, affected compilation, full Lake build, transitive axiom audit (only propext/Classical.choice/Quot.sound), assumptions and limitations.

Recovery checkpoint: StochasticKernelConvolution now verified, full build 4199, axiom count 3130. Active next: quantified zero-mode initial variance obstruction; not yet accepted until its own full build/audit.


Forcing obstruction checkpoint: both quantified counterexamples verified; full build 4200, audit 3132. Active: IBMSourceLaws independent scenery/clock coordinate construction. Random-time composition, paths and IBM calculus remain pending.


## Current checkpoint (supersedes earlier Active entries)

- Completed restricted milestones this recovery: convolution operator and finite-rank Gram energy with exact convergence transfer (1aa556d); quantified fractional forcing initial variance obstruction (b550ea7); independent two-sided Gaussian scenery and Brownian clock coordinate laws (final IBM checkpoint).
- Verification at latest checkpoint: full Lake build 4201 jobs; complete axiom audit 3153 declarations, only propext/Classical.choice/Quot.sound. Forty public declarations accepted across this recovery.
- Next active proof target: continuous jointly measurable versions of the independent source families, preserving finite laws and independence, before reflected-clock IBM composition and moments.
- Pending/blocked obligations remain as listed above; none of the full fractional, curvature, SPDE, IBM singular or pseudoprocess programs is declared complete.
- Requested level-p pseudoprocess manuscript not located recursively in C:/Operator; pseudo folder empty at this recovery. Do not silently substitute another source.
- Detailed next obligations/readiness: RESEARCH_READINESS_AND_BACKLOG.md. Exact theorem inventories and verification: RESEARCH_RECOVERY_REPORT.md.

## Fractional SPDE campaign S1: modulated scalar Brownian forcing — 2026-10-13

At independently verified initial HEAD `7bac23df33a21d4d7109e7c40baad3fc8cfdfaf4`, the preceding curvature final report was committed as `c48387e` and all subsequent repository mathematics was separately built/audited. `Foundation/SPDEModulatedResponse.lean` constructs a genuine scalar Brownian stochastic integral for a measurable bounded multiplier of the normalized fractional power forcing kernel when α>1/2. It proves exact Gaussian law, energy, an explicit upper energy bound, and actual closed source derivative graph. Under a positive global lower bound on the multiplier, its L² existence criterion is exactly α>1/2 for t>0. This is a conditional route to the leading singularity of a Mittag-Leffler resolvent, not a proof of any Mittag-Leffler bound, nonzero-generator equation, or infinite-dimensional SPDE. Full build 4277 jobs, nine exact theorem types checked, complete audit 3449 outputs with only propext/Classical.choice/Quot.sound. Logs `.lake/campaign-spde-01-*`.

## Fractional SPDE campaign S2: exact scalar forcing covariance and transfer — 2026-10-13

`Foundation/SPDEModulatedSensitivity.lean` proves the exact same-driver cross moment and squared mean-square error for two modulated scalar fractional forcing kernels. A uniform deterministic multiplier error δ yields squared stochastic error at most δ² times the exact zero-mode energy, and multiplier convergence transfers to Gaussian L² convergence. The theorems require α>1/2 and bounded measurable multipliers. They do not manufacture independent spatial Brownian coordinates, a Mittag-Leffler resolvent or an infinite-dimensional mild solution. Full build 4278 jobs, six exact theorem types checked, 3455 complete transitive axiom outputs with only the three permitted axioms. Logs `.lake/campaign-spde-02-*`.

## Fractional SPDE campaign S3: genuinely independent finite Brownian modes — 2026-10-13

`Foundation/SPDEFiniteModes.lean` realizes finitely many Brownian driver processes as orthogonal summands of the actual time Hilbert space. The family is jointly Gaussian, and its zero cross covariance proves process-level independence through Mathlib's independence theorem. Actual scalar modulated stochastic responses in those summands have exact modal energy and cross covariance; every finite scalar linear observation has energy equal to the sum of modal energies. This is a concrete independent-noise Galerkin forcing foundation, not yet a Euclidean-valued mild solution, nonzero-rate Mittag-Leffler response, or infinite-dimensional limit. Full build 4279 jobs, eight exact types checked, 3463 complete audited transitive declarations with only the permitted axioms. Logs `.lake/campaign-spde-03-*`.

## Fractional SPDE campaign S4: genuine finite-dimensional Gaussian response — 2026-10-13

`Foundation/SPDEFiniteGalerkin.lean` forms an actual measurable `ℝⁿ`-valued random field from the independent Brownian-mode responses and proves its membership in `L²(Ω;ℝⁿ)`. The exact energy is the sum of squared modal weights times deterministic kernel L² energies. All mode/time and null dimensions are included. The terminal field is a Gaussian stochastic convolution with bounded deterministic scalar multipliers, not yet a nonzero-generator Mittag-Leffler mild solution or an infinite-dimensional limit. Full build 4280 jobs, three exact theorem types checked, 3466 complete audited transitive declarations, only propext/Classical.choice/Quot.sound. Logs `.lake/campaign-spde-04-*`.

## Fractional SPDE campaign S5: temporal covariance — 2026-10-13

`Foundation/SPDETemporalCovariance.lean:13` proves the exact two-terminal-time covariance integral for scalar bounded measurable modulations when α>1/2. At line 25 the same identity is diagonal across the independently realized finite Brownian modes, with zero cross-mode moment. Lines 43 and 60 give the finite scalar-observation inner product and its deterministic sum-of-integrals formula, allowing different terminal times, multipliers, and observation coefficients. These are genuine first-chaos L² pairings, and thus do not assert path continuity, temporal Hölder regularity, or a Caputo equation. No Mittag-Leffler multiplier bounds or infinite-dimensional summability have been established. Full Lake build 4281 jobs; four exact theorem types checked; complete transitive audit 3470 declarations, only propext/Classical.choice/Quot.sound. Logs `.lake/campaign-spde-05-*`.

## Fractional SPDE campaign S6: exact temporal increment energy — 2026-10-13

`Foundation/SPDETemporalIncrements.lean:13` identifies the squared L² distance between two scalar Brownian responses with the deterministic L² distance between their kernels, allowing distinct terminal times and bounded measurable multipliers. Line 30 gives the finite orthogonal-mode sum formula for arbitrary deterministic integrand vectors, and line 47 specializes it to time increments of finite modulated spectral observations. The assumptions are α>1/2, bounded measurable multipliers, and a finite number of independent Brownian modes. This is an exact basis for later mean-square regularity estimates; no rate, pathwise version, Mittag-Leffler kernel, or Caputo solution is inferred. Full Lake build 4282 jobs; three exact public types checked; complete transitive audit 3473 declarations, only propext/Classical.choice/Quot.sound. Logs `.lake/campaign-spde-06-*`.
