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
