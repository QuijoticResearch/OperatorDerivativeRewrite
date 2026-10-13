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

