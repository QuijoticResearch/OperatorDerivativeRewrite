# Fractional Gaussian campaign: verified checkpoint and final scope

Date: 2026-10-12. Initial verified HEAD: d09656ee119054c9300a9d74b6ac9533653e800a.
Final mathematical HEAD: fc5d9fb32316c7b94cef586f0a5c15f3cc18aa41. The following documentation commit records this report without changing proofs.

## Verified milestones

| Commit | Module | Mathematical result | Full build jobs | Transitive checks |
|---|---|---|---:|---:|
| 6ecbf0a2ec08ffbec5ca9de482deea6145ce7d01 | FractionalSpectralKernel | Actual harmonizable L² kernel and nondegenerate normalization | 4188 | 2974 |
| 1448a15228ea71b07c7540e9b42277f386c16dda | FractionalSpectralGeometry | Exact increments, covariance, continuity and finite Gram positivity | 4189 | 2992 |
| b7f20776374e1dc6c538bcfba4d3e17252c34eb2 | FractionalGaussianProcess | Completed integrands, injective Cameron–Martin function realization, jointly Gaussian process and true coordinate derivative | 4190 | 3014 |
| 48b4e334b4bee8f80035ac72481188d9efdacc03 | FractionalPredictionObstruction | Genuine forecast variance lower bound and no higher-power initial remainder | 4191 | 3026 |
| 7a898a142be500e162f3daad4fc4942748d4b418 | FractionalControlledEstimate | Actual C² composition Taylor estimate with squared L² error <=3M²|t-s|^(4H)/4 | 4192 | 3039 |
| fc5d9fb32316c7b94cef586f0a5c15f3cc18aa41 | FractionalGaussianOperators | Full closed observable source derivative, dense actual divergence adjoint, polynomial graph core and bidual equality | 4193 | 3057 |

Six successful complete builds and six complete transitive audits. All 106 new public declarations (definitions, instances and theorems) have explicit-type checks and audit entries. Only `propext`, `Classical.choice`, `Quot.sound` occur. Local logs: `.lake/campaign-fractional/01-*` through `06-*`.

## Exact mathematical scope

For every real H with 0<H<1, the real two-component spectral kernel is

    1_(0,infinity)(xi) xi^(-H-1/2) (cos(t xi)-1, sin(t xi)).

Integrability is proved at both zero and infinity. Normalization uses the actual, proved nonzero norm at time one. The normalized vectors satisfy squared increment norm |t-s|^(2H), hence inner product (|s|^(2H)+|t|^(2H)-|t-s|^(2H))/2. Positive semidefiniteness is proved by finite Hilbert sums; no covariance or positivity assumption is introduced.

The deterministic integrand space is the closed Hilbert span of nonnegative-time vectors. Its continuous evaluation realization is injective, with |v(t)-v(s)| <= ||v|| |t-s|^H. The constructed process is jointly Gaussian on the verified countable Gaussian product, centered, with exactly R_H and finite moments of every finite order. All its coordinates lie in the actual closed source derivative domain with their correct constant directional gradients.

The fractional observable scalar space is the actual generated measurable L² subspace. Its derivative domain is exactly the intersection with the existing full source derivative domain, interpreted in the subtype; the graph is closed and polynomial cylinders form a graph core. Its adjoint has the exact weak-representer domain, is closed and densely defined, and its adjoint is exactly the derivative. On every full source-divergence field it equals conditional projection of the actual source divergence.

**Field-space qualification:** this derivative takes values in ambient Gaussian L²(ell²). An intrinsic identification with L² of the completed fractional Cameron–Martin space has not been formalized. The source and observable divergence domains are not asserted equal. No componentwise stronger divergence domain is substituted.

## Original Gubinelli and fractional Clark–Ocone claims

Original source: `C:\Operator\OperatorDerivative.tex`, theorem `thm:gub`, lines 570 onward; factorization proof immediately preceding it. Original files are unchanged.

Let X be the constructed fractional process and Y_t=E[X_1 | sigma(X_r:r<=t)]. The verified conditional projection is actual Mathlib conditional expectation. It satisfies Y_0=0 and ||Y_t||²>=t^(2H)/4 for 0<t<=1. For any alpha>2H, any constant C and any positive delta, some 0<t<min(delta,1] violates ||Y_t-Y_0||²<=C t^alpha. Initial past observation directions vanish. Thus a leading term constrained to that initial past space is zero and cannot rescue the manuscript's asserted exponent min(4H,2H+1)>2H. This is a substantive obstruction even for the terminal first-chaos coordinate, not merely a missing rough-path proof.

A different valid result is proved: f in C² with bounded actual second derivative has R_st=f(X_t)-f(X_s)-f'(X_s)(X_t-X_s) in L² and ||R_st||²<=3M²|t-s|^(4H)/4. This does not silently replace a conditional-prediction theorem or prove pathwise controlled rough regularity.

The manuscript's fractional Clark–Ocone identity is not imported. A causal Volterra transfer with filtration equality and the correct transformed gradient remains necessary before importing the established Brownian-driver representation. No claim is made that fBM is a Brownian semimartingale.

## Remaining obligations and H regimes

- **0<H<1/2:** spectral kernel and covariance fully covered. No pointwise time-integrand interpretation of the singular intrinsic Hilbert geometry is asserted. No rough integral or higher iterated integral constructed.
- **H=1/2:** included in every proved theorem; covariance formula specializes mathematically to min(s,t). No new sample-path Brownian identification is needed for these L² results.
- **1/2<H<1:** same exact spectral, operator and Taylor results. No Young integral or fractional-time generator identification asserted.
- Continuous sample-path modification and pathwise Hölder regularity: not yet proved for this realization. The pinned Mathlib has Kolmogorov-process infrastructure; conversion of the full Gaussian moment bounds into a quantified Kolmogorov estimate and modification remains.
- Causal Volterra kernel, inverse/adjoint transfer and equality of past sigma-algebras: open. A spectral isometry alone is not such a construction.
- Intrinsic vector-field range identification and corresponding full-domain adjoint transport: open. Ambient-field observable adjoint is complete as stated above.
- Intrinsic fractional Clark–Ocone and corrected time-local sensitivity estimates: open; the original formula is not justified by covariance alone.
- No unproved higher-curvature, SPDE, IBM, or original manuscript theorem is claimed here.

## Additional IBM source requested during this campaign

Read all 24 pages of `C:\Operator\ibm\EJP2605-044RA0.pdf`; visually inspected its cover. Source inventory and independent repair notes: `C:\Operator\ResearchAudits\EJP2605_044RA0_SOURCE_AUDIT.md`. Every PDF theorem remains UNVERIFIED in Lean. Key follow-ups include the scenery/clock derivative distinction, combined divergence domains, Bochner square integrability, boundary Dirac cancellation and genuine modified-kernel non-cancellation estimates. The source has placeholder journal metadata; acceptance status is not inferred.

The archive inventory remains read-only with respect to original sources. All 58 prior manifest hashes and the added PDF hash were checked unchanged. Lean 4.34.1, Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612, and lockfile unchanged. All 12 pre-existing untracked research documents remain unmodified. No push.

## Exact public declarations and source locations

All names below have prefix `OperatorDerivativeRewrite.Foundation.`. Line numbers refer to this checkpoint.

### Foundation/FractionalSpectralKernel.lean

- `FractionalSpectralKernel.Plane` — line 14
- `FractionalSpectralKernel.SpectralSpace` — line 15
- `FractionalSpectralKernel.spectralSpace_secondCountable` — line 17
- `FractionalSpectralKernel.wave` — line 21
- `FractionalSpectralKernel.wave_norm_sq` — line 23
- `FractionalSpectralKernel.wave_norm_sq_le_four` — line 28
- `FractionalSpectralKernel.wave_norm_sq_le` — line 32
- `FractionalSpectralKernel.wave_continuous` — line 42
- `FractionalSpectralKernel.raw` — line 48
- `FractionalSpectralKernel.kernel` — line 49
- `FractionalSpectralKernel.raw_measurable` — line 51
- `FractionalSpectralKernel.kernel_measurable` — line 55
- `FractionalSpectralKernel.raw_norm_sq` — line 58
- `FractionalSpectralKernel.raw_small_bound` — line 65
- `FractionalSpectralKernel.raw_large_bound` — line 80
- `FractionalSpectralKernel.raw_sq_integrableOn` — line 86
- `FractionalSpectralKernel.kernel_sq_integrable` — line 112
- `FractionalSpectralKernel.kernel_memLp` — line 121
- `FractionalSpectralKernel.vector` — line 126
- `FractionalSpectralKernel.vector_coeFn` — line 129
- `FractionalSpectralKernel.vector_zero` — line 132
- `FractionalSpectralKernel.vector_one_ne_zero` — line 140
- `FractionalSpectralKernel.vector_norm_sq_integral` — line 154

### Foundation/FractionalSpectralGeometry.lean

- `FractionalSpectralGeometry.wave_sub_norm_sq` — line 12
- `FractionalSpectralGeometry.kernel_sub_norm_sq` — line 18
- `FractionalSpectralGeometry.kernel_neg_norm_sq` — line 26
- `FractionalSpectralGeometry.kernel_scale_norm_sq` — line 34
- `FractionalSpectralGeometry.vector_sub_norm_sq` — line 48
- `FractionalSpectralGeometry.vector_neg_norm_sq` — line 57
- `FractionalSpectralGeometry.vector_pos_norm_sq` — line 61
- `FractionalSpectralGeometry.vector_norm_sq` — line 72
- `FractionalSpectralGeometry.normalized` — line 82
- `FractionalSpectralGeometry.normalized_norm_sq` — line 85
- `FractionalSpectralGeometry.normalized_sub_norm_sq` — line 91
- `FractionalSpectralGeometry.covariance` — line 96
- `FractionalSpectralGeometry.normalized_inner` — line 98
- `FractionalSpectralGeometry.normalized_zero` — line 106
- `FractionalSpectralGeometry.normalized_sub_norm` — line 109
- `FractionalSpectralGeometry.normalized_continuous` — line 119
- `FractionalSpectralGeometry.covariance_symm` — line 130
- `FractionalSpectralGeometry.covariance_positive` — line 137

### Foundation/FractionalGaussianProcess.lean

- `FractionalGaussianProcess.integrandSpace` — line 18
- `FractionalGaussianProcess.integrandSpace_isClosed` — line 21
- `FractionalGaussianProcess.integrandSpace_complete` — line 24
- `FractionalGaussianProcess.kernelVector` — line 27
- `FractionalGaussianProcess.kernelVector_inner` — line 31
- `FractionalGaussianProcess.cameronMartinFunction` — line 38
- `FractionalGaussianProcess.cameronMartin_increment_bound` — line 41
- `FractionalGaussianProcess.cameronMartinFunction_injective` — line 48
- `FractionalGaussianProcess.direction` — line 65
- `FractionalGaussianProcess.value` — line 68
- `FractionalGaussianProcess.process` — line 69
- `FractionalGaussianProcess.process_measurable` — line 71
- `FractionalGaussianProcess.process_isGaussianProcess` — line 74
- `FractionalGaussianProcess.process_memLp` — line 77
- `FractionalGaussianProcess.process_centered` — line 81
- `FractionalGaussianProcess.process_covariance` — line 84
- `FractionalGaussianProcess.process_law` — line 92
- `FractionalGaussianProcess.value_zero` — line 100
- `FractionalGaussianProcess.value_increment_norm` — line 102
- `FractionalGaussianProcess.increment_sq_integrable` — line 108
- `FractionalGaussianProcess.increment_secondMoment` — line 113
- `FractionalGaussianProcess.value_derivative_graph` — line 129

### Foundation/FractionalPredictionObstruction.lean

- `FractionalPredictionObstruction.pastDirections` — line 16
- `FractionalPredictionObstruction.forecast` — line 18
- `FractionalPredictionObstruction.forecast_condExp` — line 21
- `FractionalPredictionObstruction.current_mem_generated` — line 27
- `FractionalPredictionObstruction.forecast_pairing` — line 39
- `FractionalPredictionObstruction.terminal_covariance_lower` — line 55
- `FractionalPredictionObstruction.forecast_norm_sq_lower` — line 65
- `FractionalPredictionObstruction.no_higher_power_bound` — line 83
- `FractionalPredictionObstruction.pastDirections_zero` — line 108
- `FractionalPredictionObstruction.zero_past_polynomial_constant` — line 112
- `FractionalPredictionObstruction.forecast_zero` — line 124
- `FractionalPredictionObstruction.no_higher_prediction_increment_bound` — line 143

### Foundation/FractionalControlledEstimate.lean

- `FractionalControlledEstimate.square` — line 18
- `FractionalControlledEstimate.square_coeFn` — line 21
- `FractionalControlledEstimate.square_norm_sq` — line 31
- `FractionalControlledEstimate.remainder` — line 39
- `FractionalControlledEstimate.remainder_bound` — line 41
- `FractionalControlledEstimate.incrementDirection` — line 65
- `FractionalControlledEstimate.increment_coeFn` — line 68
- `FractionalControlledEstimate.increment_norm` — line 74
- `FractionalControlledEstimate.remainder_measurable` — line 79
- `FractionalControlledEstimate.remainder_memLp` — line 88
- `FractionalControlledEstimate.remainderL2` — line 99
- `FractionalControlledEstimate.remainderL2_coeFn` — line 103
- `FractionalControlledEstimate.remainderL2_norm_sq` — line 108

### Foundation/FractionalGaussianOperators.lean

- `FractionalGaussianOperators.scalarSpace` — line 18
- `FractionalGaussianOperators.derivative` — line 20
- `FractionalGaussianOperators.derivative_domain` — line 34
- `FractionalGaussianOperators.derivative_graph` — line 37
- `FractionalGaussianOperators.derivative_isClosed` — line 52
- `FractionalGaussianOperators.polynomial` — line 63
- `FractionalGaussianOperators.polynomial_graph` — line 66
- `FractionalGaussianOperators.derivative_dense_domain` — line 72
- `FractionalGaussianOperators.polynomial_graph_core` — line 84
- `FractionalGaussianOperators.divergence` — line 92
- `FractionalGaussianOperators.divergence_domain` — line 94
- `FractionalGaussianOperators.projectedSourceDivergence` — line 100
- `FractionalGaussianOperators.source_divergence_pairing` — line 104
- `FractionalGaussianOperators.source_divergence_mem` — line 120
- `FractionalGaussianOperators.divergence_source_value` — line 125
- `FractionalGaussianOperators.divergence_dense_domain` — line 132
- `FractionalGaussianOperators.divergence_isClosed` — line 135
- `FractionalGaussianOperators.divergence_adjoint_eq_derivative` — line 139
