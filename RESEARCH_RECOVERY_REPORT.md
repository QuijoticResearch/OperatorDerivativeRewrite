# Research recovery and convolution checkpoint — 2026-10-13

Initial HEAD: 953e958c2d6ba5ed21deaca4d3a36f813a0c5f95.

Recovery established that six fractional Gaussian milestones and three curvature milestones already succeeded. Their limitations remain in FRACTIONAL_GAUSSIAN_REPORT.md and GAUSSIAN_CURVATURE_REPORT.md. The latest committed audited milestone was FractionalForcingKernel: 4198 jobs and 3113 transitive checks. Archive directories are accessible: 23 fBM files, 10 IBM files (including the added PDF), two SPDE TeX manuscripts. Counts are files, not distinct verified papers.

## Convolution operator milestone

Recovered unfinished Foundation/StochasticKernelConvolution.lean, root import and axiom entries. Prior full build failed in finite_convolution_energy, despite direct Lean compilation passing. Repaired the inner-product expansion with explicit ambient subtype coercions under Lake's configured options.

Let K:E -> fullPredictable be an independently supplied bounded linear map, where E is a real complete Hilbert space. The actual integral is J K, using the established predictable Ito isometry J. Exact norm and inner product, boundedness, product integrability, adjoint K* J*, normal operator K*K, nullspace and full divergence graph membership are proved. The projected closed derivative identity is restricted to the actual derivative domain. No injectivity, isometry or SPDE solution property of K is assumed.

The independently defined finite-rank transform sums continuous scalar functionals times actual predictable fields. Its integral and energy retain every Gram cross term; no independence or orthogonality is assumed. New extensions prove exact operator error ||JK-JL||=||K-L||, equivalence of strong convergence at each parameter, and equivalence of operator-norm convergence. A Galerkin application must still prove its kernel convergence.

Verification: affected Lake target passed; complete Lake build passed (4199 jobs); explicit public types checked; 3130 complete transitive axiom checks, exactly propext, Classical.choice, Quot.sound. No sorry/admit/unsafe/custom axiom occurs in the module. Logs: .lake/campaign-evolution/02-recovery-{target,build,types,axioms}.log.

## Limitations and next obligations

This constructs scalar-valued terminal integrals of bounded predictable transforms, not a concrete semigroup multiplier on a Hilbert-valued integrand domain. Hilbert-valued convolution, nonzero-rate Mittag-Leffler forcing, Caputo existence/uniqueness, trace-class limits and sample continuity remain open. The existing zero-mode energy now supplies a direct initial-time mean-square obstruction target.

IBM remains a major pending campaign: flagship(8).tex uses two-sided scenery with covariance (|z|+|z'|-|z-z'|)/2 and reflected clock X_|Y_t|. A finite-dimensional Gaussian construction must be upgraded to jointly measurable suitable path versions before random-time composition. The bidegree atlas covers low sectors and defers full summability. Observable-domain density and local-time singular estimates remain unproved. No IBM theorem is claimed here.

Pseudoprocess work remains pending; signed kernels do not authorize probability conditional expectation. Black noise and RH excluded. No push, dependency change, source manuscript edit or unrelated document staging.

## Declaration inventory

All names below have prefix OperatorDerivativeRewrite.Foundation.StochasticKernelConvolution. and refer to Foundation/StochasticKernelConvolution.lean.
- `convolution` — line 15
- `convolution_norm` — line 18
- `convolution_inner` — line 21
- `convolution_bound` — line 25
- `convolution_pair_integrable` — line 30
- `convolution_adjoint` — line 34
- `convolution_adjoint_derivative` — line 38
- `convolution_normal` — line 45
- `convolution_zero_iff` — line 52
- `convolution_divergence_graph` — line 56
- `finiteKernel` — line 61
- `finiteKernel_apply` — line 65
- `finite_convolution_apply` — line 69
- `finite_convolution_energy` — line 76
- `convolution_operator_error` — line 92
- `convolution_tendsto_iff` — line 100
- `convolution_operator_tendsto_iff` — line 107

## Fractional forcing initial-time obstruction

Foundation/FractionalForcingObstruction.lean independently proves:
- no_higher_initial_power_bound (line 13): for alpha>1/2 and p>2alpha-1, for every real C and delta>0 there exists 0<t<delta, t<=1, such that C*t^p < ||X_t-X_0||^2 for the actual zero-generator stochasticResponse.
- no_initial_brownian_variance_bound (line 46): for 1/2<alpha<1 the same statement holds with C*t.

The proof uses the actual proved norm and zero-time identities, Gamma positivity, and continuity of t^(p-(2alpha-1)) at zero. It does not assume a scaling law or infer sample-path regularity from second moments. This disproves a uniform initial mean-square O(t^p) estimate above the true exponent in this concrete one-mode model. It does not itself disprove every almost-sure Holder assertion without a separate moment implication.

Verification: targeted Lake build passed; full build 4200 jobs; exact public types checked; full transitive audit 3132 declarations, only propext, Classical.choice, Quot.sound. Logs .lake/campaign-evolution/03-{target,build,types,axioms}.log.

Next: independent two-sided Gaussian scenery and Brownian clock coordinate families on the actual product Gaussian measure. Joint path measurability and continuous modification remain separate before IBM random-time evaluation.
