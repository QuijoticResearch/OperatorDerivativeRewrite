# Research readiness and exact next backlog — 2026-10-13

This is a partial research checkpoint, not completion of the eight-phase mission. Only exact Lean declarations identified in audit reports are verified. Manuscripts and empirical claims remain unverified.

## Campaign status

| Campaign | Verified scope | Remaining obligations |
|---|---|---|
| Fractional Gaussian | Concrete spectral kernels, exact covariance, genuine Gaussian finite-dimensional laws, completed deterministic integrands, full observable derivative/adjoint in ambient source fields, prediction counterexample, mean-square smooth Taylor bound | Continuous sample versions, causal Volterra normalization/covariance/filtration equivalence, intrinsic field range, fractional Clark-Ocone, pathwise controlled remainders |
| Gaussian curvature | Actual polynomial OU Gamma/Gamma2, finite covariance/Hadamard positivity, generalized eigenpairs, actual Wick covariance powers | Closed generator domain extension, higher iterated Gamma, complete generalized eigenbasis and fractional-time/signed interpretations |
| Fractional SPDE | Exact zero-generator forcing L2 threshold/energy/derivative; predictable scalar kernel-transform adjoints and finite-rank Gram energy; exact operator perturbation and convergence transfer; quantified initial regularity counterexample | Actual Hilbert-valued convolution domain, Mittag-Leffler convergence/Caputo identities, nonzero-rate forcing, Galerkin kernel estimates and summability, mild existence/uniqueness, paths |
| IBM foundations | Independent product Gaussian sources; two-sided scenery covariance/laws; independent Brownian-law halves and clock coordinate family | Continuous and jointly measurable source versions, random-time composition and its moments/scaling; joint bidegree source derivative; mollified scenery and actual variation/local-time calculus |
| IBM singular calculus | No model-specific singular correction theorem proved in this recovery | First-chaos projection, Stein residual, genuine nondegenerate divergence estimates, H-1 closure, observable-domain density, cross-sector limits |
| Higher-order pseudoprocess | No new theorem or ordinary probability construction claimed | Requested Level-p Clark-Ocone source absent in recursive archive search; pseudo folder empty. Signed kernel analytic domains/pairings and cylinder core must precede stochastic vocabulary |

## Precise analytic blockers and legitimate routes

1. **IBM source paths.** The current scenery/clock are measurable separately at each deterministic time and have correct finite laws. This does not prove measurability of random-time evaluation. Construct suitable continuous versions on each half-line and the clock, retain the zero-time identities and whole-family independence, then prove joint measurability and compose with absolute clock. Existing local Kolmogorov.lean supplies the condition (p,q,M); a search of the pinned Mathlib found no continuous-modification theorem. That search is evidence about available APIs, not a mathematical impossibility claim. A direct dyadic construction is a legitimate next route.
2. **Fractional SPDE kernels.** Kernel convergence is now transferred exactly by Lean, but must be proved for the independently specified Galerkin model. The nonzero-rate Mittag-Leffler series and deterministic Caputo relationship are not implemented. Whole-space convolution multiplier L2 norms do not give Hilbert-Schmidt operators on L2(R). The one-mode alpha>1/2 temporal threshold and above-exponent initial variance obstruction are actual proved restrictions.
3. **Observable derivatives.** Closedness of a pullback does not imply domain density. The fractional polynomial observable core is proved; the IBM measurable core is not. Source Sobolev membership cannot supply IBM observable measurability by assertion.
4. **Singular IBM.** FirstChaosDualClosure.tex asserts a negative-Sobolev limit after a first-chaos L2 obstruction. Neither is established here. BidegreeAtlas.tex explicitly defers complete summability. variance.tex discusses X(Y), while flagship(8).tex and FirstChaosDualClosure.tex use X(|Y|); retain this distinction before reusing formulas.
5. **Signed processes.** No probability measure, conditional expectation, martingale or positive Hilbert energy follows from a signed heat kernel. Recover the missing Level-p manuscript before auditing its claims; restricted Fourier/pairing results remain possible independently.

## Next recommended target

Construct continuous, jointly measurable versions of the already proved independent IBM source families, preserving their laws and independence. Then define reflected-clock random-time composition and prove its second moment before any Tanaka or singular-calculus claim. Start by converting the actual Gaussian increment fourth moments to an explicit compact-interval Kolmogorov estimate and constructing a dyadic modification if the pinned library lacks the required theorem.

## Readiness assessment

- **Black noise/higher interactions:** not ready to transfer Gaussian first-chaos methods; requires a separately supervised construction and scope. Not begun.
- **Signed Hurst curvature:** finite algebraic covariance results do not supply positive stochastic geometry beyond the valid Hurst range; H=2 negative-energy counterexample already exists. Signed pairing and operator-domain foundations remain.
- **Banach calculus:** existing Banach audit reports remain authoritative for their exact assumptions; Gaussian Hilbert adjoints cannot replace Banach duality or density obligations. No new Banach result claimed.
- **Further stochastic convolution/functionals:** exact bounded kernel perturbation and adjoint transfer are reusable; concrete domains, trace estimates, nonlinear products and derivative graph cores must be supplied per model.
- **Potential Mathlib contributions:** deterministic L2 spectral kernel scaling/integrability, covariance power factorization, and Gaussian kernel perturbation are candidates. Extract general lemmas, review upstream style/APIs and reduce project-specific imports before proposing upstream changes. No contribution or push made.

## Sources used

- spde/main(20261012-204518).tex and SPDE_SOURCE_AUDIT.md motivated the independently verified zero-mode threshold and initial-time obstruction; the full SPDE claims remain unverified.
- ibm/flagship(8).tex setup supplied the two-sided covariance/reflected-clock convention for the actual source-law construction.
- ibm/BidegreeAtlas.tex, FirstChaosDualClosure.tex and variance.tex supplied scope warnings and future singular/sector targets, not accepted theorems.
- Existing FRACTIONAL_GAUSSIAN_REPORT.md, GAUSSIAN_CURVATURE_REPORT.md, PAPER1_BROWNIAN_ITO_REPAIR.md and VOLTERRA_VOLATILITY_REPORT.md recover prior successful results without redoing them.

No black-noise or RH research, push, dependency change, original source edit, or unrelated-document cleanup.
