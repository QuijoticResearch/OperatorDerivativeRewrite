# A(4) campaign: frozen stopping audit

October 20, 2026. Frozen mathematical commit: `b02f945f6f1f8714f877c9c3717bc0578b7ae3dd`.

The campaign determines **classically** that `8 <= A(4) < +infinity` for the archive's eventual Laguerre–Pólya threshold. The actual integral, global zero theorem and analytic hypotheses are Lean verified. The final classical Laguerre–Pólya characterization and infimum statement are **not themselves formalized in Lean**. This boundary is part of the result, not an implicit additional axiom.

## Exact object and threshold

The object is the growing quartic cosine transform

\[
H_{t,4}(z)=\int_0^\infty e^{tu^4}\Phi(u)\cos(zu)\,du,
\qquad
\Phi(u)=\sum_{n\ge1}(2\pi^2 n^4e^{9u}-3\pi n^2e^{5u})e^{-\pi n^2e^{4u}}.
\]

`RiemannQuarticKernel.kernel`, `RiemannQuarticDomain.weighted` and `RiemannQuarticEvolution.flow_eq_cosine_integral` implement this same kernel, positive time sign and half-line normalization. The theta-moment indexing `n+1` runs over the positive integers. The source definition is `ResearchSources/a4/ibm_laguerre_polya.tex`, lines 521–534. Its SHA256 is `EAF31754F5F993EF8EB33A1917484D70F6B62F5B37A907AD85F097C3C5589D96`.

The archive defines `A(4)` / `Lambda(4)` as the infimum of real starting times `T` such that **every** `t >= T` has `H_{t,4}` in the Laguerre–Pólya class. A single time, subsequence, finite zero window or generic polynomial is insufficient.

## Verified theorem chain

All declaration names below have prefix `OperatorDerivativeRewrite.Foundation.`.

| Obligation | Exact declaration / source | Audited conclusion |
|---|---|---|
| Genuine domain and entire flow | `RiemannQuarticDomain.weighted_integrable`; `RiemannQuarticFlow.flow_differentiable` | Actual integrals exist for all real times and complex frequencies; flow is entire. |
| Reality and nontriviality | `RiemannQuarticReality.flow_im_zero`; `flow_ne_zero_on_imaginary_axis` | Real on the real axis and nonzero at zero for every real time. |
| Finite-time obstruction | `RiemannQuarticLaguerreWitness.actual_real_derivative_negative` | At `t=8`, `x=632083/10000`, the actual Laguerre expression is below `-2/10^20`. Infinite integrals and derivatives, not sampled numerical substitutes. |
| Actual transition phases | `RiemannQuarticTransitionAnalyticBranch.exists_actual_transition_phase`; `RiemannQuarticTransitionGaussianPhase.phaseSlope_model_bound` | Coherent actual saddle branches and quantitative exact arithmetic/Gaussian amplitude phases. |
| Actual signed paired approximation | `RiemannQuarticTransitionComplexPairing.eventually_uniform_complex_pair_error`; `RiemannQuarticTransitionCosinePhase.eventually_actual_cosine_disks` | Full actual-flow cosine error; unequal-height vertical residual is retained and bounded. |
| Exact transition zero control | `RiemannQuarticTransitionSimpleZeros.bounded_ratio_real_simple_zeros` | For each fixed `M`, all zeros in the complex disk `norm(z) <= M B(u)` are exactly real and simple at late times, with arbitrarily large actual stationary centers. |
| Uniform far matching | `RiemannQuarticUniformFarScale.stationary_far_cubic_scale`; `uniform_actual_far_saddles`; `uniform_far_zeros_real` | Explicit cutoff `exp(64) B(u)` constructs actual far saddle data uniformly in time and frequency. Outer zero control starts at `2 exp(64) B(u)`. |
| GLOBAL eventual zero reality | `RiemannQuarticUniformFarScale.eventually_all_zeros_real` | There exists a finite real `T` such that for every `t >= T`, every complex zero is real. No frequency restriction or unproved model hypothesis. |
| Actual growth | `RiemannQuarticEntireGrowth.exists_three_halves_growth` | For every real `t`, there is a positive `C_t` with `norm(H_t(z)) <= C_t exp(norm(z)^(3/2))` for all complex `z`. |
| All classification hypotheses | `RiemannQuarticEntireGrowth.eventually_real_entire_nonzero_subquadratic` | One theorem packages real-entire, nonzero, explicit subquadratic growth and globally real zeros for every sufficiently late time. |

Here `B(u)=4 pi exp(4u)`. The matching uses the **fixed** constant `M=2 exp(64)`. The same actual stationary center covers the bounded disk and its entire complement. It does not exchange a fixed-time large-frequency limit with a late-time limit. The separate finite-threshold interpretation check is `.lake/stardust-1155-finite-threshold-check.lean`; it checks the unrestricted `exists T, forall t >= T, forall z` conclusion and prints only the standard three axioms.

## Classical deduction and precise formal boundary

The growth estimate implies entire order at most `3/2`, strictly below two: the maximum modulus is bounded by `C_t exp(r^(3/2))`, and the defining logarithmic growth quotient has limsup at most `3/2`. Real symmetry and nontriviality are already verified. At every late time the global zero theorem therefore meets every hypothesis of the classical real-entire Laguerre–Pólya characterization. Hence there is a finite `T` for which **all subsequent** transforms belong to that class.

The characterization and polynomial-limit description are recorded in [Nguyen and Vishnyakova, *Hutchinson's intervals and entire functions from the Laguerre–Pólya class*, European Journal of Mathematics 10, article 10 (2024), Section 1.1](https://doi.org/10.1007/s40879-023-00723-z), Definition 1.2, Theorem A and the paragraph following Theorem A. The source was checked again at the stopping audit. This is established external mathematics, not a new Lean axiom or a disguised definition.

For a real-rooted polynomial, the Laguerre expression is nonnegative on the real axis, by the logarithmic derivative formula away from zeros and continuity at zeros. Locally uniform polynomial approximation to an LP function implies local convergence of derivatives by Cauchy's formula, preserving that inequality. The verified negative expression at `t=8` therefore excludes LP membership at that time. Every admissible eventual starting time is greater than eight. The set of starting times is consequently nonempty and bounded below by eight, so its infimum satisfies `8 <= A(4) < +infinity`.

**Not formalized here:** the general LP predicate/characterization, the relevant entire-order/factorization theory, the LP necessary-inequality bridge and the final infimum statement as a Lean declaration. The Lean result is the actual zero theorem and all analytic hypotheses above. The classical application is a rigorous mathematical deduction with an explicit boundary. No `axiom`, admission or altered manuscript supplies it. Rebuilding general Hadamard factorization is not required to resolve the campaign's classical finiteness question and is outside this focused stopping point.

## Limitations preserved at the freeze

- No numerical upper time or optimal threshold is obtained. Equality at the lower endpoint is not decided.
- The global theorem states reality; global simplicity has not been packaged as a final declaration. Simplicity is verified in every fixed bounded-ratio region and in the stated far-frequency domains.
- The finite `t=8` nonmembership and eventual membership do not assume membership at `t=0`. Initial membership would require the appropriate RH statement; it is not inferred.
- No relation between the quartic and quadratic thresholds, RH implication, arbitrary-order result, real-exponent interpolation or limiting real-rootedness is asserted.
- No novelty claim or comprehensive priority claim is made. Other manuscript conjectures remain unverified unless separately identified in the research ledger.

## Verification and preservation

The frozen commit passed the pinned **full root build: 5,888 jobs**, and the **complete root transitive axiom audit: 35,347 declarations**, using only `propext`, `Classical.choice` and `Quot.sound`. Every newly introduced public type and definition body at the mathematical checkpoints was actually reviewed. The final eight public types and the global finite-threshold interpretation were reread for this stopping audit, along with the actual `t=8` witness and classification source.

At the stopping audit all **1,813 Foundation/root sources** were rehashed and matched the frozen manifest byte for byte. All **107 archive files**, **43 Incoming files / 42 distinct hashes**, and **11 fully read A4 manuscripts** retained their recorded hashes. The original all-file A4 review preceded new A4 proofs. No manuscript, dependency, unrelated draft or mathematical source is changed by this stopping/report checkpoint.

Evidence: `.lake/stardust-1156-full-build.log`, `.lake/stardust-1156-audit.log`, `.lake/stardust-1156-public-types.json`, `.lake/stardust-1156-working-checkpoint.json`, `.lake/stardust-1157-final-a4-audit.json`. Reusing the successful build/audit here is justified by the independently checked identical complete source universe; a sync receipt is not substituted for either check. The mathematical commit was verified on PRIVATE remote `main` and the research branch before the queue transition. The stopping/report commit receives its own exact-commit receipt and private verification.

## Authorized next campaign

A(4) is **FROZEN at this verified stopping point**. The next authorized campaign is integer **A(2k), k >= 2**, using A(4) as the verified base and **A(6) first**, beginning with theorem-level and source/literature audits. Real exponents remain gated on a coherent reusable integer theorem; their `k -> 1+` study and independent A(2) remain afterward, followed by the final multichannel campaign. October 31, 2026 remains the hard stop. No new research campaign is authorized.
