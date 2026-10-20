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

## October 20 resumed-review addendum: global simplicity (checkpoint 1159)

The latest user instruction restored A(4) review priority after the historical freeze. The historical audit above remains an exact record of b02f945; its missing global-simplicity conclusion is now superseded by `RiemannQuarticGlobalSimpleZeros.eventually_all_zeros_real_simple`. For every sufficiently late real t, EVERY complex zero of the actual quartic flow is real and has nonzero complex derivative. The proof uses one actual stationary center for the bounded disk and far complement, the existing uniform far local simplicity theorem, and derivative oddness under reflection. The exact finite-threshold interpretation is separately Lean checked.

Fresh full root build:5889 jobs; COMPLETE transitive axiom audit:35351 declarations, only the standard three axioms; all three new public types and complete proofs reviewed. Manifest1814 and all107 archive/43Incoming/11A4 manuscript hashes verified. Deferred integer-order sources/imports are excluded from this audited commit and preserved. See PROJECT_STARDUST_REPORT.md checkpoint1159 and its evidence paths.

The classical LP characterization, LP necessary-inequality bridge and final A(4) infimum statement remain outside Lean; numerical upper and optimal thresholds remain open. No RH, initial LP membership, quadratic or noninteger conclusion is added. Consult STARDUST_CAMPAIGN_QUEUE.md for the latest active priority; this historical audit does not authorize an early campaign transition.

## Resumed review: final stopping decision (checkpoint 1160)

The resumed review is COMPLETE at mathematical commit `4f36db3a5fcd68b8fc1af7033326995ab0799501`. The known global-simplicity gap has been closed and the exact finite-threshold statement checked. The core finiteness decision and actual analytic/global-zero proof chain retain the precise classical/Lean boundary above. Numerical upper/optimal thresholds and the general LP/infimum formalization remain explicitly unproved in Lean; they are not concealed assumptions or claims of this freeze.

This report-only stopping audit rechecks the unchanged full1814 source universe, fullbuild5889/audit35351/type reviews, manuscript hashes and exact private mathematical commit. Under the ordered queue, the next authorized stage is integer A(2k), A(6) first, after this stopping/report commit is privately verified. No real-exponent/limiting stage is opened. See PROJECT_STARDUST_REPORT.md checkpoint1160 and STARDUST_CAMPAIGN_QUEUE.md.


## October 20 renewed-review addendum: polynomial-limit bridge (checkpoint 1173)

The preserved historical stopping audit above is strengthened by the resumed review. RealRootedLaguerreLimit.laguerre_nonneg_of_locally_uniform_split_polynomials_on now proves the necessary Laguerre inequality for actual locally uniform complex limits of split real polynomials. RiemannQuarticPolynomialLimitObstruction.actual_time_eight_not_polynomial_limit_on applies it to the exact quartic flow on ANY open complex neighborhood containing x=632083/10000. Thus the earlier missing necessary-inequality bridge is closed for the precise polynomial-approximation property.

RiemannQuarticOpenObstruction.exists_open_time_no_polynomial_limit further excludes that property on an OPEN real time interval about8. One positive epsilon works before ALL eventual approximation starting times, which must exceed8+epsilon. polynomialLimitStarts is the actual defined set of those times. strict_infimum_lower_bound_of_nonempty proves8<sInf of that set with its nonempty hypothesis explicit. No numerical margin is claimed. Using the same previously documented EXTERNAL classical characterization to prove nonemptiness, the classical conclusion is strengthened to8<A(4)<infinity. Lean now verifies the lower approximation exclusion and conditional strict infimum; the converse factorization/classification and resulting unconditional nonemptiness/finite threshold remain outside Lean. Historical weaker bounds are retained as historical statements, not silently promoted to stronger formal claims.

Fullbuild5918, complete root axiom audit35725 standard3, all15 public types/one definition/three complete sources read, independent repeated-root and nonreal-root checks passed, manifest1843 and107archive/43Incoming/11A4 hashes preserved. See PROJECT_STARDUST_REPORT.md checkpoint1173 for exact names, domains, quantifiers and evidence. This is an audited mathematical extension during A(4) review, not a new stopping or transition decision. The authoritative queue still requires A(4) review before pending integer work; real-exponent/limit/A(2)/final multichannel stages remain unopened.


## Renewed review: stopping decision (checkpoint 1174)

The renewed A(4) review is COMPLETE/FROZEN at mathematical commit `cf903f8b52eb0037e4416aad0e62cff276c5f45c`. This preserves the actual global reality/simplicity theorem and closes the necessary polynomial-limit lower bridge, including a positive open-time exclusion and a conditional strict infimum lower bound. The classical conclusion is now **8 < A(4) < infinity**. The general converse LP factorization/classification and resulting unconditional nonemptiness/finite threshold are still outside Lean. Numerical margin/upper/optimal thresholds and initial LP membership remain unproved; no RH implication is claimed.

The classical source was checked anew at [Nguyen and Vishnyakova, Section1.1](https://link.springer.com/article/10.1007/s40879-023-00723-z), Definition1.2, TheoremA(ii) and its following order-below-two paragraph. Its general characterization applies to nonzero real entire functions; it does not inherit the positive-coefficient restrictions of that paper's later results. The literal manuscript tilt/normalization/threshold definition and hash were rechecked. See PROJECT_STARDUST_REPORT.md checkpoint1174 for the full hypothesis match and formal stopping boundary.

All1843 source bytes match the5918-job full build and35725-declaration complete standard-three-axiom audit. Source-critical public types/definition were reread; archive107/Incoming43/A4eleven hashes preserved; the mathematical commit was privately verified before this decision. No Lean changes occur in this report/instruction-only checkpoint. After its own exact private backup, the authorized active stage is integer A(2k), A(6) first, reusing all preserved audited results. Real exponents/limit/A(2)/final multichannel stay gated; October31 remains the hard stop.


## Active resumed review: zero-free rigidity (checkpoint1179; NOT a new stopping decision)

The latest human instruction reopened A(4) review at1178. The historical freezes and all audited mathematics above remain preserved. The new EvenEntireZeroFreeRigidity proves constancy for even entire zero-free functions with the specific quartic bound C exp(|z|sqrt(|z|)), using an entire logarithm, Borel-Caratheodory and second-order Schwarz. The actual quartic transform is strictly larger at i than at0 for every real t; hence it is nonconstant and now has a verified complex zero at every real t. No early-time zero location or RH implication follows.

The explicit exp(z^2) counterexample is entire/even/zero-free with quadratic growth, but fails locally uniform approximation by split real polynomials. Thus one must retain the strict growth hypothesis in the missing converse. A global zero product, its locally uniform partial-product convergence and the actual quotient/remainder growth bound remain unconstructed. In particular, no growth bound for an entire quotient follows merely from that of its numerator. Actual starting-time nonemptiness and unconditional Lean finiteness remain open; the classical8<A(4)<infinity boundary is unchanged. Full verification and exact names are in PROJECT_STARDUST_REPORT.md checkpoint1179. This checkpoint keeps A(4) ACTIVE and does not open queued campaigns.
