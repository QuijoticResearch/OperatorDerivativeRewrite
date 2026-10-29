# Project Stardust — OperatorDerivativeRewrite

Stardust develops mathematical constructions and repairs research claims in
Lean: operator domains and adjoints, Gaussian calculus, signed higher-order
heat pseudoprocesses, actual iterated Brownian motion (IBM), and arithmetic
Fourier/Xi flows. Manuscript assertions are research questions until proved.
Counterexamples and precise unresolved obligations are research results too.

The project favors transparent, reproducible and reusable mathematics, with
proofs and domains available for inspection and future sharing. The GitHub repository is **public by the owner's decision**. This overview does
not change repository visibility, licensing, or permissions for preserved originals.
Retain upstream license/attribution notices; license material is in LICENSES/.

Start with the [mathematical blueprint](STARDUST_BLUEPRINT.md),
[commentary and opportunities](STARDUST_MATHEMATICAL_COMMENTARY.md), or
[authoritative research queue](STARDUST_CAMPAIGN_QUEUE.md).
The [research ledger](PROJECT_STARDUST_REPORT.md) records exact findings and
audit evidence. The [early README](docs/FOUNDATION_OVERVIEW_LEGACY.md) is preserved
as a historical foundation overview; its old open-problem labels are not current.

## Readable papers

The [manuscript catalog](manuscripts/INDEX.md) groups twenty-five reviewed drafts (253 pages) by mathematical subject. Every paper has complete human proofs, a compiled and visually inspected PDF, and exact Lean declaration/commit links in its theorem map. The [whole-library survey](manuscripts/LIBRARY_SURVEY.md) inventories all 2,795 frozen Foundation modules and distinguishes that module-level coverage from detailed paper-specific proof review.

| Mathematical story | Readable papers |
|---|---|
| Arithmetic transforms and global zero geometry | [Fractional endpoint/nonreal zeros](manuscripts/fractional-theta-zeros/main.pdf), [attained quartic eventual threshold](manuscripts/quartic-threshold/main.pdf), [sixth-order global reality and general even-order windows](manuscripts/sixth-order-zeros/main.pdf). Exact order/time/zero quantifiers; no RH implication. |
| Higher-order signed calculus and complex approximations | [Completed signed multichannel reconstruction](manuscripts/signed-multichannel/main.pdf), [analytic complex-root limits and compact escape](manuscripts/complex-root-limits/main.pdf). Test domains, signed pairing and probability/variation limits are explicit. |
| Actual reflected-clock Brownian calculus | [Clock regularity and original hybrid adjoints](manuscripts/ibm-clock-hybrid/main.pdf), [Observable-martingale energy and completed associativity](manuscripts/ibm-stochastic-associativity/main.pdf), [quartic variation and spatial/time–space Simpson proofs](manuscripts/ibm-spatial-calculus/main.pdf), [clock-domain exclusions and critical noise/chaos energy](manuscripts/ibm-clock-domain/main.pdf), [native time averages and fixed-past adjoint differentiation](manuscripts/ibm-average-time/main.pdf). Source-valued dual limits do not assert a completed physical-time Ito/Clark–Ocone calculus. |
| Nonlinear analysis and finite moments | [Quartic normal-map existence and sharp inverse regularity](manuscripts/quartic-normal/main.pdf), [Gaussian–cubic truncated moment boundaries](manuscripts/cubic-moment-boundaries/main.pdf). Exact domains, null-boundary realization gaps and independent algebra/certificate checks are retained. |
| Gaussian prediction, forcing and nonlocal semigroups | [Completed quadratic products and sharp moment/contraction tests](manuscripts/gaussian-quadratic-products/main.pdf), [Poisson–Gaussian graphs, jump curvature and nonlinear limits](manuscripts/poisson-gaussian-transport/main.pdf), [Gaussian forcing trace and recovery geometry](manuscripts/gaussian-forcing-trace/main.pdf), [Hermite-rank prediction and inverse-number smoothing](manuscripts/gaussian-prediction-rank/main.pdf), [Fourier positivity, actual torus laws and Poisson atoms](manuscripts/fourier-positivity/main.pdf), [Cauchy circle kernel, generator and entropy](manuscripts/cauchy-circle-entropy/main.pdf). Classical antecedents and exact prediction/operator/density hypotheses are recorded. |
| Brownian time changes | [Sticky clocks and balanced Brownian couplings](manuscripts/sticky-clock-recovery/main.pdf). Actual supported mass, inverse-clock holding transport, causal observed-clock recovery and full Brownian coordinate increment laws. |
| Finite gauge transfers | [Pinned one-sided boundary Schur gap and exact certificate](manuscripts/one-sided-schur-gap/main.pdf), [Retained boundary entropy and replacement-kernel decay](manuscripts/conditional-boundary-entropy/main.pdf), [Gauge-invariant seven-link slow modes](manuscripts/seven-link-transfer/main.pdf). Proved ground existence, actual centered stationary covariance, fixed-step persistence and finite-parameter mixing; no physical mass-gap claim. |
| Fluid calibration | [Triad information, original Gaussian gradients and dephasing](manuscripts/gaussian-triad-information/main.pdf), [Fourier-cone reality and explicit Hermitian interaction](manuscripts/cone-pairing-diagnostics/main.pdf), [Strain, pressure and angular-ratio tests](manuscripts/strain-pressure-tests/main.pdf). Nonnormal restricted-Euler geometry, local infinite-energy affine fields, trace conventions a smooth periodic viscous ABC counterexample, and a full infinite-spectrum shear angular-ratio reversal retain their distinct hypotheses. |

These are reviewed drafts, not external releases. Novelty and attribution review remain unresolved; several papers are explicitly classical formalization companions or diagnostic notes. The [editorial assessment](manuscripts/EDITORIAL_INVENTORY.md) records significance, consolidation choices and remaining issues. Earlier IBM working notes are preserved separately in the catalog.

## Selected verified mathematics

Names below have prefix `OperatorDerivativeRewrite.Foundation.`. These are
curated for substance, not a release or commit chronology. Consult the linked
types and detailed scopes before reuse.

| Result | Exact Lean declaration(s) | Scope and detailed evidence |
|---|---|---|
| Closed operator and Gaussian-adjoint foundations | `operatorDerivative_adjoint_identity`; `GaussianCore.closedDerivative_eq_divergence_adjoint`; `GaussianCore.closedDivergence_eq_derivative_adjoint` | Exact original domains and density/graph hypotheses; the Gaussian identification uses actual Hermite approximation. [Operators](Foundation/Adjoint.lean), [Gaussian source](Foundation/GaussianHermiteAdjoints.lean). |
| Full signed p-1-channel Clark–Ocone on a specified completed domain | `HigherHeatCompletedClarkOcone.clark_ocone`; `HigherHeatSignedDiagonalRealization.completed_signed_realization` | All completed analytic-cylinder observables, positive even order/horizon; equality in the test dual, with actual signed approximation. No positive pseudo-L2 isometry or probability-path law. [Stopping contract](STARDUST_PSEUDOPROCESS_STOPPING_AUDIT.md). |
| Genuine IBM correction limits and native derivative foundation | `IBMDilatedPredictableLimit.correction_continuum_tendsto`; `IBMCompactOriginalBoundary.originalPathIntegral_continuum_tendsto`; `IBMJointIntrinsicDerivative.jointDerivative_dense` | F1 uses its clock-number common-dual topology; F2 is ordinary clock L2; the genuine joint native derivative is closed/densely defined. These are not full physical-time Ito calculus. [Exact F1–F3 scope](IBM_F1_F3_VERIFIED_CHECKPOINT.md). |
| Actual stochastic change of integrator and full product associativity | `IBMStochasticIntegratorEnergy.energy_change`; `IBMStochasticProductAssociativity.actual_associativity`; `IBMCompletedBoundedAssociativity.actual_bounded_associativity` | Entire ORIGINAL output-energy L2 domain; literal HK product, correct null ideals, and bounded common predictable action on every completed family. [Audit](IBM_INTEGRATOR_ENERGY_PRODUCT_ASSOCIATIVITY_AUDIT.md). |
| Uniform actual IBM reconstruction and original divergence graph convergence | `IBMUniformStochasticReconstruction.actual_IBM_uniform`; `uniform_actual`; `uniform_native_graph` | Compact-parameter uniform L2 and original graph norm, simultaneously over all causal horizons. This is not L2 of a samplewise supremum or temporal-gradient Clark–Ocone. [Audit](IBM_UNIFORM_STOCHASTIC_RECONSTRUCTION_AUDIT.md). |
| Physical IBM variation and raw-channel obstruction | `IBMUniformQuarticVariation.quartic_tendstoInMeasure`; `IBMActualQuadraticDivergence.quadratic_lower_tail`; `first_no_finite_limit` | For actual Z=W(abs B), all uniform N-cell grids: quartic variation tends to 3T in probability, quadratic variation diverges, and raw first/second ranks cannot separately have finite probability limits. [Source](Foundation/IBMActualQuadraticDivergence.lean). |
| Actual time–space Simpson and continuous-path calculus | `IBMTimeSpaceSimpson.sums_tendstoInMeasure`; `IBMUniformTimeSpace.maximum_tendstoInMeasure`; `IBMContinuousSimpsonRealization.approximation_tendstoInMeasure` | Deterministic C1-time/C4-space F with explicit joint continuity hypotheses; probability limits, grid-prefix maximum, and Bernstein continuous-path supremum-norm convergence. Bernstein smoothing is not asserted causal. Clipped graph-dual realization retains the sine strong-domain obstruction. [Revised draft](manuscripts/ibm-signed-simpson/main.pdf). |
| Original native Hilbert obstruction and genuine tested limits | `IBMNativeWeakObstruction.no_original_weak_subsequence`; `IBMFourierCylinderSeries.native_tendsto`; `source_native_tendsto` | Specified positive-horizon native outputs have no weak intrinsic Hilbert subsequence. Curvature-summable Fourier source-lowered actions nevertheless converge in clock L2/L1. This is an action limit, not observable reconstruction. [Obstruction](Foundation/IBMNativeWeakObstruction.lean), [tested calculus](Foundation/IBMFourierCylinderSeries.lean). |
| Actual multitime mean graph and hybrid reconstruction | `IBMFourierClockGraph.multitime_clock_graph`; `IBMFourierClockClarkOcone.projected_actual_derivative`; `IBMFourierHybridReconstruction.reconstruction` | Folded/collision gradients in the ORIGINAL clock graph; finite-horizon hidden-clock Clark–Ocone and original joint divergence reconstruction with a STATIC source channel. Observed-IBM-filtration causality remains open. [Ten-page proof companion](manuscripts/ibm-clock-hybrid/main.pdf). |
| Actual quartic theta-flow eventual global real zeros | `RiemannQuarticUniformFarScale.eventually_all_zeros_real` | Every complex zero is real at every sufficiently late time of the genuine growing quartic integral. Local/far estimates share one scale. No RH implication is inferred. [Source](Foundation/RiemannQuarticUniformFarScale.lean), [full stopping scope](A4_CAMPAIGN_STOPPING_AUDIT.md). |
| Physical Haar-L2 positivity has a sharp active-axis threshold | `PhysicalHeatPositiveCone.anisotropic_physical_positive_iff_active` | For nonnegative axis weights and positive exponents, the completed physical Haar-L2 evolution preserves the real nonnegative cone for every nonnegative time exactly when every positively weighted exponent is at most two. Finite-core Gamma, transition laws and countable-step chains are also verified; closed pointwise Gamma domains and continuous-time paths remain open. [Source](Foundation/PhysicalHeatPositiveCone.lean), [paused-objective scope](STARDUST_BAKRY_OBJECTIVE2_PAUSE.md). |

## Verification and reproducibility

The pinned environment is Lean `leanprover/lean4:v4.34.1` with exact Mathlib
revision `d13f23b723b8a846827a245b89c10fc7d3f11612` in lake-manifest.json.
From a checkout with the pinned dependencies installed, the complete root build is:

```text
lake build
```

Read [the permanent build policy](STARDUST_BUILD_OPTIMIZATION.md) for measured
commands, cache strategy and full verification gates. Milestones require a
complete transitive `Lean.collectAxioms` audit of every safe Foundation
declaration, accepting only `propext`, `Classical.choice` and `Quot.sound`, plus
actual unabridged theorem-type/proof review, meaningful independent checks,
source/manuscript hashes, Git checkpoint and verified two-branch backup.
The early Foundation/AxiomAudit module is not a substitute for that complete
root audit. No sorry, new mathematical axioms or suppressed errors are allowed.

Lean declarations with conditional hypotheses remain conditional. A general
operator identity is not an instantiated stochastic theorem until its actual
process, domains, measurability and convergence requirements are discharged.
ResearchSources is read-only and excluded from research commits.

## Research and exposition

**Active:** focused Yang–Mills audit. Bakry–Émery Objective 2 is paused,
Objective 1 and intrinsic IBM remain incomplete at preserved checkpoints.
The finite SU(2) closed-cycle conditional law is verified; a gauge-covariant
block transfer and continuum-uniform connected-correlation estimate remain open.
Subsequent campaigns remain gated by the authoritative queue; this overview
does not change their order.

[Periodic reflection](STARDUST_REFLECTION_POLICY.md) remains the researcher's supporting workflow. Independent publication work is maintained on its own publication branch under the owner's editorial instructions, using frozen verified commits and preserving the research checkout and internal policies.
No novelty, publication readiness, Millennium Prize solution or RH progress
is claimed merely from the size of the library.
