# Project Stardust — OperatorDerivativeRewrite

Stardust develops mathematical constructions and repairs research claims in
Lean: operator domains and adjoints, Gaussian calculus, signed higher-order
heat pseudoprocesses, actual iterated Brownian motion (IBM), and arithmetic
Fourier/Xi flows. Manuscript assertions are research questions until proved.
Counterexamples and precise unresolved obligations are research results too.

The project favors transparent, reproducible and reusable mathematics, with
proofs and domains available for inspection and future sharing. The working
GitHub archive remains **private**. This public-facing overview neither
publishes it nor changes licensing or permissions for preserved manuscripts.
Retain upstream license/attribution notices; license material is in LICENSES/.

Start with the [mathematical blueprint](STARDUST_BLUEPRINT.md),
[commentary and opportunities](STARDUST_MATHEMATICAL_COMMENTARY.md), or
[authoritative research queue](STARDUST_CAMPAIGN_QUEUE.md).
The [research ledger](PROJECT_STARDUST_REPORT.md) records exact findings and
audit evidence. The [early README](docs/FOUNDATION_OVERVIEW_LEGACY.md) is preserved
as a historical foundation overview; its old open-problem labels are not current.

## Selected verified mathematics

Names below have prefix `OperatorDerivativeRewrite.Foundation.`. These are
curated for substance, not a release or commit chronology. Consult the linked
types and detailed scopes before reuse.

| Result | Exact Lean declaration(s) | Scope and detailed evidence |
|---|---|---|
| Closed operator-adjoint foundation | `operatorDerivative_isClosed`; `operatorDerivative_adjoint_identity` | Dense divergence domain required; both actual domains appear in the identity. [Source](Foundation/Adjoint.lean), [audit](MATHEMATICAL_AUDIT.md). |
| Gaussian derivative/divergence identification | `GaussianCore.closedDerivative_eq_divergence_adjoint`; `GaussianCore.closedDivergence_eq_derivative_adjoint` | Actual one-coordinate Gaussian operators, with finite Hermite graph approximations; no automatic transfer to arbitrary processes. [Source](Foundation/GaussianHermiteAdjoints.lean), [spectral domains](Foundation/GaussianHermiteDomains.lean). |
| Full signed p-1-channel Clark–Ocone on a specified completed domain | `HigherHeatCompletedClarkOcone.clark_ocone`; `HigherHeatSignedDiagonalRealization.completed_signed_realization` | All completed analytic-cylinder observables, positive even order/horizon; equality in the test dual, with actual signed approximation. No positive pseudo-L2 isometry or probability-path law. [Stopping contract](STARDUST_PSEUDOPROCESS_STOPPING_AUDIT.md). |
| Genuine IBM correction limits and native derivative foundation | `IBMDilatedPredictableLimit.correction_continuum_tendsto`; `IBMCompactOriginalBoundary.originalPathIntegral_continuum_tendsto`; `IBMJointIntrinsicDerivative.jointDerivative_dense` | F1 uses its clock-number common-dual topology; F2 is ordinary clock L2; the genuine joint native derivative is closed/densely defined. These are not full physical-time Ito calculus. [Exact F1–F3 scope](IBM_F1_F3_VERIFIED_CHECKPOINT.md). |
| Actual stochastic change of integrator and full product associativity | `IBMStochasticIntegratorEnergy.energy_change`; `IBMStochasticProductAssociativity.actual_associativity`; `IBMCompletedBoundedAssociativity.actual_bounded_associativity` | Entire ORIGINAL output-energy L2 domain; literal HK product, correct null ideals, and bounded common predictable action on every completed family. [Audit](IBM_INTEGRATOR_ENERGY_PRODUCT_ASSOCIATIVITY_AUDIT.md). |
| Uniform actual IBM reconstruction and original divergence graph convergence | `IBMUniformStochasticReconstruction.actual_IBM_uniform`; `uniform_actual`; `uniform_native_graph` | Compact-parameter uniform L2 and original graph norm, simultaneously over all causal horizons. This is not L2 of a samplewise supremum or temporal-gradient Clark–Ocone. [Audit](IBM_UNIFORM_STOCHASTIC_RECONSTRUCTION_AUDIT.md). |
| Actual quartic theta-flow eventual global real zeros | `RiemannQuarticUniformFarScale.eventually_all_zeros_real` | Every complex zero is real at every sufficiently late time of the genuine growing quartic integral. Local/far estimates share one scale. No RH implication is inferred. [Source](Foundation/RiemannQuarticUniformFarScale.lean), [full stopping scope](A4_CAMPAIGN_STOPPING_AUDIT.md). |

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
source/manuscript hashes, Git checkpoint and verified private backup.
The early Foundation/AxiomAudit module is not a substitute for that complete
root audit. No sorry, new mathematical axioms or suppressed errors are allowed.

Lean declarations with conditional hypotheses remain conditional. A general
operator identity is not an instantiated stochastic theorem until its actual
process, domains, measurability and convergence requirements are discharged.
ResearchSources is read-only and excluded from research commits.

## Research and exposition

**Active:** intrinsic stochastic calculus for actual IBM. Physical-time
Ito–Tanaka, pathwise variation/brackets and temporal-gradient representation
remain open outside the exact verified scopes above. Subsequent campaigns
remain gated by the authoritative queue; documentation does not release them.

[Periodic reflection](STARDUST_REFLECTION_POLICY.md) is supporting work at
natural verified checkpoints, capped at45minutes per local day total. It
preserves mathematical experience, records precise cross-library opportunities,
and maintains this overview, the blueprint and focused [paper drafts](docs/papers/IBM_STOCHASTIC_ASSOCIATIVITY_DRAFT.md).
No novelty, publication readiness, Millennium Prize solution or RH progress
is claimed merely from the size of the library.
