# Focused IBM campaign state — 2026-10-13

Initial verified HEAD: 473ced866318727d4fc372410aee7c6210415048. Working tree initially contained the same twelve unrelated untracked documents and no tracked changes.

Verified incoming foundation: IBMSourceLaws has actual independent scenery and clock coordinate families, exact two-sided covariance, Brownian finite-dimensional laws on both scenery halves and clock, and independence. The families are not yet continuous or jointly measurable in time/sample.

Active: prove continuous-path composition under explicit independently stated measurable path maps, and prove that genuine coordinate modifications with continuous paths yield measurable path maps and preserve laws. Exact-time path modification existence remains an analytic obligation; no path is defined by asserting continuity.

Pending: construct such modifications from verified Brownian coordinate laws; actual IBM random-time composition on them; conditional mixture, moments, covariance and scaling; mollified scenery; local-time Ito-Tanaka; first-chaos singular infrastructure. Manuscript statements remain UNVERIFIED until proved in Lean.

Preservation: no source manuscript edits, dependency changes, unrelated-document staging, reset or push. Every accepted milestone requires target compilation, full build, explicit types, transitive axiom audit with only propext/Classical.choice/Quot.sound, mathematical scope report, and commit.

## Conditional continuous IBM composition milestone

`Foundation/IBMContinuousComposition.lean` supplies an actual pointwise process on the product `SampleSpace × SampleSpace` from independently supplied measurable path-valued maps `X : SampleSpace → C(ℝ,ℝ)` and `Y : SampleSpace → C(ℝ≥0,ℝ)`. `path` is the continuous path t ↦ X(ωX)(|Y(ωY)(t)|); `value` is its evaluation. It proves pointwise path continuity, one-time measurability, joint time/sample measurability, independence of the entire supplied source paths on the actual product measure, and the zero-time identity when supplied paths vanish at zero. The assumptions are exactly path-map measurability, with optional zero values; no IBM law or moment is smuggled into the definitions.

`Foundation/IBMModificationBridge.lean` proves that a coordinate family with continuous sample paths and measurable deterministic-time coordinates defines a measurable `C(ℝ,ℝ)` or `C(ℝ≥0,ℝ)` random path. When each coordinate is an actual a.e. modification of `IBMSourceLaws.sceneryBase` or the verified `GaussianTimeProcess.process`, the new path keeps the one-time source law. The resulting scenery and clock path-valued variables are independent on the actual product measure. The module does not assert that these continuous modifications already exist; construction from the incoming Gaussian coordinate sources remains the central analytic obligation.

Target builds passed for both modules. Full Lake build: 4205 jobs. All 18 new public declarations have explicit type checks. Complete transitive axiom audit: 3171 declarations, exactly propext, Classical.choice, Quot.sound. Logs `.lake/campaign-ibm/02-*` and `03-*`. No prior theorem body, original manuscript or dependency pin changed.

### Exact declaration locations

Names have prefix `OperatorDerivativeRewrite.Foundation.`.
- `Foundation/IBMContinuousComposition.lean`:
  - `IBMContinuousComposition.path` — line 17
  - `IBMContinuousComposition.value` — line 21
  - `IBMContinuousComposition.path_continuous` — line 23
  - `IBMContinuousComposition.value_eq` — line 26
  - `IBMContinuousComposition.sources_independent` — line 29
  - `IBMContinuousComposition.value_measurable` — line 34
  - `IBMContinuousComposition.path_measurable` — line 42
  - `IBMContinuousComposition.value_jointly_measurable` — line 47
  - `IBMContinuousComposition.value_zero` — line 52
- `Foundation/IBMModificationBridge.lean`:
  - `IBMModificationBridge.sceneryPath` — line 13
  - `IBMModificationBridge.clockPath` — line 16
  - `IBMModificationBridge.sceneryPath_measurable` — line 19
  - `IBMModificationBridge.clockPath_measurable` — line 23
  - `IBMModificationBridge.sceneryPath_apply` — line 28
  - `IBMModificationBridge.clockPath_apply` — line 31
  - `IBMModificationBridge.scenery_modified_law` — line 35
  - `IBMModificationBridge.clock_modified_law` — line 44
  - `IBMModificationBridge.modified_sources_independent` — line 52

## Gaussian mixture and source-moment milestone

`Foundation/IBMConditionalMixture.lean` proves the actual scenery factor's centered Gaussian marginal `sceneryBase_gaussian_law`. Given an explicitly supplied continuous scenery modification `S` with deterministic-time a.e. equality to that factor, `sceneryPath_gaussian_law` and `conditional_event` prove that for each fixed clock sample the composed coordinate has centered Gaussian law with variance `|C t ωY|`. Given measurable coordinates for both supplied continuous modifications, `mixture_event` proves the exact event-law mixture over the clock factor using product-measure Fubini. It does not establish that such modifications exist.

`Foundation/IBMSourceMoments.lean` proves the actual first-chaos fourth moment and fourth-moment increment identities for the two-sided scenery and Brownian clock. These are inputs for a continuous-modification argument, not themselves continuity. `Foundation/IBMConditionalMoments.lean` proves the centered Gaussian second moment and, for each fixed clock sample under the same scenery-modification hypothesis, conditional mean zero and conditional second moment `|C t ωY|`.

Target builds, exact checks of all 10 new public statements, full Lake build (4208 jobs), and complete transitive axiom audit (3181 declarations, only propext/Classical.choice/Quot.sound) pass. Logs `.lake/campaign-ibm/04-*`, `05-*`, `06-*`. Existing source bodies, manuscripts and dependency pins were unchanged. Central open obligation: construct continuous modifications from `IBMSourceLaws` coordinate processes; thereafter prove actual IBM path construction, covariance, scaling and mollified calculus. No unconditioned IBM path or Ito–Tanaka claim is made.

### New declaration locations

- `Foundation/IBMConditionalMixture.lean`: `sceneryBase_gaussian_law` (16), `sceneryPath_gaussian_law` (32), `conditional_event` (40), `mixture_event` (51).
- `Foundation/IBMSourceMoments.lean`: `firstChaos_fourth` (17), `sceneryBase_increment_fourth` (30), `clockBase_increment_fourth` (54).
- `Foundation/IBMConditionalMoments.lean`: `gaussian_zero_second` (14), `conditional_mean` (25), `conditional_second` (35).

## Conditional covariance milestone

`Foundation/IBMConditionalCovariance.lean:27` proves the exact two-time covariance of the composed scenery at any fixed clock sample: `( |C_s| + |C_t| - ||C_t|-|C_s|| )/2`. It uses the actual two-sided source covariance and deterministic-time a.e. modification equality; no sign restriction on the clock values is imposed. The source modification remains an explicit hypothesis. Full Lake build 4209 jobs, 3182 transitive axiom checks with only propext/Classical.choice/Quot.sound, and exact theorem type check passed. Logs `.lake/campaign-ibm/07-*`.

## Conditional finite-dimensional Gaussian milestone

`Foundation/IBMConditionalFiniteDim.lean:19` proves that for every fixed clock sample the full time-indexed scenery section of the composed path is a Gaussian process on the scenery probability factor. `conditional_finite_dim_gaussian` (line 35) states the resulting joint Gaussian law for every finite set of observation times. The proof uses the verified Gaussian scenery process and a.e. equality at each deterministic scenery parameter; the clock may take either sign before absolute value. These are genuine coherent finite-dimensional conditional laws, but the required continuous scenery modification is still an explicit hypothesis. Full Lake build 4210 jobs, exact type checks, 3184 transitive axiom checks with only propext/Classical.choice/Quot.sound. Logs `.lake/campaign-ibm/08-*`.

## Conditional fourth-increment milestone

`Foundation/IBMConditionalIncrements.lean:19` proves the exact conditional fourth moment of a composed-path increment at any fixed clock sample: `3 * ||C_t|-|C_s||²`. It transfers the verified two-sided scenery fourth-increment theorem through deterministic-time a.e. modification equality. This is a quantitative estimate for the conditional IBM process, not an unconditional increment bound until the clock is integrated and continuous source modifications are constructed. Full Lake build 4211 jobs, exact type check, 3185 transitive axiom checks with only propext/Classical.choice/Quot.sound. Logs `.lake/campaign-ibm/09-*`.

## IBM singular campaign: deterministic L²-to-H⁻¹ derivative — 2026-10-13

Initial HEAD `cfa08f0b59643f6e0bf8e72405833a99109b82f9`, with the same twelve unrelated untracked documents. The previous IBM campaign's source coordinate laws, conditional composition and conditional finite-dimensional laws are verified; continuous source modifications and unconditional IBM remain open. The three IBM manuscripts and `C:/Operator/ResearchAudits/NONCLASSICAL_ARCHIVE_SOURCE_AUDIT.md` were consulted. Their stochastic singularity and closure claims remain UNVERIFIED.

`Foundation/IBMNegativeSobolev.lean` applies Mathlib's actual Fourier/Bessel-potential Sobolev infrastructure. For every `u : Lp ℂ 2 volume`, `l2_derivative_memHminusOne` proves that the distributional derivative in the unit spatial direction belongs to `H^{-1}(ℝ)`. `l2Derivative` bundles that derivative in the concrete complete Sobolev space; `l2Derivative_toDistr` identifies its underlying distribution, and `l2Derivative_add`/`l2Derivative_smul` give the algebraic linear map `l2DerivativeLinear`. This result does not yet prove a quantitative operator norm or continuity, nor identify an IBM kernel, local time, or stochastic limit. The Bessel potential uses Mathlib's Fourier convention.

Target build, exact types, full Lake build (4228 jobs), and complete transitive audit (3191 declarations; only propext/Classical.choice/Quot.sound) passed. Logs `.lake/campaign-ibm-singular-01-*`. No prior proof body, manuscript, pin or unrelated untracked file changed.

## Bounded L²-to-H⁻¹ differentiation — 2026-10-13

`Foundation/IBMNegativeSobolevBounded.lean` constructs the continuous embedding from the actual H⁻¹ Bessel-potential space to tempered distributions. It proves the algebraic L² derivative map has sequentially closed graph by comparing both continuous embeddings in the distribution space, then applies Mathlib's Banach closed-graph theorem to obtain `l2DerivativeCLM`. The operator is bounded and `l2Derivative_norm_le` provides its finite operator-norm inequality. This is deterministic infrastructure for a future first-scenery-chaos residual `-∂_w(ρ_ε*(CL))`; it neither constructs that kernel nor proves local-time convergence. No explicit sharp constant is claimed.

Target and full Lake builds passed (4229 jobs), exact public types checked, complete transitive axiom audit 3197 declarations with only propext/Classical.choice/Quot.sound. Logs `.lake/campaign-ibm-singular-02-*`.

## Random-field H⁻¹ transfer on the clock factor — 2026-10-13

`Foundation/IBMNegativeSobolevRandom.lean` lifts bounded spatial differentiation to the actual Gaussian clock factor as `randomDerivativeCLM : L²(Ω_Y;L²(ℝ,ℂ)) →L[ℂ] L²(Ω_Y;H⁻¹(ℝ))`. Its operator norm is at most that of the deterministic derivative; `randomDerivative_apply_ae` identifies almost every clock section; `randomDerivative_tendsto` transports strong Bochner-L² convergence. This precisely isolates an analytic transfer step for the manuscript residual `-∂_w(ρ_ε*(CL))`: proving the kernel itself lies in the domain and converges there still requires actual Brownian local time and coefficient estimates.

Target build, exact types, full Lake build 4230 jobs, transitive audit 3201 declarations, only propext/Classical.choice/Quot.sound. Logs `.lake/campaign-ibm-singular-03-*`.

## Origin Dirac boundary mass in H⁻¹ — 2026-10-13

`Foundation/IBMDeltaBoundary.lean` proves `delta_zero_memHminusOne` for Mathlib's actual tempered Dirac distribution on ℝ, using its Fourier transform and the integrability of `(1+|ξ|²)^(-1)` in dimension one. `deltaZeroHminusOne` bundles the boundary mass in the same concrete H⁻¹ space as the derivative residual, with an exact underlying-distribution theorem. This verifies the deterministic target for the manuscript's `L_t^0(Y) f'(x) δ_0`, but not the local-time random coefficient, boundary-layer approximation, or stochastic limit.

Target build, exact types, full Lake build 4231 jobs, complete transitive axiom audit 3204 declarations, only propext/Classical.choice/Quot.sound. Logs `.lake/campaign-ibm-singular-04-*`.
