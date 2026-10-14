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

## Random Dirac boundary channel — 2026-10-13

`Foundation/IBMRandomBoundary.lean` constructs a bounded scalar-to-H⁻¹ map `a ↦ a δ₀`, then lifts it to `randomBoundaryCLM : L²(Ω_Y;ℂ) →L[ℂ] L²(Ω_Y;H⁻¹(ℝ))` on the verified Gaussian clock factor. It proves the almost-everywhere section formula and convergence transfer. Thus any *future verified* L² clock-local-time coefficient can enter the same dual space as the interior derivative residual. No local-time coefficient, boundary-layer convergence, or full first-chaos correction is asserted here.

Target build, exact public types, full Lake build 4232 jobs, complete transitive axiom audit 3209 declarations with only propext/Classical.choice/Quot.sound. Logs `.lake/campaign-ibm-singular-05-*`.

## Interior-plus-boundary H⁻¹ assembly — 2026-10-13

`Foundation/IBMDualAssembly.lean` defines the concrete input spaces `InteriorInput = L²(Ω_Y;L²(ℝ,ℂ))` and `BoundaryInput = L²(Ω_Y;ℂ)`, and the output `DualOutput = L²(Ω_Y;H⁻¹(ℝ))`. `dualAssemblyCLM` is the bounded sum of spatial distributional differentiation and multiplication of the origin Dirac mass by a clock coefficient. `dualAssembly_norm_le` controls the two channels separately, and `dualAssembly_tendsto` proves convergence when both inputs converge in their stated spaces. These are explicit conditional analytic transfer statements; no actual IBM correction has been identified as an input pair, and no local-time estimate has been assumed.

Exact public types, target build, full Lake build 4233 jobs, and complete transitive axiom audit 3216 declarations with only propext/Classical.choice/Quot.sound passed. Logs `.lake/campaign-ibm-singular-06-*`.

## Conditional second spatial chain rule for mollified scenery — 2026-10-13

`Foundation/IBMMollifiedChainRule.lean` proves the exact identity `deriv (deriv (r ↦ f(x+U r))) r = f₂(x+U r) (V r)² + f₁(x+U r) W r`, assuming actual pointwise `HasDerivAt U V`, `HasDerivAt V W`, `HasDerivAt f f₁`, and `HasDerivAt f₁ f₂`. It also proves the first and second HasDerivAt statements. These explicit spatial derivative hypotheses will be discharged only after an actual mollified scenery is constructed; the module makes no Malliavin-derivative or Brownian local-time assertion.

Target build, exact types, full Lake build 4234 jobs, transitive axiom audit 3220 declarations, only propext/Classical.choice/Quot.sound. Logs `.lake/campaign-ibm-singular-07-*`.

## Actual convolution derivatives for supplied continuous scenery paths — 2026-10-13

`Foundation/IBMMollifiedScenery.lean` defines `U=ρ⋆X`, `V=(deriv ρ)⋆X`, and `W=(deriv (deriv ρ))⋆X` using Mathlib's actual convolution integral against Lebesgue measure. If `X` is continuous and `ρ` has compact support and is `C²`, `U_hasDerivAt` and `V_hasDerivAt` prove the pointwise first and second spatial derivative representations; `deriv_U` and `deriv_V` identify Mathlib's derivatives. `second_chain_rule` applies the separately verified chain rule to these actual convolution fields and proves `∂²_r f(x+U_r)=f₂(x+U_r)V_r²+f₁(x+U_r)W_r` under explicit test-function derivative assumptions. This is a pathwise deterministic construction from a supplied continuous scenery path, not yet a measurable stochastic mollified IBM: continuous Brownian scenery, kernel normalization/scale, random-field measurability, Gaussian covariance and quantitative approximation are open.

Target build, exact types, full Lake build 4235 jobs, transitive audit 3228 declarations, only propext/Classical.choice/Quot.sound. Logs `.lake/campaign-ibm-singular-08-*`.

## Measurable mollified scenery and random-time process — 2026-10-13

`Foundation/IBMMollifiedMeasurability.lean` proves deterministic-parameter measurability and joint spatial/sample measurability of `U,V,W` for a supplied continuous scenery family with measurable deterministic-time coordinates and a compactly supported C² kernel. It uses Mathlib's parameter-integral measurability and compact-support continuity of convolution. `Foundation/IBMMollifiedProcess.lean` defines the concrete pointwise composition `Z_t^ρ(ωX,ωY)=U_ρ(S(·,ωX))(|C_t(ωY)|)` on the joint product factor, proves every coordinate measurable, joint time/sample measurability, continuous sample paths, and a measurable continuous-path-valued random variable.

The statements are conditional on supplied continuous scenery and clock coordinate families; neither Brownian modification existence nor their a.e. equality to verified source laws is discharged. Kernel positivity, normalization and ε scaling, Gaussian derivative laws, mollifier rates and Itô–Tanaka remain open. Target builds, exact types, full Lake build 4237 jobs, transitive audit 3242 declarations, only propext/Classical.choice/Quot.sound. Logs `.lake/campaign-ibm-singular-09-*` and `10-*`.

## Concrete normalized mollifier and pointwise limit — 2026-10-13

`Foundation/IBMMollifier.lean` constructs a specific sequence of smooth compactly supported nonnegative kernels by normalizing Mathlib's real bump functions with inner radius `1/(n+1)` and outer radius `2/(n+1)`. Each kernel integrates to one, and its support shrinks to the origin. For any supplied continuous scenery path, its convolution converges at every fixed spatial point. The same result gives pointwise convergence of the conditional mollified random-time process at each fixed time and joint sample to the supplied composition `S(|C_t|)`.

This proves an actual approximate-identity property, not convergence of the first two spatial derivatives, a rate, uniform path convergence, continuous Brownian modifications, or an IBM-specific singular correction. Target and full Lake builds passed (4239 jobs), exact public types checked, and complete transitive axiom audit covered 3250 declarations with only subsets of propext/Classical.choice/Quot.sound. Logs `.lake/campaign-ibm-singular-11-*`.

## Sectionwise tempered-distribution identity — 2026-10-13

`Foundation/IBMDualDistribution.lean` identifies the previously constructed H⁻¹-valued assembly on almost every Gaussian clock sample. For arbitrary `u : L²(clock;L²(space))` and `a : L²(clock;ℂ)`, `assembly_apply_ae` gives the H⁻¹ identity `dualAssembly(u,a)(ω)=∂u(ω)+a(ω)δ₀`. `assembly_toDistr_ae` pushes this identity into Mathlib's actual tempered-distribution space and identifies the two distribution terms precisely. This is an exact formula for the bounded analytic operator; it does not claim that an IBM local-time kernel or coefficient has been constructed. Full Lake build 4240 jobs, exact types, complete transitive audit 3252 declarations with only subsets of propext/Classical.choice/Quot.sound. Logs `.lake/campaign-ibm-singular-12-*`.

## Concrete bounded H⁻¹–H¹ pairing — 2026-10-13

`Foundation/IBMBesselDuality.lean` defines the weighted-L² pairing of Mathlib's actual complex Bessel-potential spaces `H⁻¹(ℝ)` and `H¹(ℝ)`. `pairing_norm_le` proves the sharp Cauchy–Schwarz bound; `pairingCLM` gives a continuous complex-linear functional on `H¹` for each `H⁻¹` element; `pairingCLM_norm_le` bounds its operator norm; `pairing_left_separating` proves that these functionals distinguish H⁻¹ elements. This is the concrete Hilbert-model dual pairing. Its agreement with tempered-distribution action on Schwartz tests and an onto-isometric identification with the full strong dual are not yet proved here. Full Lake build 4241 jobs, exact types, complete transitive axiom audit 3260 declarations with only subsets of propext/Classical.choice/Quot.sound. Logs `.lake/campaign-ibm-singular-13-*`.

## IBM observable-operator campaign: abstract closed restriction — 2026-10-13

Initial HEAD `dbd7da1ae22729c8bf917aadd2a939c74ff41346`. The twelve unrelated untracked documents remain untouched. The previous campaign verified independent Brownian *coordinate laws* and conditional random-time composition, but did not construct continuous Brownian source modifications. Mathlib's pinned `IsPreBrownianReal` API does not expose a continuous-modification theorem; this remains the exact blocker for unconditional IBM and the genuine IBM observable sigma-algebra. The archive's density assumption in `ibm/EnergyFirst.tex` is unverified and its source mollification is not automatically IBM-observable.

`Foundation/ObservableRestriction.lean` defines, for any real normed source and target and any source partial linear operator `A`, the maximal restriction to an observable submodule `V`. `derivative_domain` identifies the domain as the intersection of `V` with `A.domain`, and `derivative_graph` identifies its graph with the continuous preimage of the source graph. `derivative_isClosed` proves closedness whenever `A` is closed, with no density hypothesis on either domain or any claim that the observable core is dense. This is a reusable abstract result and a structural prerequisite for IBM, not a concrete IBM compression.

Full Lake build 4242 jobs, exact public types, complete transitive audit 3264 declarations with only subsets of propext/Classical.choice/Quot.sound. Logs `.lake/campaign-ibm-observable-01-*`.

## Projected source divergence is a one-sided adjoint inclusion — 2026-10-13

`Foundation/ObservableProjectedDivergence.lean` works with a real Hilbert source `H`, a Hilbert target `E`, a source partial derivative `A`, and an observable Hilbert submodule `V` (`[CompleteSpace V]`). `projectedSourceDivergence` orthogonally projects `A.adjoint u` into `V`. `projected_pairing` proves the exact adjoint identity on every restricted-domain input, assuming the source domain is dense. When the observable restriction domain is *also* dense, `source_divergence_mem` proves inclusion of every source-adjoint integrand into the observable adjoint domain, and `divergence_source_value` identifies its observable adjoint value with the projected source divergence. The theorem does not identify the full observable adjoint domain with the source-adjoint domain. Observable density is an explicit hypothesis, not inferred from source density; IBM instantiation remains blocked by continuous source modifications and observable-core density.

Full Lake build 4243 jobs, exact public types, complete transitive audit 3268 declarations with only subsets of propext/Classical.choice/Quot.sound. Logs `.lake/campaign-ibm-observable-02-*`.

## Sufficient observable-core density criterion — 2026-10-13

`Foundation/ObservableCoreDensity.lean:17` proves `derivative_dense_of_projection_invariant`: if `A.domain` is dense in the source Hilbert space and orthogonal projection onto a complete observable submodule `V` maps `A.domain` into itself, then the maximal restricted derivative domain is dense in `V`. The proof uses surjectivity and continuity of orthogonal projection to transfer the dense source domain. This is a sufficient condition, not an equivalence and not a proof that IBM's conditional-expectation projection preserves the Malliavin domain. Establishing that stability for the actual IBM observable sigma-algebra is a separate open obligation.

Full Lake build 4244 jobs, exact type, complete transitive audit 3269 declarations with only subsets of propext/Classical.choice/Quot.sound. Logs `.lake/campaign-ibm-observable-03-*`.

## Concrete positive-time IBM scenery observable factor — 2026-10-13

`Foundation/IBMSceneryObservableRestriction.lean` instantiates the abstract restriction with the verified Gaussian derivative `closedCylindricalDerivative` and the observable subspace generated by positive-time scenery coordinates. `positiveScenery_coordinate` proves these are *definitionally identical* to the positive-time coordinates of `IBMSourceLaws.sceneryBase`, the actual two-sided Brownian scenery source. `derivative_eq_existing` identifies the abstract restriction with the independently constructed Gaussian observable derivative at spectral exponent `H=1/2`; `derivative_dense` and `derivative_closed` transfer its verified dense polynomial core and closedness. This is a real Brownian scenery *source-factor* instantiation. It does not construct the joint product-source derivative, the random-time IBM observable sigma-algebra, or density of the intrinsic IBM core.

Full Lake build 4245 jobs, exact types, complete transitive audit 3274 declarations with only subsets of propext/Classical.choice/Quot.sound. Logs `.lake/campaign-ibm-observable-04-*`.

## Observable graph norm and subcore closure — 2026-10-13

`Foundation/ObservableSubcores.lean` proves `graph_norm_eq`: the maximal observable restriction inherits the source graph norm exactly under subspace inclusion. For any partial operator `B` contained in the maximal restriction, `subcore_closable` proves closability when the source operator is closed, and `subcore_closure_le` proves that `B.closure` remains inside the maximal restriction. Neither result assumes subcore density, nor upgrades inclusion to equality; such equality requires a separate graph-core theorem. These results can control future IBM-observable cylinders once their measurability and source-domain membership are verified.

Full Lake build 4246 jobs, exact types, complete transitive audit 3277 declarations with only subsets of propext/Classical.choice/Quot.sound. Logs `.lake/campaign-ibm-observable-05-*`.

## Exact observable-density criterion — 2026-10-13

`Foundation/ObservableDensityCriterion.lean` proves `derivative_dense_iff_annihilator_zero`: for a Hilbert observable submodule, the maximal restricted derivative domain is dense if and only if every observable vector orthogonal to *all* domain elements is zero. This is the exact necessary-and-sufficient Hilbert criterion. It does not establish the premise for the IBM observable sigma-algebra; a nonzero annihilator would refute density, while proving its absence would establish density. The earlier projection-invariance theorem is a sufficient route, not a replacement for this equivalence.

Full Lake build 4247 jobs, exact type, complete transitive audit 3278 declarations with only subsets of propext/Classical.choice/Quot.sound. Logs `.lake/campaign-ibm-observable-06-*`.

## Dense-source-domain transfer obstruction — 2026-10-13

`Foundation/ObservableDensityObstruction.lean` proves that for any source partial operator `A` and vector `v ∉ A.domain`, the source domain intersects the line `ℝ∙v` only at zero (`span_outside_domain`). `restricted_line_domain_bot` identifies the maximal observable restriction domain on that line as `⊥`, and `restricted_line_not_dense` proves that it is not dense. `exists_nondense_restriction_of_proper_domain` packages the consequence: even when the source domain is dense, if it is proper, some nonzero observable subspace has nondense restricted domain. This is a valid abstract counterexample pattern, not a claim that the IBM observable subspace is such a line or that its intrinsic core fails to be dense.

Full Lake build 4248 jobs, exact types, complete transitive audit 3282 declarations with only subsets of propext/Classical.choice/Quot.sound. Logs `.lake/campaign-ibm-observable-07-*`.

## Conditional IBM observable L² space — 2026-10-13

`Foundation/IBMConditionalObservable.lean` takes explicitly supplied measurable continuous scenery and clock path maps on the verified joint Gaussian source. It defines the sigma-algebra generated by every composition coordinate `X(ω)(|Y(ω)(t)|)`, the corresponding closed real L² submodule, and the contractive conditional-expectation projection into it. `observableSigma_le`, `observableSpace_isClosed`, and `observableProjection_norm_le` verify measurability, closedness, and contraction. This is a conditional construction: the required continuous Brownian modifications have not been built from the verified source coordinates, so it is not yet the unconditional genuine IBM observable space. No source derivative-domain stability or intrinsic observable-core density follows from these results.

Full Lake build 4249 jobs, exact public types, complete transitive audit 3288 declarations with only subsets of propext/Classical.choice/Quot.sound. Logs `.lake/campaign-ibm-observable-08-*`.

## Closure of projected source divergence — 2026-10-13

`Foundation/ObservableProjectedDivergenceClosure.lean` packages the projected source adjoint on its original source-adjoint domain as the partial linear operator `projectedOperator`. Under independently assumed density of both the source derivative domain and the observable restricted derivative domain, `projectedOperator_le_adjoint` proves graph inclusion in the full observable adjoint. `projectedOperator_closable` proves this partial operator is closable, and `projectedOperator_closure_le_adjoint` proves its closure remains inside the full observable adjoint. These are strict one-sided statements: equality requires a separate graph-core theorem and is not asserted for IBM.

Full Lake build 4250 jobs, exact public types, complete transitive audit 3292 declarations with only subsets of propext/Classical.choice/Quot.sound. Logs `.lake/campaign-ibm-observable-09-*`.

## Conditional IBM observable projection geometry — 2026-10-13

`Foundation/IBMConditionalProjectionGeometry.lean` proves `observableProjection_fixed`: every element of the supplied-path observable L² space is fixed by conditional expectation. `observableProjection_pairing` proves that projecting any source L² function preserves its inner product against every observable test function. Both are exact orthogonal-projection identities on the conditional IBM observable space. They do not imply preservation of the source Malliavin derivative domain; no continuous Brownian modifications have been supplied from the actual coordinates.

Full Lake build 4251 jobs, exact public types, complete transitive audit 3294 declarations with only subsets of propext/Classical.choice/Quot.sound. Logs `.lake/campaign-ibm-observable-10-*`.

## Sharp H⁻¹–H¹ Hilbert duality — 2026-10-13

`Foundation/IBMBesselDualitySharp.lean` strengthens the existing IBM Sobolev test geometry. `pairingCLM_norm_eq` proves the weighted-L² pairing functional has operator norm exactly the H⁻¹ norm. `pairingCLM_existsUnique` proves every continuous complex-linear functional on the actual Bessel-potential H¹ space is uniquely represented by an H⁻¹ vector through this pairing, using Mathlib's Riesz representation on the isometric L² model. This is an onto isometric *conjugate-linear* Hilbert dual representation at the level of propositions. It does not yet prove that the manuscript's IBM first-chaos distribution coincides with this pairing on Schwartz tests or that the singular limit is intrinsically IBM-observable.

Full Lake build 4252 jobs, exact public types, complete transitive audit 3296 declarations with only subsets of propext/Classical.choice/Quot.sound. Logs `.lake/campaign-ibm-observable-11-*`.

## Fourth-order frontier: exact spatial overlap — 2026-10-13

`Foundation/IBMSpatialOverlap.lean` defines `signedOverlap` as the signed length of overlap of two oriented spatial intervals. `signedOverlap_eq_min_covariance` proves its exact four-term Brownian covariance-kernel identity, including reversed orientations. `sceneryBase_covariance_min` identifies the verified nonnegative scenery covariance with `min`, and `sceneryBase_increment_covariance` gives the exact covariance of two genuine source-scenery increments. `Foundation/IBMConditionalOverlap.lean` proves `conditional_increment_covariance`: for any fixed Brownian-clock sample and supplied continuous scenery modification, two IBM increments have conditional scenery covariance equal to the signed overlap of their reflected-clock spatial intervals. Physical-time disjointness does not imply conditional independence. The continuous modification still is a hypothesis, not an established source realization.

Full Lake build 4254 jobs, exact public types, complete transitive audit 3301 declarations with only subsets of propext/Classical.choice/Quot.sound. Logs `.lake/campaign-ibm-fourth-01-*`.

## Fourth-order frontier: reflected-clock crossing correction — 2026-10-13

`Foundation/IBMReflectedClockCorrection.lean` defines `crossingPenalty x y = 2 (|xy|-xy)` and proves the exact pathwise identity `reflected_increment_sq`: `(|y|-|x|)^2 = (y-x)^2 - crossingPenalty x y`. `crossingPenalty_bounds`, `crossingPenalty_pos_iff`, and the sign-specific identities establish that the penalty is nonnegative, bounded by the unreflected squared increment, and strictly positive exactly for opposite-sign nonzero endpoints. `Foundation/IBMConditionalReflectedMoments.lean` applies the existing verified fourth-increment moment to give `conditional_increment_fourth_crossing`, `conditional_increment_fourth_le`, and `conditional_increment_fourth_eq_of_same_sign`. These are for a fixed clock sample and a supplied continuous scenery modification; they do not yet average over the Brownian clock or prove a partition limit.

Full Lake build 4256 jobs, exact public types, complete transitive audit 3311 declarations with only subsets of propext/Classical.choice/Quot.sound. Logs `.lake/campaign-ibm-fourth-02-*`.

## Fourth-order frontier: exact finite-family quartic expectation — 2026-10-13

`Foundation/IBMFiniteQuartic.lean` proves `conditional_increment_fourth_integrable` for each supplied-path IBM increment under the scenery modification hypothesis. `quarticSum` is the sum of fourth powers over an arbitrary finite family of physical-time intervals. `conditional_quarticSum_expectation` proves its exact scenery-conditional expectation: `3` times the sum of squared *reflected* clock displacements. `conditional_quarticSum_crossing` decomposes it into the unreflected squared clock-increment sum minus the exact sum of crossing penalties. `conditional_quarticSum_le` gives the corresponding upper bound. No independence of the intervals is needed for this first moment. This does not establish an unconditional expectation limit, a second-moment estimate, or convergence of quartic variation; those require clock averaging and spatial-overlap/Wick analysis.

Full Lake build 4257 jobs, exact public types, complete transitive audit 3316 declarations with only subsets of propext/Classical.choice/Quot.sound. Logs `.lake/campaign-ibm-fourth-03-*`.

## Fourth-order frontier: mixed Gaussian eighth moment — 2026-10-13

`Foundation/GaussianQuarticWick.lean` proves `value_four`, the exact fourth Hermite polynomial; `quartic_coeFn`, an a.e. identity decomposing the actual fourth power into fourth, second, and zeroth Wiener chaoses; `quartic_inner`; and `firstChaos_fourth_product`. For arbitrary coefficient-space directions `h,k`, the latter proves `E[A⁴B⁴] = 9u²v² + 72uvc² + 24c⁴`, where `u=‖h‖²`, `v=‖k‖²`, and `c=⟨h,k⟩`. This includes degenerate and perfectly correlated cases and supplies the reusable Gaussian algebra needed for IBM pair-increment variance. It is not yet a conditional IBM pair-increment theorem; identifying `c` with reflected-clock spatial overlap remains the next step.

Full Lake build 4258 jobs, exact public types, complete transitive audit 3321 declarations with only subsets of propext/Classical.choice/Quot.sound. Logs `.lake/campaign-ibm-fourth-04-*`.

## Fourth-order frontier: IBM paired-increment Wick identity — 2026-10-13

`Foundation/IBMSceneryQuarticPair.lean` proves `scenery_increment_fourth_product`: for two oriented nonnegative intervals of the verified Brownian scenery source, the mixed eighth moment is `9u²v² + 72uvc² + 24c⁴`, with `u=|b-a|`, `v=|d-c|`, and `c=signedOverlap a b c d`. `Foundation/IBMConditionalQuarticPair.lean` transfers this to two supplied-path IBM increments at every fixed clock sample in `conditional_increment_fourth_product`. `conditional_fourth_centered_product` subtracts the product of their conditional fourth moments and identifies the nonnegative scenery-correlation contribution exactly as `72uvc²+24c⁴`. This is a rigorous finite-dimensional formula for arbitrary time pairs, not a partition variance bound after Brownian-clock averaging. Continuous scenery paths remain an explicit modification hypothesis.

Full Lake build 4260 jobs, exact public types, complete transitive audit 3325 declarations with only subsets of propext/Classical.choice/Quot.sound. Logs `.lake/campaign-ibm-fourth-05-*`.

## Fourth-order frontier: exact conditional variance of finite quartic sums — 2026-10-13

`Foundation/IBMFiniteQuarticSecondMoment.lean` proves `conditional_fourth_memLp_two` for every fixed-clock fourth-power increment, using the actual Gaussian Wick L² representative. `conditional_fourth_product_integrable` justifies products. `conditional_quarticSum_second_moment_expand` rigorously interchanges finite sums and scenery integration. `conditional_quarticSum_centered_second_moment` gives an exact conditional variance formula for any finite family of physical-time intervals: a double sum of `72 u_p u_q c_{pq}² + 24 c_{pq}⁴`, where `u_p` is the magnitude of the reflected-clock displacement and `c_{pq}` is signed spatial overlap. Every summand is nonnegative. The remaining partition-limit obligation is quantitative control of the Brownian-clock distribution of these overlaps, plus clock averaging and continuous source modifications; no `L²` convergence or normalization has been claimed.

Full Lake build 4261 jobs, exact public types, complete transitive audit 3329 declarations with only subsets of propext/Classical.choice/Quot.sound. Logs `.lake/campaign-ibm-fourth-06-*`.

## Fourth-order frontier: clock-averaged finite quartic bound — 2026-10-13

`Foundation/IBMClockQuarticBound.lean` proves `clockBase_increment_second` from the verified Brownian clock law and `clockModified_increment_second` for any a.e. continuous clock modification. `clock_reflected_increment_integrable` and `clock_reflected_increment_second_le` show that expected squared reflected-clock displacement is at most physical elapsed time. `averaged_conditional_quarticSum_le` integrates the exact scenery-conditional fourth-power sum over the clock factor and bounds this *iterated expectation* by three times the total length of any finite ordered interval family. Thus a genuine partition of `[0,T]` has the upper bound `3T` when its lengths sum to `T`; equality and convergence to `3T` have not been proved. The theorem assumes continuous source modifications, which remain unconstructed, and does not identify the iterated integral with an independently established joint IBM expectation by Fubini.

Full Lake build 4262 jobs, exact public types, complete transitive audit 3334 declarations with only subsets of propext/Classical.choice/Quot.sound. Logs `.lake/campaign-ibm-fourth-07-*`.

## Fourth-order frontier: exact finite-partition Taylor identity — 2026-10-13

`Foundation/IBMFourthTaylor.lean` defines the actual degree-four Taylor remainder and proves `remainder_bound`: for `f ∈ C⁵` with `‖f⁽⁵⁾‖ ≤ M`, its magnitude is at most `(M/120)|y-x|⁵`. `taylor_four_explicit` identifies the fourth-degree polynomial with the actual first through fourth iterated derivatives at the left endpoint. `increment_identity` and `finite_path_identity` prove the exact single-step and finite-path telescoping formulas. `conditional_ibm_partition_identity` instantiates the formula pathwise for any supplied continuous IBM composition along any finite deterministic time array, preserving separate first-, second-, third-, fourth-rank terms and the remainder. The theorem proves no convergence of those terms, weighted quartic variation, compensation, or higher-order stochastic Itô formula. Continuous Brownian source modifications remain an unproved prerequisite for an unconditional IBM application.

Full Lake build 4263 jobs, exact public types, complete transitive audit 3340 declarations with only subsets of propext/Classical.choice/Quot.sound. Logs `.lake/campaign-ibm-fourth-08-*`.

## Fourth-order frontier: finite quartic variation is IBM-observable — 2026-10-13

`Foundation/IBMObservableQuartic.lean` proves `observable_value_measurable` for each composition coordinate relative to the *generated* sigma-algebra `IBMConditionalObservable.observableSigma X Y`. `finiteQuartic` is the fourth-power sum over any finite interval family, and `finiteQuartic_observable_measurable` proves its measurability under that generated sigma-algebra, not merely the ambient joint-source measurable space. `finiteQuartic_eq_conditional_sum` identifies it definitionally with the sum used in the conditional moment and variance theorems. Thus finite-mesh quartic variation is intrinsic to the supplied observed path. The theorem does not construct continuous Brownian source modifications or establish a measurable limiting variation.

Full Lake build 4264 jobs, exact public types including the explicit generated sigma-algebra instance, complete transitive audit 3344 declarations with only subsets of propext/Classical.choice/Quot.sound. Logs `.lake/campaign-ibm-fourth-09-*`.

## Fourth-order frontier: finite joint quartic expectation — 2026-10-13

`Foundation/IBMJointQuartic.lean` proves `quarticSum_measurable` under coordinate measurability of supplied continuous scenery and clock modifications, then `quarticSum_integrable` under their a.e. agreement with the verified Brownian sources. `joint_quarticSum_expectation` applies Fubini on the actual product measure to identify the joint finite quartic expectation exactly with the clock average of the conditional scenery formula, `3` times the sum of squared reflected-clock displacements. `joint_quarticSum_le` bounds this joint expectation by three times the total physical length of any finite ordered interval family. This closes the previous finite-sum Fubini gap. Continuous source modifications are still supplied as hypotheses, not constructed. The theorem does not establish equality with `3T` or convergence of quartic variation along refining partitions.

Full Lake build 4265 jobs, exact public types, complete transitive audit 3349 declarations with only subsets of propext/Classical.choice/Quot.sound. Logs `.lake/campaign-ibm-fourth-10-*`.

## Fourth-order frontier: exact finite crossing deficit — 2026-10-13

`Foundation/IBMJointQuartic.lean` additionally proves `clock_increment_square_integrable`, `clock_crossingPenalty_integrable`, and `joint_quarticSum_deficit`. For every finite family of ordered physical-time intervals, the *actual joint* quartic expectation is exactly `3` times total interval length minus `3` times the clock expectation of the summed zero-crossing penalties. The correction is nonnegative by `IBMReflectedClockCorrection.crossingPenalty_bounds`, so the prior joint upper bound follows. The precise missing analytic lemma for a `3T` expectation limit is that the expected total crossing penalty tends to zero along the chosen deterministic partition family. Neither that decay nor a variance limit has been established. Measurable continuous source modifications remain explicit hypotheses.

Full Lake build 4265 jobs, exact public types, complete transitive audit 3352 declarations with only subsets of propext/Classical.choice/Quot.sound. Logs `.lake/campaign-ibm-fourth-11-*`.

## EJP 2026 paper: source-first finite scenery smoothing — 2026-10-13

The local manuscript `C:/Operator/ibm/EJP2605-044RA0.pdf`, page 4, gives Lemma 2.1's Brownian scenery mollifier second-moment estimate and Lemma 2.2(a)'s derivative-kernel energy estimate. `Foundation/IBMFiniteScenerySmoothing.lean` independently verifies their finite-positive-kernel analogues before continuous source modifications or pathwise convolution. The constructed Brownian spectral direction satisfies `direction_increment_sq`: squared Hilbert distance is exactly `|r-x|`. `smoothDirection_error_sq_le_weighted` and `smoothScenery_error_sq_le_weighted` bound squared Gaussian L² smoothing error by the discrete first absolute moment `∑ w(r)|r-x|`, with weights nonnegative and summing to one. `smoothDirection_energy_le` and `smoothScenery_energy_le` bound the corresponding Cameron–Martin/Gaussian L² energy by `|x|` plus that moment. `smoothScenery_error_fourth` is the exact Gaussian fourth-moment identity, and `smoothScenery_error_fourth_le_weighted` gives the resulting `3(moment)²` bound. A support-radius version and `smoothScenery_tendsto` establish L² convergence for shrinking finite positive kernels. This is a genuinely source-law construction in the order advocated by the campaign. It does not yet construct the paper's continuous convolution `ρ_ε*X`, its Malliavin derivative kernel, or the fixed-ε Itô–Tanaka formula; those require Bochner integration and measurable continuous source modifications, with exact hypotheses tracked separately.

Full Lake build 4266 jobs, exact public types, complete transitive audit 3366 declarations with only subsets of propext/Classical.choice/Quot.sound. Logs `.lake/campaign-ejp-01-*`.

## EJP 2026 paper: literal finite scenery random variables — 2026-10-13

`Foundation/IBMFiniteScenerySmoothing.lean` now defines `finiteSceneryValue` as the literal finite sum `∑ w(r) sceneryBase(r,ω)`. `smoothScenery_ae_eq_finiteValue` proves that this random function represents the independently constructed Gaussian L² Hilbert average almost everywhere. `finiteScenery_error_second` identifies its exact second error moment with the squared spectral Hilbert distance; `finiteScenery_error_second_le_weighted` is the discrete positive-kernel version of the paper's Lemma 2.1 in literal expectation notation. `finiteScenery_error_fourth` and `finiteScenery_error_fourth_le_weighted` extend the paper's second-moment estimate to an exact fourth Gaussian error moment and a `3(∑w|r-x|)²` bound. The statements concern finite kernels and the verified source coordinates; they do not silently identify a continuous convolution or construct a continuous IBM process.

Full Lake build 4266 jobs, exact public types, complete transitive audit 3372 declarations with only subsets of propext/Classical.choice/Quot.sound. Logs `.lake/campaign-ejp-02-*`.

## EJP 2026 paper: exact finite-kernel scenery covariance — 2026-10-13

`Foundation/IBMFiniteScenerySmoothing.lean` proves `finiteScenery_cross_moment` for two literal finite weighted scenery sums, with no positivity, mass-one, or disjoint-support restriction. `finiteScenery_mean_zero` and `finiteScenery_cross_moment_covariance` identify the exact double weighted Brownian covariance-kernel sum, and `finiteScenery_covariance` states it as measure-theoretic covariance. This supplies a finite-dimensional source-first covariance calculus for the paper's smoothed fields. The continuum convolution kernel and its spatial derivatives are not yet recovered as limits, and no full fixed-ε first-chaos or Itô–Tanaka assertion follows from this finite statement alone.

Full Lake build 4266 jobs, exact public types, complete transitive audit 3376 declarations with only subsets of propext/Classical.choice/Quot.sound. Logs `.lake/campaign-ejp-03-*`.

## EJP paper-to-Lean claim audit — 2026-10-13

`EJP2605_044RA0_LEAN_CROSSWALK.md` records the manuscript's main claims against exact verified Lean declarations and separates finite source-kernel mathematics, supplied continuous-path results, and unproved continuum stochastic-calculus steps. The key reverse-order next step is a Bochner-valued convolution of the verified Gaussian Hilbert directions, before the random-time composition or Skorohod/Itô identification. No claim of a full formalized EJP Itô–Tanaka theorem or actual first-chaos closure is made.

## Continuous source-first IBM scenery — 2026-10-13

`Foundation/IBMContinuousScenery.lean` verifies strong measurability, local Bochner integrability, compact-kernel Gaussian L² convolution, exact transfer through the isonormal embedding, and the continuous-kernel cross moment against a source coordinate. The kernel is continuous on a finite interval; no whole-line mollifier or normalization has yet been instantiated. No sample-path Brownian modification, random-time evaluation, Malliavin derivative kernel, or IBM Itô correction is claimed. Full build: 4267 jobs. Public theorem types checked. Transitive audit: 3383 declaration outputs, only the three permitted axioms. Logs `.lake/campaign-ibm-cont-01-*`.

## Continuous scenery covariance geometry — 2026-10-13

`Foundation/IBMContinuousCovariance.lean` gives the exact two-kernel Gaussian covariance and energy as iterated Brownian-covariance integrals for continuous compact-interval kernels. No sign or normalization assumptions are needed. Full build 4268 jobs, checked public types, 3386 transitive axiom outputs using only `propext`, `Classical.choice`, `Quot.sound`. The whole-line mollifier, error bounds, spatial/Malliavin derivatives and stochastic correction remain separate obligations.

## Continuous Gaussian smoothing rates — 2026-10-13

`Foundation/IBMContinuousRadius.lean` establishes `√δ` Hilbert-direction error, `δ` Gaussian L² squared error, exact Gaussian fourth moment, `3δ²` fourth-moment bound, and strong Gaussian L² convergence for continuous positive mass-one kernels integrated over an interval wholly within radius `δ` of the target. This is an actual Bochner convolution, but the radius condition is stronger than the manuscript's first-absolute-moment estimate and no pathwise or random-time statement follows. Full build 4269 jobs, checked theorem types, 3391 transitive axiom outputs with only the permitted three axioms.

## Whole-line smooth Gaussian L² scenery — 2026-10-13

`Foundation/IBMContinuousDerivative.lean` constructs the actual whole-line Bochner convolution for compactly supported smooth kernels and proves first/second spatial derivative formulas in Gaussian L² under `C¹`/`C²` hypotheses. This uses the source's proven local Bochner integrability and Mathlib's derivative-of-convolution theorem. No sample-path smooth modification, nonlinear chain rule, Malliavin derivative kernel, or random-time composition is asserted. Full build 4270 jobs, checked theorem types, 3399 transitive axiom outputs using only the permitted three axioms.

## Whole-line smoothing and derivatives on one object — 2026-10-13

`Foundation/IBMWholeLineSmoothing.lean` identifies the compact-interval kernel average with the actual whole-line convolution under an explicit shifted-support condition, then transfers the `δ` Gaussian L² rate and shrinking-radius convergence. This links the preceding smoothing and spatial-derivative modules without a sample-path assumption. Full build 4271 jobs, checked theorem types, 3403 transitive axiom outputs with only the three allowed axioms. Explicit normalized mollifier families, Malliavin derivative kernels, random-time evaluation, and Stein cancellation remain open.

## Full source derivative of continuous Gaussian scenery — 2026-10-13

`Foundation/IBMContinuousMalliavin.lean` constructs the exact deterministic source Malliavin kernel as a Bochner integral of Gaussian Hilbert directions and proves that both compact and supported whole-line convolutions belong to the full closed derivative domain with that kernel as constant gradient. The weighted source graph is Bochner integrable in the product graph norm, and its integral equals the convolution/derivative pair. This is a verified concrete derivative-integral commutation, independent of predictable projection. Full build 4272 jobs, checked theorem types, 3414 transitive axiom outputs with only the permitted three axioms. Random-time evaluation, nonlinear source derivatives, Stein cancellation, and continuous Brownian modifications remain open.

## Concrete normalized Gaussian scenery mollifier — 2026-10-13

`Foundation/IBMConcreteMollifier.lean` applies the existing explicit `C∞` normalized bump family to the actual source Gaussian L² scenery. Shifted support and restricted mass are proved. The squared L² error is at most `2/(n+1)` and the canonical Gaussian fourth error moment is at most `3(2/(n+1))²`; fixed-point strong L² convergence follows. Each mollified class has first/second spatial derivatives in Gaussian L² and an exact full closed Malliavin derivative equal to the integrated source Hilbert kernel. No sample-path differentiability, joint measurable version, or IBM clock composition is claimed. Full build 4273 jobs; types checked; 3424 transitive axiom outputs using only the permitted three axioms.

## Uniform source-first mollifier convergence — 2026-10-13

`Foundation/IBMUniformSmoothing.lean` proves the explicit normalized Gaussian L² mollifiers converge uniformly in spatial `x` on all of `ℝ`, using the previously verified radius-independent norm error `≤ √(2/(n+1))`. This is a Banach-valued uniform convergence theorem, not a sample-path assertion. Full build 4274 jobs, checked types, 3426 transitive axiom outputs with only the three permitted axioms.

## Source-first full derivative graph smoothing — 2026-10-13

`Foundation/IBMGraphSmoothing.lean` upgrades the actual normalized Gaussian scenery mollifiers to uniform convergence in the full closed Malliavin graph, not merely in Gaussian L². The coefficient, constant-gradient, and graph-pair errors have exactly the same norm as the source L² error, bounded uniformly in `x` by `√(2/(n+1))`. Every mollifier pair belongs to the actual closed derivative graph; the source pair does too. The theorem does not construct a jointly measurable Brownian modification or permit evaluating at an independent random time. Full Lake build 4275 jobs, checked public types, 3436 audited transitive axiom outputs with only the permitted three axioms. Logs `.lake/campaign-ibm-cont-09-*`.

Direct review of the EJP paper's pages 8–10 shows the fixed-ε leading Stein cancellation is governed by the derivative-field covariance relations `Cov(U,V)=1/2` and `Var(V)+Cov(U,W)=0`, leaving a fifth-derivative term with coefficient `1/4`. The paper's divergent residual depends on Brownian local-time Sobolev estimates. These relations and the local-time step remain independent formalization obligations; the verified graph convergence does not imply either one.

## EJP bulk covariance differentiation — 2026-10-13

`Foundation/IBMVarianceCancellation.lean` derives the exact first and second spatial derivatives of the variance of the actual Gaussian L² whole-line convolution. Under an explicitly stated zero second-variance-derivative assumption, it proves `‖V‖²+⟪U,W⟫=0`; under unit first-variance slope, it proves `⟪U,V⟫=1/2`. The hypotheses are not yet discharged for the concrete mollifier in the paper's bulk region. This cleanly isolates the next covariance-integral calculation before Gaussian Stein cancellation, local-time estimates, and the first-chaos obstruction. Full Lake build 4276 jobs, exact types checked, 3440 audited axiom outputs with only the three permitted axioms. Logs `.lake/campaign-ibm-cont-10-*`.

## Adjoint-first IBM campaign A1: positive bulk and boundary covariance — 2026-10-13

Initial HEAD `9bcfb65d3c3bba8396a812cb17086f9debda9aaf`. `Foundation/IBMFiniteBulkVariance.lean:16–39` verifies the positive-half-line Brownian covariance of shifted finite scenery directions and the exact affine variance `x + Σ_{r,s}w_r w_s min(r,s)` for mass-one weights. `Foundation/IBMContinuousBulkVariance.lean:18–126` constructs a genuine Gaussian L² offset convolution as a Bochner integral of the verified two-sided source coordinates. For continuous mass-one offset kernels wholly within the positive half-line, its variance is exactly `x + C_ρ`, with `C_ρ = ∫_s ρ(-s)∫_r ρ(-r)min(r,s)` independent of x. The result is instantiated with the explicit normalized bump when x is at least its outer radius. The exact two-sided covariance decomposition adds `max(-(x+r),0)+max(-(x+s),0)` to the positive-bulk kernel, identifying the pointwise origin-boundary correction. The Lean bridge identifying the offset integral with the earlier `wholeLineScenery ρ x` by translation remains open, as does integration of the boundary correction, the derivative-field covariance identities and Gaussian Stein cancellation. Full Lake build 4284 jobs; ten theorem types checked; complete transitive axiom audit 3483 declarations, only propext/Classical.choice/Quot.sound. Logs `.lake/campaign-ibm-adjoint-01-*`.

## Adjoint-first IBM campaign A2: actual whole-line interior cancellation — 2026-10-13

`Foundation/IBMOffsetTranslation.lean:12–38` proves the interval-translation identity and identifies the offset Gaussian field with the previously established `wholeLineScenery`, using the explicit support of the normalized bump. Consequently `concrete_wholeLineScenery_affine_variance` (line 49) proves for `x≥rOut(n)` the exact variance `‖U_n(x)‖²=x+C_n`, with `C_n` the fixed double integral from A1. For strict interior `x>rOut(n)`, `concrete_wholeLineVariance_deriv` and `_second_deriv` (lines 56, 65) prove slopes 1 and 0 by neighborhood equality. Crucially, `concrete_interior_cross_covariance` (line 76) now proves `⟪U_n,V_n⟫=1/2`, and `concrete_interior_covariance_cancellation` (line 84) proves `‖V_n‖²+⟪U_n,W_n⟫=0` for the actual Gaussian L² whole-line convolution and its first two spatial derivative fields. These discharge the previously conditional hypotheses in `IBMVarianceCancellation` on the positive bulk. Negative bulk, the integrated origin-boundary correction, Gaussian Stein expectation identities, pathwise random-field versions and local-time terms remain open. Full Lake build 4285 jobs; eight exact types checked; complete transitive audit 3491 declarations with only propext/Classical.choice/Quot.sound. Logs `.lake/campaign-ibm-adjoint-02-*`.

## Adjoint-first IBM campaign A3: exact boundary-layer variance — 2026-10-13

`Foundation/IBMBoundaryVariance.lean:13` proves the unrestricted double Brownian-covariance integral for the genuine offset Gaussian direction. At line 37 the variance is expanded using the exact two-sided identity from A1: its integrand is `ρ(-s)ρ(-r)[x+min(r,s)+max(-(x+r),0)+max(-(x+s),0)]`. `concrete_wholeLineScenery_boundary_variance` (line 53) transfers this to the actual normalized whole-line scenery mollifier for every spatial x, including when its support crosses the origin. The negative-part terms vanish in the positive interior and make the boundary contribution explicit; the proof does not yet collapse them to a one-dimensional integral or establish a Dirac/distributional limit. This also shows why the manuscript's unit variance slope must be restricted to the positive bulk: the unrestricted two-sided covariance has additional terms. Full Lake build 4286 jobs; three exact public types checked; complete transitive audit 3494 declarations, only propext/Classical.choice/Quot.sound. Logs `.lake/campaign-ibm-adjoint-03-*`.

## Adjoint-first IBM campaign A4: joint Gaussian mollifier derivative fields — 2026-10-13

`Foundation/IBMJointMollifierGaussian.lean:15` identifies every whole-line Gaussian L² scenery convolution with a deterministic source Hilbert direction under the original isonormal integration operator. The genuine three-coordinate process built from the normalized bump and its first two kernel derivatives is jointly Gaussian by `gaussianTriple_jointGaussian` (line 32), not inferred from marginal laws. Its covariance matrix is the source-direction Gram matrix (line 37). Lines 43–54 identify all three coordinates with the existing `wholeLineScenery` Gaussian L² fields. The concrete positive-interior contractions are `Cov(U,V)=1/2` (line 60) and `Var(V)+Cov(U,W)=0` (line 69), under `x>rOut(n)`. This supplies Phase 2's joint-law and covariance prerequisites but does not yet prove the nonlinear Gaussian Stein expectation formula or a pathwise random-field version. Full Lake build 4287 jobs; eight exact theorem types checked; complete transitive audit 3502 declarations, only propext/Classical.choice/Quot.sound. Logs `.lake/campaign-ibm-adjoint-04-*`.

## Adjoint-first IBM campaign A5: quartic Stein cancellation — 2026-10-13

`Foundation/IBMGaussianSteinMoments.lean:17–84` derives the actual mixed Gaussian moments `E[U²V²]=Var(U)Var(V)+2Cov(U,V)²` and `E[U³W]=3Var(U)Cov(U,W)` through the existing centered-square and Wick pairings, themselves proved from Gaussian source derivative/divergence duality. The formulas are specialized to the verified jointly Gaussian mollifier triple at lines 99 and 109. On the strict positive interior, `concrete_quartic_stein_cancellation` (line 122) combines the already proved contractions to obtain `(1/2)E[U²V²]+(1/6)E[U³W]=1/4`. `concrete_quartic_correction_expectation` (line 158) verifies integrability and the single expectation `E[(U²/2)V²+(U³/6)W]=1/4`, the exact fixed-mollifier Stein result for `f(z)=z⁴/24` at zero shift. This is a real IBM-specific nonlinear source-adjoint consequence, but the full bounded-smooth `f` formula, random-time integration, local-time boundary and singular first-chaos limit are not proved. Full Lake build 4288 jobs; eleven exact theorem types checked; complete transitive audit 3513 declarations, only propext/Classical.choice/Quot.sound. Logs `.lake/campaign-ibm-adjoint-05-*`.

## Adjoint-first IBM campaign A6: all-point quartic boundary Stein formula — 2026-10-13

`Foundation/IBMGaussianSteinMoments.lean:182` proves for every spatial x that the actual integrable quartic correction has expectation `(1/2)Var(U)[Var(V)+Cov(U,W)]+Cov(U,V)²`. The triple's covariance is independently identified with the Gaussian L² inner product of the original whole-line convolution fields (line 208). `quartic_correction_variance_geometry` (line 218) therefore rewrites the expectation exactly as `(1/4)(σ²_n)'(x)²+(1/4)σ²_n(x)(σ²_n)''(x)`, where `σ²_n(x)=‖wholeLineScenery(kernel n)x‖²`. `quartic_boundary_stein_deviation` (line 258) subtracts the positive-bulk value `1/4`, giving the finite-mollifier boundary deviation `(1/4)[((σ²_n)')²−1+σ²_n(σ²_n)'']`. This holds through the scenery origin; it asserts no Dirac limit, first-chaos convergence, or all-smooth-f Stein identity. Full Lake build 4288 jobs; four exact public types checked; complete transitive audit 3517 declarations, only propext/Classical.choice/Quot.sound. Logs `.lake/campaign-ibm-adjoint-06-*`.

## Adjoint-first IBM campaign A7: negative bulk and corrected two-sided slope — 2026-10-13

`Foundation/IBMNegativeBulkVariance.lean:14` proves the negative-half-line covariance `⟪direction(x+r),direction(x+s)⟫=-x-max(r,s)` when both shifted points are nonpositive. For a continuous mass-one offset kernel with `x+b≤0`, lines 28–76 prove the exact variance `-x-C^-_ρ`, where `C^-_ρ=∫_s ρ(-s)∫_r ρ(-r)max(r,s)`. The normalized whole-line mollifier inherits this at `x≤-rOut(n)` (line 78). Strictly outside the negative support, its first and second variance derivatives are `-1` and `0` (lines 87, 96), and the Gaussian derivative contractions are `⟪U,V⟫=-1/2` and `‖V‖²+⟪U,W⟫=0` (lines 105, 114). The quartic Stein correction expectation nevertheless equals `1/4` on this side too (line 125), because the first variance slope enters quadratically. Thus a claimed unit positive slope on both exterior half-lines is false for the two-sided Brownian scenery covariance; the correct slopes are `+1` and `-1`. These remain fixed-mollifier Gaussian L² and expectation statements, without a pathwise or singular-limit claim. Pinned full Lake build: 4289 jobs. Nine exact public theorem types checked. Complete transitive axiom audit: 3526 declarations, only `propext`, `Classical.choice`, `Quot.sound`. Logs `.lake/campaign-ibm-adjoint-07-*`.

## Adjoint-first IBM campaign A8: Brownian-clock evaluation in iterated Gaussian L² — 2026-10-13

`Foundation/IBMRandomTimeHilbert.lean:18` proves continuity of the concrete smooth scenery as a Gaussian L²-valued spatial map. The maps `randomMollifiedClass n t` and `randomSourceClass t` (lines 25–28) evaluate these **Hilbert classes** at the measurable reflected pre-Brownian clock on a separate Gaussian source; both maps are strongly measurable (lines 31, 36). The exact scenery norm `‖X_x‖²=|x|` (line 46), the uniform mollifier error, and the clock's verified first moment yield genuine membership in `L²(Ω_Y;L²(Ω_X))` (lines 83, 93). The explicit objects at lines 107–111 satisfy `‖U_{n,|Y_t|}-X_{|Y_t|}‖_{L²(Ω_Y;L²(Ω_X))}≤√rOut(n)` (line 114) and converge strongly as `n→∞` (line 137), for each deterministic `t≥0`. The statement is nonvacuous and removes the random-clock evaluation obstruction **only for Hilbert classes**; it does not produce a jointly measurable real field on `Ω_X×ℝ`, a sample-path composition on `Ω_X×Ω_Y`, or a pathwise Itô–Tanaka formula. Full pinned Lake build 4290 jobs, 11 exact theorem types checked, 3537 transitive axiom outputs with only `propext`, `Classical.choice`, `Quot.sound`. Logs `.lake/campaign-ibm-adjoint-08-*`.

## IBM smooth-field increment moments — 2026-10-13

Incoming HEAD: `ccc014559b5985011893d1a89278f0fda6c9344f`. This is one IBM commit beyond the supplied checkpoint: random-clock evaluation is already constructed in iterated L², with no asserted pointwise process. The working tree initially had no tracked changes and twelve unrelated untracked documents. No other active Codex writer or Lean/Lake process was observed; no additional agents were launched.

`Foundation/IBMSmoothIncrementMoments.lean` proves five declarations in namespace `OperatorDerivativeRewrite.Foundation.IBMSmoothIncrementMoments`:

- `convolution_increment_fourth_integrable`: the actual isonormal convolution increment has an integrable fourth power.
- `convolution_increment_fourth`: its fourth moment equals three times the fourth power of the established Gaussian L² increment norm. This holds even without kernel regularity; the existing Bochner-integral conventions remain in force.
- `convolution_increment_fourth_le`: a bound C on the first derivative convolution over [a,b] gives fourth moment at most `3 C⁴ |t-s|⁴` for both points in that interval, for compactly supported C¹ kernels.
- `convolution_compact_increment_bound`: for every compactly supported C² kernel and compact interval, such a nonnegative constant exists. Compactness bounds the continuous L² derivative; the Banach-valued mean-value inequality controls increments; the exact Gaussian fourth moment transfers the estimate to actual deterministic-point representatives.
- `gaussianTriple_compact_increment_bound`: the result applies to each actual normalized mollified field U,V,W, using the concrete bump's C∞ regularity and compact support of its derivatives.

Classification A: unconditional IBM-specific Gaussian field estimates on the actual scenery source. The equality is a scalar integral at deterministic spatial points; the bound is uniform over pairs of spatial points in a fixed compact interval. No Brownian clock or supplied continuous source modification is assumed. This closes a quantitative input for a countable-skeleton continuity construction, not the continuity construction itself. Constants depend on the mollifier, derivative field and interval; no uniform-in-mollifier bound is claimed.

Full pinned Lake build passed 4,291 jobs. Five exact public theorem types checked. Environment-wide transitive axiom audit passed 5,905 safe Foundation declarations, including generated declarations, with only `propext`, `Classical.choice`, `Quot.sound`. This broader counting method is not directly comparable to the historical 3,537 explicit-declaration count. Audit source and logs are retained in `.lake/campaign-ibm-pathwise-01-*`. No prior proof body, dependency pin, manuscript or unrelated document was changed.

Remaining: joint measurable smooth modification, deterministic-coordinate L² agreement on that modification, derivative compatibility on one full-measure event, continuous Brownian clock, local time and actual fixed-mollifier Itô–Tanaka. Existing conditional pathwise chain rules and iterated-L² random-clock convergence do not discharge these obligations. Zeroth-chaos quartic expectations remain distinct from first-chaos projection.


## IBM dyadic common-event control — 2026-10-13

The previous smooth increment milestone was committed as `fb66fe5` (`fb66fe5` is a descendant of incoming HEAD `ccc0145`). `Foundation/IBMSmoothIncrementTails.lean` adds five public theorems in namespace `OperatorDerivativeRewrite.Foundation.IBMSmoothIncrementTails`:

- `convolution_increment_tail`: Markov fourth-power tail estimate with an explicit compact derivative bound.
- `gaussianTriple_compact_tail`: for each actual normalized U,V,W field and compact interval, one constant controls all point pairs and all positive thresholds.
- `gaussianTriple_grid_control`: for arbitrary finite rows of point pairs inside that interval, if `Σ_l m_l h_l⁴/δ_l⁴ < ∞`, then on one full-measure event all row increments are eventually smaller than δ_l simultaneously. The only summability hypothesis is a deterministic grid budget; no stochastic continuity, independence, or desired conclusion is assumed.
- `gaussianTriple_dyadic_control`: on each unit interval [a,a+1], all 2^l adjacent dyadic increments are eventually smaller than `(3/4)^l`, almost surely. The budget is exactly `(32/81)^l` and is proved summable. This theorem is unconditional on the actual Gaussian source.
- `gaussianTriple_common_dyadic_control`: the same full-measure event works for every natural mollifier scale, all three derivative fields, and every integer unit interval. The starting level can depend on the sample, scale, field and interval.

Classification A: unconditional IBM-specific countable-skeleton estimates. This advances the required common-event step without claiming a pathwise extension. No modification, joint spatial/sample measurability, pathwise derivative, local time, or Itô–Tanaka identity is constructed here. Establishing a continuous extension still requires a deterministic dyadic chaining/extension proof, measurable selection by pointwise limits, and deterministic-point identification through mean-square continuity. Obtaining C² requires compatibility of the three continuous extensions with the already verified L² derivative identities; continuity of three separately constructed versions would not alone suffice.

Full Lake build passed 4,292 jobs. Five exact new public types checked. Complete environment-wide safe Foundation axiom audit passed 5,912 declarations (generated declarations included), using only `propext`, `Classical.choice`, `Quot.sound`. Logs and audit source: `.lake/campaign-ibm-pathwise-02-*`. The previous module's verified proof bodies were preserved. No dependency pin, manuscript, unrelated untracked document, reset, push, automation or additional agent was used.


## IBM signed-kernel random-clock integrability — 2026-10-13

The dyadic milestone was committed as `ce7de19`. `Foundation/IBMRandomDerivativeIntegrability.lean` adds four theorems and two definitions in namespace `OperatorDerivativeRewrite.Foundation.IBMRandomDerivativeIntegrability`:

- `kernelMass R ρ = ∫_{-R}^R |ρ(-r)| dr` is the actual absolute kernel mass.
- `offsetScenery_norm_sq_le`: for a continuous signed kernel and R≥0, the existing offset Gaussian convolution obeys `‖Uρ(x)‖² ≤ kernelMass(R,ρ)² (|x|+R)`. This uses the exact Brownian source energy, the triangle inequality and a genuine Bochner integral bound. Neither positivity nor mass one is assumed.
- `wholeLineScenery_norm_sq_le`: the same global bound holds for the original whole-line convolution if ρ vanishes when |z|>R. The previously verified translation theorem identifies the two actual integrals.
- `randomKernelClass ρ t ω = wholeLineScenery ρ |Y_t(ω)|` is an actual Gaussian-L²-valued function on the existing clock factor.
- `randomKernelClass_memLp`: every compactly supported C¹ kernel has `randomKernelClass ρ t ∈ L²(ΩY;L²(ΩX))` at every deterministic clock time. A support radius is obtained from actual compactness, and the growth bound is dominated using the verified clock's integrable first absolute moment. No clock continuity or localization is assumed.
- `randomDerivativeClass_memLp`: this applies to all three actual normalized U,V,W derivative kernels at every fixed clock time, including their signs. This closes global iterated-L² integrability of V and W, beyond the previously verified U case.

Classification A: unconditional IBM-specific Gaussian-class integrability. It is a fixed-time statement, not time-integrated stochastic-integrand square integrability and not a product-space pointwise process. No random representative interchange, nonlinear observable integrability, local supremum integrability or Brownian stochastic integral is asserted. The remaining class-to-field bridge is essential before transferring this conclusion to actual pointwise random-time coefficients.

Full pinned Lake build passed 4,293 jobs. All six new public declaration types checked. Environment-wide safe Foundation transitive axiom audit passed 5,918 declarations, generated declarations included, using only `propext`, `Classical.choice`, `Quot.sound`. Logs and audit source: `.lake/campaign-ibm-pathwise-03-*`. A proof-token scan found no prohibited proof constructs in the new modules (the English word 'admit' appears only in a documentation sentence). Existing verified proof bodies, dependency pins, manuscripts and unrelated files were preserved.

Manuscript checked directly: original PDF SHA256 `5A91914A535AD19BDDF219D7A9AB9F8B5F20A52DD4EC6ED7333AA80B403182BE`. Rendered pages 4 and 6 were inspected. Proposition 3.4 uses local-time coefficient g′(0), consistent with `|Y_t|=|Y_0|+∫sgn(Y_s)dY_s+L⁰_t`. This is manuscript inspection, not a Lean proof of Tanaka or of its IBM application. No new manuscript claim was disproved in this campaign; the previously recorded negative-bulk slope correction remains in force. The PDF is unchanged.


## Pathwise bridge completion report and dependency map — 2026-10-13

### Verified outcome and Git history

The campaign establishes quantitative common-event control of the actual mollified Gaussian scenery skeleton and global fixed-time integrability of its derivative convolutions at the Brownian clock. It does **not** establish a jointly measurable C² modification or a stochastic IBM change-of-variables formula.

Initial HEAD: `ccc014559b5985011893d1a89278f0fda6c9344f`.
Final mathematical HEAD: `ba284cee17a8b8bf133814ea3ddd90d67074c31e`.
The documentation-only commit following this report is identified in the final chat response; its own hash cannot be embedded in its contents.

Substantive verified commits:

1. `fb66fe5e6759d2b83e4f2dd52c8a6bbeeb130671` — exact and compact-uniform fourth moments of the actual Gaussian convolution increments; explicit fourth-power integrability.
2. `ce7de19daccf58256a68e9846d68ba88fe78cd09` — probability tails, finite-grid Borel–Cantelli control, explicit dyadic estimates and one common full-measure event across all scales/derivative fields/integer windows.
3. `ba284cee17a8b8bf133814ea3ddd90d67074c31e` — signed-kernel global growth and fixed-time global L² integrability at the actual independent clock, including U,V,W.

The supplied `023cbcd` checkpoint was historical: incoming `ccc0145` had already proved iterated-L² random-clock evaluation and mollification convergence. That result was inspected and reused, not recreated. The twelve initially untracked unrelated documents remain untouched. No reset, push, automation, extra agent or dependency upgrade was performed.

### Exact new declarations and interpretation

All names have prefix `OperatorDerivativeRewrite.Foundation.`. Source paths are relative to `C:/OperatorDerivativeRewrite`.

| Module | Declaration and source line | Mathematical content and assumptions |
| --- | --- | --- |
| `Foundation/IBMSmoothIncrementMoments.lean` | `IBMSmoothIncrementMoments.convolution_increment_fourth_integrable`, 16 | Fourth power of the actual deterministic-point convolution increment is integrable. |
| same | `convolution_increment_fourth`, 25 | E[(Gρ(t)−Gρ(s))⁴] = 3‖Uρ(t)−Uρ(s)‖⁴. General kernel; actual Bochner conventions. |
| same | `convolution_increment_fourth_le`, 45 | Compactly supported C¹ kernel and explicit derivative bound C on [a,b] imply fourth moment ≤3C⁴|t−s|⁴. |
| same | `convolution_compact_increment_bound`, 66 | For compactly supported C² kernels, compactness supplies C≥0 independently of s,t in [a,b]. |
| same | `gaussianTriple_compact_increment_bound`, 85 | Specializes to each concrete normalized U,V,W field, using the actual smooth bump derivatives. |
| `Foundation/IBMSmoothIncrementTails.lean` | `IBMSmoothIncrementTails.convolution_increment_tail`, 18 | Markov tail bound P(δ⁴≤ΔG⁴)≤3C⁴|t−s|⁴/δ⁴, δ>0. |
| same | `gaussianTriple_compact_tail`, 38 | One compact constant for all pairs and positive thresholds of each actual U,V,W field. |
| same | `gaussianTriple_grid_control`, 57 | Arbitrary finite rows inside [a,b], cardinalities m_l, spacings ≤h_l and positive thresholds δ_l; deterministic summability Σm_l h_l⁴/δ_l⁴ gives almost-sure eventual simultaneous control. |
| same | `gaussianTriple_dyadic_control`, 108 | For each unit interval and actual field, all 2^l adjacent dyadic increments are eventually <(3/4)^l almost surely. Budget (32/81)^l is actually proved summable. |
| same | `gaussianTriple_common_dyadic_control`, 141 | A single probability-one event covers all natural mollifier scales, all three fields and every integer unit interval; eventual levels are allowed to vary. |
| `Foundation/IBMRandomDerivativeIntegrability.lean` | `IBMRandomDerivativeIntegrability.kernelMass`, 18 | Actual absolute kernel mass on [−R,R]. |
| same | `offsetScenery_norm_sq_le`, 23 | Continuous signed ρ and R≥0 give ‖offsetScenery(x)‖²≤A²(|x|+R), A=∫[−R,R]|ρ(−r)|. |
| same | `wholeLineScenery_norm_sq_le`, 54 | Same bound for the original convolution when ρ vanishes outside [−R,R], using the actual translation bridge. |
| same | `randomKernelClass`, 69 | Actual Gaussian-L²-valued map ωY↦Uρ(|Y_t(ωY)|). |
| same | `randomKernelClass_memLp`, 74 | Every compactly supported C¹ kernel has this map in L²(clock;L²(scenery)), at each fixed t. |
| same | `randomDerivativeClass_memLp`, 108 | The same holds for the actual normalized U,V,W kernels. No clock continuity or localization required. |

The new theorems are category **A**, unconditional IBM-specific source-field results. Their Gaussian L² equalities are Hilbert-class statements, while the dyadic bounds concern actual scalar representatives on a countable skeleton. Neither interpretation is silently promoted to an uncountable pathwise equality. The finite-grid theorem has an explicit deterministic summability assumption, discharged in the dyadic application. No stochastic regularity assumption equivalent to the desired conclusion is introduced.

### Build and proof integrity

The three full pinned Lake builds passed **4,291**, **4,292**, and **4,293** jobs, respectively. All sixteen new public declaration types were inspected. The final environment-wide axiom audit checked **5,918 safe Foundation declarations**, including generated declarations, and accepted only `propext`, `Classical.choice`, `Quot.sound`. Earlier milestones checked 5,905 and 5,912. These counts are broader than the historical explicit-declaration audit and must not be interpreted as a declaration-growth comparison.

The audit imports the complete root library, runs `Lean.collectAxioms` for every safe declaration with the Foundation namespace prefix, and throws an error for any other axiom. Logs, exact type output and audit source are retained under `.lake/campaign-ibm-pathwise-01-*`, `02-*`, `03-*`. The new modules contain no proof holes, unsafe definitions or custom axioms. `git diff --check` passed before the final documentation update. The pinned Lean is `v4.34.1`; Mathlib remains pinned at `v4.34.1` with its existing manifest.

### Status of the requested mathematical program

| Requested component | Actual status |
| --- | --- |
| Continuous Brownian sources | Open. Verified coordinate laws and fourth moments remain available; no unconditional continuous modification was constructed. |
| Jointly measurable smooth scenery | Open. New compact moment bounds and one common full-measure dyadic-control event are established. The extension and C² compatibility steps remain. |
| Random-clock mollified IBM | Unconditional fixed-time iterated-L² U construction/convergence was incoming; new global integrability covers V,W too. Existing pointwise continuous processes remain category B, conditional on supplied continuous source paths. |
| Nonlinear pathwise chain rule | Existing category B deterministic convolution theorem `IBMMollifiedScenery.second_chain_rule` remains valid for supplied continuous scenery and explicit test-function derivative assumptions. No new unconditional Gaussian-path instantiation. |
| Brownian local time | Not constructed. Pinned-library searches found no applicable completed Tanaka/local-time theorem. |
| Genuine fixed-mollifier Itô–Tanaka | Not proved. No Brownian integral or local-time term is supplied by the new results. |
| IBM-specific source-adjoint link | Incoming convolution graph identities and Gaussian isometries remain verified. They support L² estimates and smoothing; no new identity connects an actual stochastic change-of-variables correction to the clock adjoint. |
| Full smooth-test Gaussian Stein identity | Open beyond incoming quartic moment/variance identities. New results do not supply a general smooth-test integration-by-parts theorem. |
| First-scenery-chaos residual | Not identified from an actual Itô–Tanaka correction. Quartic expectations remain zeroth-chaos statements. |
| Ordinary L² obstruction | Not proved for an actual correction. No lower-bound/non-Cauchy theorem was established. |
| IBM-specific H⁻¹ convergence | Not proved. Incoming category C bounded differentiation, Dirac channel and assembly transfer remain reusable, but no actual local-time kernel has been supplied. |
| Higher-chaos reconstruction | Open. Neither sector limits nor a convergent full reconstruction were established. |
| Intrinsic observable domain | Incoming abstract restriction/projected-divergence infrastructure remains reusable. Actual IBM cylinder-core density and intrinsic closedness were not discharged. |

**Strongest change-of-variables result actually available:** the deterministic spatial second chain rule for convolution of a supplied continuous scenery path, with explicit first/second derivatives of the test function. It is not a stochastic IBM Itô–Tanaka theorem. No full fixed-mollifier or singular unmollified formula is claimed.

### Dependency map and exact missing edges

Write G_{n,j}(r,ω) for the actual `gaussianTriple n r j ω`, j=0,1,2. Its deterministic-point L² classes are already identified with U,V,W. Let I=[a,b]. The following are desired theorem signatures, not implemented declarations.

1. **Continuous extension and measurable path selection.** From the now-verified moment estimates and dyadic common event, prove

   `∃ S : SampleSpace → C(I,ℝ), Measurable S ∧ ∀ r : I, (fun ω => S ω r) =ᵐ[gaussianProduct] (fun ω => G_{n,j}(r,ω))`.

   Dependencies: deterministic dyadic chaining/uniform continuity on the dense skeleton; complete-target extension; selection by countable limits; mean-square continuity to identify every deterministic coordinate. Obstacle: missing probability/metric-space construction, not missing Gaussian moments. A dyadic increment event alone does not constitute this theorem. Unit-interval constructions must agree on common boundaries, and the resulting global version must be measurable.

2. **Derivative compatibility of the selected continuous fields.** For measurable continuous modifications U,V,W with the actual deterministic-coordinate L² agreement, prove

   `∀ᵐ ω, ∀ r, HasDerivAt (U ω) (V ω r) r ∧ HasDerivAt (V ω) (W ω r) r`.

   Dependencies: legitimate identification of the L² fundamental-theorem-of-calculus integral with the samplewise integral, local integrability/Fubini, a countable common event for endpoint integral identities, then continuity and the classical fundamental theorem. Obstacle: functional-analytic/probability interface. Strong L² differentiation by itself does not imply this conclusion. This yields the actual C² modification needed for the primary theorem.

3. **Actual product-space random-time agreement and integrability.** For the jointly measurable modified field and the actual clock, prove deterministic-time product-a.e. agreement between the pointwise composition and the iterated-L² object, e.g.

   `∀ t, pointwise U(|Y_t|) represents randomMollifiedL2 n t`.

   Dependencies: joint field measurability, deterministic-coordinate modification equality, product Fubini and source independence. The new V,W integrability can then transfer to actual coefficients. Nonlinear test functions still need bounded-derivative or separately proved moment assumptions. Time-integrated stochastic coefficient estimates need an additional finite-horizon argument. Obstacle: representative/product-L² interface.

4. **Continuous Brownian clock.** Construct a measurable path-valued modification of `GaussianTimeProcess.process` with each coordinate a.e. equal to the original, preserving coherent Gaussian laws. Dependencies: actual Brownian moment bounds, dyadic extension and deterministic-point identification. Path-space independence must use measurability on the separate source factors, not pairwise scalar independence. Obstacle: probability construction. An alternative valid Wiener-path probability space may be used with an explicit law/adjoint bridge.

5. **Local time and deterministic reflected-clock composition.** Construct L⁰ and prove

   `g(|Y_t|)−g(|Y_0|) = ∫₀ᵗ g′(|Y_s|)sgn(Y_s)dY_s + g′(0)L⁰_t + (1/2)∫₀ᵗg″(|Y_s|)ds`

   with defined Brownian stochastic integrals, appropriate integrability/localization, and a genuine probability limit defining local time. Dependencies: continuous Brownian clock, stochastic integration and smooth approximation of |·| with convergent derivative terms. Obstacle: substantial probability theory. The convention is `|Y_t|=|Y_0|+∫sgn(Y_s)dY_s+L⁰_t`, so the boundary coefficient is g′(0), not g′(0)/2.

6. **Fixed-mollifier IBM formula and adjoint identification.** Substitute the actual pathwise chain rule into item 5, and identify the adapted clock integral with the existing clock divergence on its proved domain. Dependencies: items 1–5, actual integrability of nonlinear coefficients and measurable conditioning on scenery. Obstacle: stochastic-domain/interface closure. Source graph membership alone is insufficient.

7. **Actual first-chaos residual and Sobolev limit.** Define the correction from item 6, prove its scenery first-chaos projection by source duality, retain every differentiated term and the origin term, then identify actual clock-dependent interior and boundary kernels. Desired limit: `Kε → K` in `L²(ΩY;H⁻¹(ℝ))`. Dependencies: correct projection coefficients, local-time spatial measurability/integrability, actual L² approximate-identity convergence and coefficient convergence; then reuse the existing bounded H⁻¹ assembly. Obstacle: analytic estimates and stochastic projection, not absence of a general bounded derivative operator. Ordinary L² nonconvergence separately requires quantitative lower bounds.

8. **Higher sectors and intrinsic observables.** Prove sector energies/convergence and a reconstruction in a common space before asserting a full correction. For intrinsic IBM calculus, construct actual observable-domain elements and establish the required cylinder-core density or retain a nondense partial adjoint. Dependencies: actual IBM paths and correction plus observable sigma-algebra analysis. Obstacle: mathematical domain/density questions, not merely an operator wrapper.

### Manuscript fidelity and novelty classification

The original 24-page manuscript was checked through its archived text and direct rendered inspection of pages 4 and 6. SHA256 remains `5A91914A535AD19BDDF219D7A9AB9F8B5F20A52DD4EC6ED7333AA80B403182BE`. Page 6 Proposition 3.4 is the intended fixed-mollifier identity; its local-time normalization agrees with item 5. This visual/formula audit is not a Lean proof of the proposition. A complete external literature/novelty review was not completed during this campaign.

The new bounds formalize standard Gaussian moments, compact derivative estimates, Markov and first Borel–Cantelli in the concrete IBM source model. They are verified specialized applications, not claims of mathematical novelty. Existing abstract Sobolev machinery remains category C. No new manuscript claim was disproved here; the incoming category D correction that negative-bulk variance has slope −1 rather than +1 remains essential. All stochastic formula/residual/limit obligations above are category E until proved.

The integration-first source calculus materially simplifies these verified class-level results: its constructed isonormal isometry and source energy make exact Gaussian moments and signed-kernel growth available without assuming sample paths. It has not yet simplified or strengthened a **proved stochastic IBM Itô–Tanaka theorem**, because that theorem remains absent. Defining D=J* does not by itself supply a jointly measurable smooth field, Brownian local time, or intrinsic observable-domain density.

### Three most valuable next targets

1. Close item 1 on one compact interval: measurable continuous modification of each actual Gaussian convolution field from the now-proved dyadic common event, with deterministic-coordinate agreement.
2. Close item 2 and the product-space portion of item 3: pathwise derivative compatibility on one common event and legitimate random-clock evaluation of those exact classes.
3. Construct Brownian local time and prove the reflected-clock smooth-composition theorem in item 5, then instantiate the actual fixed-mollifier IBM formula and clock-adjoint domain identity.


## Quijotic continuity milestone A — 2026-10-13

Incoming HEAD: `36997d45a478c4b2d05fcc48dfdb79d13e2dadc7`. Workspace and Foundation reads passed; a harmless workspace file was written, read and deleted. ResearchSources/ibm contains the original EJP PDF and the corresponding flagship(8).tex. Original PDF SHA256 is unchanged: `5A91914A535AD19BDDF219D7A9AB9F8B5F20A52DD4EC6ED7333AA80B403182BE`. The full preserved PDF text was extracted outside ResearchSources and page 6 was rendered and inspected. The first request attachment was truncated at A4; the replacement was read in full. Git had no tracked changes initially. Twelve unrelated untracked documents and ResearchSources were preserved. Process command-line enumeration through CIM was denied; the accessible process listing showed no Lean/Lake/Git writer. This is limited process evidence, not a guarantee against external writers.

`Foundation/IBMDyadicExtension.lean` closes the unconditional continuous-modification obligation for the actual normalized mollifier triple. It reuses `gaussianTriple_common_dyadic_control`, without another Borel–Cantelli construction. The dyadic rate (3/4)^l corresponds to Holder exponent log_2(4/3), approximately 0.415; the implementation proves continuity and does not assert a Holder theorem. `index_refinement` and `grid_refinement` prove nested-grid compatibility. `rounded_cauchy`, `extension_tendsto`, `extension_tail` and `extension_continuous` construct the actual local limit; the uniform tail is 3(3/4)^l beyond the event's starting level. The explicit dyadic affine interpolant `linear` is measurable in the Gaussian sample at each spatial coordinate and converges uniformly (`linear_tendstoUniformly`, error at most 4(3/4)^l). Continuity of the limit is proved directly by adjacent-cell estimates, rather than by assuming continuity of the interpolants.

`good_measurableSet` and `good_ae` retain one measurable full-measure event for every scale, all three derivative orders and every integer window. Off it, all selected paths are zero. `localPath_coordinate_ae` identifies the limit with the original Gaussian coordinate using spatial L2 continuity and uniqueness of convergence in measure. This is deterministic-coordinate a.e. agreement, not an uncountable intersection of coordinate equalities. `localPath_neighbor`, `windowPath_compatible`, and `field_on_window` prove exact overlap agreement, including interval endpoints, for every sample. A locally finite closed cover gives `field_continuous` globally on R. `field_coordinate_measurable`, `field_jointly_measurable`, and `path_measurable` construct actual real random fields and measurable continuous-path maps. `field_coordinate_ae` proves the original-source modification property. `field_isGaussianProcess` preserves the complete joint Gaussian family indexed by N x Fin 3 x R, including cross-scale finite-dimensional laws.

Classification: verified unconditional IBM-specific result. No supplied continuous scenery or Brownian clock appears in these statements. The fields for i=0,1,2 modify precisely the original U,V,W Gaussian convolution representatives. This completes Milestone A's central mathematical assertion. It does not prove pathwise derivative compatibility merely because three continuous fields now exist.

`Foundation/IBMSpatialFundamental.lean` also proves `wholeLineScenery_continuous`, `wholeLineScenery_integral_deriv`, and `concreteMollifier_integral_derivatives`. Both U(b)-U(a)=integral V and V(b)-V(a)=integral W are actual Gaussian-L2 Bochner identities for arbitrary real endpoints, with integrability justified by continuity of the derivative class. This closes B1 only. Samplewise integral identification, the countable common endpoint event and the pathwise FTC remain required for B2/B3.

Full pinned Lake build: 4,295 jobs, successful. Public types of the continuity, joint measurability, coordinate identification, Gaussian law, interpolation convergence, path measurability and Hilbert FTC theorems were inspected. Environment-wide audit passed 6,010 safe Foundation declarations, allowing only propext, Classical.choice, Quot.sound; no exceptions. Sources and logs: `.lake/quijotic-milestone-a-{build,audit}.*`. New proof sources contain no sorry/admit/unsafe/custom axiom. Existing proof bodies and dependency pins were preserved. Only the two new modules, root imports and audit/state documentation are included in this milestone commit.

Downstream targets: identify samplewise integrals of these exact fields with the Bochner identities; deduce common-event pathwise U'=V and V'=W; transfer fixed-time random-clock L2 integrability to actual jointly measurable product-space evaluations. Continuous Brownian clock/source construction, local time, stochastic Tanaka, fixed-mollifier IBM formula, nonlinear source graph membership, actual first-chaos residual and IBM-specific H^-1 convergence remain open.
