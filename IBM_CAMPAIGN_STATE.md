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
