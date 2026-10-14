# PROJECT STARDUST — OVERNIGHT DISCOVERIES

## Durable campaign state

Started 2026-10-14 from e7dac26ea306c89e3df9ddba015b54554a7caf2b in C:\OperatorDerivativeRewrite. No prior PROJECT_STARDUST_REPORT.md existed. Tracked tree was clean. Preserve the twelve unrelated untracked documents and ResearchSources. Lean 4.34.1 / pinned Mathlib unchanged. No agents, automation, manuscript writes, dependency upgrades, destructive cleanup or push.

This report is durable research memory. Entries marked verified have completed the full build, public type inspection and transitive axiom audit. Ongoing conjectures are separate. No execution after the active session is promised.

## Discovery 1 — Actual Poisson adjunction reconstructs the all-order Charlier ladder

Verified: Foundation/PoissonCharlierLadder.lean constructs monic polynomials recursively by P0=1 and P(n+1)(x)=x Pn(x-1)-lambda Pn(x). Their genuine scalar Poisson-L2 and rate-weighted field-L2 representatives satisfy D P(n+1)=(n+1)Pn and delta Pn=P(n+1), in the exact maximal operator graphs. Every degree has actual number-operator eigenvalue n. These facts follow from the previously verified closed mutual adjoints, with full polynomial moment domains; no formal operator is substituted for a closed operator.

The same adjoint duality proves orthogonality and ||Pn||²=n! lambda^n. The field norm includes its real rate factor: inner_field(Pn,Pm)=lambda inner_scalar(Pn,Pm). This normalization is essential to the ladder and energy calculation.

Mathematical significance: the Gaussian Wick and Poisson Charlier systems are both reconstructed by source raising/lowering adjunction, despite distinct local chain rules. This is known Charlier mathematics, now connected to the repository's actual unbounded Poisson operators; no new mathematical novelty claim. Reference for standard nomenclature/recurrences: https://dlmf.nist.gov/18.22.

Verification: full Lake build 4310 jobs (.lake/stardust-01-build.log), all 21 public declarations type-checked and 6255 safe Foundation declarations transitively audited (.lake/stardust-01-audit.lean and .log). Only propext, Classical.choice, Quot.sound. No placeholders/custom axioms/unsafe additions. The independently verified milestone commit is the commit containing this entry.

Reflection: equal ladder energy does not imply equal multiplication algebra or ordinary chain rules. Poisson polynomial completeness and a unitary transfer to Gaussian chaos are not yet proved. A future focused campaign could establish polynomial density, the Poisson number spectral decomposition and a precise Hilbert transfer while exhibiting multiplication defects.

## Investigation register

| Direction | Status | Next obligation |
| --- | --- | --- |
| All-order actual Poisson Charlier ladder | VERIFIED, COMPLETE BASIS | Density, normalized basis and full centered recovery now verified |
| Nonlinear Wick prediction from fractional observations | VERIFIED | Sharp asymptotics and full-past versus one-coordinate comparison |
| Bounded right inverse of full Gaussian divergence on centered L2 | VERIFIED | Full gradient-range projection and comparison with adapted representation |
| Gaussian/Poisson Hilbert transfer versus multiplication | VERIFIED ON COMPLETE SCALAR SPACES | Exact closed-operator intertwining; retain multiplication defect |
| Source-Hilbert to physical IBM white-noise kernel bridge | OPEN FROM IBM CAMPAIGN | Construct actual isometry before physical kernel/H^-1 claims |
| Quartic Banach inverse regularity at zero | VERIFIED, EXHAUSTED | Optimal exponent 1/3; move to nondegenerate data away from zero |
| Quadratic Gaussian metric roughness and antipodes | VERIFIED | Higher-degree or actual normalized-kernel applications |
| Bochner-field Gaussian divergence recovery | VERIFIED | Apply to actual nonlinear observables with L2 membership discharged |
| Actual IBM cubic per-path time integrability/projection | VERIFIED | Joint clock moments, representatives/Fubini and physical kernel |
| Full Gaussian gradient-range Hodge decomposition | VERIFIED | Intrinsic/predictable restrictions and concrete source-kernel comparison |

## Complete public locations — discovery 1

All names have prefix OperatorDerivativeRewrite.Foundation.PoissonCharlierLadder.

| Name | Source |
| --- | --- |
| polynomial | Foundation/PoissonCharlierLadder.lean:15 |
| value | Foundation/PoissonCharlierLadder.lean:20 |
| value_zero | Foundation/PoissonCharlierLadder.lean:22 |
| value_succ | Foundation/PoissonCharlierLadder.lean:25 |
| value_lowering | Foundation/PoissonCharlierLadder.lean:29 |
| value_memLp | Foundation/PoissonCharlierLadder.lean:47 |
| value_field_memLp | Foundation/PoissonCharlierLadder.lean:51 |
| scalar | Foundation/PoissonCharlierLadder.lean:55 |
| field | Foundation/PoissonCharlierLadder.lean:58 |
| scalar_apply | Foundation/PoissonCharlierLadder.lean:61 |
| field_apply | Foundation/PoissonCharlierLadder.lean:65 |
| lowering_graph | Foundation/PoissonCharlierLadder.lean:70 |
| raising_graph | Foundation/PoissonCharlierLadder.lean:78 |
| number_eigen_graph | Foundation/PoissonCharlierLadder.lean:89 |
| graph_duality | Foundation/PoissonCharlierLadder.lean:96 |
| eigen_graph | Foundation/PoissonCharlierLadder.lean:106 |
| scalar_orthogonal | Foundation/PoissonCharlierLadder.lean:123 |
| field_inner | Foundation/PoissonCharlierLadder.lean:135 |
| scalar_norm_sq_succ | Foundation/PoissonCharlierLadder.lean:147 |
| scalar_norm_sq | Foundation/PoissonCharlierLadder.lean:154 |
| scalar_inner | Foundation/PoissonCharlierLadder.lean:170 |

## Discovery 2 — Nonlinear fractional prediction survives in every Wick degree

Verified: GaussianWickPredictionBound proves that the actual Wick polynomial of any observed source direction belongs to the full generated Gaussian sigma-algebra space, even with uncountable, correlated or degenerate observations. For arbitrary terminal direction u, observed direction h_i and degree n, the pairing of the actual conditional projection of Wick_n(u) against Wick_n(h_i) is n! <u,h_i>^n. Cauchy then gives the exact nondivided energy lower bound; zero observation directions are allowed in that abstract statement.

The actual fractional Brownian specialization uses its previously constructed source direction and full past up to t. For 0<H<1, 0<t<=1, every degree n has
||E[Wick_n(X_1) | past_t]||² >= n! (t^(2H))^n / 4^n.
A sharper covariance quotient bound is also proved for all t>0. The conditional projection is the repository's actual conditional expectation in Gaussian L2; no ad hoc projection, independence assumption or covariance inverse is introduced. Wick_n is not itself Gaussian when n>1.

Mathematical significance: the earlier first-chaos prediction obstruction extends to all nonlinear Hermite degrees by testing against one observed Wick coordinate. It connects conditional-space density, chaos algebra and the actual fractional covariance kernel. The bound supplies a norm-level lower scale t^(Hn); it is a lower bound, not an exact prediction asymptotic or a matching upper estimate. No new global memory/Markov claim is made.

Verification: full pinned Lake build 4311 jobs (.lake/stardust-02-build.log); all seven public types checked; 6267 safe Foundation declarations transitively audited, only propext/Classical.choice/Quot.sound (.lake/stardust-02-audit.lean and .log). Discovery 1 commit: ffe1a503a484bf6061536c1f2c6508e5dca0fd21. Discovery 2 is the commit containing this entry.

Reflection/new questions: find sharp small-time prediction asymptotics and matching upper bounds, and compare conditioning on the entire past with conditioning on the single current coordinate. Any proposed remainder estimate must respect the degree-dependent lower scale. The proof does not yet establish sharpness or a new process regularity theorem. This is worth a focused fractional prediction campaign after the operator discoveries.

### Public locations — discovery 2

Prefix: OperatorDerivativeRewrite.Foundation.GaussianWickPredictionBound.

| Name | Source |
| --- | --- |
| observed_wick_mem | Foundation/GaussianWickPredictionBound.lean:14 |
| forecast_wick_pairing | Foundation/GaussianWickPredictionBound.lean:27 |
| forecast_wick_energy_lower | Foundation/GaussianWickPredictionBound.lean:40 |
| Fractional.forecast | Foundation/GaussianWickPredictionBound.lean:60 |
| Fractional.forecast_covariance_lower | Foundation/GaussianWickPredictionBound.lean:63 |
| Fractional.forecast_norm_sq_lower | Foundation/GaussianWickPredictionBound.lean:80 |
| Fractional.forecast_small_time_lower | Foundation/GaussianWickPredictionBound.lean:98 |

## Discovery 3 — Bounded minimum-norm recovery for full Gaussian source divergence

Verified: GaussianDivergenceRecovery constructs R f = sum_{n>=1} n^(-1) D P_n f for EVERY ambient Gaussian-L2 target f. Orthogonal summability and the closed divergence graph are proved from the complete actual number-sector decomposition. Thus (R f, f-P0 f) belongs to the full source divergence graph without assuming f is Malliavin differentiable.

R is a genuine bounded linear operator with ||R f||<=||f||. Its exact energy is ||R f||²=sum_{n>=1} n^(-1)||P_n f||². It is perpendicular to every divergence-free field and has minimum norm among all source divergence preimages of f-P0 f. The full source divergence range is exactly {f: inner gaussianOne f=0}.

The adjoint gives another substantive identity: if (f,g) belongs to the FULL closed derivative graph, R* g=f-P0 f. This bounded adjoint is a potential-recovery operator, not the unbounded Malliavin derivative itself. It demonstrates why naming an arbitrary bounded integration map and taking its adjoint does not automatically reconstruct the full derivative.

Mathematical significance: integration-first source recovery is available on the entire centered L2 target, with one inverse number weight. It connects the Gaussian chaos energy, Poincare estimate, closed unbounded adjunction, orthogonal kernel decomposition and minimum-norm inverse. This is classical source Hodge/pseudoinverse mathematics, newly verified through the repository's actual graph infrastructure; no novelty claim.

Limitations: this is full ambient Gaussian source divergence, not predictable Ito representation, not an intrinsic IBM observable domain, and not spatial H^-1 regularity. The inverse number weight concerns chaos degree; it cannot substitute for a physical spatial frequency estimate. No martingale representation property is inferred.

Verification: full Lake build 4312 jobs (.lake/stardust-03-build.log); all 19 public types checked; 6300 safe Foundation declarations transitively audited with only propext/Classical.choice/Quot.sound (.lake/stardust-03-audit.lean and .log). Prior checkpoints: ffe1a503a484bf6061536c1f2c6508e5dca0fd21 and b968ae9 (fractional Wick prediction). Discovery 3 is the commit containing this entry.

Reflection: source-divergence recovery is now a priority for nonlinear observables because it requires no target derivative-domain hypothesis. A future focused campaign should identify the orthogonal projection onto the full gradient range and its closed-range decomposition, then compare this source recovery with adapted representation. Poisson transfer would additionally require the unproved complete Charlier spectral decomposition.

### Public locations — discovery 3

Prefix: OperatorDerivativeRewrite.Foundation.GaussianDivergenceRecovery.

| Name | Source |
| --- | --- |
| inverseGradientComponent | Foundation/GaussianDivergenceRecovery.lean:13 |
| inverseGradient_norm_sq | Foundation/GaussianDivergenceRecovery.lean:16 |
| inverseGradient_norm_sq_le | Foundation/GaussianDivergenceRecovery.lean:26 |
| inverseGradient_summable | Foundation/GaussianDivergenceRecovery.lean:38 |
| recovery | Foundation/GaussianDivergenceRecovery.lean:46 |
| centeredComponent | Foundation/GaussianDivergenceRecovery.lean:49 |
| centeredComponent_hasSum | Foundation/GaussianDivergenceRecovery.lean:52 |
| inverseGradient_divergence_graph | Foundation/GaussianDivergenceRecovery.lean:56 |
| recovery_graph | Foundation/GaussianDivergenceRecovery.lean:70 |
| recovery_energy_hasSum | Foundation/GaussianDivergenceRecovery.lean:83 |
| recovery_norm_le | Foundation/GaussianDivergenceRecovery.lean:99 |
| recovery_inverse_energy_hasSum | Foundation/GaussianDivergenceRecovery.lean:104 |
| recovery_add | Foundation/GaussianDivergenceRecovery.lean:108 |
| recovery_smul | Foundation/GaussianDivergenceRecovery.lean:125 |
| recoveryOperator | Foundation/GaussianDivergenceRecovery.lean:139 |
| recovery_orthogonal_kernel | Foundation/GaussianDivergenceRecovery.lean:148 |
| recovery_minimal_norm | Foundation/GaussianDivergenceRecovery.lean:166 |
| exists_divergence_iff_centered | Foundation/GaussianDivergenceRecovery.lean:178 |
| recovery_adjoint_derivative | Foundation/GaussianDivergenceRecovery.lean:193 |

## Discovery 4 — Quartic Banach recovery cannot have a local linear modulus

Verified: BanachQuarticInverseObstruction proves the actual L4 duality map and normal map have cubic homogeneity. Under the existing explicit positive lower bound on delta, completeness and a nonzero source vector, every dual neighborhood of zero violates every proposed linear inverse bound. Precisely: for any real K and r>0, there is ||f||<r with K||f||<||inverse(f)-inverse(0)||. Consequently the full inverse is not globally Lipschitz for any Lipschitz constant.

The proof uses the genuine complete-space normalFourEquiv, not a scalar toy inverse: shrinking the source by a shrinks its dual datum by a³. The existing 1/3-Holder theorem remains valid. This milestone rules out a linear modulus, but does not yet formally prove failure of EVERY Holder exponent above 1/3; that sharper claim remains a clear homogeneity-based next theorem.

Mathematical significance: the linear Gaussian source recovery of discovery 3 and the nonlinear Banach quartic inverse have fundamentally different stability near zero. Bijectivity and a quantitative coercive normal map do not upgrade the quartic inverse to Lipschitz regularity. This corrects a tempting inference, not a documented erroneous repository theorem; all existing verified statements remain intact.

Verification: full Lake build 4313 jobs (.lake/stardust-04-build.log); seven public types checked; 6307 safe Foundation declarations audited transitively with only propext/Classical.choice/Quot.sound (.lake/stardust-04-audit.lean and .log). Gaussian recovery checkpoint: d66d16dc3f7142b1ca6456394b0c089283790fdb. Discovery 4 is the commit containing this entry.

Reflection: investigate the exact optimal Holder exponent and stability away from zero. Do not infer a global Lipschitz algorithm for Banach recovery from the Gaussian bounded inverse. This branch warrants a focused quantitative nonlinear inverse campaign if recovery algorithms become a priority.

### Public locations — discovery 4

Prefix: OperatorDerivativeRewrite.Foundation.BanachQuarticInverseObstruction.

| Name | Source |
| --- | --- |
| dualityFour_smul | Foundation/BanachQuarticInverseObstruction.lean:17 |
| normalFour_smul | Foundation/BanachQuarticInverseObstruction.lean:26 |
| normalFour_zero | Foundation/BanachQuarticInverseObstruction.lean:30 |
| inverse_normalFour | Foundation/BanachQuarticInverseObstruction.lean:35 |
| inverse_zero | Foundation/BanachQuarticInverseObstruction.lean:40 |
| no_local_linear_bound | Foundation/BanachQuarticInverseObstruction.lean:48 |
| inverse_not_lipschitz | Foundation/BanachQuarticInverseObstruction.lean:78 |

## Discovery 5 — Finite Gaussian/Poisson chaos isometry does not preserve squaring

Verified: GaussianPoissonChaosTransfer matches the exact inner products of every finite Charlier expansion and Gaussian Wick expansion with the same coefficient list and variance lambda. It constructs an actual matching source direction in the repository's l2 CoefficientSpace, so the concrete norm transfer has no existential or artificial direction hypothesis.

This Hilbert transfer does not identify ordinary polynomial multiplication. The actual centered Poisson square decomposes as P2+P1+lambda P0. The corresponding Gaussian square is Wick2+lambda Wick0, with an actual AE square realization. The Poisson square pairs with its first polynomial mode by lambda>0; the Gaussian square pairs with its first Wick mode by exactly zero. Both second modes nevertheless have norm²=2 lambda². Thus equal chaos Gram geometry is compatible with different products, jump chain rules and parity.

Mathematical significance: the adjoint ladders discovered in milestone 1 support a concrete finite Hilbert transfer, while the product defect prevents a naive algebraic transfer of nonlinear observables. This directly tests a tempting stronger conjecture rather than assuming a Gaussian analogy supplies jump calculus.

Limitations: finite coefficients only. No completed unitary onto the whole Poisson L2 space, polynomial density, full Poisson chaos projection characterization, multiplication-preserving map, process coupling or limit theorem is claimed. The nonzero Poisson pairing concerns the genuine first polynomial eigenmode; it does not substitute for an unproved full spectral completeness theorem.

Verification: full Lake build 4314 jobs (.lake/stardust-05-build.log); all 15 public types checked; 6332 safe Foundation declarations transitively audited, only propext/Classical.choice/Quot.sound (.lake/stardust-05-audit.lean and .log). Prior Banach checkpoint: f45c9ca. Discovery 5 is the commit containing this entry.

Reflection: a future Poisson spectral campaign should first prove polynomial density and then extend the finite isometry to a unitary on the appropriate generated spaces. The multiplication defect should remain part of its specification. Shared number eigenvalues do not make Gaussian and Poisson stochastic calculus interchangeable.

### Public locations — discovery 5

Prefix: OperatorDerivativeRewrite.Foundation.GaussianPoissonChaosTransfer.

| Name | Source |
| --- | --- |
| poissonExpansion | Foundation/GaussianPoissonChaosTransfer.lean:15 |
| gaussianExpansion | Foundation/GaussianPoissonChaosTransfer.lean:18 |
| poissonExpansion_inner | Foundation/GaussianPoissonChaosTransfer.lean:21 |
| gaussianExpansion_inner | Foundation/GaussianPoissonChaosTransfer.lean:29 |
| finite_chaos_inner_transfer | Foundation/GaussianPoissonChaosTransfer.lean:38 |
| finite_chaos_norm_transfer | Foundation/GaussianPoissonChaosTransfer.lean:44 |
| matchingDirection | Foundation/GaussianPoissonChaosTransfer.lean:51 |
| matchingDirection_norm_sq | Foundation/GaussianPoissonChaosTransfer.lean:54 |
| concrete_finite_chaos_norm_transfer | Foundation/GaussianPoissonChaosTransfer.lean:58 |
| charlier_one | Foundation/GaussianPoissonChaosTransfer.lean:63 |
| charlier_two | Foundation/GaussianPoissonChaosTransfer.lean:67 |
| poisson_square_decomposition | Foundation/GaussianPoissonChaosTransfer.lean:74 |
| poisson_square_first_inner | Foundation/GaussianPoissonChaosTransfer.lean:89 |
| gaussian_square_first_inner | Foundation/GaussianPoissonChaosTransfer.lean:95 |
| gaussian_square_coeFn | Foundation/GaussianPoissonChaosTransfer.lean:101 |

## Discovery 6 — Quadratic Gaussian chaos preserves local metric roughness but folds antipodes

Verified: GaussianQuadraticGeometry computes the exact second-chaos distance. For source directions h,k with ||h||²=||k||²=v,
||Wick2(h)-Wick2(k)||²=2(v+<h,k>)||h-k||².
When <h,k>>=0, the distance is bounded below by 2v||h-k||² and above by 4v||h-k||². These are nonvacuous metric comparisons for positive fixed variance, using the actual Gaussian L2 realization and source Hilbert inner product.

Globally Wick2(h)=Wick2(-h). Thus the quadratic-chaos map is not injective on a full nontrivial sphere, even though it preserves metric regularity up to constants on positively correlated fixed-variance pairs. The source geometry is the same second-chaos Gram kernel found earlier, now used as an exact nonlinear metric calculation.

Mathematical significance: higher chaos does not automatically improve mean-square increment regularity at fixed variance. For a source-direction process satisfying the explicit fixed-variance and positive-pair-correlation hypotheses, its quadratic Wick increments have the same L2 metric exponent, up to constants. The initial-time variance power of a vanishing process is a different question. This is a precise geometric restriction, not a sample-path Holder theorem or a full curvature/manifold formalization.

Verification: full Lake build 4315 jobs (.lake/stardust-06-build.log); five public types checked; 6337 safe Foundation declarations transitively audited, only propext/Classical.choice/Quot.sound (.lake/stardust-06-audit.lean and .log). Finite Gaussian/Poisson transfer checkpoint: 2ec5d9b. Discovery 6 is the commit containing this entry.

Reflection: test this metric comparison on normalized fractional and SPDE kernel directions. A focused kernel-geometry campaign could extend it to every chaos degree and identify the projective/folding geometry explicitly. Do not infer an improved regularity exponent merely from increasing polynomial degree.

### Public locations — discovery 6

Prefix: OperatorDerivativeRewrite.Foundation.GaussianQuadraticGeometry.

| Name | Source |
| --- | --- |
| wick_two_norm_sq | Foundation/GaussianQuadraticGeometry.lean:13 |
| wick_two_distance_sq | Foundation/GaussianQuadraticGeometry.lean:18 |
| fixed_variance_distance_sq | Foundation/GaussianQuadraticGeometry.lean:26 |
| positive_correlation_distance_bounds | Foundation/GaussianQuadraticGeometry.lean:33 |
| wick_two_antipodal | Foundation/GaussianQuadraticGeometry.lean:47 |

## Discovery 7 — Minimum-norm Gaussian divergence recovery transfers to random Bochner fields

Verified: GaussianBochnerDivergenceRecovery lifts the bounded recovery operator to L2(mu;GaussianL2) for an arbitrary external measurable space and measure mu. The lifted field satisfies the ORIGINAL source divergence graph almost everywhere, has norm at most the input norm, and is minimum norm among all Bochner-L2 preimages of the centered input field.

The exact range criterion is fiber centering: a Bochner-L2 scalar field u has an actual Bochner-L2 divergence preimage iff inner(gaussianOne,u(x))=0 for mu-almost every x. No finite-measure, independent-parameter, intrinsic stochastic-integral, or source-differentiability hypothesis is added. This is a theorem in the verified BochnerClosedOperator.lift graph, not merely a formal pointwise family with unproved measurability.

Mathematical significance: stochastic parameters, time variables and Gaussian source recovery can now be combined by a bounded operator. It connects the all-chaos recovery with the closed fiber calculus used in Brownian, IBM and SPDE branches. Once an actual observable is known to be a Bochner-L2 field, no further source-derivative domain theorem is needed to construct its centered full-divergence representation.

Limitations: the Bochner-L2 membership of an actual random-clock cubic observable is still an analytic input; this transfer does not prove it. It does not construct a predictable stochastic integral, local time, a physical spatial kernel or an IBM H^-1 limit. A joint scalar representative identification still uses the existing justified product/Fubini machinery.

Verification: full Lake build 4316 jobs (.lake/stardust-07-build.log); all eight public types checked; 6352 safe Foundation declarations transitively audited, only propext/Classical.choice/Quot.sound (.lake/stardust-07-audit.lean and .log). Quadratic geometry checkpoint: 388488d. Discovery 7 is the commit containing this entry.

Reflection: apply this transfer to verified actual finite-horizon Gaussian response fields, then polynomial observables with discharged moment estimates. New active exploration: continuity of finite Wick polynomials in source direction may remove the explicit per-clock-path Bochner integrability hypothesis in the earlier IBM cubic time projection. This would still be distinct from a joint clock L2 estimate and from stochastic Ito–Tanaka.

### Public locations — discovery 7

Prefix: OperatorDerivativeRewrite.Foundation.GaussianBochnerDivergenceRecovery.

| Name | Source |
| --- | --- |
| fiberRecovery | Foundation/GaussianBochnerDivergenceRecovery.lean:14 |
| fiberCenter | Foundation/GaussianBochnerDivergenceRecovery.lean:17 |
| fiberRecovery_coeFn | Foundation/GaussianBochnerDivergenceRecovery.lean:20 |
| fiberCenter_coeFn | Foundation/GaussianBochnerDivergenceRecovery.lean:24 |
| fiberRecovery_graph | Foundation/GaussianBochnerDivergenceRecovery.lean:28 |
| fiberRecovery_norm_le | Foundation/GaussianBochnerDivergenceRecovery.lean:36 |
| fiberRecovery_minimal_norm | Foundation/GaussianBochnerDivergenceRecovery.lean:42 |
| exists_fiber_divergence_iff_centered | Foundation/GaussianBochnerDivergenceRecovery.lean:52 |

## Discovery 8 — Wick continuity discharges the actual IBM per-path time hypothesis

Verified: GaussianWickContinuity derives continuity of every finite Wick degree in its source direction from the exact mixed-moment distance formula. It proves continuity of cube and the polarized cubic correction for continuous direction families; no choice of pointwise Gaussian representatives is assumed.

IBMClockCubicTimeProjection applies this to the actual mollified scenery directions. The cubic spatialCorrection and its genuine SpectralSpace sourceVector are continuous in x. Consequently both the Gaussian-L2 correction along |clockPath(omegaY)(s)| and its source Hilbert vector are Bochner integrable on EVERY finite horizon for EVERY actual constructed clock path.

The earlier IBMClockCubicCorrection.time_integrated_source_vector theorem had an explicit Integrable hypothesis. The new IBMClockCubicTimeProjection.time_integrated_projection discharges that hypothesis unconditionally and proves
P1 integral_0^T C_n(|Y_s|) ds = isonormalEmbedding(integral_0^T sourceVector_n(|Y_s|) ds)
in the scenery Gaussian-L2 section at each actual clock path. The exact sourceVector retains the origin variance layer and reflected-clock nonnegative geometry. Both integrals are independently shown to exist.

Mathematical significance: an exploratory general Gaussian continuity theorem resolves a concrete open IBM input from the preceding campaign. Per-clock-path Bochner integrability follows from continuity and compact time, without needing joint clock moment estimates. This distinction prevents imposing an unnecessary probabilistic prerequisite on a valid section-level theorem.

Limitations: joint L2 over the Brownian clock, scalar representative/time-integral Fubini identification, source graph-norm time interchange, physical white-noise identification, Brownian local time, stochastic Ito–Tanaka, residual L2 obstruction and spatial H^-1 limits remain separate. This is unconditional source-section time projection, not the complete stochastic IBM correction. The manuscript's stochastic interior term additionally carries its overall 1/2 factor.

Verification: full Lake build 4318 jobs (.lake/stardust-08-build.log); all eleven new public types checked; 6363 safe Foundation declarations transitively audited with only propext/Classical.choice/Quot.sound (.lake/stardust-08-audit.lean and .log). Bochner recovery checkpoint: ac57c27. Discovery 8 is the commit containing this entry.

Reflection: prioritize actual representative/Fubini and random-clock moment/domain estimates now that this per-path hypothesis is removed. This application justifies shifting some research effort from general infrastructure toward concrete nonlinear source observables. The next source-kernel and local-time dependencies are unchanged.

### Public locations — discovery 8

Prefix: OperatorDerivativeRewrite.Foundation.

| Name | Source |
| --- | --- |
| GaussianWickContinuity.wick_norm_sq | Foundation/GaussianWickContinuity.lean:13 |
| GaussianWickContinuity.wick_distance_sq | Foundation/GaussianWickContinuity.lean:17 |
| GaussianWickContinuity.wick_continuous | Foundation/GaussianWickContinuity.lean:23 |
| GaussianWickContinuity.cube_continuous | Foundation/GaussianWickContinuity.lean:38 |
| GaussianWickContinuity.correction_continuous_of | Foundation/GaussianWickContinuity.lean:44 |
| IBMClockCubicTimeProjection.tripleCoefficient_continuous | Foundation/IBMClockCubicTimeProjection.lean:16 |
| IBMClockCubicTimeProjection.spatialCorrection_continuous | Foundation/IBMClockCubicTimeProjection.lean:27 |
| IBMClockCubicTimeProjection.sourceVector_continuous | Foundation/IBMClockCubicTimeProjection.lean:32 |
| IBMClockCubicTimeProjection.sectionClass_time_integrable | Foundation/IBMClockCubicTimeProjection.lean:42 |
| IBMClockCubicTimeProjection.sourceVector_time_integrable | Foundation/IBMClockCubicTimeProjection.lean:50 |
| IBMClockCubicTimeProjection.time_integrated_projection | Foundation/IBMClockCubicTimeProjection.lean:58 |

## Discovery 9 — The quartic inverse exponent 1/3 is optimal at zero

Verified: BanachQuarticHolderSharpness.no_local_holder_bound upgrades discovery 4. Under the same explicit lower bound, completeness and a nonzero source vector, EVERY exponent q>1/3 fails locally at zero: for any radius r>0 and any proposed real constant K, there is ||f||<r with K||f||^q<||inverse(f)-inverse(0)||.

Together with the previously verified global 1/3-Holder inverse estimate, this establishes the precise optimal Holder exponent at zero for the actual complete-space quartic normal equation. Cubic homogeneity and a justified small-parameter limit prove the obstruction. No scalar replacement for the full Banach inverse, assumed inverse asymptotic or missing limit interchange occurs.

This supersedes the explicit unresolved sharper-exponent note in discovery 4. The source nontriviality and positive lower bound are essential hypotheses; no obstruction is claimed for the zero source space. Stability away from zero remains a separate question.

Verification: full Lake build 4319 jobs (.lake/stardust-09-build.log); the exact new public type checked; 6364 safe Foundation declarations transitively audited with only propext/Classical.choice/Quot.sound (.lake/stardust-09-audit.lean and .log). An informational ring normalization suggestion appears in the build log, but Lean completed with no errors or placeholders. IBM time-projection checkpoint: 8d5def4. Discovery 9 is the commit containing this entry.

Reflection: nonlinear inverse estimates have a proved sharp boundary at zero. A numerical or operator reconstruction plan should respect this modulus instead of seeking a globally or locally linear inverse estimate. A focused campaign can now examine nondegenerate data away from zero, rather than repeating the exhausted near-zero Lipschitz conjecture.

Public location: OperatorDerivativeRewrite.Foundation.BanachQuarticHolderSharpness.no_local_holder_bound — Foundation/BanachQuarticHolderSharpness.lean:17.

## Discovery 10 — Full Gaussian source Hodge decomposition and closed gradient range

Verified: GaussianSourceHodge defines the actual gradient range by the output projection of the full closed derivative graph. Membership is equivalent to (R* v,v) belonging to that same graph. This characterizes the range as a continuous preimage of a closed graph and proves it is closed, without an assumed closed-range theorem.

Its orthogonal complement is exactly the full source divergence kernel, including domain membership. The genuine orthogonal gradientProjection splits every ambient Gaussian vector field into its gradient part and a divergence-free residual. For EVERY vector field v, (R* v,gradientProjection v) lies in the full derivative graph. Thus the bounded potential-recovery adjoint provides the correct potential domain automatically; it is still not the unbounded derivative itself.

Mathematical significance: discovery 3's minimum-norm divergence recovery now yields the complementary full source Hodge geometry. It connects closed unbounded adjunction, the Gaussian spectral gap, bounded recovery, and orthogonal projection. The construction is actual operator-domain mathematics, not a formal decomposition into unspecified derivatives and kernels.

Limitations: ambient source fields, not predictable fields or intrinsic IBM observables. No adapted projection, stochastic PRP, physical spatial Helmholtz decomposition or geometric curvature theorem is inferred. The Bochner transfer can subsequently be applied with its explicit actual L2 domain input.

Verification: full Lake build 4320 jobs (.lake/stardust-10-build.log); all ten public types checked; 6385 safe Foundation declarations transitively audited with only propext/Classical.choice/Quot.sound (.lake/stardust-10-audit.lean and .log). Sharp quartic inverse checkpoint: 92adc06. Discovery 10 is the commit containing this entry.

Reflection: the formerly open full gradient-range question in the register is resolved. Next compare the solenoidal kernels of the actual Poisson one-count model and Gaussian source, then revisit which intrinsic/predictable restrictions survive source Hodge projection. Do not replace these restrictions with ambient source completeness.

### Public locations — discovery 10

Prefix: OperatorDerivativeRewrite.Foundation.GaussianSourceHodge.

| Name | Source |
| --- | --- |
| gradientRange | Foundation/GaussianSourceHodge.lean:12 |
| mem_gradientRange_iff | Foundation/GaussianSourceHodge.lean:15 |
| gradientRange_recovery_characterization | Foundation/GaussianSourceHodge.lean:23 |
| gradientRange_isClosed | Foundation/GaussianSourceHodge.lean:38 |
| gradientRange_orthogonal_iff_divergence_zero | Foundation/GaussianSourceHodge.lean:50 |
| gradientProjection | Foundation/GaussianSourceHodge.lean:66 |
| gradientProjection_mem | Foundation/GaussianSourceHodge.lean:68 |
| residual_divergence_zero | Foundation/GaussianSourceHodge.lean:71 |
| recovery_adjoint_kernel_zero | Foundation/GaussianSourceHodge.lean:78 |
| potential_gradient_graph | Foundation/GaussianSourceHodge.lean:88 |

## Discovery 11 — Divergence kernels expose a dimensional obstruction to naive transfer

Verified: DivergenceKernelContrast proves that the full maximal divergence of the positive-rate one-count Poisson model has trivial kernel. The count-zero boundary fixes u(0)=0, and the actual divergence recurrence inductively fixes every positive-mass atom. This is an operator-graph theorem on genuine rate-weighted L2 classes.

For the actual Gaussian source, the polynomial skew field X_k h-X_h k belongs to the full divergence domain and has divergence zero. Its exact norm² is 2(||h||²||k||²-<h,k>²). Explicit distinct unit l2 source directions give a nonzero example of norm²=2. The cancellation is verified from the genuine rank-divergence graphs, not assumed as a formal rotational symmetry.

Mathematical significance: matching scalar chaos norms does not match the uniqueness geometry of divergence preimages. Gaussian minimum-norm selection matters because solenoidal fields actually exist; the one-count Poisson preimage, when it exists, is unique. This is a DIMENSIONAL comparison between one count and a Gaussian source with at least two directions, not a claim that all Poisson divergences are injective.

Verification: full Lake build 4321 jobs (.lake/stardust-11-build.log); all seven public types checked; 6402 safe Foundation declarations transitively audited with only propext/Classical.choice/Quot.sound (.lake/stardust-11-audit.lean and .log). Source Hodge checkpoint: 197147f. Discovery 11 is the commit containing this entry.

Reflection: compare multidimensional Poisson skew/curl fields before generalizing the injectivity result. Current next step: construct unique contractive recovery for finite positive Charlier expansions, while leaving the full polynomial-density obligation explicit. Do not infer vector-valued noise transfer merely from a scalar Hilbert isometry.

### Public locations — discovery 11

Prefix: OperatorDerivativeRewrite.Foundation.DivergenceKernelContrast.

| Name | Source |
| --- | --- |
| poisson_divergence_zero_iff | Foundation/DivergenceKernelContrast.lean:16 |
| firstChaosPolynomial_eq_embedding | Foundation/DivergenceKernelContrast.lean:42 |
| rankDivergence_linear_symmetric | Foundation/DivergenceKernelContrast.lean:46 |
| skewField | Foundation/DivergenceKernelContrast.lean:57 |
| skewField_divergence_zero | Foundation/DivergenceKernelContrast.lean:60 |
| skewField_norm_sq | Foundation/DivergenceKernelContrast.lean:70 |
| gaussian_nonzero_divergence_kernel | Foundation/DivergenceKernelContrast.lean:85 |

## Discovery 12 — Unique norm-one Poisson recovery on finite centered polynomial sectors

Verified: PoissonPolynomialRecovery constructs a genuine maximal divergence preimage for every finite positive Charlier expansion f=sum c_i P_(i+1). The field is u=sum c_i P_i in the ORIGINAL rate-weighted field L2. Its graph is proved by linear assembly of the actual raising graphs, and the source target is proved centered by its real integral.

The exact energies are ||u||²=sum c_i² i! lambda^(i+1) and ||f||²=sum (i+1)c_i² i! lambda^(i+1). Hence ||u||<=||f|| uniformly in polynomial degree. The preimage is unique among ALL fields in the maximal divergence graph, by discovery 11's actual zero-kernel theorem. It is not merely uniqueness among polynomial candidates.

Mathematical significance: the adjoint-first Poisson ladder now supplies a non-Gaussian integration/recovery operator with the same inverse-number energy pattern as Gaussian recovery, but distinct uniqueness geometry and product corrections. This is a valid restricted integration-first result without pretending polynomial completeness has been proved.

Limitations: finite positive Charlier expansions only. Extending to every centered Poisson L2 target requires a genuine density/completeness argument. The current research search identified an analytic route through exponential moments, Taylor polynomial approximation in L2, and approximation of positive-mass atom indicators; the needed approximation proof is not yet established. Do not replace this missing proof with an assumed chaos decomposition.

Verification: full Lake build 4322 jobs (.lake/stardust-12-build.log); all eight public types checked; 6421 safe Foundation declarations transitively audited with only propext/Classical.choice/Quot.sound (.lake/stardust-12-audit.lean and .log). Kernel contrast checkpoint: eccd9d0. Discovery 12 is the commit containing this entry.

Reflection: Poisson polynomial completeness is now a high-value focused obligation because it would extend several independently verified finite results at once: full recovery, Poincare, the complete number decomposition and Gaussian/Poisson Hilbert transfer. A multidimensional Poisson campaign must separately account for solenoidal kernels.

### Public locations — discovery 12

Prefix: OperatorDerivativeRewrite.Foundation.PoissonPolynomialRecovery.

| Name | Source |
| --- | --- |
| target | Foundation/PoissonPolynomialRecovery.lean:14 |
| recovery | Foundation/PoissonPolynomialRecovery.lean:17 |
| recovery_graph | Foundation/PoissonPolynomialRecovery.lean:20 |
| recovery_unique | Foundation/PoissonPolynomialRecovery.lean:26 |
| target_centered | Foundation/PoissonPolynomialRecovery.lean:34 |
| recovery_norm_sq | Foundation/PoissonPolynomialRecovery.lean:48 |
| target_norm_sq | Foundation/PoissonPolynomialRecovery.lean:56 |
| recovery_norm_le | Foundation/PoissonPolynomialRecovery.lean:65 |

## Discovery 13 — An actual IBM time-section source-divergence primitive

Verified: IBMClockCubicSourcePrimitive proves the cubic observable and every actual clock section are centered. Its integratedCorrection is the previously justified Gaussian-L2 Bochner time integral along the actual reflected clock. Centering commutes with the time integral by a proved bounded-functional/Bochner interchange.

The canonical sourcePrimitive is R(integratedCorrection). It belongs to the FULL scenery-source divergence graph with divergence equal to integratedCorrection. Its norm is bounded by the target norm, it has minimum norm among every source divergence preimage, and it equals the Bochner time integral of R applied to the actual correction sections. No target Malliavin differentiability or time/source derivative-domain assumption is needed.

Mathematical significance: the exploratory source recovery now constructs an IBM-specific nonvacuous source integration identity for a nonlinear time-integrated observable. This tests the integration-first program directly on the actual mollified clock/scenery construction rather than only on an abstract Gaussian polynomial. The chain is actual continuous source directions -> justified section time integral -> centering -> full closed source divergence primitive.

Limitations: the identity holds in scenery Gaussian-L2 at each actual clock path. Joint clock L2 bounds, scalar representative/time-Fubini identification, predictable Brownian-clock integration, local time and fixed-mollifier Ito–Tanaka are not thereby proved. The primitive is a full source-divergence primitive of the cubic spatial g'' integral; it is not claimed to be the paper's complete stochastic correction, which includes the overall 1/2 and separate clock/boundary terms. Source chaos regularization is not spatial H^-1 regularization.

Verification: full Lake build 4323 jobs (.lake/stardust-13-build.log); all nine public types checked; 6431 safe Foundation declarations transitively audited, only propext/Classical.choice/Quot.sound (.lake/stardust-13-audit.lean and .log). Poisson recovery checkpoint: 5c6e9d1. Discovery 13 is the commit containing this entry.

Reflection: this result justifies a focused actual-source observable campaign. The next missing steps should be concrete joint-domain/representative and physical spatial-kernel estimates, not another abstract source adjoint definition. Active check: first-chaos recovery should preserve norm exactly, confirming that this new primitive cannot automatically cure the identified first-chaos singularity.

### Public locations — discovery 13

Prefix: OperatorDerivativeRewrite.Foundation.IBMClockCubicSourcePrimitive.

| Name | Source |
| --- | --- |
| correction_centered | Foundation/IBMClockCubicSourcePrimitive.lean:16 |
| section_centered | Foundation/IBMClockCubicSourcePrimitive.lean:27 |
| integratedCorrection | Foundation/IBMClockCubicSourcePrimitive.lean:31 |
| integratedCorrection_centered | Foundation/IBMClockCubicSourcePrimitive.lean:34 |
| sourcePrimitive | Foundation/IBMClockCubicSourcePrimitive.lean:45 |
| sourcePrimitive_graph | Foundation/IBMClockCubicSourcePrimitive.lean:50 |
| sourcePrimitive_time_integral | Foundation/IBMClockCubicSourcePrimitive.lean:56 |
| sourcePrimitive_norm_le | Foundation/IBMClockCubicSourcePrimitive.lean:61 |
| sourcePrimitive_minimal_norm | Foundation/IBMClockCubicSourcePrimitive.lean:65 |

## Discovery 14 — Source recovery preserves the first-chaos obstruction

Verified: GaussianFirstChaosRecovery identifies R(X_h) with the actual constant rank-one source field h*gaussianOne, using both closed derivative and divergence graphs plus kernel orthogonality. Its norm equals ||X_h||, and the distance between any two recovered first-chaos classes equals their original Gaussian-L2 distance exactly.

For any target f, the first number-sector energy ||P1 f||² is a lower bound on ||R f||², by the actual inverse-energy series. Higher-chaos inverse weighting cannot cancel that positive term. The exact pure-first-chaos distance result transfers non-Cauchy behavior as well as norm divergence; it does not conflate these with absence of every possible random-variable limit.

Mathematical significance: the new full source primitive is useful operator recovery, but it cannot be invoked as a cure for a first-chaos L2 singularity. This closes a tempting loophole in applying discoveries 3 and 13 to the IBM limit program. Negative chaos order and negative spatial Sobolev order are different structures.

Limitations: no actual IBM kernel norm divergence or non-Cauchy sequence is proved here; its physical kernel/local-time estimates remain open. The result is a verified generic obstruction-transfer principle, not a substitute for those analytic inputs.

Verification: full Lake build 4324 jobs (.lake/stardust-14-build.log); all six public types checked; 6437 safe Foundation declarations transitively audited, only propext/Classical.choice/Quot.sound (.lake/stardust-14-audit.lean and .log). IBM source primitive checkpoint: fb5f935229546640bf8058b3ea98c5e96984006b. Discovery 14 is the commit containing this entry.

Reflection: retain source recovery as a construction tool, while prioritizing physical kernel and local-time estimates for singular closure. A proposed limit argument must explicitly distinguish chaos smoothing from spatial smoothing. Active Poisson exploration: actual exponential/coherent L2 vectors may supply a legitimate completeness route beyond the finite polynomial recovery theorem.

### Public locations — discovery 14

Prefix: OperatorDerivativeRewrite.Foundation.GaussianFirstChaosRecovery.

| Name | Source |
| --- | --- |
| firstChaos_derivative_graph | Foundation/GaussianFirstChaosRecovery.lean:14 |
| firstChaos_divergence_graph | Foundation/GaussianFirstChaosRecovery.lean:22 |
| recovery_firstChaos | Foundation/GaussianFirstChaosRecovery.lean:31 |
| recovery_firstChaos_norm | Foundation/GaussianFirstChaosRecovery.lean:53 |
| recovery_firstChaos_distance | Foundation/GaussianFirstChaosRecovery.lean:64 |
| recovery_norm_sq_ge_firstProjection | Foundation/GaussianFirstChaosRecovery.lean:78 |

## Discovery 15 — Nonpolynomial Poisson coherent vectors on the actual adjoint domains

Verified: PoissonCoherentVectors derives finite exponential moments for every real parameter from an actual summable Poisson-weight series. Its scalar exponential L2 class has the genuine moment exp(lambda(exp(theta)-1)), and pairings follow the exact two-parameter moment formula.

The mean-one coherent vector E_theta=exp(-lambda(exp(theta)-1))*exp(theta N) has integral 1 and inner product exp(lambda(exp(theta)-1)(exp(eta)-1)). Mean-one does not mean unit L2 norm. These are actual L2 equivalence classes; the normalization and every integral interchange are verified.

The genuine maximal difference graph is D exp(theta N)=(exp(theta)-1) exp(theta N) in the rate-weighted field space. A proved count-times-exponential moment also gives the full divergence graph: delta exp(theta N)=(N exp(-theta)-lambda) exp(theta N), including the count-zero boundary. This is a nonpolynomial adjoint-domain progression, not a postulated ordinary chain rule.

Mathematical significance: the source program now has an analytic family beyond finite count polynomials, with exact Hilbert kernels and both closed operator domains. Its kernel suggests a completed Gaussian/Poisson coherent-state transfer, but that transfer is not claimed here. This family offers a legitimate alternative completeness route through atomwise Laplace probes.

Limitations: no polynomial density or full Charlier spectral completeness is inferred from exponential moments alone. There is no dynamic Poisson stochastic integral, process-level change of measure, or full Gaussian coherent-family identification in this module. Active next proof: totality of the exponential family itself by justified dominated convergence, followed separately by polynomial approximation.

Verification: full Lake build 4325 jobs (.lake/stardust-15-build.log); all nineteen public types checked; 6468 safe Foundation declarations transitively audited, only propext/Classical.choice/Quot.sound (.lake/stardust-15-audit.lean and .log). First-chaos recovery checkpoint: c31865b. Informational ring-normalization suggestions appear, with no Lean errors/placeholders. Discovery 15 is the commit containing this entry.

Reflection: this family may connect stochastic operator domains, likelihood/exponential families and Gaussian Hilbert kernels. Focused future work should prove the actual completed transfer and preserve the already verified multiplication and kernel differences; matching a scalar reproducing kernel does not identify the entire calculus.

### Public locations — discovery 15

Prefix: OperatorDerivativeRewrite.Foundation.PoissonCoherentVectors.

| Name | Source |
| --- | --- |
| exponential | Foundation/PoissonCoherentVectors.lean:14 |
| weighted_exponential_hasSum | Foundation/PoissonCoherentVectors.lean:16 |
| exponential_memLp | Foundation/PoissonCoherentVectors.lean:39 |
| exponential_integral | Foundation/PoissonCoherentVectors.lean:49 |
| scalar | Foundation/PoissonCoherentVectors.lean:54 |
| field | Foundation/PoissonCoherentVectors.lean:57 |
| scalar_apply | Foundation/PoissonCoherentVectors.lean:60 |
| field_apply | Foundation/PoissonCoherentVectors.lean:64 |
| scalar_inner | Foundation/PoissonCoherentVectors.lean:69 |
| coherent | Foundation/PoissonCoherentVectors.lean:81 |
| coherent_inner | Foundation/PoissonCoherentVectors.lean:84 |
| scalar_integral | Foundation/PoissonCoherentVectors.lean:96 |
| coherent_integral | Foundation/PoissonCoherentVectors.lean:101 |
| exponential_difference_graph | Foundation/PoissonCoherentVectors.lean:110 |
| count_exponential_memLp | Foundation/PoissonCoherentVectors.lean:118 |
| divergenceValue | Foundation/PoissonCoherentVectors.lean:134 |
| divergenceValue_memLp | Foundation/PoissonCoherentVectors.lean:137 |
| divergenceScalar | Foundation/PoissonCoherentVectors.lean:146 |
| exponential_divergence_graph | Foundation/PoissonCoherentVectors.lean:149 |

## Discovery 16 — IBM source recovery preserves the first-chaos obstruction

Verified: for every actual Gaussian L2 class f, the norm of its existing first-chaos projection is at most the norm of R f. For each constructed clock path and finite horizon, the integrated source vector therefore has norm and pairwise distances bounded by the actual cubic source primitive. Cauchy convergence of the primitives forces Cauchy convergence of these vectors.

This connects the minimum-norm Gaussian inverse to the IBM kernel obstruction: source divergence recovery cannot erase a failure of first-chaos convergence. It supplies a necessary condition, not an actual blow-up or non-Cauchy estimate. Joint clock L2, physical kernel identification, local-time estimates, and stochastic Ito–Tanaka remain open.

Verification: full Lake build 4326 jobs (.lake/stardust-16-build.log); six public declarations checked; 6475 safe Foundation declarations transitively audited with only propext/Classical.choice/Quot.sound (.lake/stardust-16-audit.log). Discovery 15 checkpoint: 4decbfb. Discovery 16 is the commit containing this entry.

Reflection: prioritize an actual integrated-kernel estimate before treating recovery as a route to an IBM stochastic formula. The source inverse already gives all that can be obtained from Hilbert-space inversion alone.

### Public locations — discovery 16

Prefix: OperatorDerivativeRewrite.Foundation.IBMSourcePrimitiveObstruction.

| Name | Source |
| --- | --- |
| firstProjection_norm_le_recovery | Foundation/IBMSourcePrimitiveObstruction.lean:16 |
| integratedSourceVector | Foundation/IBMSourcePrimitiveObstruction.lean:44 |
| integrated_source_projection | Foundation/IBMSourcePrimitiveObstruction.lean:48 |
| integratedSourceVector_norm_le_primitive | Foundation/IBMSourcePrimitiveObstruction.lean:54 |
| integratedSourceVector_distance_le_primitive | Foundation/IBMSourcePrimitiveObstruction.lean:60 |
| integratedSourceVector_cauchy_of_primitive_cauchy | Foundation/IBMSourcePrimitiveObstruction.lean:73 |

## Discovery 17 — exponential probes are total in Poisson L2

For a strictly positive rate, a scalar Poisson L2 class orthogonal to exp(theta N) for every real theta is zero. Consequently the closed linear span of this actual exponential family is the entire scalar L2 space.

Proof mechanism: after lower atoms have been eliminated, multiply the probe exp(-j N) by exp(j r) and let j tend to infinity. Dominated convergence isolates the r-th atom; positivity of each Poisson weight forces its value to vanish. Strong induction eliminates all atoms. This gives a complete analytic observation family using the proved exponential moments, without assuming polynomial density.

Significance: atomwise separation connects discrete probability, Laplace-type transforms, Hilbert orthogonality, and the closed stochastic difference calculus. Polynomial/Charlier completeness is still a separate obligation. The active next investigation is actual L2 Taylor approximation, not an inference from pointwise convergence alone.

Verification: full Lake build 4327 jobs (.lake/stardust-17-build.log); three public types checked; 6481 safe Foundation declarations transitively audited, only propext/Classical.choice/Quot.sound (.lake/stardust-17-audit.log). Discovery 16 checkpoint: ebe0ba8. Discovery 17 is the commit containing this entry.

### Public locations — discovery 17

Prefix: OperatorDerivativeRewrite.Foundation.PoissonExponentialTotal.

| Name | Source |
| --- | --- |
| exponential_orthogonal_zero | Foundation/PoissonExponentialTotal.lean:82 |
| exponentialSpan | Foundation/PoissonExponentialTotal.lean:92 |
| exponentialSpan_closure | Foundation/PoissonExponentialTotal.lean:95 |

## Discovery 18 — genuine polynomial density in Poisson L2

For every strictly positive Poisson rate, the closed linear span of the actual L2 classes of ordinary real polynomials is the whole scalar L2 space. Finite Taylor polynomials for exp(theta N) converge in L2 to the exponential class for every real theta.

The proof controls every Taylor sum by exp(abs(theta) N), whose L2 membership was proved in discovery 15. Uniform integrability and pointwise Taylor convergence supply actual L2 convergence; discovery 17 then supplies totality. Pointwise convergence alone is not used to justify density.

This closes the analytic polynomial-density obligation without postulating a classical spectral theorem. Charlier completeness still requires the separate algebraic spanning bridge now under investigation. Full all-L2 Poisson recovery and a completed Gaussian/Poisson Hilbert transfer are promising subsequent campaigns, not conclusions of this file.

Verification: full Lake build 4328 jobs (.lake/stardust-18-build.log); seven public types checked; 6492 safe Foundation declarations transitively audited, only propext/Classical.choice/Quot.sound (.lake/stardust-18-audit.log). Discovery 17 checkpoint: 8211986. Discovery 18 is the commit containing this entry.

Reflection: exponential integrability has become an effective route from analytic test families back to a discrete polynomial calculus. Prioritize completing the genuine spectral basis and closed-operator extension; retain the proved multiplication and divergence-kernel differences from Gaussian calculus.

### Public locations — discovery 18

Prefix: OperatorDerivativeRewrite.Foundation.PoissonPolynomialDensity.

| Name | Source |
| --- | --- |
| polynomialClass | Foundation/PoissonPolynomialDensity.lean:16 |
| polynomialSpan | Foundation/PoissonPolynomialDensity.lean:19 |
| taylorPolynomial | Foundation/PoissonPolynomialDensity.lean:22 |
| taylor_eval | Foundation/PoissonPolynomialDensity.lean:25 |
| taylor_eval_bound | Foundation/PoissonPolynomialDensity.lean:39 |
| taylorClass_tendsto | Foundation/PoissonPolynomialDensity.lean:58 |
| polynomialSpan_closure | Foundation/PoissonPolynomialDensity.lean:84 |

## Discovery 19 — Charlier spectral completeness

The reconstructed all-order Charlier ladder spans every real polynomial algebraically. Its actual scalar Poisson L2 span is consequently dense for every strictly positive rate. This closes the analytic-and-algebraic completeness obligation that earlier finite-sector results deliberately left open.

Proof mechanism: verified raising/lowering identities give the three-term multiplication recurrence X P(n+1)=P(n+2)+(lambda+n+1)P(n+1)+lambda(n+1)P(n), with the separate vacuum case. The ladder span contains constants and is invariant under multiplication by X, hence contains every polynomial. A legitimate linear polynomial-to-L2 embedding transfers the spanning statement; discovery 18 supplies density.

Significance: the orthogonal ladder is now a complete spectral family in the actual probability space, not just a collection of eigenvectors. Full closed-operator recovery and a completed normalized Gaussian/Poisson Hilbert transfer are now justified research directions. They still require their own constructions and graph checks.

Verification: full Lake build 4329 jobs (.lake/stardust-19-build.log); nine public types checked; 6509 safe Foundation declarations transitively audited, only propext/Classical.choice/Quot.sound (.lake/stardust-19-audit.log). Discovery 18 checkpoint: e2ad6c6. Discovery 19 is the commit containing this entry.

Reflection: a previously blocked branch now merits a focused Poisson spectral-calculus campaign. Completeness does not identify Gaussian and Poisson multiplication, does not eliminate the divergence-kernel contrast, and does not prove a process-level stochastic representation theorem.

### Public locations — discovery 19

Prefix: OperatorDerivativeRewrite.Foundation.PoissonCharlierCompleteness.

| Name | Source |
| --- | --- |
| X_mul_zero | Foundation/PoissonCharlierCompleteness.lean:13 |
| X_mul_succ | Foundation/PoissonCharlierCompleteness.lean:17 |
| algebraicSpan | Foundation/PoissonCharlierCompleteness.lean:33 |
| X_mul_mem | Foundation/PoissonCharlierCompleteness.lean:36 |
| algebraicSpan_eq_top | Foundation/PoissonCharlierCompleteness.lean:56 |
| polynomialEmbedding | Foundation/PoissonCharlierCompleteness.lean:68 |
| polynomialEmbedding_ladder | Foundation/PoissonCharlierCompleteness.lean:94 |
| scalarSpan | Foundation/PoissonCharlierCompleteness.lean:97 |
| scalarSpan_closure | Foundation/PoissonCharlierCompleteness.lean:100 |

## Discovery 20 — complete Charlier coordinates and Gaussian Hilbert transfer

The actual positive-rate Poisson scalar L2 space now has a normalized Charlier Hilbert basis, with unconditional expansion by its genuine inner-product coefficients. Normalization divides P_n by sqrt(n! lambda^n), whose strict positivity is proved.

Composing its coordinate isometry with the existing complete scalar Gaussian Hermite coordinate isometry gives an actual linear isometric equivalence of the two full scalar L2 spaces. It maps each normalized Charlier vector to the corresponding normalized Hermite vector and preserves every chaos coefficient.

This extends the finite-coefficient geometry of discovery 5 to complete scalar spaces. The Gaussian target here is GaussianCore.GaussianL2, the existing one-variable standard Gaussian model, not the entire infinite-source Gaussian space. The equivalence preserves Hilbert geometry; ordinary multiplication is not identified. Full closed derivative/divergence graph intertwining is not yet claimed.

Verification: full Lake build 4330 jobs (.lake/stardust-20-build.log); twelve public types checked; 6538 safe Foundation declarations transitively audited, only propext/Classical.choice/Quot.sound (.lake/stardust-20-audit.log). Discovery 19 checkpoint: dc12c72. Discovery 20 is the commit containing this entry.

Reflection: scalar spectral coordinates are now reusable across the Gaussian/Poisson branches. The most useful next step is full Poisson divergence recovery, with the rate-weighted field geometry retained explicitly, followed by actual operator graph transfer.

### Public locations — discovery 20

Prefix: OperatorDerivativeRewrite.Foundation.PoissonCharlierHilbertBasis.

| Name | Source |
| --- | --- |
| normalizer | Foundation/PoissonCharlierHilbertBasis.lean:13 |
| normalizer_pos | Foundation/PoissonCharlierHilbertBasis.lean:16 |
| normalized | Foundation/PoissonCharlierHilbertBasis.lean:22 |
| normalized_orthonormal | Foundation/PoissonCharlierHilbertBasis.lean:25 |
| normalized_span | Foundation/PoissonCharlierHilbertBasis.lean:40 |
| basis | Foundation/PoissonCharlierHilbertBasis.lean:54 |
| basis_apply | Foundation/PoissonCharlierHilbertBasis.lean:58 |
| coefficient | Foundation/PoissonCharlierHilbertBasis.lean:61 |
| expansion_hasSum | Foundation/PoissonCharlierHilbertBasis.lean:65 |
| gaussianTransfer | Foundation/PoissonCharlierHilbertBasis.lean:69 |
| transfer_normalized | Foundation/PoissonCharlierHilbertBasis.lean:73 |
| transfer_coefficient | Foundation/PoissonCharlierHilbertBasis.lean:79 |

## Discovery 21 — full Poisson divergence recovery

For every strictly positive rate, every actual scalar Poisson L2 target f has a genuine maximal divergence preimage of f minus its mean. The recovery is a bounded linear map into the rate-weighted field L2 space, with norm at most one. The divergence range is exactly the centered subspace. Its preimage is unique among all maximal-domain fields, using the previously proved zero divergence kernel.

Construction: normalize the weighted field ladder and sum the scalar coefficient at degree n+1 divided by sqrt(n+1). The complete scalar basis proves square summability; field orthogonality proves convergence. Closedness of the actual maximal divergence graph identifies the limit. The inverse energy is the sum of squared inverse coefficients, and is bounded by the scalar target energy. The zero scalar coefficient is proved equal to the actual Poisson integral.

This extends discovery 12 from finite positive polynomial expansions to all centered L2, without differentiability assumptions on the target. Gaussian and Poisson both have bounded centered source recovery, while their kernels differ: Poisson recovery is unique; the multidirectional Gaussian recovery selects a minimum-norm solution among solenoidal alternatives. No process-level predictable Poisson representation theorem follows from this source result.

Verification: full Lake build 4331 jobs (.lake/stardust-21-build.log); twenty-three public types checked; 6584 safe Foundation declarations transitively audited, only propext/Classical.choice/Quot.sound (.lake/stardust-21-audit.log). Discovery 20 checkpoint: 4659ba0. Discovery 21 is the commit containing this entry.

Reflection: the Poisson branch now supports complete L2 spectral recovery. Next investigate its sharp Poincare estimate and exact closed-operator graph transfer, then move to a different branch. Completeness and recovery need no further repeated exploratory proofs.

### Public locations — discovery 21

Prefix: OperatorDerivativeRewrite.Foundation.PoissonDivergenceRecovery.

| Name | Source |
| --- | --- |
| normalizer_succ | Foundation/PoissonDivergenceRecovery.lean:13 |
| normalizedField | Foundation/PoissonDivergenceRecovery.lean:21 |
| normalizedField_orthonormal | Foundation/PoissonDivergenceRecovery.lean:24 |
| normalized_raising_graph | Foundation/PoissonDivergenceRecovery.lean:40 |
| coefficient | Foundation/PoissonDivergenceRecovery.lean:52 |
| inverseCoefficient | Foundation/PoissonDivergenceRecovery.lean:55 |
| coefficient_energy | Foundation/PoissonDivergenceRecovery.lean:58 |
| inverseCoefficient_sq_le | Foundation/PoissonDivergenceRecovery.lean:64 |
| recovery_summable | Foundation/PoissonDivergenceRecovery.lean:73 |
| recovery | Foundation/PoissonDivergenceRecovery.lean:83 |
| centered | Foundation/PoissonDivergenceRecovery.lean:86 |
| centered_hasSum | Foundation/PoissonDivergenceRecovery.lean:89 |
| recovery_graph | Foundation/PoissonDivergenceRecovery.lean:97 |
| recovery_unique | Foundation/PoissonDivergenceRecovery.lean:112 |
| recovery_energy | Foundation/PoissonDivergenceRecovery.lean:120 |
| recovery_norm_le | Foundation/PoissonDivergenceRecovery.lean:136 |
| zero_mode_difference_graph | Foundation/PoissonDivergenceRecovery.lean:148 |
| exists_divergence_iff_zero_mode | Foundation/PoissonDivergenceRecovery.lean:156 |
| coefficient_zero_integral | Foundation/PoissonDivergenceRecovery.lean:167 |
| exists_divergence_iff_centered | Foundation/PoissonDivergenceRecovery.lean:176 |
| recovery_add | Foundation/PoissonDivergenceRecovery.lean:181 |
| recovery_smul | Foundation/PoissonDivergenceRecovery.lean:190 |
| recoveryOperator | Foundation/PoissonDivergenceRecovery.lean:198 |


## Consolidated open and completed investigations after discovery 21

| Direction | Status | Next obligation |
| --- | --- | --- |
| Poisson exponential totality, polynomial density, Charlier completeness | VERIFIED, COMPLETED | Use the results; do not reopen density as an assumption |
| Full centered Poisson divergence recovery | VERIFIED | Sharp Poincare and exact spectral graph transfer |
| Complete scalar Gaussian/Poisson Hilbert transfer | VERIFIED | Weighted field geometry and full closed graphs |
| Actual IBM cubic source primitives | VERIFIED PER CLOCK PATH | Physical integrated-kernel estimates and joint clock moments |
| IBM primitive convergence obstruction | VERIFIED NECESSARY CONDITION | Prove actual vector non-Cauchy/blow-up if true |
| Fractional nonlinear Wick prediction | VERIFIED LOWER BOUNDS | Exact single-coordinate forecast and sharp full-past asymptotics |
| Quartic inverse exponent at zero | VERIFIED OPTIMAL 1/3 | Investigate disjoint-image degeneracy away from zero |
| Scalar representative IBM time Fubini | OPEN | Product L1 control from Bochner L2 sections, or actual majorant |

Current priority: full Poisson source calculus is now tractable without postulated density. The physical IBM bridge and fractional full-past asymptotics remain analytically distinct obstacles. Most surprising connection so far: analytic exponential probes close the discrete polynomial spectral gap in the formal infrastructure, enabling the same centered source-recovery principle as Gaussian chaos despite different multiplication and kernel structure.

## Discovery 22 — sharp full-domain Poisson Poincare and divergence coercivity

Every genuine maximal difference graph pair (f,g) satisfies norm(f minus its mean) <= norm(g) in the rate-weighted field space. Thus the variance is at most lambda times the ordinary Poisson expectation of the squared forward difference. The normalized first Charlier mode lies in the actual difference graph and attains equality, so the constant is sharp.

Every genuine maximal divergence graph pair (u,f) also satisfies norm(u)<=norm(f). The proof uses the unique all-L2 recovery from discovery 21, with no finite-polynomial restriction on either inequality. The sharper bound norm(R f)<=norm(centered f) follows by uniqueness, and adjoint duality with this recovered field gives the Poincare estimate.

Reusable principle: bounded centered divergence recovery plus adjoint graph duality yields full-domain Poincare; injective divergence additionally yields coercivity. This connects the actual Gaussian/Poisson source program at the level of closed operators, beyond matching finite eigenvalues.

Verification: full Lake build 4332 jobs (.lake/stardust-22-build.log); nine public types checked; 6593 safe Foundation declarations transitively audited, only propext/Classical.choice/Quot.sound (.lake/stardust-22-audit.log). Discovery 21 checkpoint: 780aeef. Discovery 22 is the commit containing this entry.

Reflection: the Poisson density/recovery/Poincare chain is now a completed investigation. Exact operator intertwining and process-level applications deserve a focused future campaign. Exploration now moves to disjoint-image quartic degeneracy away from zero, rather than re-proving this completed chain.

### Public locations — discovery 22

Prefix: OperatorDerivativeRewrite.Foundation.PoissonRecoveryPoincare.

| Name | Source |
| --- | --- |
| centered_zero_mode | Foundation/PoissonRecoveryPoincare.lean:13 |
| recovery_centered | Foundation/PoissonRecoveryPoincare.lean:17 |
| recovery_norm_le_centered | Foundation/PoissonRecoveryPoincare.lean:26 |
| centered_pairing | Foundation/PoissonRecoveryPoincare.lean:31 |
| poincare | Foundation/PoissonRecoveryPoincare.lean:45 |
| divergence_coercive | Foundation/PoissonRecoveryPoincare.lean:56 |
| centered_first_normalized | Foundation/PoissonRecoveryPoincare.lean:64 |
| normalized_first_lowering_graph | Foundation/PoissonRecoveryPoincare.lean:70 |
| poincare_equality_first_mode | Foundation/PoissonRecoveryPoincare.lean:76 |

## Discovery 23 — quartic singularities persist at nonzero data

Verified general obstruction: if two source vectors have disjoint actual L4 images, the quartic normal map satisfies A(u+a v)=A(u)+a^3 A(v). For every nonzero v, the inverse violates every proposed local linear modulus at A(u), not only at the origin. All identities are equalities of actual Lp classes and genuine dual maps.

A concrete counterexample is constructed in L4 of a positive-rate Poisson law with the identity bounded source map. The indicators of count zero and count one are nonzero and disjoint. The image of the first indicator is a proved nonzero dual datum, yet every dual neighborhood contains inverse perturbations violating any linear bound. This is a nonlinear Banach normal equation on the actual Poisson probability space; the identity map here is not asserted to be the maximal Poisson divergence.

Corrected conjecture: merely keeping the target away from zero does not restore local Lipschitz regularity for the general quartic inverse. The origin homogeneity obstruction from discoveries 4 and 9 was not the only possible degeneracy. A positive nondegenerate Hessian/coercivity condition would require a separate theorem and can fail along disjoint images.

Verification: full Lake build 4333 jobs (.lake/stardust-23-build.log); seven public types checked; 6603 safe Foundation declarations transitively audited, only propext/Classical.choice/Quot.sound (.lake/stardust-23-audit.log). Discovery 22 checkpoint: 849f550. Discovery 23 is the commit containing this entry.

Reflection: this deserves a focused Banach regularity campaign with explicit source-image overlap hypotheses. The concrete discrete counterexample connects Poisson atom geometry to nonlinear dual recovery and prevents overgeneralization of finite-dimensional radial intuition.

### Public locations — discovery 23

Prefix: OperatorDerivativeRewrite.Foundation.BanachQuarticDisjointObstruction.

| Name | Source |
| --- | --- |
| dualityFour_disjoint_add | Foundation/BanachQuarticDisjointObstruction.lean:15 |
| normalFour_disjoint_add | Foundation/BanachQuarticDisjointObstruction.lean:27 |
| no_local_linear_bound_at_disjoint_image | Foundation/BanachQuarticDisjointObstruction.lean:34 |
| poissonAtom | Foundation/BanachQuarticDisjointObstruction.lean:65 |
| poissonAtom_ne_zero | Foundation/BanachQuarticDisjointObstruction.lean:68 |
| poissonAtoms_disjoint | Foundation/BanachQuarticDisjointObstruction.lean:75 |
| actual_poisson_nonzero_datum_obstruction | Foundation/BanachQuarticDisjointObstruction.lean:89 |

Research-register correction: the claim that nonzero quartic data alone should yield local Lipschitz recovery is REFUTED by discovery 23. Future regularity work must test image overlap or actual Hessian lower bounds. Zero-data sharpness is completed; disjoint-image degeneracy is also completed and should not be rediscovered.

## Discovery 24 — all-degree normalized Wick metric transfer for fractional sources

For any two unit Gaussian source directions with nonnegative correlation, their degree n+1 Wick distance squared lies between (n+1)! times the source distance squared and (n+1)(n+1)! times that distance squared. This is a two-sided comparison in actual Gaussian L2, derived from mixed Wick moments and scalar power bounds on correlations in [0,1].

For the repository's actual fractional Gaussian realization, every positive-time direction has strictly positive norm and can be normalized to unit variance. Its covariance is proved nonnegative for all nonnegative times, so the comparison applies at every pair of positive times and every positive Wick degree, for every 0<H<1. No independence, invertible covariance matrix, or time generator is assumed.

This extends discovery 6 beyond second chaos and supplies a concrete Gaussian/fractional transfer of mean-square geometry. It says that normalized higher Wick degrees retain source metric roughness up to explicit constants. It does not by itself prove sample-path Holder exponents, sharp full-past prediction asymptotics, or behavior of normalization at time zero.

Verification: full Lake build 4334 jobs (.lake/stardust-24-build.log); seven public types checked; 6612 safe Foundation declarations transitively audited, only propext/Classical.choice/Quot.sound (.lake/stardust-24-audit.log). Discovery 23 checkpoint: e216495. Discovery 24 is the commit containing this entry.

Reflection: nonlinear chaos degree alone does not imply improved mean-square temporal smoothness after variance normalization. A future focused fractional campaign can combine these bounds with independently proved normalized-source increment estimates and actual path-version construction.

### Public locations — discovery 24

Prefix: OperatorDerivativeRewrite.Foundation.GaussianWickMetricTransfer.

| Name | Source |
| --- | --- |
| unit_positive_correlation_bounds | Foundation/GaussianWickMetricTransfer.lean:30 |
| unitDirection | Foundation/GaussianWickMetricTransfer.lean:48 |
| fractional_direction_norm_pos | Foundation/GaussianWickMetricTransfer.lean:52 |
| unitDirection_norm | Foundation/GaussianWickMetricTransfer.lean:60 |
| fractional_covariance_nonneg | Foundation/GaussianWickMetricTransfer.lean:66 |
| fractional_unit_correlation_nonneg | Foundation/GaussianWickMetricTransfer.lean:82 |
| fractional_unit_wick_bounds | Foundation/GaussianWickMetricTransfer.lean:89 |

## Discovery 25 — representative Fubini without a uniform majorant

On finite parameter and source measures, integrable scalar L2 sections with a jointly strongly measurable scalar representative have an integrable product representative. Their scalar column integrals equal the Bochner L2 integral almost everywhere and themselves belong to actual L2. No uniform pointwise L2 majorant or independently supplied column L2 class is required.

Proof: Cauchy–Schwarz controls the integral of the absolute test pairing by norm(V) norm(v_x), making every such product pairing integrable from Bochner integrability. The constant test class gives product L1 integrability and almost-everywhere column integrability. Indicator test classes and justified scalar Fubini identify all set integrals of the Bochner class and the column integral; integrable-function uniqueness gives actual almost-everywhere equality. L2 membership then transfers from the Bochner class.

This is a reusable bridge between quotient-valued integration and actual scalar observables. It strengthens the earlier BochnerL2Fubini rule in the scalar finite-measure setting, and directly targets the remaining per-clock IBM cubic representative gap. It does not assert infinite-source-measure versions, arbitrary vector-valued representative uniqueness, joint clock L2 moments, or stochastic integration.

Verification: full Lake build 4335 jobs (.lake/stardust-25-build.log); five public types checked; 6617 safe Foundation declarations transitively audited, only propext/Classical.choice/Quot.sound (.lake/stardust-25-audit.log). Discovery 24 checkpoint: efa90f1. Discovery 25 is the commit containing this entry.

Reflection: a uniform spatial/time pointwise majorant was stronger than needed for the scalar representative bridge. Existing unconditional Bochner integrability can be used directly once joint measurability is established. The next application tests the actual constructed IBM cubic correction rather than leaving the principle abstract.

### Public locations — discovery 25

Prefix: OperatorDerivativeRewrite.Foundation.BochnerL2RepresentativeFubini.

| Name | Source |
| --- | --- |
| pairing_norm_integral_le | Foundation/BochnerL2RepresentativeFubini.lean:24 |
| pairing_integrable_of_slices | Foundation/BochnerL2RepresentativeFubini.lean:39 |
| representative_integrable | Foundation/BochnerL2RepresentativeFubini.lean:63 |
| integral_coeFn_ae | Foundation/BochnerL2RepresentativeFubini.lean:71 |
| column_integral_memLp | Foundation/BochnerL2RepresentativeFubini.lean:107 |

## Discovery 26 — actual IBM scalar cubic time integral identified

For every constructed clock path and every finite real horizon, the actual scalar time integral of the cubic correction is the almost-everywhere representative of integratedCorrection. It belongs to scenery Gaussian L2 and has mean zero. Its joint time/scenery representative is genuinely product L1 integrable. All hypotheses of discovery 25 are discharged using actual joint measurability and unconditional per-path Bochner integrability.

This closes the previously open per-clock scalar representative/Fubini gap. The source primitive from discovery 13 now recovers a class explicitly identified with the actual scalar cubic time integral, and the source-vector projection/obstruction from discoveries 8 and 16 applies to that class.

Limits: every statement fixes the clock path. Joint random-clock/scenery L2 membership still requires an integrable clock-dependent norm bound. The result does not prove graph-norm derivative interchange, adapted or predictable-clock integration, local time, a fixed-mollifier stochastic Ito–Tanaka formula, physical white-noise kernel identification, or the singular spatial H^-1 limit. The integral is the g'' cubic time section; the full manuscript correction also has its overall factor 1/2 and boundary term.

Verification: full Lake build 4336 jobs (.lake/stardust-26-build.log); seven public types checked; 6624 safe Foundation declarations transitively audited, only propext/Classical.choice/Quot.sound (.lake/stardust-26-audit.log). Discovery 25 checkpoint: 8f86ebe. Discovery 26 is the commit containing this entry.

Reflection: the representative obstacle could be removed from existing L2 integration foundations without a new pointwise majorant. Prioritize actual joint clock moments and the physical kernel bridge; do not reopen per-clock scalar Fubini as an unproved assumption.

### Public locations — discovery 26

Prefix: OperatorDerivativeRewrite.Foundation.IBMClockCubicRepresentative.

| Name | Source |
| --- | --- |
| timeRepresentative | Foundation/IBMClockCubicRepresentative.lean:15 |
| timeRepresentative_measurable | Foundation/IBMClockCubicRepresentative.lean:18 |
| integratedValue | Foundation/IBMClockCubicRepresentative.lean:25 |
| timeRepresentative_integrable | Foundation/IBMClockCubicRepresentative.lean:28 |
| integratedCorrection_coeFn | Foundation/IBMClockCubicRepresentative.lean:36 |
| integratedValue_memLp | Foundation/IBMClockCubicRepresentative.lean:43 |
| integratedValue_centered | Foundation/IBMClockCubicRepresentative.lean:47 |

## Discovery 27 — countable SPDE forcing modes and exact L2 criterion

A countable family of actual independent Brownian forcing modes is constructed through the separable Hilbert space L2(count; TimeHilbert). Each mode embeds isometrically into the existing Gaussian product space. The series of modal responses c_n X_n(v_n) converges unconditionally in actual Gaussian L2 exactly when the nonnegative energies sum c_n^2 norm(v_n)^2 is summable. Its limiting energy is that exact sum.

For the existing bounded-modulation fractional responses, the criterion becomes summability of c_n^2 times the actual temporal integral of the squared modulated response kernel. This extends finite forcing calculations to countably many modes on a single consistent Gaussian realization. It does not assume a solution to an SPDE, spatial semigroup convergence, boundary regularity, or a path version of the summed field.

The limit remains in the complete first-chaos range and has a genuine full source-divergence primitive. Recovery preserves its norm exactly. Countably many unit Brownian modes provide a concrete failure of L2 summability: the first N cutoff energy is exactly N. Independent Gaussianity is proved from the actual joint Gaussian source and zero cross covariance; orthogonality alone is not used as a general independence assertion.

Verification: full Lake build 4337 jobs (.lake/stardust-27-build.log); twenty-one public types checked; 6662 safe Foundation declarations transitively audited, only propext/Classical.choice/Quot.sound (.lake/stardust-27-audit.log). Discovery 26 checkpoint: 2a62349. Discovery 27 is the commit containing this entry.

Reflection: the infinite-mode trace/energy condition is a genuine obstruction, and Gaussian source recovery preserves the completed first-chaos norm. A focused SPDE campaign should combine the exact criterion with actual spatial spectral weights and temporal increment estimates. Merely increasing the finite Galerkin dimension is not a proof of an infinite-dimensional stochastic solution.

### Public locations — discovery 27

Prefix: OperatorDerivativeRewrite.Foundation.SPDECountableModes.

| Name | Source |
| --- | --- |
| ModeHilbert | Foundation/SPDECountableModes.lean:14 |
| modeVector | Foundation/SPDECountableModes.lean:20 |
| modeVector_apply | Foundation/SPDECountableModes.lean:23 |
| modeEmbedding | Foundation/SPDECountableModes.lean:29 |
| modeVector_inner | Foundation/SPDECountableModes.lean:44 |
| gaussianMode | Foundation/SPDECountableModes.lean:51 |
| gaussianModes_orthogonal | Foundation/SPDECountableModes.lean:54 |
| gaussianSeries_summable_iff | Foundation/SPDECountableModes.lean:61 |
| infiniteResponse | Foundation/SPDECountableModes.lean:67 |
| infiniteResponse_hasSum | Foundation/SPDECountableModes.lean:70 |
| infiniteResponse_energy | Foundation/SPDECountableModes.lean:75 |
| modulatedSeries_summable_iff | Foundation/SPDECountableModes.lean:89 |
| infiniteResponse_firstChaos | Foundation/SPDECountableModes.lean:97 |
| infiniteResponse_recovery_norm | Foundation/SPDECountableModes.lean:108 |
| infiniteResponse_recovery_graph | Foundation/SPDECountableModes.lean:116 |
| brownianMode | Foundation/SPDECountableModes.lean:126 |
| brownianModes_jointGaussian | Foundation/SPDECountableModes.lean:129 |
| brownianModes_independent | Foundation/SPDECountableModes.lean:134 |
| finiteResponse_energy | Foundation/SPDECountableModes.lean:147 |
| brownian_unit_modes_not_summable | Foundation/SPDECountableModes.lean:152 |
| brownian_unit_cutoff_energy | Foundation/SPDECountableModes.lean:161 |

Consolidated priorities after discovery 27:
1. IBM joint random-clock/scenery L2 and the physical integrated-kernel bridge. Per-clock representative Fubini is now completed.
2. SPDE countable-mode spectral energy and actual spatial/temporal convergence. The forcing summability criterion is completed.
3. Fractional full-past prediction asymptotics and normalized-source increments; nonlinear Wick lower bounds and metric transfer are completed.

Other focused campaigns: exact full Gaussian/Poisson operator intertwining; quartic inverse regularity under actual overlap/Hessian bounds. Completed investigations should be used, not repeatedly reopened.

## Discovery 28 — global growth of compact-kernel scenery

Every continuous compactly supported spatial kernel has a nonnegative constant C with norm(wholeLineScenery rho x)<=C(1+abs(x)) for every real x. The estimate is for the actual Gaussian L2 convolution class. The actual Brownian source scenery norm squared is abs(x), and its norm is at most 1+abs(x).

Compact support controls a fixed-radius integration window around x. A compact uniform kernel bound and the source scenery norm bound control the Bochner integral on that shifted window, whose measure is independent of x. This yields global growth, not just the earlier compact-interval continuity bounds. Every concrete mollifier derivative coefficient U, V and W inherits such a bound through the genuine source isometries.

The bound is intentionally coarse and fixed-kernel: its constant can grow with the mollifier index. It is suitable for clock moment domination and is not a uniform singular-limit estimate. Joint cubic L2 remains the active next obligation, using a separate cubic norm bound and actual finite Gaussian clock moments.

Verification: full Lake build 4338 jobs (.lake/stardust-28-build.log); four public types checked; 6667 safe Foundation declarations transitively audited, only propext/Classical.choice/Quot.sound (.lake/stardust-28-audit.log). Discovery 27 checkpoint: 58315fc. Discovery 28 is the commit containing this entry.

Reflection: local smoothness infrastructure did not by itself control an unbounded random clock. This global polynomial estimate makes the clock integrability problem tractable without a maximal-clock moment or an unsupported uniform pointwise bound.

### Public locations — discovery 28

Prefix: OperatorDerivativeRewrite.Foundation.IBMSceneryGlobalGrowth.

| Name | Source |
| --- | --- |
| sourceScenery_norm_sq | Foundation/IBMSceneryGlobalGrowth.lean:11 |
| sourceScenery_norm_le | Foundation/IBMSceneryGlobalGrowth.lean:16 |
| compact_kernel_global_growth | Foundation/IBMSceneryGlobalGrowth.lean:20 |
| tripleCoefficient_global_growth | Foundation/IBMSceneryGlobalGrowth.lean:70 |

## Discovery 29 — actual cubic Gaussian growth estimates

The actual cubic source class has norm squared 15 norm(h)^6. Hence norm(cube h)<=4 norm(h)^3. Cubic polarization gives norm(mixedCube u v)<=12 B^3 whenever both source norms are at most B; the actual IBM correction class has norm at most 18 B^3 when all three source directions have norm at most B.

These are genuine Gaussian L2 norm estimates with all domains already constructed, not pointwise polynomial bounds on Gaussian samples. They make nonlinear products controllable through deterministic source norms and provide the remaining analytic ingredient for combining compact-kernel growth with random-clock Gaussian moments. The numerical upper constants are convenient bounds and are not claimed optimal.

Verification: full Lake build 4339 jobs (.lake/stardust-29-build.log); four public types checked; 6671 safe Foundation declarations transitively audited, only propext/Classical.choice/Quot.sound (.lake/stardust-29-audit.log). Discovery 28 checkpoint: 22947b4. Discovery 29 is the commit containing this entry.

Reflection: the cubic observable is L2 despite being non-Gaussian, and source-norm control supplies a polynomial domination route. Active application: fixed-time joint clock/scenery L2 for the actual mollified IBM correction; no uniform mollifier or stochastic time limit is yet concluded.

### Public locations — discovery 29

Prefix: OperatorDerivativeRewrite.Foundation.GaussianCubicGrowth.

| Name | Source |
| --- | --- |
| cube_norm_sq | Foundation/GaussianCubicGrowth.lean:10 |
| cube_norm_le | Foundation/GaussianCubicGrowth.lean:19 |
| mixedCube_norm_le | Foundation/GaussianCubicGrowth.lean:23 |
| correction_norm_le | Foundation/GaussianCubicGrowth.lean:38 |

## Discovery 30 — fixed-time joint clock/scenery cubic L2

For every fixed mollifier n and every nonnegative time t, the actual constructed cubic IBM correction value belongs to L2 of the full joint scenery/clock product measure. This is unconditional joint membership at a fixed time, beyond the earlier per-clock-section results.

The spatial correction class has a global bound C_n (1+abs(x))^3, using discoveries 28–29 and all three genuine mollifier coefficient directions. The actual constructed clock has L6 membership by its verified coordinate modification of the Gaussian Brownian process. The product-square integral is justified using the existing scenery sections, joint measurability, and the integrable sixth-moment clock majorant. No independence of the U,V,W scenery directions or arbitrary product-domain closure is assumed.

Limits: the constant depends on n. This does not yet prove joint L2 for the finite-horizon scalar time integral or uniform control as the mollifier is removed. Predictable-clock integration, stochastic Ito–Tanaka, physical kernel identification and singular H^-1 limits remain open. The active next proof is an actual finite-horizon product-square and column-integral bound.

Verification: full Lake build 4340 jobs (.lake/stardust-30-build.log); five public types checked; 6676 safe Foundation declarations transitively audited, only propext/Classical.choice/Quot.sound (.lake/stardust-30-audit.log). Discovery 29 checkpoint: defdb31. Discovery 30 is the commit containing this entry.

Reflection: the fixed-time joint clock moment obligation can be discharged from coarse global source growth and existing Gaussian moments. The singular-limit obstruction is separate and is not improved by allowing constants to depend on the mollifier.

### Public locations — discovery 30

Prefix: OperatorDerivativeRewrite.Foundation.IBMClockCubicJointL2.

| Name | Source |
| --- | --- |
| spatialCorrection_global_growth | Foundation/IBMClockCubicJointL2.lean:15 |
| clock_memLp_six | Foundation/IBMClockCubicJointL2.lean:32 |
| clock_cubic_growth_memLp | Foundation/IBMClockCubicJointL2.lean:37 |
| section_energy | Foundation/IBMClockCubicJointL2.lean:52 |
| value_memLp_joint | Foundation/IBMClockCubicJointL2.lean:59 |

## Discovery 31 — actual clock sixth moment and temporal domination

The actual constructed Brownian clock has sixth absolute moment 15 t^3 at every nonnegative time. The proof uses the verified modification identity and the cubic Gaussian L2 norm identity, not an assumed law for a path supremum. The actual first-chaos sixth moment is independently derived as 15 norm(h)^6.

The scalar growth factor satisfies (1+abs(x))^6<=64(1+abs(x)^6), hence its actual clock expectation is at most 64(1+15 t^3). This provides a polynomial finite-horizon majorant for the jointly integrated cubic square, using only fixed-time clock moments. No maximal-clock moment theorem is inferred.

Verification: full Lake build 4341 jobs (.lake/stardust-31-build.log); four public types checked; 6681 safe Foundation declarations transitively audited, only propext/Classical.choice/Quot.sound (.lake/stardust-31-audit.log). Discovery 30 checkpoint: 3e586d2. Discovery 31 is the commit containing this entry.

Reflection: exact source moments can replace unnecessarily strong path-supremum hypotheses when finite time integrals are handled through justified product integration. Active next step: finite-measure L2 column integration and the actual joint IBM time-integral estimate.

### Public locations — discovery 31

Prefix: OperatorDerivativeRewrite.Foundation.IBMClockSixthMoment.

| Name | Source |
| --- | --- |
| firstChaos_sixth_integral | Foundation/IBMClockSixthMoment.lean:13 |
| clock_sixth_integral | Foundation/IBMClockSixthMoment.lean:21 |
| one_add_abs_sixth_bound | Foundation/IBMClockSixthMoment.lean:31 |
| clock_growth_sixth_integral_le | Foundation/IBMClockSixthMoment.lean:39 |
