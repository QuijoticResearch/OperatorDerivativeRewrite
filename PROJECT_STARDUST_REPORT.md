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
| All-order actual Poisson Charlier ladder | VERIFIED | Polynomial completeness and Gaussian spectral transfer |
| Nonlinear Wick prediction from fractional observations | VERIFIED | Sharp asymptotics and full-past versus one-coordinate comparison |
| Bounded right inverse of full Gaussian divergence on centered L2 | VERIFIED | Full gradient-range projection and comparison with adapted representation |
| Gaussian/Poisson finite-chaos isometry versus multiplication | VERIFIED | Polynomial density and completion; retain proved multiplication defect |
| Source-Hilbert to physical IBM white-noise kernel bridge | OPEN FROM IBM CAMPAIGN | Construct actual isometry before physical kernel/H^-1 claims |

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
