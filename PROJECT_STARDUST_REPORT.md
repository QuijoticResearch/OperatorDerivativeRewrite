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
| Gaussian/Poisson finite-chaos isometry versus multiplication | PROMISING, UNPROVED | Match verified Gram matrices; calculate second-degree product defect |
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
