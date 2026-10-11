# Poisson P1–P5 verified development report

Starting point: `0b2b05c804b4ece2ddc49052e988a96593a76d2f` (P0 finite-support integration by parts). All results below use Mathlib's actual `poissonMeasure` on `ℕ`, with `rate : ℝ≥0` and `hr : 0 < rate` wherever positive atom masses or domain identification are required. The original manuscripts and dependency pins were not changed.

## Milestones and commits

| Milestone | Commit | Verified result |
| --- | --- | --- |
| P1 | `632105306418d9d30ea3921d6c452f7003ad24e8` | Dense finite-support Hilbert cores, actual pointwise values, weighted formal adjoint identity, closability. |
| P2a | `2787ea258d8f42c8235d209c4e924a6522874fc0` | Closed maximal pointwise graph operators and coordinate evaluation. |
| P2b | `f4121ca5d1d4b113f8596c7cede12291cca82bec` | Exact two-sided weighted-moment domain criteria. |
| P3a | `77f753a39404d9157f17ec1cbae1765787e309e8` | Truncation formulas and vanishing single-atom boundary masses. |
| P3b | `1fd3bb2b257d36d75726f6517efe51bd3b5df6f2` | Ambient scalar and field L² truncation convergence. |
| P3c | `b37d0e2e00807b9dc9fdae70db237278cd1fd408` | Simultaneous graph convergence and both exact graph-core identities. |
| P4 | `14cbed27af5ef307f57fa30beb9930d1c0cb8732` | Core-adjoint and closed maximal mutual-adjoint equalities. |
| P5 restricted calculus | `bb6c91fcc5efd2932028535b56bbe8bad5dfebab` | Bounded-domain product rule, all polynomial moments finite, low-order integrals, closed-operator centered-count examples, ordinary chain-rule failure. |

## Exact operators and domains

Write `μ = poissonLaw rate`, `wₙ = poissonWeight rate n = μ({n})`, `S = Lp ℝ 2 μ`, and `K = Lp ℝ 2 ((rate : ℝ≥0∞) • μ)`. The field norm includes the factor `rate`; this is required for the unscaled divergence formula.

`coreDifference rate hr : S →ₗ.[ℝ] K` and `coreDivergence rate hr : K →ₗ.[ℝ] S` have finite-support graph domains. Their actual formulas are `D₀f(n)=f(n+1)-f(n)` and `δ₀u(0)=-rate*u(0)`, `δ₀u(n+1)=(n+1)*u(n)-rate*u(n+1)`. The maximal operators use precisely these pointwise formulas and have closed graphs. Positive Poisson atom masses make the formulas independent of representative choices.

[PoissonWeightedDomains.lean](Foundation/PoissonWeightedDomains.lean) proves the exact equivalences:

- `mem_maximalDifference_domain_iff_moment`: `f ∈ dom(D) ↔ Summable (fun n => (n:ℝ) * wₙ * (f n)^2)`.
- `mem_maximalDivergence_domain_iff_moment`: `u ∈ dom(δ) ↔ Summable (fun n => (n+1:ℝ) * wₙ * (u n)^2)`.

These are not definitions of the adjoints and do not assume graph-core density. The divergence criterion is an exact one-site weighted moment, obtained from the cancellation-aware pointwise expression.

## Principal Lean declarations

- [PoissonDifferenceOperators.lean](Foundation/PoissonDifferenceOperators.lean): `scalarEmbedding_injective`, `fieldEmbedding_injective`, `scalarEmbedding_dense`, `fieldEmbedding_dense`, `coreDifference_finsupp_graph`, `coreDivergence_finsupp_graph`, `coreDifference_formalAdjoint`, `coreDifference_isClosable`, and `coreDivergence_isClosable`.
- [PoissonMaximalOperators.lean](Foundation/PoissonMaximalOperators.lean): `maximalDifference_isClosed`, `maximalDivergence_isClosed`, `coreDifference_le_maximal`, and `coreDivergence_le_maximal`.
- [PoissonTruncationConvergence.lean](Foundation/PoissonTruncationConvergence.lean): `cut_toLp_tendsto`, `scalar_truncate_tendsto`, and `field_truncate_tendsto`.
- [PoissonGraphApprox.lean](Foundation/PoissonGraphApprox.lean): `difference_output_tendsto`, `divergence_output_tendsto`, `maximalDifference_mem_coreClosure`, `maximalDivergence_mem_coreClosure`, `closure_coreDifference_eq_maximal` (`closure(D₀)=D`), and `closure_coreDivergence_eq_maximal` (`closure(δ₀)=δ`). Both graph limits use one finite-coordinate truncation sequence in their input and output components. The outgoing and incoming boundary atoms are controlled in their actual Hilbert norms.
- [PoissonAdjoints.lean](Foundation/PoissonAdjoints.lean): `difference_adjoint_le_maximalDivergence`, `divergence_adjoint_le_maximalDifference`, `coreDifference_adjoint_eq_maximalDivergence`, `coreDivergence_adjoint_eq_maximalDifference`, `maximalDifference_adjoint_eq_maximalDivergence` (`D*=δ`), and `maximalDivergence_adjoint_eq_maximalDifference` (`δ*=D`). The reverse inclusions test each adjoint graph pair against genuine count indicators, including the zero-count boundary; no adjoint domain is postulated.
- [PoissonBoundedCalculus.lean](Foundation/PoissonBoundedCalculus.lean): `bounded_product_mem_maximalDifference` establishes that the pointwise product of two uniformly bounded count functions lies in `dom(D)`, and `bounded_difference_product_rule` proves at every count the **actual maximal operator** formula `D(fg)=f Dg+g Df+(Df)(Dg)`. Both input functions and their product are genuine L² classes. This is a proved restricted domain, not an assertion that the whole maximal domain is an algebra.
- [PoissonMoments.lean](Foundation/PoissonMoments.lean): `summable_poisson_power_moment` for every natural power, `polynomial_memLp_two` for every real polynomial, `integral_poisson_count` (`∫n dμ=rate`), and `integral_poisson_count_sq` (`∫n² dμ=rate²+rate`). Integrability is proved before either real integral is manipulated.
- [PoissonPolynomialExamples.lean](Foundation/PoissonPolynomialExamples.lean): `divergence_one_eq_centeredCount` (`δ1=N−rate`), `difference_centeredCount_eq_one` (`D(N−rate)=1`), `difference_centeredCount_sq_eq` (`D((N−rate)²)=2(N−rate)+1`), and `ordinary_chain_rule_fails`. The relevant scalar and field L² memberships and operator-domain memberships have separate proved declarations.

[Foundation/AxiomAudit.lean](Foundation/AxiomAudit.lean) contains `#print axioms` for all new top-level declarations, including supporting definitions and lemmas. Exact elaborated types of the two moment domains, both graph-core equalities, both mutual adjoints, the bounded product rule, low-order integrals, and the centered-count identities were independently checked with Lean `#check`.

## Verification and limitations

At the last Lean-source commit, the complete `lake build` succeeded: **4017 jobs**. `lake env lean Foundation/AxiomAudit.lean` also succeeded. Every new Poisson declaration audited transitively depends only on `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx`, custom axiom, `sorry`, `admit`, or `unsafe` declaration appears in the new modules. The only build warnings are two pre-existing unused-section-variable warnings in `Foundation/Adjoint.lean`.

P1–P4 are complete as stated. P5's product theorem is deliberately restricted to uniformly bounded count functions; no theorem characterizes the maximal domain of the multiplication map on arbitrary `dom(D)` pairs. The compensated count and its square are unbounded, but their own L² memberships and derivative domains are proved separately using Poisson moments. No Poisson-process stochastic integral, Clark–Ocone formula, or martingale representation is claimed. The original Gaussian developments remain imported and build successfully.

Independent Astra High review should focus on (1) the rate weighting of `K` and its effect on the adjoint normalization; (2) the two directions of each weighted-moment domain theorem; (3) both boundary-atom graph limits, especially the divergence incoming atom; (4) use of positive atom masses when passing from a.e. to pointwise coefficient equations; and (5) the explicit bounded-domain scope of the product theorem. The next mathematical extension, if desired, is to characterize admissible multipliers on the full maximal difference domain without assuming general L² multiplication closure.
