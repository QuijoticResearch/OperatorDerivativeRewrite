# Independent audit of the one-site Poisson development P0–P5

**Verdict: PASS WITH QUALIFICATIONS.**

The four principal operator identities are proved with the claimed domains and values. No blocking mathematical or Lean defect was found. The qualification concerns scope: the bounded-function product theorem is correct, but extending multiplication closure to arbitrary maximal-domain elements is false, even if their product is assumed to belong to scalar L². This report gives an explicit counterexample and a valid next milestone.

## 1. Scope and verification record

Audited repository: `C:\OperatorDerivativeRewrite`.

Audited HEAD: `c94b49ea666905a2e44e9ee92b9185e47da1e858`, commit timestamp `2026-10-11T18:36:47-04:00`.

The review inspected the actual definitions and proof bodies in all twelve `Foundation/Poisson*.lean` modules, their relevant generic operator/product dependencies, and the pinned Mathlib partial-map and Poisson definitions. The project’s `POISSON_P1_P5_REPORT.md` and `MATHEMATICAL_AUDIT.md` were not used as evidence. Independent parallel source reviews checked the domain, graph/adjoint, and product/example arguments.

Environment: Lean `v4.34.1`; Mathlib commit `d13f23b723b8a846827a245b89c10fc7d3f11612`, matching the unchanged lockfile.

Executed checks:

- `lake build`: exit 0, **4017 jobs**, successful. The only displayed warnings were the existing unused section-variable warnings in `Foundation/Adjoint.lean:24,30`. Lake reused/replayed up-to-date build artifacts; this was not a clean rebuild after deleting the cache.
- `lake env lean Foundation/AxiomAudit.lean`: exit 0; **1079 transitive axiom reports**. All reported axiom sets were subsets of `propext`, `Classical.choice`, and `Quot.sound`.
- An independently generated temporary audit imported `OperatorDerivativeRewrite` and ran both `#check @...` and `#print axioms ...` on **all 201 explicitly named definitions, abbreviations and theorems** in the twelve Poisson modules, including same-line `@[simp]` declarations. Exit 0. Every name was also present in the repository’s existing axiom audit. No unexpected implicit mathematical hypotheses appeared in the operator, domain, convergence, product or example declarations.
- Each of the four principal equality theorems reports exactly `[propext, Classical.choice, Quot.sound]`. No `sorryAx`, custom axiom, compiler-trust axiom, or unchecked computational proof was reported.
- Source scans of the Poisson modules and the directly reused project operator/product modules found no `sorry`, `admit`, custom `axiom`, `unsafe`, `implemented_by`, or `native_decide` shortcut.

Temporary audit sources and logs were written outside the repository under `C:\Users\ramir\AppData\Local\Temp\poisson-independent-audit-dc39e0e56c674b15877eb713d6b34690`. The elaborated declarations are in `all-poisson-audit.log`; the repository-wide output is `full-axiom-audit.log`.

Declaration inventory:

| Module | Named declarations checked |
|---|---:|
| PoissonDifferenceCore | 34 |
| PoissonDifferenceOperators | 43 |
| PoissonCoordinateEvaluation | 17 |
| PoissonMaximalOperators | 15 |
| PoissonWeightedDomains | 13 |
| PoissonTruncation | 10 |
| PoissonTruncationConvergence | 6 |
| PoissonGraphApprox | 13 |
| PoissonAdjoints | 12 |
| PoissonBoundedCalculus | 11 |
| PoissonMoments | 8 |
| PoissonPolynomialExamples | 19 |

No Lean source, original manuscript, dependency pin, or existing document was edited. No commit was created. The six preexisting untracked research/audit documents were preserved. This audit document is the sole new repository file from this review.

## 2. Exact mathematical objects and normalization

Write λ for the real value of `rate : ℝ≥0` and assume `hr : 0 < rate` for the operator theory. Let

- μλ = `ProbabilityTheory.poissonMeasure rate`;
- wₙ = μλ({n}) = exp(−λ) λⁿ/n!;
- S = L²(ℕ, μλ; ℝ);
- K = L²(ℕ, λ μλ; ℝ).

The field norm is **‖u‖K² = λ Σₙ wₙ u(n)²**. K is not silently assigned the unweighted scalar inner product. For positive finite λ the two spaces have the same square-integrable representatives, but their norms and adjoint normalization differ.

Source: [PoissonDifferenceCore.lean:23](C:/OperatorDerivativeRewrite/Foundation/PoissonDifferenceCore.lean:23), [PoissonDifferenceOperators.lean:18](C:/OperatorDerivativeRewrite/Foundation/PoissonDifferenceOperators.lean:18), and `fieldFinsupp_inner` at [line 234](C:/OperatorDerivativeRewrite/Foundation/PoissonDifferenceOperators.lean:234).

The actual Mathlib measure is a sum of weighted Dirac measures, with a proved probability-measure instance: [Mathlib Poisson/Basic.lean:41](C:/OperatorDerivativeRewrite/.lake/packages/mathlib/Mathlib/Probability/Distributions/Poisson/Basic.lean:41), lines 41–69. Its integration API is used with integrability hypotheses, not merely with totalized real integrals.

`poisson_weight_succ` proves

    (n+1) wₙ₊₁ = λ wₙ.

It follows by the explicit factorial/mass formula; this recurrence is not a field assumed in an abstract measure interface. `poisson_weight_pos` proves wₙ > 0 at every count when λ > 0. See [Core:29](C:/OperatorDerivativeRewrite/Foundation/PoissonDifferenceCore.lean:29) and [Core:41](C:/OperatorDerivativeRewrite/Foundation/PoissonDifferenceCore.lean:41).

The finite-support operators are

    D₀f(n) = f(n+1) − f(n),
    δ₀u(0) = −λ u(0),
    δ₀u(n+1) = (n+1)u(n) − λ u(n+1).

Their codomains are K and S respectively. The value at zero is explicitly split from the successor formula; no natural-number subtraction convention inserts an unwanted incoming term.

`poisson_shift_finsupp` and `poisson_difference_ibp_finsupp` prove, for actual finite-support functions,

    ∫ n f(n) dμλ = λ ∫ f(n+1) dμλ,
    λ ∫ D₀f(n) u(n) dμλ = ∫ f(n) δ₀u(n) dμλ.

See [Core:160](C:/OperatorDerivativeRewrite/Foundation/PoissonDifferenceCore.lean:160), [Core:279](C:/OperatorDerivativeRewrite/Foundation/PoissonDifferenceCore.lean:279). Finite-support preservation, L² membership, and integrability of the pairings are proved separately (Core:68–139, 202–226). The IBP proof establishes integrability of its shifted, diagonal and backward terms before using `integral_sub` (279–310). Thus the normalization and integral manipulations are genuine.

## 3. Finite-support embeddings, representatives and density

`scalarFinsupp` and `fieldFinsupp` embed actual `ℕ →₀ ℝ` functions using `MemLp.toLp`. Their linear maps are `scalarEmbedding` and `fieldEmbedding`.

The main representative issue is resolved correctly. `ae_eq_implies_pointwise` uses wₙ > 0 to show that μλ-a.e. equality implies equality at each n; the weighted version uses λ > 0. Consequently the embeddings are injective and evaluating an L² class at an atom is unambiguous. See [Operators:67](C:/OperatorDerivativeRewrite/Foundation/PoissonDifferenceOperators.lean:67), lines 67–103, and [CoordinateEvaluation:104](C:/OperatorDerivativeRewrite/Foundation/PoissonCoordinateEvaluation.lean:104).

`scalarCoordinate` and `fieldCoordinate` realize evaluation as continuous linear functionals, using singleton inner products divided by wₙ and λwₙ respectively. Both denominators are proved nonzero. See [CoordinateEvaluation:13](C:/OperatorDerivativeRewrite/Foundation/PoissonCoordinateEvaluation.lean:13), lines 13–32, 77–89.

The core graphs are ranges of the actual input/output embedding maps (Operators:148–156). Their domains are precisely the embedded finite-support functions: this follows from the proved graph equality and the range definition, not from an arbitrary choice of domain.

Ambient density is proved by testing orthogonality against singleton indicators and using positivity of each mass. The relevant declarations are `scalarEmbedding_dense`, `fieldEmbedding_dense`, `coreDifference_dense_domain` and `coreDivergence_dense_domain`; see [Operators:302](C:/OperatorDerivativeRewrite/Foundation/PoissonDifferenceOperators.lean:302), lines 302–379. This establishes ambient density only; the separate graph argument in Section 5 is essential and is actually present.

## 4. Exact maximal domains and closedness

Use the abbreviations D = `PoissonMaximalOperators.maximalDifference rate hr` and δ = `PoissonMaximalOperators.maximalDivergence rate hr`. Their graphs require the pointwise formulas at every count:

    graph D = {(f,g) ∈ S×K : ∀n, g(n)=f(n+1)−f(n)},
    graph δ = {(u,v) ∈ K×S :
      v(0)=−λu(0), ∀n, v(n+1)=(n+1)u(n)−λu(n+1)}.

See [MaximalOperators:14](C:/OperatorDerivativeRewrite/Foundation/PoissonMaximalOperators.lean:14) and [MaximalOperators:36](C:/OperatorDerivativeRewrite/Foundation/PoissonMaximalOperators.lean:36). These definitions specify a genuine maximal pointwise graph, not a closed extension selected to make an equality true.

The following elaborated theorems have only `(rate : ℝ≥0) (hr : 0 < rate)` and the displayed L² input as hypotheses, under namespace `OperatorDerivativeRewrite.Foundation.PoissonWeightedDomains`:

| Declaration | Exact mathematical content | Source |
|---|---|---|
| `mem_maximalDifference_domain_iff_memLp_difference` | For f∈S, f∈dom D iff (n↦f(n+1)−f(n))∈K | [line 74](C:/OperatorDerivativeRewrite/Foundation/PoissonWeightedDomains.lean:74) |
| `mem_maximalDifference_domain_iff_moment` | For f∈S, f∈dom D iff Σₙ n wₙ f(n)² < ∞ | [line 97](C:/OperatorDerivativeRewrite/Foundation/PoissonWeightedDomains.lean:97) |
| `mem_maximalDivergence_domain_iff_memLp_divergence` | For u∈K, u∈dom δ iff its full divergence expression belongs to S | [line 163](C:/OperatorDerivativeRewrite/Foundation/PoissonWeightedDomains.lean:163) |
| `mem_maximalDivergence_domain_iff_moment` | For u∈K, u∈dom δ iff Σₙ (n+1) wₙ u(n)² < ∞ | [line 185](C:/OperatorDerivativeRewrite/Foundation/PoissonWeightedDomains.lean:185) |

The Lean conclusions use `MemLp ... 2 ...` and `Summable`, rather than a possibly totalized finite real sum. Both implications of each membership characterization are proved. The reverse direction constructs the actual output class with `toLp` and proves its graph equations using atom positivity.

The moment equivalences reindex the Poisson recurrence. Removing the diagonal term is legitimate because it is already in L²: Df∈K iff f(·+1)∈K, and δu∈S iff the incoming weighted shift belongs to S. See WeightedDomains:34–71 and 120–160. No extra moment condition is smuggled in. There is only one field component, so this argument does not discard cancellations between multiple spatial components. It must not be copied into a multisite divergence theorem without a new proof.

`maximalDifferenceGraph_isClosed` and `maximalDivergenceGraph_isClosed` prove closedness as intersections of closed continuous-coordinate equations, [MaximalOperators:99](C:/OperatorDerivativeRewrite/Foundation/PoissonMaximalOperators.lean:99), lines 99–139. The resulting `LinearPMap` closedness is at lines 194–201.

A particularly important adversarial check concerns Mathlib defaults. `Submodule.toLinearPMap` supplies a zero map if the relation is not single-valued. The development proves vertical-zero for both core and maximal graphs, then proves equality of the resulting partial-map graph with the intended graph (Operators:158–190; MaximalOperators:142–191). It therefore does not exploit that fallback. Mathlib’s nonclosable-closure and nondense-adjoint fallback cases are likewise excluded by actual closability and density proofs.

## 5. Graph-core approximation and shift boundaries

Let T_N f retain coordinates 0,…,N, so it is Lean’s `truncate f (N+1)`. The exact output decompositions are

    D₀(T_N f) = 1_{n<N} Df − f(N)e_N,
    δ₀(T_N u) = 1_{n≤N} δu + (N+1)u(N)e_{N+1}.

The first is proved in [TruncationConvergence:77](C:/OperatorDerivativeRewrite/Foundation/PoissonTruncationConvergence.lean:77); the second in [GraphApprox:13](C:/OperatorDerivativeRewrite/Foundation/PoissonGraphApprox.lean:13). They are transferred to actual L² outputs at GraphApprox:87 and 105. The two different cutoff endpoints are intentional and correct.

Exact singleton norms yield

    ‖f(N)e_N‖K² = λ w_N f(N)² → 0,
    ‖(N+1)u(N)e_{N+1}‖S²
      = w_{N+1}(N+1)²u(N)²
      = λ(N+1)w_Nu(N)² → 0.

The first uses scalar L² summability. The second uses the exact maximal-divergence domain characterization, not ambient L² alone. See [Truncation:79](C:/OperatorDerivativeRewrite/Foundation/PoissonTruncation.lean:79), lines 79–101, and [GraphApprox:32](C:/OperatorDerivativeRewrite/Foundation/PoissonGraphApprox.lean:32), lines 32–83.

`cut_toLp_tendsto` proves genuine norm convergence of coordinate cuts using uniform integrability and eventual pointwise equality; `scalar_truncate_tendsto` and `field_truncate_tendsto` transfer this to the actual classes ([TruncationConvergence:27](C:/OperatorDerivativeRewrite/Foundation/PoissonTruncationConvergence.lean:27), lines 27–74).

`difference_output_tendsto` and `divergence_output_tendsto` then prove convergence of actual core outputs. The subsequent graph-pair limits use the **same N+1 truncation sequence** for input and output, via `prodMk` and closure membership. See [GraphApprox:122](C:/OperatorDerivativeRewrite/Foundation/PoissonGraphApprox.lean:122), lines 122–172. Thus ambient density has not been substituted for graph density. Convergence in the product Hilbert topology gives graph-norm convergence.

The explicit zero, interior, boundary and tail cases in `PoissonTruncation.lean:24–76` also cover N=0. No boundary term has been dropped.

## 6. Exact operator equalities and absence of circularity

All names below have the prefix `OperatorDerivativeRewrite.Foundation.`. After elaboration, the complete parameter list for each equality is `(rate : NNReal) (hr : 0 < rate)`. There are no assumed core, adjoint, integrability, or summability hypotheses.

| Declaration | Conclusion | Source |
|---|---|---|
| `PoissonTruncationConvergence.closure_coreDifference_eq_maximal` | `(coreDifference rate hr).closure = maximalDifference rate hr` | [GraphApprox:175](C:/OperatorDerivativeRewrite/Foundation/PoissonGraphApprox.lean:175) |
| `PoissonTruncationConvergence.closure_coreDivergence_eq_maximal` | `(coreDivergence rate hr).closure = maximalDivergence rate hr` | [GraphApprox:193](C:/OperatorDerivativeRewrite/Foundation/PoissonGraphApprox.lean:193) |
| `PoissonAdjoints.coreDifference_adjoint_eq_maximalDivergence` | `(coreDifference rate hr).adjoint = maximalDivergence rate hr` | [Adjoints:159](C:/OperatorDerivativeRewrite/Foundation/PoissonAdjoints.lean:159) |
| `PoissonAdjoints.coreDivergence_adjoint_eq_maximalDifference` | `(coreDivergence rate hr).adjoint = maximalDifference rate hr` | [Adjoints:170](C:/OperatorDerivativeRewrite/Foundation/PoissonAdjoints.lean:170) |
| `PoissonAdjoints.maximalDifference_adjoint_eq_maximalDivergence` | `(maximalDifference rate hr).adjoint = maximalDivergence rate hr` | [Adjoints:181](C:/OperatorDerivativeRewrite/Foundation/PoissonAdjoints.lean:181) |
| `PoissonAdjoints.maximalDivergence_adjoint_eq_maximalDifference` | `(maximalDivergence rate hr).adjoint = maximalDifference rate hr` | [Adjoints:188](C:/OperatorDerivativeRewrite/Foundation/PoissonAdjoints.lean:188) |

These are equalities of `LinearPMap`s. They identify domains and all operator values, not merely restrictions to a common core.

The proof order is noncircular:

1. Finite-support IBP proves formal adjointness.
2. Dense core domains give inclusions into the opposite Hilbert adjoints, which are closed. This proves both cores closable (Operators:381–403).
3. Independent coordinate/moment and truncation arguments identify the graph closures with the maximal operators.
4. Testing an arbitrary core-adjoint graph pair against every singleton determines its full coordinate formula. `difference_adjoint_le_maximalDivergence` explicitly treats n=0 separately; `divergence_adjoint_le_maximalDifference` cancels λwₙ>0. See [Adjoints:82](C:/OperatorDerivativeRewrite/Foundation/PoissonAdjoints.lean:82) and [Adjoints:134](C:/OperatorDerivativeRewrite/Foundation/PoissonAdjoints.lean:134).
5. Closedness of the adjoint plus the independently proved graph-core theorem gives the other inclusions.
6. `operatorClosure_adjoint_eq` identifies the adjoint before and after closure, yielding the two maximal adjoint equalities.

The generic theorem in [AdjointClosure.lean:41](C:/OperatorDerivativeRewrite/Foundation/AdjointClosure.lean:41) proves its claim by comparing actual adjoint graphs and extending continuous inner-product equations to a graph closure. No unproved bidual or essential-adjointness assumption is used.

Mathlib’s `adjointDomain` is continuity of the pairing on the original domain with its inherited norm, not continuity with the graph norm; see [Mathlib LinearPMap:90](C:/OperatorDerivativeRewrite/.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/LinearPMap.lean:90). This is the correct unbounded Hilbert-adjoint domain. The identity with the adjoint graph is invoked only after proving density.

## 7. Polynomial moments and centered-count tests

`PoissonMoments.summable_poisson_power_moment` proves every natural power moment by an explicit eventual ratio bound. `poisson_power_memLp_two` and `polynomial_memLp_two` derive genuine L² membership. The first and second count integrals are λ and λ²+λ, with integrability proved before series conversion. See [Moments:11](C:/OperatorDerivativeRewrite/Foundation/PoissonMoments.lean:11), lines 11–77 and 88–159.

With N(n)=n and X=N−λ, the example declarations establish:

| Declaration | Actual operator statement | Source |
|---|---|---|
| `difference_centeredCount_eq_one` | DX = 1 in K | [Examples:79](C:/OperatorDerivativeRewrite/Foundation/PoissonPolynomialExamples.lean:79) |
| `divergence_one_eq_centeredCount` | δ1 = X in S | [Examples:92](C:/OperatorDerivativeRewrite/Foundation/PoissonPolynomialExamples.lean:92) |
| `difference_centeredCount_sq_eq` | D(X²) = 2X+1 in K | [Examples:143](C:/OperatorDerivativeRewrite/Foundation/PoissonPolynomialExamples.lean:143) |

Each theorem assumes only positive rate. Domain membership is proved separately at Examples:57,67,117; the relevant outputs have separately proved L² membership. The names do not disguise prescribed unrelated derivative values.

`difference_centeredCount_sq_apply` (127) proves the pointwise formula; `ordinary_chain_rule_fails` (153) refutes the ordinary differential square rule at coordinate zero. This is a positive-mass atom, so the failure is not confined to a null set. The examples verify both the λ scaling and the essential jump correction +1.

## 8. Product theorem: valid bounded result, false unrestricted extension

`PoissonBoundedCalculus.bounded_difference_product_rule`, [line 106](C:/OperatorDerivativeRewrite/Foundation/PoissonBoundedCalculus.lean:106), has exactly these mathematical hypotheses:

    rate : ℝ≥0, hr : 0 < rate,
    f g : ℕ → ℝ, Cf Cg : ℝ,
    hf : ∀ n, |f n| ≤ Cf,
    hg : ∀ n, |g n| ≤ Cg,
    n : ℕ.

It proves the coordinatewise identity for the **actual maximal-operator outputs** of the bounded-function classes:

    D(fg)(n) = f(n)Dg(n) + g(n)Df(n) + Df(n)Dg(n).

`bounded_product_mem_maximalDifference` proves product-domain membership first, using the actual estimate |D(fg)|≤2CfCg ([line 58](C:/OperatorDerivativeRewrite/Foundation/PoissonBoundedCalculus.lean:58)). Individual bounded-function domain membership and operator evaluation are separate results at lines 79 and 94. Nonnegative bounds follow from the supplied inequalities on the nonempty count space; no inconsistent sign assumption is needed.

This is a genuine bounded-domain theorem. It is stated pointwise, with actual L² operator values on the left and within the right-hand side. It does not separately package all right-hand-side products as L² classes. They are bounded here and hence genuinely square integrable; presenting a packaged L² identity would be an API improvement, not a repair of a false theorem.

### Counterexample to arbitrary maximal-domain multiplication

The following is an analytic audit argument, **not a newly Lean-verified theorem**.

For any λ>0 define

    f(n) = wₙ^(−1/4) / sqrt(n+1).

Every wₙ is positive. The ratio of successive terms of sqrt(wₙ) is sqrt(λ/(n+1)), so Σₙ sqrt(wₙ)<∞. Therefore

    Σₙ (n+1) wₙ f(n)² = Σₙ sqrt(wₙ) < ∞,

which establishes both f∈S and f∈dom D by the exact proved domain criterion. However,

    Σₙ wₙ (f(n)²)² = Σₙ 1/(n+1)² < ∞,
    Σₙ n wₙ (f(n)²)² = Σₙ n/(n+1)² = ∞.

The divergence of the last series follows, for n≥1, from n/(n+1)² ≥ 1/(4n). Thus **f²∈S but f²∉dom D**, although both factors belong to dom D.

Even bare L² product closure fails: f(n)=wₙ^(−1/4) belongs to dom D because Σₙ(n+1)sqrt(wₙ)<∞ by the same ratio test, whereas its square has squared L² norm Σₙ1=∞.

Hence the outstanding P5 goal must not be interpreted as making dom D an algebra. Requiring only fg∈L² is also insufficient. The pointwise finite-difference identity is algebraically universal; its operator-domain and termwise-integrability assertions are separate mathematical obligations.

## 9. Comparison with established theory

Günter Last’s [*Stochastic analysis for Poisson processes*](https://arxiv.org/pdf/1405.4416), [submitted 17 May 2014](https://arxiv.org/abs/1405.4416), defines the add-one difference in Eq. (2.1), characterizes its maximal L² domain in Theorem 5.1, gives divergence duality in Theorem 5.3, identifies pathwise divergence in Eq. (5.27)/Theorem 5.5, and states the corrected product rule in Eq. (6.3). Relevant printed pages are 4, 13, 16, 18–19 and 20.

Specializing the intensity space to one point of mass λ gives precisely the repository’s forward difference, field norm λE[u²], and divergence n u(n−1)−λu(n), with boundary −λu(0). This specialization is the audit’s comparison, not a Lean theorem identifying a general configuration-space construction with the repository model.

The mathematics is established Poisson Malliavin calculus. The explicit finite-support graph approximation and equality of concrete partial operators are useful formalization work, not evidence of new mathematical results. This audit makes no claim of priority over every public Lean repository.

Already reused formal infrastructure includes Mathlib’s actual Poisson distribution and integrable-series theorems in [Poisson/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/Probability/Distributions/Poisson/Basic.lean), and its unbounded adjoint machinery in [InnerProductSpace/LinearPMap.lean](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/Analysis/InnerProductSpace/LinearPMap.lean). The project supplies concrete difference/divergence graphs, exact domains, boundary estimates, graph cores and their identifications on top of those libraries.

## 10. Findings and recommended next milestone

**Blocking defects in the checked Lean development: none found.**

Nonblocking qualifications:

- The result is one-site, real-valued and positive-rate. It proves neither a general Poisson random-measure calculus nor multisite divergence domains, chaos expansions, stochastic integration, or abstract curvature results.
- Arbitrary maximal-domain multiplication is false. A claim that all of P5 establishes such closure would overstate the existing bounded theorem.
- The product theorem is a pointwise equality of actual operator outputs; an explicit L² product API remains to be supplied.
- These are formalizations of known mathematics. Different proof architecture does not establish mathematical novelty.

**Smallest safe next milestone: bounded multipliers acting on the full maximal derivative domain.**

For bounded m:ℕ→ℝ and arbitrary f∈dom D, prove the actual class of mf is in dom D and prove in K

    D(mf) = m(·+1) Df + (Dm)f.

The weighted-moment characterization gives domain preservation immediately from |m|≤C. Both m(·+1) and Dm are bounded, with |Dm|≤2C. Consequently each displayed product is genuinely in K, using f∈S, λ>0 and the established L∞×L² infrastructure. The expanded three-term jump product rule can then be packaged as an L² identity as well. This requires no assumed graph density or new operator axioms.

Acceptance criteria: retain the existing maximal operators, prove domain membership independently of the formula, prove L² membership of each term, establish equality of the actual L² outputs, and audit its axioms. Formalizing the counterexample above would provide an additional guard against future all-domain algebra claims.

