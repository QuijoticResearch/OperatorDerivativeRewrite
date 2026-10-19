# Bakry–Émery axiom replacement plan

Date: 2026-10-11. Repository inspected: `C:\OperatorDerivativeRewrite`.
Verified HEAD: `d9021ec16bef728e8e8c26f5018c54a08df3e793`.
Lean: `v4.34.1`; Mathlib lock: `d13f23b723b8a846827a245b89c10fc7d3f11612`.

**Verdict: REVISE.** The actual one-dimensional Gaussian inequality is mathematically valid and has a credible reuse path. It is not the general curvature-dimension theorem described in the manuscript. Several alleged downstream consequences are false or are only comments/placeholder propositions. Proving Gaussian log-Sobolev would eliminate the named axiom; it would not repair those other claims.

**Recommended scope:** prove the exact Gaussian inequality with its existing hypotheses, and additionally prove that its entropy integral is finite. Reuse the concrete one-dimensional proof in `markov-semigroups` after a compatibility and axiom audit. Do not build an abstract diffusion-semigroup library for this dependency. Do not import that library wholesale merely because a theorem is named “Bakry–Émery.”

Only this plan was created for this task. No Lean theorem, original source, manuscript, dependency, or Git commit was changed. The pre-existing untracked `INDEPENDENT_GRAPH_CORE_AUDIT.md` was preserved.

## 1. Evidence and verification scope

The entire original Lean file was searched for executable axioms and for entropy, log-Sobolev, curvature, hypercontractivity, and related uses. The relevant original definitions/proofs and manuscript passages were read directly. The unchanged original prefix through line 2464 was piped to Lean with inspection commands; it elaborates successfully. Thus the types below are checked elaborations, not interpretations of comments.

The whole original file does **not** compile against the current rewrite environment. A direct check reported errors at lines 3156, 3272, 3300, 3609, 3630, 3696, and 4456, including the invalid attempted L² multiplication at 3272. Consequently, a complete kernel dependency audit of the broken original file is not available. The dependency conclusions below combine checked proof terms in the elaborating prefix with a whole-file reference search; they do not certify later noncompiling declarations.

The unchanged rewrite passed:

- Full `lake build`: exit 0, “Build completed successfully (3359 jobs).”
- `lake env lean Foundation/AxiomAudit.lean`: exit 0; 714 reports for 713 distinct declarations.
- The union of reported axioms was exactly `{propext, Classical.choice, Quot.sound}`; no `sorryAx` or custom axiom.
- Git HEAD remained the commit above.

The direct Lake executable used was `C:/Users/ramir/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake.exe`. External Lean repositories were inspected at pinned commits, but were **not** independently built or kernel-audited in this task. External source inspection is a reuse lead, not a certification.

## 2. Exact original axiom, definitions, and dependencies

### 2.1 The sole mathematical axiom

The only executable `axiom` declaration in the original development is [OperatorDerivative.lean:2354](C:/Operator/OperatorDerivative.lean:2354), `bakry_emery_log_sobolev`. Its complete elaborated binder structure, with standard real-number instance terms suppressed, is:

```lean
bakry_emery_log_sobolev :
  ∀ (f f' : ℝ → ℝ),
    (∀ x : ℝ, HasDerivAt f (f' x) x) →
    (∀ x : ℝ, 0 < f x) →
    MeasureTheory.Integrable
      (fun x : ℝ => (f x) ^ 2)
      (ProbabilityTheory.gaussianReal 0 1) →
    MeasureTheory.Integrable
      (fun x : ℝ => (f' x) ^ 2)
      (ProbabilityTheory.gaussianReal 0 1) →
    gaussian_entropy (fun x : ℝ => (f x) ^ 2)
        (ProbabilityTheory.gaussianReal 0 1) ≤
      2 * gaussian_fisher f f'
        (ProbabilityTheory.gaussianReal 0 1)
```

There are **no** implicit probability-space, measure, operator, curvature, generator, or semigroup parameters in this declaration. In particular, the surrounding section variables `{Ω} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]` are unused and disappear from its elaborated type. The measure is concretely the standard real Gaussian, of mean zero and variance one; its Borel measurable structure is the standard instance.

Its dependencies are the two definitions below and ordinary Mathlib calculus, integration, and Gaussian infrastructure. It does not depend on `ou_curvature_bound` or the verified rewrite's Malliavin operators.

The exact mathematical content is **Entγ(f²) ≤ 2 ∫ |f′|² dγ**, with **γ = N(0,1)**.
The derivative is genuinely linked to `f` by `HasDerivAt`; there is no independently prescribed derivative defect in this particular declaration.

### 2.2 Definitions whose meaning must be preserved or clarified

| Original declaration | Actual content | Assessment |
|---|---|---|
| [gaussian_entropy, line 2284](C:/Operator/OperatorDerivative.lean:2284) | `∫ f log f dμ - (∫ f dμ) log(∫ f dμ)`, for `f : ℝ → ℝ`, `μ : Measure ℝ` | Usual entropy only when the integrals have their intended finite meaning. It has no integrability or positivity guard. |
| [gaussian_fisher, line 2291](C:/Operator/OperatorDerivative.lean:2291) | `∫ (f')² dμ`, with arguments `f f' : ℝ → ℝ` | The `f` argument is unused. This is Dirichlet energy, not the Fisher information of a density. |
| [ou_carre_du_champ, line 2297](C:/Operator/OperatorDerivative.lean:2297) | `ou_carre_du_champ (f' : ℝ → ℝ) (x : ℝ) := (f' x)^2` | Merely a formula on a supplied function. |
| [ou_gamma2, line 2301](C:/Operator/OperatorDerivative.lean:2301) | `ou_gamma2 (f' f'' : ℝ → ℝ) (x : ℝ) := (f'' x)^2 + (f' x)^2` | No generator or actual iterated carré-du-champ construction. |
| [ou_curvature_bound, line 2306](C:/Operator/OperatorDerivative.lean:2306) | `∀ (f' f'' : ℝ → ℝ) (x : ℝ), ou_gamma2 f' f'' x ≥ ou_carre_du_champ f' x` | Correct nonnegativity-of-a-square lemma. No assumption identifies either supplied function with derivatives of an underlying function. |

Lean's real Bochner integral returns zero for a nonintegrable integrand. Thus the entropy definition alone must never be used to claim finiteness. The axiom does not explicitly assert integrability of `f² log(f²)`. The Gaussian LSI theorem does imply that integrability under its other hypotheses, but this implication must be proved, not inferred from Lean's totalized integral.

This is not a counterexample to the actual Gaussian axiom: the desired analytic conclusion is true. It is a specification risk, particularly when extending or reusing the entropy definition.

### 2.3 Complete direct downstream dependency map

```text
bakry_emery_log_sobolev
  └── log_sobolev_1d  (line 2366; direct application at line 2376)
```

`log_sobolev_1d` has exactly the axiom's arguments and conclusion. Its checked axiom report is:
```text
[bakry_emery_log_sobolev, propext, Classical.choice, Quot.sound]
```

No further theorem in the original source references either declaration. The axiom is not registered as a simplification rule. In particular, no actual proof term connects it to the original Leibniz/Itô development. The longer pipeline is narrative, not an implemented chain of theorems.

Two nearby results should not be counted as downstream mathematical consequences:

```lean
log_sobolev_tensorization :
  ∀ (n : ℕ) (C : ℝ), 0 < C →
    (∀ (f f' : ℝ → ℝ),
      (∀ x : ℝ, HasDerivAt f (f' x) x) →
      (∀ x : ℝ, 0 < f x) →
      gaussian_entropy (fun x => (f x)^2) (gaussianReal 0 1) ≤
        C * gaussian_fisher f f' (gaussianReal 0 1)) →
    True
```

At [line 2381](C:/Operator/OperatorDerivative.lean:2381), this contains neither a product measure nor a multidimensional inequality. Its hypothesis also drops both integrability hypotheses of the axiom, so even the proposed premise is not directly supplied by `log_sobolev_1d`.

The elaborated type at [line 2429](C:/Operator/OperatorDerivative.lean:2429) is:
```lean
sobolev_embedding_from_hypercontractivity.{u_1, u_2} :
  ∀ (E : EnergySpace),
    (∀ (F : E.L2Ω) (ε : ℕ), 0 < ε →
      ∃ C_const : ℝ, ‖F‖ ≤ C_const * (‖F‖ + ‖E.D F‖)) →
    True
```

The unannotated `ε` is inferred as **ℕ**. More importantly, there is no semigroup or L⁴ norm, the premise holds by choosing `C_const = 1`, and the conclusion is `True`. Its proof and the tensorization proof use only the usual foundational axioms, not the Bakry–Émery axiom. Neither proves its advertised mathematical assertion.

### 2.4 Related assumptions hidden in structures

These are hypotheses of conditional theorems, not new kernel axioms. An axiom audit alone cannot validate their intended Gaussian realizations.

- [UnboundedEnergySpace.mul_dom, line 155](C:/Operator/OperatorDerivative.lean:155) has type
  `∀ (F G : U.L2Ω), F ∈ (adjoint U.δ).domain → G ∈ (adjoint U.δ).domain → U.mul F G ∈ (adjoint U.δ).domain`.
  It asserts closure of the full adjoint domain under a total `mul : L2Ω → L2Ω → L2Ω`. No L⁴ assumption appears, despite the “D¹,⁴ closure” comment.
- [UnboundedCylindricalStructure.cyl_dense, line 349](C:/Operator/OperatorDerivative.lean:349), with `{U : UnboundedEnergySpace}` and `self : U.UnboundedCylindricalStructure`, says
  `∀ F ∈ U.D.domain, ∃ seq : ℕ → U.L2Ω, ∀ k, self.is_cylindrical (seq k)`.
  It asserts **no convergence**. One cylindrical element suffices for this field.
- [UnboundedCylindricalStructure.leibniz_closure, line 369](C:/Operator/OperatorDerivative.lean:369) assumes that the cylindrical product identity implies `U.LeibnizCondition_unbounded`. The latter quantifies over all `F,G ∈ dom D` and a proof `FG ∈ dom D`, with the structure's total scalar-vector products. No L⁴ domain is present. The theorem at line 407 invokes this field.
- [EnergySpace.CylindricalStructure.leibniz_closure, line 1448](C:/Operator/OperatorDerivative.lean:1448) similarly assumes extension to its entire bounded ambient interface. The theorem at line 1482 invokes it.

The implicit parameters in these projections are just the indicated bundled `U` or `E`, their universe levels, and `self`; Hilbert structures and dense-domain facts are fields of those bundles. They are not secretly obtained from Gaussian log-Sobolev. The later concrete unbounded structure repeats a `mul_dom` field at line 2836.

Eliminating `bakry_emery_log_sobolev` will not discharge these structural obligations.

## 3. Mathematical assessment and manuscript comparison

### 3.1 Three different claims

| Claim | Necessary setting and conclusion | Verdict |
|---|---|---|
| A. Standard Gaussian LSI | γ = N(0,1); genuine derivative, f and f′ in L²(γ); Entγ(f²) ≤ 2‖f′‖²₂, with finite entropy | True. This is exactly the named axiom's mathematical target. Strict positivity can be retained for compatibility but is not mathematically necessary. |
| B. Abstract Bakry–Émery criterion | A conservative ergodic diffusion Markov semigroup with invariant probability measure, actual generator L, diffusion chain rule, justified Γ/Γ₂ calculus and analytic limits; CD(κ,∞), κ > 0, implies Entμ(f²) ≤ (2/κ)∫Γ(f) dμ | True with suitable hypotheses. Those hypotheses and objects are absent from the original axiom. |
| C. Consequences for an arbitrary operator derivative D = δ* | Adjointness/closedness alone imply neither Markov positivity, diffusion chain rules, positive curvature, LSI, nor algebra closure of dom D | Unsupported in this generality. Additional structure is indispensable. Some advertised Gaussian consequences are themselves false. |

The classical distinction and normalization can be checked in [Gentil, sections 2–3, especially Theorem 2.7](https://arxiv.org/pdf/1009.3421). An explicit ergodicity hypothesis appears in [Chafaï–Lehec, Theorem 5.10](https://djalil.chafai.net/docs/M2/chafai-lehec-m2-lsie-lecture-notes.pdf). These are references for known mathematics; the corrections and counterexamples below also follow by the displayed computations.

The axiom's regularity is sufficient mathematically. Everywhere `HasDerivAt` gives continuity and identifies f′ with the derivative. On each compact interval the Gaussian density has a positive lower bound, so f′ ∈ L²(γ) implies local Lebesgue L¹ integrability of f′. The fundamental theorem of calculus then gives local absolute continuity. Cutoff and smoothing arguments place f in Gaussian W¹,². Lean implementation of these bridges is an obligation, not a reason to add C∞ or boundedness silently.

### 3.2 What a valid abstract version would require

For a future general result, specify all of the following, rather than an arbitrary pair of closed adjoints:

1. A probability space and a strongly continuous, conservative, positivity-preserving Markov contraction semigroup Pₜ on L²(μ), symmetric and μ-invariant. If symmetry is relaxed, the exact symmetric energy and integration-by-parts identity must be restated and proved.
2. Its actual generator L and a dense test algebra with justified products, compositions, generator actions, and semigroup regularization. Γ and Γ₂ must be **defined from L**:
   - Γ(f,g) = ½[L(fg) − f Lg − g Lf].
   - Γ₂(f) = ½[LΓ(f,f) − 2Γ(f,Lf)].
3. The diffusion chain rule LΦ(f) = Φ′(f)Lf + Φ″(f)Γ(f,f), and the corresponding Γ chain rule, on the required tests. Positivity and generator symmetry yield the energy/IBP identities, with every term integrable.
4. κ > 0 and Γ₂(f) ≥ κΓ(f,f) on a sufficient common test domain. At minimum, the calculus must apply to log(Pₜg) for the positive regularized densities used in the proof, through proved approximation if these are not literal core elements.
5. A justified entropy trajectory: differentiability under the spatial integral, finite Fisher information, IBP for the evolving functions, and the time integrability needed for the fundamental theorem of calculus.
6. Ergodicity strong enough for Entμ(Pₜg) → 0 for the bounded positive densities in the proof. For such densities, prove this from suitable convergence and boundedness; do not infer it from invariance alone.
7. A proved approximation argument to the advertised form domain. Entropy lower semicontinuity and energy convergence must be established without treating a nonintegrable real integral as entropy.

These are sufficient hypotheses for a rigorous diffusion version, not the claim that a bare inequality between arbitrary “Gamma” functions has this consequence. The analytic clauses must either be consequences of a concretely constructed model or explicit, independently meaningful hypotheses of the abstract theorem. In particular, do not introduce a record field containing the final integrated entropy bound and advertise the resulting projection theorem as a proof from Γ₂.

**Why ergodicity matters:** take μ = γ ⊗ (½δ₀ + ½δ₁), and let L act as the Gaussian OU generator only in the real coordinate. The semigroup is symmetric, conservative, Markov and invariant; Γ₂ ≥ Γ holds on each component. A function equal to 1 on one component and 2 on the other has zero energy and strictly positive Entμ(f²), by strict convexity of r log r. Thus curvature plus invariance alone is insufficient. The disconnected factor is preserved by the semigroup.

A jump generator without the diffusion chain rule is another different setting; ordinary and modified log-Sobolev inequalities cannot be interchanged by reusing the same formal formulas.

### 3.3 Constants, signs, and operator direction

Use this single convention throughout:

| Object | Convention |
|---|---|
| Standard Gaussian | γ(dx) = (2π)⁻¹ᐟ² exp(−x²/2) dx |
| Markov generator | Lf = f″ − x f′, negative semidefinite in L² |
| Scalar number operator | N = δD = −L, on {f ∈ dom D : Df ∈ dom δ} |
| Semigroup | Pₜ = exp(tL) = exp(−tN), t ≥ 0 |
| Energy | E(f) = ∫(f′)² dγ = ‖Df‖²₂ |
| Carré du champ | Γ(f,g) = f′g′ |
| Iterated carré du champ | Γ₂(f) = (f″)² + (f′)², after proving the generator identity |
| Fisher information | I(g) = ∫(g′)²/g dγ for positive g |
| Square relation | I(f²) = 4E(f) for positive f |
| LSI | Entμ(f²) ≤ (2/κ)E(f); Gaussian κ = 1 |
| Hypercontractivity | q(t) − 1 = (p − 1)exp(2κt). If LSI is written Ent(f²) ≤ C E(f), this is exp(4t/C). |

In particular the Gaussian L²→L⁴ time is (log 3)/2.

For gₜ = Pₜg and Φ(t) = Entμ(gₜ), the justified diffusion calculation gives

- Φ′(t) = −I(gₜ).
- I′(t) = −2∫gₜ Γ₂(log gₜ) dμ ≤ −2κ I(gₜ).
- Φ″(t) = 2∫gₜ Γ₂(log gₜ) dμ.
- I(gₜ) ≤ exp(−2κt)I(g).
- Using entropy convergence to zero, Entμ(g) ≤ I(g)/(2κ).

The original prose at [lines 2316–2333](C:/Operator/OperatorDerivative.lean:2316) has a wrong factor in Φ′, an incorrect formula for Φ″ in terms of Γ₂(√gₜ), and a reversed inequality for the negative quantity Φ′. The correct comparison is Φ′(t) ≥ exp(−2κt)Φ′(0). Its intermediate 1/κ factor for the square energy is also wrong; the final 2/κ factor is right.

The earlier comment at [line 2271](C:/Operator/OperatorDerivative.lean:2271) omits a term in Gaussian IBP. The correct formula is ∫f′g dγ = ∫xfg dγ − ∫fg′ dγ; Stein's identity is its g = 1 specialization.

The original [EnergySpace.numberOperator, line 2486](C:/Operator/OperatorDerivative.lean:2486) is **Dδ on vector fields**, not the scalar δD governing this LSI. In the genuine Gaussian theory δD is unbounded, with an explicit composition domain. A bounded Dδ in the original abstract structure cannot be substituted for it.

### 3.4 False proposed consequences: explicit counterexamples

**D¹,²(γ) is not contained in L⁴(γ).** Set f(x) = exp(x²/6). Then
f²γ has tail exp(−x²/6), and (f′)²γ has a polynomial factor times the same decaying Gaussian tail. Both are integrable. But f⁴γ has tail exp(x²/6), so f ∉ L⁴. Smooth cutoff approximations put f in the Gaussian W¹,² graph domain. Hence f·f ∉ L², and dom D is not a pointwise algebra.

Similarly exp(x²/12) belongs to W¹,⁴(γ) but not L⁸(γ), and is unbounded. Thus the proposed D¹,⁴→L⁸ or L∞ repairs are false too. Finite-dimensional Euclidean Sobolev embeddings for unweighted Lebesgue measure cannot simply be transferred to a Gaussian probability measure.

The inverse-semigroup argument at [lines 2415–2427](C:/Operator/OperatorDerivative.lean:2415) fails: on Hermite mode n, exp(tN) has multiplier exp(tn), while a first-order graph norm grows like √(1+n) and the N graph norm like √(1+n²). No claimed uniform polynomial bound controls exp(tn). A general graph-domain element need not even lie in dom exp(tN).

The manuscript's statement [line 739](C:/Operator/OperatorDerivative.tex:739),
D¹,⁴ = D¹,² ∩ L⁴, is also false. Let χ be a smooth compactly supported cutoff equal to 1 near zero, and let f(x) = χ(x)|x|²ᐟ³. Then f is bounded, its weak derivative behaves like |x|⁻¹ᐟ³ near zero, and the Gaussian density there is comparable to a positive constant. Thus f′ is locally L² but not L⁴. This gives f ∈ D¹,² ∩ L⁴ but f ∉ D¹,⁴. Meyer's inequalities do not remove the L⁴ derivative requirement.

Gaussian LSI itself is consistent with all these examples: its gain is entropy control, not an automatic fixed Lᵖ improvement for every Gaussian Sobolev function.

### 3.5 Comparison with the manuscript and stronger claims

| Manuscript location | Claim | What the Lean source actually supports |
|---|---|---|
| [Line 1338](C:/Operator/OperatorDerivative.tex:1338) | One axiom is a semigroup interpolation theorem | The sole axiom is the final one-dimensional Gaussian inequality. |
| [Line 1375](C:/Operator/OperatorDerivative.tex:1375) | Γ₂ ≥ κΓ implies LSI with 2/κ is declared as an axiom; OU curvature proved | The general theorem is absent. Only the numerical OU square inequality is proved; generator identification and interpolation are absent. |
| [Line 1377](C:/Operator/OperatorDerivative.tex:1377) | The closure field packages D¹,⁴ graph approximation requiring Meyer/Littlewood–Paley | Its Lean field has no L⁴ restriction; its “density” field has no convergence. Moreover the manuscript itself defines D¹,ᵖ by graph completion at line 503. |
| [Line 1419](C:/Operator/OperatorDerivative.tex:1419) | `log_sobolev_1d` derived from an axiom | Accurate for the wrapper alone. |
| [Line 739](C:/Operator/OperatorDerivative.tex:739) | D¹,⁴ = D¹,² ∩ L⁴ | False, as above. |
| [Lines 1018–1026](C:/Operator/OperatorDerivative.tex:1018) | Product extension using L⁴ control and graph approximation | The L⁴ exponents are appropriate. Its displayed D(FG) must only be introduced after closedness establishes domain membership; the written limit argument anticipates that conclusion. |

The manuscript's abstract representation/factorization claims, stochastic-volatility random representers, and deterministic-representer obstruction (introduction, Sections on representation and stochastic volatility) extend beyond a fixed standard Gaussian LSI statement. Nothing in this plan proves those extensions. In particular, non-Gaussian or random-coefficient divergences need their own positivity, diffusion, domain, and curvature analysis. Operator adjointness by itself supplies none of those.

**Direct repair of the calculus dependency:** for F,G approximated by genuine cylinders in the L⁴ graph norm, Hölder gives FₙGₙ→FG in L² and
FₙDGₙ + GₙDFₙ → F DG + G DF in vector L². Closedness of D then proves FG ∈ dom D and the product rule. Domain membership is a conclusion of closedness, not a premise smuggled into a “defect” map. This argument needs neither LSI nor L⁸/L∞ embeddings. If D¹,⁴ is defined as the L⁴ graph completion, the approximation is part of its definition; identifying that completion with a different maximal weak-derivative domain is a separate theorem.

Consequently there are two useful projects: replace the valid Gaussian axiom, and repair the restricted-domain calculus. Neither should be represented as automatically solving the other.

## 4. Existing formalizations and reuse decision

### 4.1 Pinned Mathlib: use existing analysis, not a new integration library

The local locked source is [Mathlib at d13f23b](https://github.com/leanprover-community/mathlib4/tree/d13f23b723b8a846827a245b89c10fc7d3f11612), dated 2026-09-24. Searches of this tree did not locate a named Gaussian LSI, Bakry–Émery criterion, Mehler/OU development, or hypercontractivity theorem. This is a bounded search result, not a novelty claim about every public Lean repository.

Relevant existing APIs, inspected in that checkout:

| Exact file under `Mathlib/` | Existing declarations and intended use |
|---|---|
| `Analysis/SpecialFunctions/Log/NegMulLog.lean` | `Real.continuous_mul_log`, `Real.convexOn_mul_log`, `Real.self_sub_one_le_mul_log`: zero-compatible entropy integrands, convexity, lower bounds |
| `InformationTheory/KullbackLeibler/KLFun.lean` | `InformationTheory.klFun`, `klFun_nonneg`, `continuous_klFun`: k(r)=r log r+1−r, a nonnegative function for r≥0 |
| `InformationTheory/KullbackLeibler/Basic.lean` | `InformationTheory.klDiv`, `klDiv_of_not_integrable`, `klDiv_eq_lintegral_klFun_of_ac`: extended-valued relative entropy; a possible later bridge, not the Gaussian LSI itself |
| `Analysis/Convex/Integral.lean:197` | `ConvexOn.map_integral_le`: Jensen and nonnegativity of finite square entropy |
| `Analysis/Calculus/ParametricIntegral.lean` | Differentiation under the integral; use its actual domination and measurability hypotheses |
| `MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean:1148` | `intervalIntegral.integral_eq_sub_of_hasDerivAt`: FTC under pointwise derivatives and interval integrability |
| `MeasureTheory/Integral/Lebesgue/Add.lean:233` | `MeasureTheory.lintegral_liminf_le`: Fatou, retaining extended values |
| `MeasureTheory/Function/ConvergenceInMeasure.lean:273` | `MeasureTheory.TendstoInMeasure.exists_seq_tendsto_ae`: subsequences for entropy lower semicontinuity |
| `Analysis/Calculus/BumpFunction/Convolution.lean` and `Analysis/Calculus/ContDiff/Convolution.lean` | Bump-function smoothing, `ae_convolution_tendsto_right_of_locallyIntegrable`, and convolution regularity; weighted graph convergence still has to be assembled |
| `Probability/Distributions/Gaussian/Real.lean` | `gaussianReal`, Gaussian densities/moments and distribution identities |
| `MeasureTheory/Integral/Prod.lean` and Lp infrastructure | Fubini, Hölder, integrability, Lp convergence and norm estimates |

[KLFun source](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/InformationTheory/KullbackLeibler/KLFun.lean) and [FTC source](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean#L1148) are particularly useful for the first and final milestones.

A finite-valued entropy definition is acceptable as an interface once finiteness has been proved. During limit arguments use the nonnegative `klFun` integral or extended relative entropy; never obtain a finite entropy theorem merely by converting an infinite value to a real number.

### 4.2 A concrete Gaussian proof already exists outside Mathlib

The most relevant repository is [mrdouglasny/markov-semigroups](https://github.com/mrdouglasny/markov-semigroups), pinned here to
[`acf649108ea2222f4a8544a2782f448cb502492a`](https://github.com/mrdouglasny/markov-semigroups/commit/acf649108ea2222f4a8544a2782f448cb502492a), 2026-06-02 13:10:37 UTC. This is the dependency revision used by the inspected gaussian-hilbert lockfile.

The concrete chain has real proof bodies:

| File under `MarkovSemigroups/` | Exact declarations |
|---|---|
| [Instances/WorkInProgress/Euclidean.lean](https://github.com/mrdouglasny/markov-semigroups/blob/acf649108ea2222f4a8544a2782f448cb502492a/MarkovSemigroups/Instances/WorkInProgress/Euclidean.lean) | `Gaussian1D.γ` (57), `ouSemigroup` (64), `ouEnergy` (72), `IsCore` (132), `hasDerivAt_ouSemigroup_C1` (505), `deriv_ouSemigroup_eq` (574), `ouSemigroup_compose` (905), `ouSemigroup_entropy_sq_ergodic` (1209) |
| [General/OUEntropyDecomposition.lean](https://github.com/mrdouglasny/markov-semigroups/blob/acf649108ea2222f4a8544a2782f448cb502492a/MarkovSemigroups/General/OUEntropyDecomposition.lean) | `Gaussian1D.ouSemigroup_fisher_info_decay` (200), `hasDerivAt_entropy_ouSemigroup` (607), `hasDerivWithinAt_entropy_ouSemigroup_zero` (1654) |
| [Instances/WorkInProgress/EuclideanEntropyDecay.lean](https://github.com/mrdouglasny/markov-semigroups/blob/acf649108ea2222f4a8544a2782f448cb502492a/MarkovSemigroups/Instances/WorkInProgress/EuclideanEntropyDecay.lean) | `Gaussian1D.boltzmannEntropy_ouSemigroup_decay_le` (181), `ouSemigroup_entropy_sq_decay_bound_proved` (278), `bakryEmerySpace` (797) |
| `Instances/WorkInProgress/EuclideanHermite.lean` | `Gaussian1D.ouSemigroup_preserves_IsCore` (903), smoothing helpers |
| `Instances/WorkInProgress/EuclideanStein.lean` | `Gaussian1D.ouSemigroup_l2_sq_hasDerivWithinAt_proved` (1221), weighted IBP helpers |
| [Diffusion/CarreDuChamp.lean](https://github.com/mrdouglasny/markov-semigroups/blob/acf649108ea2222f4a8544a2782f448cb502492a/MarkovSemigroups/Diffusion/CarreDuChamp.lean) | `BakryEmerySpace` (62), `BakryEmerySpace.satisfiesLogSobolev` (227) |
| `Abstract/DirichletForm.lean` | `DirichletSpace.entropy` (108), `DirichletSpace.SatisfiesLogSobolev` (119) |

Important restrictions:

- `Gaussian1D.IsCore f` means f is C∞ and there exists M with |f|, |f′| and |f″| ≤ M everywhere. It does not include every function of the original axiom, nor nonconstant polynomials.
- Its positive-density Fisher/entropy lemmas require C¹ regularity, a fixed positive lower bound ε, an upper bound M and a bound on |g′|. They are substantive intermediate estimates, not mere restatements of LSI.
- The core square-entropy theorem uses g = f²+ε, proves the estimates, and passes ε↓0.
- The one-dimensional import closure comprises seven project modules, about 8,060 source lines, with other imports from Mathlib. A comment-stripped scan found no executable `axiom`, `sorry`, `admit` or unchecked-code construct in those seven modules. Some comments still describe now-proved results as axioms or partial proofs. Those comments must not be used as the audit result.
- This task did not rebuild that separate project. A fresh transitive `#print axioms` audit and statement check on the actual port remain mandatory.

**Critical distinction:** `BakryEmerySpace` itself has a field `semigroup_entropy_sq_decay_bound` at line 138, containing the integrated entropy estimate, and `semigroup_entropy_sq_ergodic` at line 146. Its `satisfiesLogSobolev` theorem takes their limit. It is not, by itself, a derivation of that estimate from the generator's Γ₂ criterion. The concrete Gaussian instance is useful precisely because it supplies the entropy-decay field using the actual proof above. Importing the abstract wrapper and assuming this field would move the original gap into a structure.

Its `gradient_decay` field at line 89 is only an integrated energy estimate. Such an estimate alone is not the weighted Fisher-information inequality needed for LSI.

### 4.3 gaussian-hilbert and lean-malliavin

[gaussian-hilbert](https://github.com/mrdouglasny/gaussian-hilbert), commit
[`4d055b0bf3722c73bd6c327eeabd8a8a72ab4c7e`](https://github.com/mrdouglasny/gaussian-hilbert/commit/4d055b0bf3722c73bd6c327eeabd8a8a72ab4c7e), 2026-06-05 23:17:26 UTC:

- [GaussianHilbert/HypercontractivityFromBE.lean:133](https://github.com/mrdouglasny/gaussian-hilbert/blob/4d055b0bf3722c73bd6c327eeabd8a8a72ab4c7e/GaussianHilbert/HypercontractivityFromBE.lean#L133), `oneDimGaussianLSI`, applies the concrete Gaussian instance above. The parameter called “LSI(1)” is curvature/rate ρ=1; its square-energy constant is **2**, not 1.
- The same file has `stdGaussianFin_LSI` (152) and `stdGaussianFin_dirichletMarkovSemigroup_isHypercontractive` (232). Do not classify their dependencies from the historical header alone: at the pinned Markov revision, the three formerly assumed finite-dimensional lemmas are now theorems: `GaussianFin.ouSemigroupFin_preserves_IsCore` in `EuclideanFin.lean:3569`, `ouSemigroupFin_entropy_sq_decay_bound` there at 5316, and `ouSemigroupFin_l2_sq_hasDerivWithinAt` in `EuclideanFinBE.lean:447`.
- The abstract `Hypercontractivity.lean` still declares `stroock_varopoulos` (621), `gross_lsi_implies_hypercontractive` (648) and `gross_hypercontractive_implies_lsi` (658). The inspected concrete hypercontractivity path uses a proved alternative. An import containing an axiom is not evidence that a particular theorem depends on it; only a transitive audit settles that question.
- The one-dimensional chain is sufficient here. No broad finite-dimensional/hypercontractive import is needed merely to discharge the original axiom.

The inspected gaussian-hilbert configuration uses Lean/Mathlib v4.30.0, with Mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`; this project uses v4.34.1. It is not a drop-in compatible dependency. Prefer a narrowly scoped, attributed port or an upstream-compatible revision after testing; preserve Apache-2.0 notices if copying code. Do not downgrade this repository or alter its lockfile to make a speculative import work.

[lean-malliavin](https://github.com/savarin/lean-malliavin), commit
[`a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272`](https://github.com/savarin/lean-malliavin/commit/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272), 2026-08-31 20:53:26 UTC, is relevant for comparing Gaussian Sobolev constructions:
[**Malliavin/MalliavinDerivative.lean**](https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/MalliavinDerivative.lean) contains `mderiv_closable`, `domD12`, and `mderivPMap`; [**Malliavin/CylindricalGrowth.lean:406**](https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CylindricalGrowth.lean#L406) contains `cylinder_growth_mem_domD12`. Its more general Gaussian-space model may help a future core comparison. No drop-in LSI or general Γ₂ theorem was located in the inspected material. Existence of a closed Malliavin derivative is not an LSI proof.

**Reuse decision:** concrete one-dimensional Mehler/Fisher/entropy proofs are the best candidate. The full abstract curvature criterion is not needed for the exact axiom. Reusing established proofs is more valuable than constructing another large semigroup hierarchy here.

## 5. What the verified foundation contributes—and what it does not

All local paths below are relative to [the rewrite repository](C:/OperatorDerivativeRewrite).

| Existing verified component | Genuine use for this project | Still missing |
|---|---|---|
| `Foundation/GaussianCore.lean`: `polynomial_memLp` (21), `polynomial_hasDerivAt` (47), `polynomial_stein` (98), `polynomial_integration_by_parts` (131) | Finite moments, actual polynomial differentiation, correct Gaussian IBP | IBP and differentiation on positive regularized nonpolynomial Mehler trajectories |
| `Foundation/GaussianHermite.lean`: `hermiteBasis` (171), raising/lowering graph theorems (198, 231) | A possible spectral L² semigroup, energy normalization, tests for the scalar number operator | Positivity/Markov properties do not follow merely by assigning diagonal multipliers |
| `Foundation/GaussianHermiteDomains.lean`: `closedDerivative_domain_iff` (33), `closedDerivative_norm_sq` (90) | Exact Gaussian derivative graph and energy; Hermite approximation | Entropy is nonlinear and not controlled by Parseval alone |
| `Foundation/InfiniteGaussianPolynomialProducts.lean`: `polynomialDomain_memLp`, `polynomialDerivative_memLp`, `polynomialDerivative_product` | All finite moments and a genuine intrinsic product rule on cylinders | Extension to L⁴ Sobolev graph completion; no algebra structure on all dom D |
| `Foundation/InfiniteGaussianIBP.lean`: `rankDivergence_memLp`, `polynomialDerivative_rank_pairing` | Actual integration by parts and domain-compatible products | A positive diffusion semigroup and nonlinear chain rules on its trajectories |
| `Foundation/InfiniteGaussianOperators.lean`: `cylindricalDerivative_isClosable`, `hilbertDivergence_mem_iff` | Closed D and exact adjoint δ | Markovianity and curvature are additional properties |
| `Foundation/InfiniteGaussianProjectionConvergence.lean:313,320,327`: `cylindricalDivergence_adjoint_eq_closedDerivative`, `closedPolynomialDivergence_eq_hilbertDivergence`, `hilbertDivergence_polynomial_graph_core_sequence` | Full polynomial divergence graph core, without losing cancellations | This is graph-norm information, not entropy dissipation or Lᵖ smoothing |
| `Foundation/LpProducts.lean`: `mul_L4_memLp_two`, `smul_L4_memLp_two`, `lpMul_norm_le`, `lpSmul_norm_le` | Correct product domains and the short L⁴ graph-closure argument | These estimates do not show that an arbitrary L² graph-domain element lies in L⁴ |

The new infinite-dimensional graph-core theorem is substantial operator infrastructure. It is not needed to establish one-dimensional Gaussian LSI, and it must not be cited as if it automatically supplies the missing nonlinear analysis.

No current local module was found constructing the required Mehler semigroup, proving its Markov/invariance properties, defining Γ and Γ₂ from its generator, proving weighted Fisher decay, or establishing entropy differentiation and time integration. The original numerical formulas for Γ/Γ₂ are not substitutes.

## 6. Minimal corrected replacement theorem

Introduce a new, clearly named Gaussian theorem; do not edit the legacy statement during this investigation.

Let

```text
entropySq μ f =
  ∫ x, (f x)² * log((f x)²) ∂μ
  − (∫ x, (f x)² ∂μ) * log(∫ x, (f x)² ∂μ).
```

**Replacement target, preserving every legacy hypothesis:**

For f,f′ : ℝ→ℝ, if f has derivative f′ everywhere, f>0 everywhere,
∫f²dγ<∞ and ∫(f′)²dγ<∞, then

1. `Integrable (fun x => (f x)^2 * Real.log ((f x)^2)) γ`;
2. `entropySq γ f ≤ 2 * ∫ x, (f' x)^2 ∂γ`.

These are finite Bochner-integral statements; the first is a conclusion. Do not add entropy integrability, boundedness, C∞ regularity, graph-core membership, LSI, or Fisher decay to the final hypotheses. The proof may first establish stronger regularity cases, clearly labelled.

Proposed final name: `GaussianCore.gaussian_logSobolev_of_hasDerivAt`, under the project's existing `OperatorDerivativeRewrite.Foundation` namespace. Prove a helper without the positivity assumption if convenient; retain an exact compatibility corollary. Once this theorem is verified, the old axiom can be replaced by a theorem via definitional equality of the entropy/energy expressions in a separately authorized edit. The general CD theorem must remain explicitly unproved until its own infrastructure exists.

A bounded smooth-core theorem is a useful milestone, but it does **not** yet discharge the original axiom. The core-to-full-domain passage is required.

## 7. Incremental Lean implementation plan

All names and files in this section are **proposed**, not declarations already established by this task. Each milestone must compile independently against the pinned toolchain, add axiom queries for every public declaration, and preserve all existing theorem statements. Stop and reassess if a port requires assuming any analytic estimate listed as a conclusion below.

### M1 — Nonvacuous square entropy: the first Sol Medium task

**Exact statements.** On a finite measure space, f ∈ L⁴ implies f² log(f²) ∈ L¹. On a probability space, its square entropy is nonnegative. Specialize integrability to every real polynomial under γ.

**Expected file and declarations:** `Foundation/GaussianEntropy.lean`, with a generic probability/finite-measure section and a Gaussian specialization. Suggested signatures, with no proof bodies supplied in this plan:

```lean
-- {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
integrable_sq_mul_log_of_memLp_four
  [IsFiniteMeasure μ] {f : Ω → ℝ}
  (hf : MemLp f 4 μ) :
  Integrable (fun ω => (f ω)^2 * Real.log ((f ω)^2)) μ

entropySq_nonneg_of_memLp_four
  [IsProbabilityMeasure μ] {f : Ω → ℝ}
  (hf : MemLp f 4 μ) :
  0 ≤ entropySq μ f

GaussianCore.polynomial_sq_mul_log_integrable (p : ℝ[X]) :
  Integrable
    (fun x : ℝ => (p.eval x)^2 * Real.log ((p.eval x)^2))
    GaussianCore.γ
```

Define `entropySq` by the displayed formula, with a docstring stating when its real integral has the intended meaning. Add a.e. congruence and constant/zero evaluation only as useful supporting lemmas. Do not claim square entropy is finite on all L² functions.

**Reuse:** `InformationTheory.klFun_nonneg`, `continuous_klFun`, `Real.log_le_sub_one_of_pos`, `Real.convexOn_mul_log`, `ConvexOn.map_integral_le`, existing Lp/Hölder/integrability lemmas, and `GaussianCore.polynomial_memLp`.

**Proof:** for r≥0, derive 0≤k(r)≤1+r² where k(r)=r log r+1−r, handling r=0 separately. Therefore k(f²) is integrable from L⁴, and f²log(f²)=k(f²)−1+f² is integrable. Apply Jensen to r log r on [0,∞) for nonnegativity. This proves a real integrability estimate, not a repackaged integrability hypothesis.

**Dependencies:** existing Mathlib and the verified polynomial-moment theorem only; no external library or semigroup.

**Acceptance:** full build; all new axiom reports use only the standard three axioms; no added hypotheses of entropy integrability; no positivity assumption on f; zero and constants are handled; polynomial corollary follows from existing moments. Include the new module in the library import root and its declarations in the audit, after implementation is authorized.

**Risk/difficulty:** low mathematical difficulty, modest Lean integrability bookkeeping. This is the exact first implementation request recommended to Sol Medium. Stop after this small verified module rather than starting a semigroup framework.

### M2a — Concrete one-dimensional Mehler kernel and measure identities

**Statement:** for t≥0 and bounded continuous f,

Pₜf(x) = ∫ f(exp(−t)x + √(1−exp(−2t))y) dγ(y).

Prove P₀f=f, preservation of constants/order/bounds, invariance ∫Pₜf dγ=∫f dγ, and PₛPₜf=Pₛ₊ₜf on the stated class. Prove Pₜf→∫f dγ pointwise as t→∞, with bounded domination sufficient for entropy limits.

**Definitions:** `GaussianMehler.mehler` in `Foundation/GaussianMehler.lean`. Restrict all identities to classes for which their integrals are established. No arbitrary real-integral semigroup identity for nonintegrable functions.

**Reuse:** source-level port from `Gaussian1D.ouSemigroup`, `ouSemigroup_preserves_bounds`, `ouSemigroup_compose`, and its invariance/ergodicity proofs; Mathlib Gaussian linear combinations, Fubini and dominated convergence. Use the existing γ definition.

**Strategy/dependencies:** audit and port the narrow dependency slice at v4.34.1, preserving attribution. Derive invariance from the fact that aX+bY is standard Gaussian for independent standard X,Y and a²+b²=1. Derive composition by the corresponding Gaussian combination. Do not infer Markov positivity from a spectral expansion.

**Acceptance:** actual Mehler integral, constants and variance normalization checked; every integral justified. If a full L² operator is bundled, prove a.e. congruence and contraction first. For the narrow LSI route, a pointwise bounded-function family is enough; a general strongly continuous semigroup hierarchy is optional.

**Risk/difficulty:** medium; source migration and Gaussian distribution APIs. Keep kernel, invariance, composition, and ergodicity as separate compiling increments if needed.

### M2b — Genuine derivatives and Fisher-information decay

**Statement:** for a C¹ g with 0<ε≤g≤M and |g′|≤M, prove
(Pₜg)′=exp(−t)Pₜg′ and
I(Pₜg)≤exp(−2t)I(g), for t≥0.
Here I(g)=∫(g′)²/g dγ and all integrands are proved integrable.

**Definitions:** `GaussianFisher.fisherInformation` in `Foundation/GaussianFisherDecay.lean`; use actual `deriv g`, not unrelated supplied data. Any regularity record contains only derivative/bound hypotheses, not the decay conclusion.

**Reuse:** `Gaussian1D.hasDerivAt_ouSemigroup_C1` and `ouSemigroup_fisher_info_decay`; Mathlib differentiation under integrals, Cauchy–Schwarz and invariance from M2a.

**Proof:** differentiated Mehler formula plus weighted Cauchy–Schwarz:
(Pₜg′)²/(Pₜg) ≤ Pₜ((g′)²/g). Integrate and use invariance. This concrete commutation proof avoids the need for an abstract Γ₂ library.

**Acceptance:** the derivative is verified through the Mehler integral; positivity of Pₜg and integrability of all divisions are proved; t=0 handled; no assumed Fisher decay. Optionally add a separate polynomial generator calculation Γ₂(f)=(f″)²+(f′)², explicitly derived from L, but it is not a dependency of this direct proof.

**Risk/difficulty:** medium to high Lean analysis; known mathematics. A bound on integrated unweighted energy is not a substitute for the weighted estimate.

### M3 — Entropy dissipation on a regularized core

**Statement:** under the positive bounded hypotheses above, prove for t>0

d/dt Entγ(Pₜg) = −I(Pₜg),

with continuity of the entropy trajectory at t=0 and convergence to zero as t→∞.

**Definitions:** `Foundation/GaussianEntropyDissipation.lean`, `entropyTrajectory` and positive-time `HasDerivAt` theorems. Entropy uses the M1 formula adapted to a density, with proved finiteness.

**Reuse:** `Gaussian1D.hasDerivAt_entropy_ouSemigroup`, its smoothing/Stein dependencies, `ouSemigroup_entropy_sq_ergodic`; Mathlib parametric integration, FTC and DCT.

**Proof:** Mehler smoothing and time differentiation, followed by genuine Gaussian IBP with log(Pₜg); the invariant mean removes the normalization term. Prove domination on each compact positive-time interval. The shortest route need not prove a derivative at t=0: integrate from a>0 and then send a↓0 using continuity and M2b's bound.

**Dependencies:** M2a–M2b and finite entropy on bounded functions.

**Acceptance:** no record field or hypothesis is the entropy derivative/decay conclusion; IBP is justified for the actual evolving nonpolynomial functions. Explicitly state the regularity available at t>0 versus at zero.

**Risk/difficulty:** high implementation effort if porting fails; this is the main semigroup analytic step, already represented by a long public proof.

### M4 — Gaussian LSI on the bounded smooth core

**Statement:** for f∈C∞ with f, f′, f″ bounded,
Entγ(f²)≤2∫(f′)²dγ, with entropy integrability proved and without requiring f to be strictly positive.

**Definitions:** `Foundation/GaussianLogSobolevCore.lean`, an explicit `GaussianSmoothBoundedCore` predicate matching the upstream `IsCore`, and `gaussian_logSobolev_core`.

**Reuse:** M1–M3, upstream `boltzmannEntropy_ouSemigroup_decay_le` and `ouSemigroup_entropy_sq_decay_bound_proved`; FTC and dominated convergence. A direct verified adapter to the upstream core theorem can replace duplicated implementation once its imports, constants, hypotheses and axioms are checked.

**Proof:** set gε=f²+ε. Establish I(gε)≤4∫(f′)². Integrate dissipation and Fisher decay to obtain
Entγ(gε)≤½I(gε)≤2E(f).
Send ε↓0 by bounded domination and continuity of r log r at zero.

**Acceptance:** no positivity assumption on f and no assumed LSI; numerical factor 2 obtained from 4×∫₀∞exp(−2t)dt. The theorem is explicitly labelled a core result and is not advertised as a replacement for the full old axiom.

**Risk/difficulty:** low mathematical difficulty after M3; medium Lean assembly. Beware mismatching upstream parameter ρ=1 with energy constant C=2.

### M5 — Approximation for the legacy derivative hypotheses

**Statement:** if f has derivative f′ everywhere and f,f′∈L²(γ), there are smooth compactly supported fₙ with
‖fₙ−f‖L²(γ)→0 and ‖fₙ′−f′‖L²(γ)→0.

**Definitions:** `Foundation/GaussianSobolevApproximation.lean`; use ordinary functions, `ContDiff`, `HasCompactSupport`, `MemLp`, and explicit L² convergence. The theorem must not take this approximation as a hypothesis.

**Reuse:** Gaussian density positivity on compact intervals; `intervalIntegral.integral_eq_sub_of_hasDerivAt`; Mathlib bump/convolution regularity, local integrability and Lp approximation. Reuse any compatible public approximation theorem only after matching its actual weighted derivative hypotheses.

**Proof:** derive local absolute continuity from the legacy assumptions; apply smooth cutoffs; control the extra cutoff-derivative term in L²(γ); mollify on compact sets where Gaussian and Lebesgue norms are comparable; choose a diagonal sequence. Each fₙ is in M4's core.

**Dependencies:** calculus/Lp infrastructure, not LSI. This proof is independent of any identification of the polynomial operator closure with a separately defined maximal Sobolev domain.

**Acceptance:** approximation theorem has only the original derivative and L² hypotheses; no bound on f, no assumed entropy integrability, no unproved weighted core-density field. Record the actual derivative of every approximant.

**Risk/difficulty:** standard mathematics, potentially substantial Lean work. Availability of a convolution theorem does not by itself prove weighted Sobolev graph convergence. This is the main unresolved extension obligation for the legacy axiom after reusing the public core LSI.

### M6 — Entropy limit and exact axiom replacement

**Statement:** the two-part replacement theorem in section 6, preferably first without the unnecessary strict-positivity assumption.

**Definitions:** `Foundation/GaussianLogSobolev.lean`, `gaussian_logSobolev_of_hasDerivAt` and an exact legacy-compatible corollary.

**Reuse:** M4–M5, `TendstoInMeasure.exists_seq_tendsto_ae`, Fatou for nonnegative integrands, and continuity of k(r)=r log r+1−r.

**Proof:** use the approximants from M5. Their means mₙ=∫fₙ² converge to m=∫f² and their energies converge to E(f). On a probability space,

∫k(fₙ²)dγ = Entγ(fₙ²) + k(mₙ) ≤ 2E(fₙ)+k(mₙ).

Extract an a.e.-convergent subsequence and apply Fatou to k(fₙ²)≥0. The limit integral is finite and ≤2E(f)+k(m). This first proves integrability of f²log(f²), then the desired inequality. It never invokes a real entropy inequality for a function whose entropy has not been shown finite.

**Acceptance:** exact old hypotheses retained, entropy integrability is an output, full build and transitive axiom audit pass; the compatibility corollary has no extra core/density/LSI hypothesis. Only then is replacement of the original axiom justified in a later authorized edit.

**Risk/difficulty:** moderate; avoiding totalized integrals and mishandled liminf/real conversions is essential.

### M7 — Optional operator-domain and higher-dimensional bridges

These are later projects, not necessary to eliminate the exact one-dimensional axiom.

- **One-dimensional closed operator:** for every (f,g)∈graph(closedDerivative), prove finite Entγ(f²)≤2‖g‖²₂. Use the verified polynomial graph approximants, M6 applied to polynomials, and the M6 Fatou argument. No independent maximal-domain identification is required for this route. Expected file: `GaussianOperatorLogSobolev.lean`. Acceptance: the actual closed operator appears, and no entropy/core approximation is assumed.
- **Finite and countable Gaussian products:** prove genuine tensorization with dimension-independent constant, then pass from cylindrical functions to dom D by graph approximation and entropy lower semicontinuity. Reuse the actual finite-dimensional public results after a separate dependency audit, or prove tensorization. Correlated coordinates require the covariance/Cameron–Martin energy, not an unjustified identity-covariance gradient.
- **Restricted-domain product repair:** define the L⁴ graph completion of genuine cylinders, prove its map into dom D using closedness, and prove the L⁴×L⁴→L² product rule using `LpProducts`. Acceptance: membership and Leibniz are conclusions; no assertion dom D is an algebra. This is a short independent route to the intended calculus, not a consequence of M6.
- **Abstract CD(κ,∞):** implement actual generator/Γ/Γ₂ calculus and discharge section 3.2's analytic assumptions model by model. This is a much larger undertaking. A Gaussian theorem must never be renamed or described as this general result.

Each optional bridge needs its own build, axiom audit, precise domain statement, and review. Neither an L²-density theorem nor the verified divergence graph core substitutes for the relevant Lᵖ or entropy limit argument.

## 8. Difficulty, stopping criteria, and recommendation

The exact Gaussian theorem is established classical mathematics; no new mathematical insight is required to make it true. The main work is integration/regularity formalization and compatibility with existing code. The external concrete core proof materially reduces the case for creating a semigroup library here, but the port and full-domain extension remain real work.

| Item | Mathematical difficulty | Lean risk |
|---|---|---|
| M1 finite/nonnegative entropy | Low | Low–moderate |
| M2 concrete Mehler and Fisher estimates | Standard graduate analysis | Moderate–high; existing proofs available |
| M3 entropy differentiation | Standard but analytically delicate | High if rewritten; port first |
| M4 bounded smooth-core LSI | Low after M3 | Moderate |
| M5 weighted graph approximation | Standard Sobolev analysis | High; inspect and reuse approximation APIs carefully |
| M6 full legacy statement | Moderate limit argument | Moderate |
| General abstract CD theorem | Larger analytic framework | Very high relative to the immediate need |

No estimate in calendar days is warranted before the narrow external proof slice is tested against v4.34.1.

**REVISE** the claimed scope and the proposed downstream Sobolev consequences. **Proceed** with a Gaussian-specific, explicitly named replacement preserving the original axiom's mathematical hypotheses. Keep abstract Bakry–Émery theory and non-Gaussian operator claims separate. If the actual priority is only Leibniz closure, use the L⁴ graph-completion argument directly instead of making that repair depend on log-Sobolev.

**First Lean milestone for Sol Medium:** implement only M1 in `Foundation/GaussianEntropy.lean`: prove `integrable_sq_mul_log_of_memLp_four`, `entropySq_nonneg_of_memLp_four`, and `GaussianCore.polynomial_sq_mul_log_integrable`, with actual Mathlib integration estimates, then build and audit. This deliberately proves neither LSI nor any Sobolev embedding. Do not modify the original files, add a dependency, or start a general semigroup hierarchy in that first milestone.

There is no unresolved mathematical obstruction to the precise Gaussian replacement. The unresolved formal obligations are the audited compatible core-proof port and the full-domain approximation/entropy limit. The general curvature-dimension theorem, the false Sobolev claims, and the manuscript's non-Gaussian extensions are not discharged by that replacement.
