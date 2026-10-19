# Independent adversarial audit: Gaussian log-Sobolev M1–M4

**Verdict: PASS for the bounded-C¹ theorem actually stated.**

Audited commit: `d9109c4e910e90dd1067fc01f59ceebfcfa4f7e1`.
Audit date: 2026-10-11. Repository: `C:\OperatorDerivativeRewrite`.

No substantive mathematical error, concealed regularity assumption, circular dependency, or unchecked proof was found in the nine requested modules. The final result is genuinely for every real C¹ function whose value and actual derivative are bounded. It allows sign changes, zeros, and the identically zero function. It is not restricted to polynomials, compact support, C∞ functions, or normalized densities.

This verdict does **not** certify M5–M6, replacement of the original Bakry–Émery axiom, a general curvature-dimension theorem, or optimality of the constant. The development proves the inequality with coefficient 2 for the standard variance-one Gaussian measure.

## 1. Evidence and audit boundary

I read the definitions and proof bodies of all nine modules, inspected relevant local and Mathlib dependencies, and checked the statements after elaboration. `MATHEMATICAL_AUDIT.md` was not used as evidence. The replacement plan was consulted to identify intended scope and M5, not to establish correctness of proofs.

HEAD equals the requested commit. There were initially no tracked modifications. Three existing untracked documents were preserved: `BAKRY_EMERY_REPLACEMENT_PLAN.md`, `INDEPENDENT_GRAPH_CORE_AUDIT.md`, and `M3_ENTROPY_DISSIPATION_STRATEGY.md`.

| Module in `Foundation/` | Top-level declarations checked | Responsibility |
|---|---:|---|
| `GaussianEntropy.lean` | 8 | Integrability, Jensen, zero convention |
| `GaussianMehler.lean` | 18 | Kernel, Gaussian laws, invariance, composition, ergodicity |
| `GaussianFisherDecay.lean` | 10 | Actual spatial derivative, weighted Cauchy–Schwarz, Fisher decay |
| `GaussianEntropyDissipation.lean` | 15 | Entropy definition, finiteness and endpoint limits |
| `GaussianSteinBounded.lean` | 7 | Boundary estimates and bounded C¹ Stein identity |
| `GaussianRotationStein.lean` | 5 | Rotation, product integrability, rotated Stein |
| `GaussianMehlerTimeDerivative.lean` | 13 | Positive-time differentiation |
| `GaussianEntropyDissipationProof.lean` | 18 | Outer differentiation, Fubini, negative Fisher identity |
| `GaussianLogSobolevCore.lean` | 7 | Entropy/Fisher inequality and regularization limit |
| **Total** | **101** | Includes definitions and measure abbreviations |

The full build passed: **3380 jobs**, exit status 0. There were two pre-existing unused-section-variable warnings in `Foundation/Adjoint.lean:24` and `:30`; neither is a mathematical assumption problem for these results.

Environment: Lean `v4.34.1`, Mathlib revision `d13f23b723b8a846827a245b89c10fc7d3f11612`. No pin was changed. Commands, from the repository:

```powershell
& 'C:\Users\ramir\.elan\toolchains\leanprover--lean4---v4.34.1\bin\lake.exe' build
& 'C:\Users\ramir\.elan\toolchains\leanprover--lean4---v4.34.1\bin\lake.exe' env lean Foundation/AxiomAudit.lean
& 'C:\Users\ramir\.elan\toolchains\leanprover--lean4---v4.34.1\bin\lake.exe' env lean .lake/build/independent-gaussian-lsi-probe.lean
```

Audit-only artifacts were placed in ignored `.lake/build/`; existing Lean sources were not edited:

- [Full build log](C:/OperatorDerivativeRewrite/.lake/build/independent-gaussian-lsi-build.log).
- [Independent Lean probe](C:/OperatorDerivativeRewrite/.lake/build/independent-gaussian-lsi-probe.lean): `#check @...` and `#print axioms` for all 101 declarations, plus expanded bounded-C¹ and zero-function checks.
- [Elaborated statements and direct axiom output](C:/OperatorDerivativeRewrite/.lake/build/independent-gaussian-lsi-probe.log).
- [Complete declaration/location inventory](C:/OperatorDerivativeRewrite/.lake/build/independent-gaussian-lsi-declarations.txt).
- [Repository transitive axiom audit](C:/OperatorDerivativeRewrite/.lake/build/independent-gaussian-lsi-transitive-axioms.log).

These are local verification artifacts, not new library modules. The build was a complete project build invocation, not a claim of rebuilding every cached dependency from scratch.

## 2. Exact definitions and principal theorem statements

Every Gaussian abbreviation resolves to `GaussianCore.γ = ProbabilityTheory.gaussianReal 0 1`, defined at [GaussianCore.lean:18](C:/OperatorDerivativeRewrite/Foundation/GaussianCore.lean:18). In the following display γ denotes that fixed measure:

```lean
entropySq μ f =
  (∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂μ) -
  (∫ x, f x ^ 2 ∂μ) * Real.log (∫ x, f x ^ 2 ∂μ)

GaussianEntropyDissipation.entropyDensity g =
  (∫ x, g x * Real.log (g x) ∂γ) -
  (∫ x, g x ∂γ) * Real.log (∫ x, g x ∂γ)

GaussianFisher.fisherInformation g = ∫ x, (deriv g x) ^ 2 / g x ∂γ

GaussianMehler.mehler t f x =
  ∫ y, f (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * y) ∂γ
```

The entropy includes the mass-centering term. No normalization ∫g=1 is assumed. These are real-valued definitions using totalized integrals; mathematical finiteness comes from the separate proofs below.

The following principal statements retain every mathematical hypothesis. Names are under `OperatorDerivativeRewrite.Foundation`, with subnamespaces shown. There are no additional section-variable hypotheses on the Gaussian statements. The full elaborated output, including universe parameters, is in the probe log.

### M1

At [GaussianEntropy.lean:42](C:/OperatorDerivativeRewrite/Foundation/GaussianEntropy.lean:42):

```lean
integrable_sq_mul_log_of_memLp_four
  {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}
  [IsFiniteMeasure μ] {f : Ω → ℝ} (hf : MemLp f 4 μ) :
  Integrable (fun x => f x ^ 2 * Real.log (f x ^ 2)) μ
```

At line 62, `entropySq_nonneg_of_memLp_four` has the same function hypothesis and an `IsProbabilityMeasure μ` instance and concludes `0 ≤ entropySq μ f`. At line 97, `GaussianCore.polynomial_sq_mul_log_integrable (p : ℝ[X])` proves the displayed integrability for `p.eval` under γ, using proved polynomial Lp membership.

### M2

At [GaussianFisherDecay.lean:51](C:/OperatorDerivativeRewrite/Foundation/GaussianFisherDecay.lean:51):

```lean
GaussianFisher.hasDerivAt_mehler_C1 (t : ℝ) {f : ℝ → ℝ}
  (hf_C1 : ContDiff ℝ 1 f) {M : ℝ}
  (hf_bd : ∀ x, ‖f x‖ ≤ M) (hf'_bd : ∀ x, ‖deriv f x‖ ≤ M)
  (x₀ : ℝ) :
  HasDerivAt (GaussianMehler.mehler t f)
    (Real.exp (-t) * GaussianMehler.mehler t (deriv f) x₀) x₀
```

This spatial derivative is valid for every real t for the defined kernel. Gaussian invariance and the following decay theorem restrict t to nonnegative times.

At [GaussianFisherDecay.lean:369](C:/OperatorDerivativeRewrite/Foundation/GaussianFisherDecay.lean:369):

```lean
GaussianFisher.fisherInformation_decay
  (g : ℝ → ℝ) (hg : ContDiff ℝ 1 g)
  {ε M : ℝ} (hε : 0 < ε)
  (hg_lo : ∀ x, ε ≤ g x) (hg_hi : ∀ x, g x ≤ M)
  (hg'_bd : ∀ x, |deriv g x| ≤ M) (t : ℝ) (ht : 0 ≤ t) :
  GaussianFisher.fisherInformation (GaussianMehler.mehler t g) ≤
    Real.exp (-2 * t) * GaussianFisher.fisherInformation g
```

### M3

At [GaussianMehlerTimeDerivative.lean:126](C:/OperatorDerivativeRewrite/Foundation/GaussianMehlerTimeDerivative.lean:126), with its definitions `a t = exp(-t)` and `b t = sqrt(1-exp(-2*t))`:

```lean
GaussianMehlerTimeDerivative.hasDerivAt_mehler_time
  (t : ℝ) (ht : 0 < t) (x : ℝ) {g : ℝ → ℝ}
  (hg : ContDiff ℝ 1 g) {M B : ℝ}
  (hgb : ∀ z, ‖g z‖ ≤ M) (hdgb : ∀ z, ‖deriv g z‖ ≤ B) :
  Integrable (fun y => deriv g (a t * x + b t * y) *
    (-a t * x + (a t ^ 2 / b t) * y)) γ ∧
  HasDerivAt (fun s => GaussianMehler.mehler s g x)
    (∫ y, deriv g (a t * x + b t * y) *
      (-a t * x + (a t ^ 2 / b t) * y) ∂γ) t
```

At [GaussianEntropyDissipationProof.lean:453](C:/OperatorDerivativeRewrite/Foundation/GaussianEntropyDissipationProof.lean:453):

```lean
GaussianEntropyDissipationProof.hasDerivAt_entropy_dissipation
  (t : ℝ) (ht : 0 < t) {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
  {ε M B : ℝ} (hε : 0 < ε) (hlo : ∀ z, ε ≤ g z)
  (hhi : ∀ z, g z ≤ M) (hdgb : ∀ z, ‖deriv g z‖ ≤ B) :
  HasDerivAt (GaussianEntropyDissipation.entropyTrajectory g)
    (-GaussianFisher.fisherInformation (GaussianMehler.mehler t g)) t
```

`deriv_entropy_dissipation` at line 464 follows from this actual `HasDerivAt` result. No C², LSI, Fisher-decay, or entropy-dissipation assumption appears in the M3 theorem. Fisher decay is used subsequently in M4, not assumed to justify M3.

### M4

At [GaussianLogSobolevCore.lean:21](C:/OperatorDerivativeRewrite/Foundation/GaussianLogSobolevCore.lean:21):

```lean
GaussianLogSobolevCore.entropyDensity_le_half_fisher
  (g : ℝ → ℝ) (hg : ContDiff ℝ 1 g)
  {ε M : ℝ} (hε : 0 < ε) (hlo : ∀ x, ε ≤ g x)
  (hhi : ∀ x, g x ≤ M) (hderiv : ∀ x, ‖deriv g x‖ ≤ M) :
  GaussianEntropyDissipation.entropyDensity g ≤
    (1 / 2 : ℝ) * GaussianFisher.fisherInformation g
```

At [GaussianLogSobolevCore.lean:198](C:/OperatorDerivativeRewrite/Foundation/GaussianLogSobolevCore.lean:198):

```lean
GaussianLogSobolevCore.gaussian_logSobolev_core
  {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) {M : ℝ}
  (hfb : ∀ x, ‖f x‖ ≤ M) (hfdb : ∀ x, ‖deriv f x‖ ≤ M) :
  entropySq γ f ≤ 2 * ∫ x, (deriv f x) ^ 2 ∂γ
```

`M ≥ 0` follows from the bound at any point. Separate finite bounds A and B can be combined using `max A B`.

To test the meaning independently of local names, the probe compiled the expanded inequality from ordinary `Differentiable ℝ f`, `Continuous (deriv f)`, and separate value/derivative bounds. It used Mathlib's `contDiff_one_iff_deriv` and wrote `gaussianReal 0 1` in every integral. Thus there is no weakened local definition masquerading as bounded C¹ regularity. The plan's proposed C∞/bounded-second-derivative core is a smaller class than the actual proved class.

## 3. Adversarial mathematical checks

### 3.1 Genuine entropy integrability

**Finding: pass.** [GaussianEntropy.lean:42–70](C:/OperatorDerivativeRewrite/Foundation/GaussianEntropy.lean:42) establishes integrability of f² and f⁴ from L⁴. It bounds the nonnegative `InformationTheory.klFun(f²)` by `1 + f⁴`, then reconstructs f² log(f²) from that integrable expression. Jensen receives both required integrability proofs. It is not applied to arbitrary totalized integrals.

For bounded inputs, [GaussianEntropyDissipation.lean:39–57](C:/OperatorDerivativeRewrite/Foundation/GaussianEntropyDissipation.lean:39) uses continuity of r log r on a compact interval to supply a constant integrable majorant, treating zero without dividing by the input. `core_sq_mul_log_integrable` at [GaussianLogSobolevCore.lean:189](C:/OperatorDerivativeRewrite/Foundation/GaussianLogSobolevCore.lean:189) additionally provides standalone M1-based finiteness for the final core. Integrability of the energy integrand follows from the bounded continuous actual derivative and is proved inside `regularized_fisher_le_energy` at lines 118–123.

**API qualification, not a gap:** the real definitions `entropySq`, `entropyDensity`, and `fisherInformation` should not be presented as extended-valued entropy/Fisher functionals without domain conditions. No false finiteness conclusion of that kind is used in the audited proof.

### 3.2 Mehler normalization, positivity, invariance and composition

**Finding: pass.** The kernel at [GaussianMehler.lean:23](C:/OperatorDerivativeRewrite/Foundation/GaussianMehler.lean:23) uses a=e⁻ᵗ and b=√(1−e⁻²ᵗ). For t≥0, a²+b²=1, explicitly proved in [GaussianMehlerTimeDerivative.lean:21](C:/OperatorDerivativeRewrite/Foundation/GaussianMehlerTimeDerivative.lean:21). At t=0, a=1 and b=0, giving P₀f=f.

The Mehler module proves, rather than assumes:

- `kernel_integrable` (40), `mehler_zero` (47), `mehler_const` (51), `mehler_mono` (55), `mehler_nonneg` (62), and `mehler_norm_le` (68).
- `gaussian_combination_map` (118), using the law of a linear combination of independent standard Gaussians; `kernel_map` (143) specializes the variance to one.
- `integral_mehler` (158), using genuine product integrability and Fubini, followed by the Gaussian pushforward law.
- `mehler_compose` (181), for s,t≥0, using correctly combined variances and justified double integrals.
- `mehler_continuous` (76) and `mehler_tendsto_mean` (91), using bounded domination and continuity.

The real definition exists also for t<0, but no negative-time Gaussian invariance, Markov group, or backward semigroup is inferred. Nonnegative-time restrictions are present where required.

### 3.3 Weighted Cauchy–Schwarz and denominators

**Finding: pass.** [GaussianFisherDecay.lean:32](C:/OperatorDerivativeRewrite/Foundation/GaussianFisherDecay.lean:32) proves integrability of (deriv g)²/g from measurability, ε>0, ε≤g, and a derivative bound, with majorant M²/ε. The lower bound for Pₜg is proved at line 117.

`weighted_cauchy_schwarz_mehler` (189) uses g′/√g and √g. Positivity justifies square-root and division identities. Squares and products of these factors are proved integrable before applying Cauchy–Schwarz. The helper theorem (128) also handles a zero second-factor norm by proving that factor zero almost everywhere; it does not divide by a possibly zero integral.

`fisherInformation_mehler_integrable` (326) proves finiteness of the evolved integrand. `fisherInformation_decay` (369) combines the actual derivative `(Pₜg)′=aPₜg′`, the pointwise weighted estimate `(Pₜg′)²/Pₜg≤Pₜ((g′)²/g)`, invariance for the bounded continuous Fisher integrand, and a²=e⁻²ᵗ. No component is a hypothesis equivalent to decay. The final signed f retains no positive lower bound.

### 3.4 Stein, rotation orientation, and avoidance of C²

**Finding: pass.** [GaussianSteinBounded.lean:81](C:/OperatorDerivativeRewrite/Foundation/GaussianSteinBounded.lean:81) proves, for `ContDiff ℝ 1 h`, |h|≤A, and |deriv h|≤B,

> ∫ h′ dγ = ∫ xh dγ.

Supporting results (22–70) prove Gaussian integrability, convert to weighted Lebesgue integrals, differentiate hρ with ρ′=−xρ, and prove boundary terms vanish. Boundary decay is derived using integrability of the weighted function and its derivative, not presumed merely from C¹ regularity.

[GaussianRotationStein.lean:20](C:/OperatorDerivativeRewrite/Foundation/GaussianRotationStein.lean:20) proves invariance of

> (X,Y) ↦ (Z,V) = (aX+bY, −bX+aY), with a²+b²=1.

It reuses Mathlib Gaussian rotation invariance and handles the sign of b in the angle representation. The inverse is X=aZ−bV, Y=bZ+aV.

`rotated_stein_identity` (135) assumes bounded measurable k and bounded C¹ ψ with bounded actual derivative and concludes exactly

> E[ψ(X)k(aX+bY)(−bX+aY)] = −b E[ψ′(X)k(aX+bY)].

After rotation, Stein differentiates ψ(aZ−bV) in V, producing **−b**. It never differentiates k. Applying this with k=g′ therefore requires no g″. `rotated_stein_integrable` (60) proves all four relevant product integrals using bounds and Gaussian first moments. This is why bounded C¹ inputs suffice.

### 3.5 Differentiation under both integrals

**Finding: pass.** [GaussianMehlerTimeDerivative.lean:30–126](C:/OperatorDerivativeRewrite/Foundation/GaussianMehlerTimeDerivative.lean:30) proves b(t)>0 for t>0, a′=−a, and b′=a²/b. For each t₀>0 it constructs a neighborhood contained in positive times where b(s)>c=b(t₀)/2>0. There,

> |g′(a(s)x+b(s)y)(−a(s)x+a(s)²y/b(s))| ≤ B(|x|+|y|/c).

For fixed x, this is integrable in y by the first absolute Gaussian moment. Measurability, integrability at the base parameter, and actual pointwise derivatives are supplied to Mathlib's differentiation-under-integral theorem. Integrability of the differentiated kernel is included in the resulting conclusion.

[GaussianEntropyDissipationProof.lean:23–169](C:/OperatorDerivativeRewrite/Foundation/GaussianEntropyDissipationProof.lean:23) proves u=Pₜg is C¹, ε≤u≤M and |u′|≤B for t≥0. For ψ=1+log u it proves C¹ regularity, ψ′=u′/u, and bounds

> |ψ|≤L=1+|log ε|+|log M|, and |ψ′|≤B/ε.

There is no assumption ε<1<M. Logarithmic differentiation always has a positive argument.

In `hasDerivAt_entropy_raw` (230), the common outer majorant on the positive-time neighborhood is

> LB(|x|+m₁/c), where m₁=∫|y|dγ(y).

It is integrable in x. The kernel derivative majorant is also integrable on γ×γ, being a sum of coordinate absolute values. The proof supplies parameter measurability and the actual derivative of u log u. It does not formally differentiate a possibly nonintegrable expression.

`hasDerivAt_entropyTrajectory_raw` (303) treats the centered mass term using invariance on a neighborhood of t>0, within the valid time range.

### 3.6 Fubini and the negative Fisher sign

**Finding: pass.** In [GaussianEntropyDissipationProof.lean:342](C:/OperatorDerivativeRewrite/Foundation/GaussianEntropyDissipationProof.lean:342), `entropy_pairing_eq_neg_fisher` obtains product integrability from the rotated Stein infrastructure. Fubini, including the local facts `hL` and `hR` around lines 407 and 413, uses those integrability proofs.

The calculation, with a,b evaluated at t, is

> −ax+a²y/b = (a/b)(−bx+ay),
>
> E[ψ(X)∂ₜu(X)] = (a/b)E[ψ(X)g′(aX+bY)(−bX+aY)]
> = −a E[ψ′(X)g′(aX+bY)] = −∫(u′)²/u dγ.

The last equality uses ψ′=u′/u and u′=aPₜg′. Cancellation of b uses b>0. The resulting Fisher integrand is separately integrable (`evolved_fisher_integrable`, 324). The `HasDerivAt` entropy result is assembled at line 453.

### 3.7 Time zero and infinity

**Finding: pass.** [GaussianEntropyDissipation.lean:103](C:/OperatorDerivativeRewrite/Foundation/GaussianEntropyDissipation.lean:103), `entropyTrajectory_continuous`, proves continuity by dominated convergence. Lines 128 and 133 identify the value and limit at t=0. No time derivative at zero is asserted or needed.

`entropyTrajectory_tendsto_atTop` (149) uses pointwise Mehler ergodicity and uniform bounds, then separately passes the mass integral and the r log r integral to their limits. Their centered difference is zero. The proof supplies the outer domination that pointwise convergence alone would not provide.

M4 applies the mean-value/monotonicity theorem on [0,∞), using differentiation only in its interior and continuity at its endpoint. These match the proved hypotheses.

### 3.8 Constant 2 and removal of ε, including f=0

**Finding: pass.** [GaussianLogSobolevCore.lean:21–80](C:/OperatorDerivativeRewrite/Foundation/GaussianLogSobolevCore.lean:21) sets

> H(t)=Entγ(Pₜg)−(1/2)e⁻²ᵗ I(g).

M3 and Fisher decay give H′(t)=−I(Pₜg)+e⁻²ᵗI(g)≥0 for t>0. Continuity and H(t)→0 imply H(0)≤0. This proves Entγ(g)≤I(g)/2 without needing a separate improper time-integration theorem. It does not use LSI circularly.

For gε=f²+ε, `regularized_deriv` (82) proves the actual derivative 2ff′. `regularized_fisher_le_energy` (88) proves both integrabilities and uses a positive denominator to derive

> I(f²+ε)=∫4f²(f′)²/(f²+ε)dγ ≤ 4∫(f′)²dγ.

Thus 2=(1/2)×4, matching variance one and a=e⁻ᵗ. There is no factor lost through entropy centering or a different Gaussian variance. Optimality of 2 is not separately proved.

`regularized_entropy_tendsto` (139) uses εₙ=1/(n+1), the uniform bound f²+εₙ≤M²+1, and separate dominated-convergence arguments for mass and r log r. `Real.continuous_mul_log` applies at zero. No uniform positive lower bound is sought as εₙ→0.

In the final proof (198), K=3M²+1 bounds each regularized function and its derivative, so the positive-density inequality applies. The limit permits all zeros of f. The probe also compiled `entropySq γ (fun _ => 0)=0` and the complete zero-function inequality. No division by ∫f² occurs, so zero mass causes no exception.

## 4. Hidden hypotheses, totalization, and proof trust

No custom core predicate hides the conclusion. `ContDiff ℝ 1` and `deriv` are Mathlib definitions. An independently supplied derivative is never substituted for the actual derivative without proof. The dependency order is acyclic: Gaussian/Stein analysis establishes M3; M3 and independently proved Fisher decay establish the positive-density M4 result; regularization gives the final theorem.

Two auxiliary APIs need precise interpretation:

- `GaussianMehler.mehler_norm_le` ([line 68](C:/OperatorDerivativeRewrite/Foundation/GaussianMehler.lean:68)) bounds a totalized integral without requiring measurability. It is valid but alone is not an integrability certificate. `kernel_integrable` and continuity/C¹ supply that certificate in the main proofs.
- `GaussianEntropyDissipationProof.timeVelocity_local_bound` ([line 177](C:/OperatorDerivativeRewrite/Foundation/GaussianEntropyDissipationProof.lean:177)) likewise supplies a bound under weaker hypotheses than the differentiation theorem. Actual differentiation and Fubini separately establish integrability; the bound is not substituted for those obligations.

The source scan found no `sorry`, `admit`, custom `axiom` declaration, `unsafe`, `native_decide`, or `implemented_by` shortcut in the nine modules. Some files set `backward.isDefEq.respectTransparency false`; this affects elaboration, not kernel proof checking.

The repository's `Foundation/AxiomAudit.lean` completed with **815 axiom reports**. The exhaustive independent probe for these modules completed with **101 reports**. These sets overlap; they are not 916 distinct theorems. Every reported axiom was in the explicit whitelist:

```text
propext
Classical.choice
Quot.sound
```

Both logs had zero `sorryAx` and zero Lean errors. `#print axioms` follows dependencies transitively, excluding custom mathematical axioms from the dependency chains of these declarations, including any accidentally imported legacy axiom. This does not purport to audit every unrelated Mathlib declaration. No source change is needed to make the existing M1–M4 statements honest.

## 5. M5: feasibility and actual Mathlib reuse

### 5.1 The remaining mathematical task

The plan's M5, which is not established by the present core theorem, is:

> If f has actual derivative h at every real x and f,h∈L²(γ), construct smooth compactly supported fₙ with fₙ→f and deriv fₙ→h in L²(γ).

This is mathematically valid. It requires substantial formal analysis, not a new conjecture. The derivative need not be continuous or bounded. The old axiom at [OperatorDerivative.lean:2354](C:/Operator/OperatorDerivative.lean:2354) supplies an everywhere `HasDerivAt` hypothesis and integrability of the two squares, not C¹ regularity or graph approximation.

Two bridges must be proved:

1. On each compact interval the positive continuous Gaussian density has a positive minimum. Gaussian L² therefore implies local Lebesgue L² and L¹. Everywhere differentiability plus this local integrability allows the existing interval FTC to identify differences of f with integrals of h. Local absolute continuity need not be assumed.
2. Approximation must control **both** the function and its actual derivative. Ambient L² density, including Hermite density, does not by itself prove this for a class not yet identified with the operator graph domain.

If the derivative hypothesis were weakened to an a.e. classical derivative, an additional local absolute-continuity or weak-derivative condition would be necessary: a Cantor-type singular function shows why an a.e. classical derivative alone is insufficient. This is not a defect in the actual everywhere hypothesis.

M1's L⁴ theorem does not provide full-domain entropy finiteness under M5's L² hypotheses. M6 must use the core LSI and a nonnegative entropy-integrand/Fatou argument to prove finiteness at the limit before manipulating real entropy integrals.

### 5.2 Reusable pinned Mathlib declarations

These declarations were checked in the pinned local sources. Links point to that same revision. Current public API documentation was used only as corroboration.

| File/declaration | Supplies | Does not supply |
|---|---|---|
| [Analysis/Normed/Lp/SmoothApprox.lean:87](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/Analysis/Normed/Lp/SmoothApprox.lean#L87), `MeasureTheory.MemLp.exist_eLpNorm_sub_le`; line 102, `MeasureTheory.Lp.dense_hasCompactSupport_contDiff` | Smooth compact-support approximation for finite p≥1 and a measure finite on compact sets, including Gaussian ambient L² | Derivative convergence or weighted graph density |
| [LpSeminorm/Basic.lean:790](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/MeasureTheory/Function/LpSeminorm/Basic.lean#L790), `eLpNorm_le_of_measure_le_smul`; line 795, `MemLp.of_measure_le_smul` | Lp transfer under a proved measure domination | The compact Gaussian density comparison itself |
| [FundThmCalculus.lean:1148](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean#L1148), `intervalIntegral.integral_eq_sub_of_hasDerivAt`; line 1176, `integral_deriv_eq_sub` | FTC with actual derivatives and interval integrability | Local Lebesgue integrability from Gaussian integrability |
| [FDeriv/Measurable.lean:400](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/Analysis/Calculus/FDeriv/Measurable.lean#L400), `measurable_deriv` | Actual derivative measurability; an everywhere derivative candidate equals it | Continuity or boundedness of the derivative |
| [ContDiff/Convolution.lean](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/Analysis/Calculus/ContDiff/Convolution.lean), `HasCompactSupport.hasDerivAt_convolution_right`, `HasCompactSupport.contDiff_convolution_right` | Regularity with a suitable smooth compact operand and additive invariant measure | Direct Gaussian convolution calculus: γ is not translation invariant. Differentiating the kernel alone also does not identify convolution of h |
| [BumpFunction/Convolution.lean](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean), `ContDiffBump.convolution_tendsto_right_of_continuous`, `ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable` | Pointwise and a.e. approximate-identity convergence | Automatic weighted L² convergence of functions and derivatives |
| [Analysis/Distribution/Sobolev.lean](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/Analysis/Distribution/Sobolev.lean) | Fourier/Bessel-potential Sobolev infrastructure | A ready-made identification of this Gaussian weighted derivative domain and its smooth compact-support core |

No directly matching Gaussian weighted Sobolev graph-approximation theorem was found in the inspected pinned Mathlib files and searches. This is a bounded search finding, not a claim of global absence from public Lean libraries. Reuse ambient smooth approximation; the evidence does not justify a new general Sobolev or semigroup dependency.

### 5.3 A potentially shorter one-dimensional route

After the local FTC bridge, cutoff-and-mollification is sound. In one dimension there is also a way to reuse existing **ambient** smooth L² density without first building a general convolution/Sobolev theorem. The following is a proposed architecture, not an already verified Lean result:

1. Take a smooth cutoff χ equal to one on [−1,1], supported in [−2,2], with 0≤χ≤1 and bounded derivative. Put f_R(x)=χ(x/R)f(x). Its actual derivative is p_R=χ(x/R)h(x)+(1/R)χ′(x/R)f(x). Tail convergence handles the first terms; the extra derivative term has L² norm at most C/R times ‖f‖₂. Thus the cutoffs converge in both required norms.
2. On a fixed compact interval containing the support, transfer f_R and p_R to unweighted L². Local FTC gives ∫p_R dx=0 and recovers f_R as a primitive of p_R.
3. Apply `MemLp.exist_eLpNorm_sub_le` under Lebesgue measure to approximate p_R by smooth functions. Multiply them by a fixed smooth cutoff equal to one on the support of p_R, to put all supports in a fixed larger compact interval K. A cutoff valued in [0,1] does not enlarge this L² error.
4. Correct the small integral error: choose a fixed smooth bump q supported in K with ∫q=1 and replace each approximant v by w=v−(∫v)q. Since ∫p_R=0 and supports lie in K, Cauchy–Schwarz gives |∫v|≤|K|^(1/2)‖v−p_R‖₂. The corrected approximants still converge in L² and have zero integral.
5. Define actual primitives F(x)=∫_a^x w, with a left of K. FTC proves `deriv F=w`; smoothness follows from smoothness of w, and zero integral gives compact support. On K, |F−f_R|≤|K|^(1/2)‖w−p_R‖₂; outside K both vanish. This controls function error as well as derivative error. Transfer to Gaussian L² and diagonalize in R and the approximation index.

These derivatives are proved derivatives of actual primitives, not independently prescribed values. The argument uses one-dimensional FTC and is not a substitute for a multidimensional weighted Sobolev theorem. Compare its Lean cost with convolution after establishing the local bridge.

## 6. Smallest safe next Sol Medium milestone

**Implement only `Foundation/GaussianLocalSobolev.lean`: a local-integrability/FTC bridge.** Do not combine it with the full approximation theorem or full-domain LSI.

Proposed names and statements, not existing declarations:

1. `memLp_two_volume_restrict_Icc_of_memLp_gaussian`: for all a,b∈ℝ, h∈L²(γ) implies h∈L²(volume restricted to Icc a b). Prove a finite measure-comparison constant from the positive minimum of the Gaussian density on a nonempty compact interval; handle an empty interval separately. Include the quantitative L² bound if it follows directly from that comparison.
2. `intervalIntegrable_derivative_of_gaussian_sq_integrable`: from `∀ x, HasDerivAt f (h x) x` and `Integrable (fun x => (h x)^2) γ`, prove `IntervalIntegrable h volume a b` for every a,b. Derive h=deriv f and measurability, rather than assuming new analytic hypotheses.
3. `integral_derivative_eq_sub_of_gaussian_sq_integrable`: under exactly the same assumptions prove `∫ x in a..b, h x = f b - f a` using the existing interval FTC. This does not need f∈L²(γ); do not require C¹ or assumed absolute continuity.

**Acceptance:** only actual everywhere differentiation and Gaussian square integrability are inputs. No assumed Lebesgue integrability, entropy finiteness, approximation, or operator-domain membership. Compile and audit the new declarations, then stop for review. A subsequent milestone can prove quantitative smooth-cutoff graph approximation; smoothing/primitive approximation and diagonalization follow separately.

The first bridge is low mathematical difficulty and moderate Lean work (restricted measures, `withDensity`, measurability and Lp conversion). Full M5 is standard mathematics but potentially substantial implementation. M6 still needs its independent nonnegative-Fatou entropy-limit and integrability argument. Neither is discharged by this audit.

## 7. Preservation and disposition

Only this requested Markdown report and ignored audit artifacts were created. Existing Lean sources, manuscripts, pins, and uncommitted documents were preserved. No commit was made.

Original-source SHA-256 values checked at the end:

```text
C:\Operator\OperatorDerivative.lean
9B8BA956878B80F3C2AC8F239D335C0F49582C88D0693E63554F481ACBEBDF29

C:\Operator\OperatorDerivative.tex
FCA841CCA43DC712AAD2FCF02CB04010ABD7CFCDA4A231022D58A3B23D3BB983
```

**Recommendation:** accept the M1–M4 bounded-C¹ Gaussian result and proceed with the focused M5 local-integrability/FTC bridge. Keep the core label until weighted graph approximation and the entropy-limit extension are actually proved.
