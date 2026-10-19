# Independent full Gaussian log-Sobolev audit: M5–M6

**Verdict: PASS WITH QUALIFICATIONS.** The M5 approximation theorem and M6 one-dimensional Gaussian log-Sobolev theorem pass mathematical and Lean dependency review. No missing hypothesis or circular argument was found in these proofs. A proved adapter with the exact legacy axiom signature is available and was checked in temporary files. The qualifications concern the untouched legacy development and the scope of the result: that legacy file currently fails compilation elsewhere, and neither this result nor its adapter proves an abstract Bakry–Émery curvature criterion.

Audited on 2026-10-11 at repository HEAD **`b305edc62a8b6ba1290ba178b9886628a2c49add`**, with Lean **4.34.1** and locked Mathlib revision **`d13f23b723b8a846827a245b89c10fc7d3f11612`**. The initial tracked working tree was clean. Existing untracked planning/audit documents were preserved. No Lean source, original manuscript, dependency pin, or Git commit was changed by this audit.

## 1. Evidence and verification

This assessment is based on the actual definitions and proof bodies, elaborated declaration types, relevant Mathlib proof bodies, and fresh Lean runs. `MATHEMATICAL_AUDIT.md` was not used as proof evidence. All supporting M5 modules were inspected, including the local FTC bridge, cutoffs, controlled-support density, zero-integral correction, primitives, quantitative estimates, and global choice of approximants.

| Check | Result |
|---|---|
| Full pinned `lake build` | PASS: 3445 jobs; existing unused-section-variable warnings in `Foundation/Adjoint.lean:24,30` |
| Fresh `lake env lean Foundation/GaussianSobolevGlobalApprox.lean` | PASS |
| Fresh `lake env lean Foundation/GaussianLogSobolevFull.lean` | PASS |
| `lake env lean Foundation/AxiomAudit.lean` | PASS: 878 axiom reports; the only reported axioms are `propext`, `Classical.choice`, `Quot.sound` |
| Independent transitive enumeration of M5–M6 declarations | PASS: 104 matching declarations, including private/generated declarations; no axiom outside that whitelist |
| Import environment of `Foundation.GaussianLogSobolevFull` | Original `bakry_emery_log_sobolev` declaration is absent |
| Exact legacy-type adapter | PASS: Lean `Meta.isDefEq` confirms equality of elaborated types |
| Temporary original-prefix replacement under the original theorem name | PASS; both replacement and unchanged `log_sobolev_1d` have only the three standard axioms |
| Untouched complete `C:\Operator\OperatorDerivative.lean` under the pinned environment | FAIL: seven existing error locations, listed in section 8 |

The final M5 theorem and both public M6 theorems each have exactly these transitive axioms:

```text
[propext, Classical.choice, Quot.sound]
```

These are standard Lean logical/classical foundations, not unproved mathematical assumptions about Sobolev approximation or entropy. No `sorryAx`, custom analytic axiom, native proof shortcut, or circular dependency was found. A source scan of `Foundation` also found no executable `sorry`, `admit`, custom `axiom`, `native_decide`, `unsafe`, or `implemented_by` proof shortcut. The standard audit is complemented by independent `Lean.collectAxioms` calls; the conclusion does not rely on text searches alone.

Reproduction uses the pinned executable, bypassing the default elan shim:

```powershell
$lake = 'C:\Users\ramir\.elan\toolchains\leanprover--lean4---v4.34.1\bin\lake.exe'
Set-Location C:\OperatorDerivativeRewrite
& $lake build
& $lake env lean Foundation/GaussianSobolevGlobalApprox.lean
& $lake env lean Foundation/GaussianLogSobolevFull.lean
& $lake env lean Foundation/AxiomAudit.lean
```

Supplementary probes and logs are in [the temporary audit directory](C:/Users/ramir/AppData/Local/Temp/operator-lsi-audit-b305edc). `NewTheorems.lean` prints explicit types, enumerates the imported project modules, rejects the presence of the legacy axiom, and audits all declarations whose names contain `GaussianLocalSobolev`, `GaussianSobolev`, or `GaussianLogSobolevFull`. `LegacyAdapter.lean` checks the exact old signature; `ReplacementPrefix.lean` tests the same-name replacement in a temporary copy of the original prefix through the log-Sobolev section. The original files were never edited.

## 2. Exact public statements and absence of hidden hypotheses

All new names below are under `OperatorDerivativeRewrite.Foundation`. `GaussianCore.γ` is definitionally `ProbabilityTheory.gaussianReal 0 1`: [GaussianCore.lean:18](C:/OperatorDerivativeRewrite/Foundation/GaussianCore.lean:18). This is the real Gaussian with mean zero and variance one, not a variable measure or a rescaled Gaussian.

The elaborated M5 declaration, with ordinary concrete real instances suppressed, is:

```lean
GaussianSobolevGlobalApprox.exists_smooth_compact_graph_sequence
  {f h : ℝ → ℝ}
  (hd : ∀ x, HasDerivAt f (h x) x)
  (hf_sq : Integrable (fun x => f x ^ 2) GaussianCore.γ)
  (hh_sq : Integrable (fun x => h x ^ 2) GaussianCore.γ) :
  ∃ F : ℕ → ℝ → ℝ,
    (∀ n, ContDiff ℝ ∞ (F n)) ∧
    (∀ n, HasCompactSupport (F n)) ∧
    Tendsto (fun n => ∫ x, (F n x - f x) ^ 2 ∂GaussianCore.γ)
      atTop (𝓝 0) ∧
    Tendsto (fun n => ∫ x, (deriv (F n) x - h x) ^ 2 ∂GaussianCore.γ)
      atTop (𝓝 0)
```

Source: [GaussianSobolevGlobalApprox.lean:66](C:/OperatorDerivativeRewrite/Foundation/GaussianSobolevGlobalApprox.lean:66). There are exactly the three displayed hypotheses. In particular there is no positivity, boundedness, continuous-derivative, entropy-integrability, absolute-continuity, or graph-density assumption. `ContDiff ℝ ∞` describes the approximants, not the original function.

The elaborated M6 declaration is:

```lean
GaussianLogSobolevFull.gaussian_logSobolev_of_hasDerivAt
  {f h : ℝ → ℝ}
  (hd : ∀ x, HasDerivAt f (h x) x)
  (hf_sq : Integrable (fun x => f x ^ 2) GaussianCore.γ)
  (hh_sq : Integrable (fun x => h x ^ 2) GaussianCore.γ) :
  Integrable (fun x => f x ^ 2 * Real.log (f x ^ 2)) GaussianCore.γ ∧
    entropySq GaussianCore.γ f ≤ 2 * ∫ x, h x ^ 2 ∂GaussianCore.γ
```

Source: [GaussianLogSobolevFull.lean:231](C:/OperatorDerivativeRewrite/Foundation/GaussianLogSobolevFull.lean:231). `entropySq` is the centered entropy

\[
\operatorname{Ent}_\gamma(f^2)
=\int f^2\log(f^2)\,d\gamma
 -\left(\int f^2\,d\gamma\right)\log\left(\int f^2\,d\gamma\right).
\]

Its actual definition is at [GaussianEntropy.lean:27](C:/OperatorDerivativeRewrite/Foundation/GaussianEntropy.lean:27). The conclusion is genuine absolute integrability plus the inequality, not just an inequality between totalized real integrals.

The public compatibility theorem [GaussianLogSobolevFull.lean:267](C:/OperatorDerivativeRewrite/Foundation/GaussianLogSobolevFull.lean:267), `gaussian_logSobolev_of_hasDerivAt_pos`, makes `f h` explicit, inserts `(∀ x, 0 < f x)` after `hd`, and returns the inequality alone. Positivity is unused because the stronger theorem already permits zeros and sign changes.

`#check @...` with `pp.explicit true` confirms no additional abstract measure, probability-space, operator, or regularity binder. `HasDerivAt` uses the ordinary real structures. The supplied `h` cannot be freely prescribed: [GaussianLocalSobolev.derivative_eq_deriv:90](C:/OperatorDerivativeRewrite/Foundation/GaussianLocalSobolev.lean:90) proves `h = deriv f` from `hd`.

## 3. M5 mathematical dependency audit

| Stage | Actual declaration and source | Adversarial check |
|---|---|---|
| Local measure comparison | `GaussianLocalSobolev.exists_local_measure_comparison`, [line 39](C:/OperatorDerivativeRewrite/Foundation/GaussianLocalSobolev.lean:39) | Obtains a strictly positive lower bound for the continuous Gaussian density on `Icc a b`; constructs a finite comparison constant. Empty intervals are included. |
| Local L² and FTC | `memLp_two_volume_restrict_Icc_of_memLp_gaussian`, [line 83](C:/OperatorDerivativeRewrite/Foundation/GaussianLocalSobolev.lean:83); `intervalIntegrable_derivative_of_gaussian_sq_integrable`, [line 96](C:/OperatorDerivativeRewrite/Foundation/GaussianLocalSobolev.lean:96); `integral_derivative_eq_sub_of_gaussian_sq_integrable`, [line 111](C:/OperatorDerivativeRewrite/Foundation/GaussianLocalSobolev.lean:111) | Measurability follows from `h = deriv f` and `measurable_deriv`. Local L² implies local L¹ on a finite interval. The actual interval FTC is applied, with no assumed C¹ or local absolute continuity. Unordered intervals handle reversed endpoints. |
| Cutoff graph convergence | `GaussianSobolevCutoffs.hasDerivAt_truncated`, [line 51](C:/OperatorDerivativeRewrite/Foundation/GaussianSobolevCutoffs.lean:51); `cutoff_derivative_bound`, [line 63](C:/OperatorDerivativeRewrite/Foundation/GaussianSobolevCutoffs.lean:63); `simultaneous_sq_error_tendsto`, [line 135](C:/OperatorDerivativeRewrite/Foundation/GaussianSobolevCutoffs.lean:135) | The cutoff is an actual smooth bump at scale `n+1`, with values in `[0,1]`. Its derivative is bounded by `C/(n+1)`. Actual product differentiation gives `χ h + χ' f`. Dominated convergence controls both errors, including the extra derivative term. |
| Compact derivative and zero integral | `GaussianSobolevSmoothApprox.compact_derivative_memLp_volume`, [line 20](C:/OperatorDerivativeRewrite/Foundation/GaussianSobolevSmoothApprox.lean:20); `compact_derivative_integral_zero`, [line 60](C:/OperatorDerivativeRewrite/Foundation/GaussianSobolevSmoothApprox.lean:60); `compact_primitive_representation`, [line 98](C:/OperatorDerivativeRewrite/Foundation/GaussianSobolevSmoothApprox.lean:98) | Transfers to Lebesgue L² using actual compact support, obtains L¹, and proves zero total derivative integral from FTC and vanishing boundary values. This is not imposed on an arbitrary approximating derivative. |
| Controlled smooth density | `GaussianSobolevFixedSupport.exists_fixed_support_smooth_approx`, [line 13](C:/OperatorDerivativeRewrite/Foundation/GaussianSobolevFixedSupport.lean:13) | Uses Mathlib ambient smooth L² density, then multiplies by a bump equal to one on the original support. All approximants remain in the fixed enlarged interval. Ambient density is not misidentified as graph density. |
| Unit bump and correction | `exists_unit_integral_bump`, [line 69](C:/OperatorDerivativeRewrite/Foundation/GaussianSobolevFixedSupport.lean:69); `corrected_properties`, [line 90](C:/OperatorDerivativeRewrite/Foundation/GaussianSobolevFixedSupport.lean:90) | The bump is constructed using `ContDiffBump.normed` and its proved integral. For `w = v - (∫v)q`, smoothness, support, actual integrability and `∫w = 0` are proved. |
| Actual smooth primitive | `primitive_hasDerivAt`, [line 44](C:/OperatorDerivativeRewrite/Foundation/GaussianSobolevPrimitives.lean:44); `corrected_primitive_properties`, [line 103](C:/OperatorDerivativeRewrite/Foundation/GaussianSobolevPrimitives.lean:103) | Defines `F(x)=∫a..x w`, proves its actual derivative is `w` and proves C∞ regularity. Support on the right uses the established zero integral; support on the left uses vanishing of `w`. |
| Quantitative graph estimates | `integral_v_bound`, [line 70](C:/OperatorDerivativeRewrite/Foundation/GaussianSobolevQuantitative.lean:70); `correction_error`, [line 117](C:/OperatorDerivativeRewrite/Foundation/GaussianSobolevQuantitative.lean:117); `fixed_support_graph_error`, [line 323](C:/OperatorDerivativeRewrite/Foundation/GaussianSobolevQuantitative.lean:323) | Finite-interval Cauchy–Schwarz controls the correction and primitive errors. All relevant square integrals are genuinely finite. The Gaussian comparison is used in the correct direction. |
| Fixed-support existence | `fixed_support_smooth_graph_approx`, [line 381](C:/OperatorDerivativeRewrite/Foundation/GaussianSobolevQuantitative.lean:381) | Produces one smooth compactly supported function meeting both error tolerances. Assumptions are actual derivative, compact support of `f`, and Gaussian square integrability of `h`; no continuity of `h` is introduced. |
| Global diagonal choice | `GaussianSobolevGlobalApprox.cutoff_graph_witness`, [line 35](C:/OperatorDerivativeRewrite/Foundation/GaussianSobolevGlobalApprox.lean:35); public theorem, [line 66](C:/OperatorDerivativeRewrite/Foundation/GaussianSobolevGlobalApprox.lean:66) | The tolerance is `1/(n+1)`. A single `Classical.choose` sequence is defined at line 76. Both limits use that same sequence and actual derivatives. |

The quantitative argument uses, for `K=[A,B]`,

\[
|\!\int v|\le\sqrt{B-A}\,\|v-h\|_2,\qquad
\|w-h\|_2\le(1+\sqrt{B-A}\,\|q\|_2)\|v-h\|_2.
\]

It then bounds the Gaussian function error by `(B-A)‖w-h‖₂²` and the Gaussian derivative error by `‖w-h‖₂²`. The proof of [standard_gaussian_le_volume:202](C:/OperatorDerivativeRewrite/Foundation/GaussianSobolevQuantitative.lean:202) establishes the Gaussian-density upper bound used here. Local Gaussian-to-Lebesgue transfer uses a different, compact-interval comparison; these directions are not confused.

Although `L2Norm` is defined using a real integral at [Quantitative:41](C:/OperatorDerivativeRewrite/Foundation/GaussianSobolevQuantitative.lean:41), every relevant estimate assumes or proves `MemLp`. The equality with the genuine `eLpNorm` is proved at line 44. This prevents nonintegrable inputs from being assigned a misleading zero norm in this proof chain.

For the final sequence, all value and derivative differences are square integrable before invoking the squared triangle estimate. Both errors are bounded by `2/(n+1)` plus twice the corresponding cutoff error; both bounds tend to zero. There is no independent selection of a derivative sequence.

Relevant existing Mathlib infrastructure includes `MeasureTheory.MemLp.exist_eLpNorm_sub_le` in [SmoothApprox.lean:87](C:/OperatorDerivativeRewrite/.lake/packages/mathlib/Mathlib/Analysis/Normed/Lp/SmoothApprox.lean:87) and `intervalIntegral.integral_eq_sub_of_hasDerivAt` in [FundThmCalculus.lean:1148](C:/OperatorDerivativeRewrite/.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean:1148). Their hypotheses are supplied by earlier proved steps.

## 4. M6 entropy limit audit

The central limit proof is the private `GaussianLogSobolevFull.klFun_fatou_bound`, [line 125](C:/OperatorDerivativeRewrite/Foundation/GaussianLogSobolevFull.lean:125). Its approximation and energy-convergence hypotheses are discharged in the final theorem; they are not assumed by the public result.

1. **Mass and energy convergence are proved.** `lpNorm_sq_eq_integral_sq` (line 13), `lpNorm_sub_tendsto_zero` (line 26), and `integral_sq_tendsto_of_graph_error` (line 41) use `MemLp`, the reverse norm triangle inequality, and continuity of squaring. Thus `∫F_n² → ∫f²` and `∫(deriv F_n)² → ∫h²`. These are not inferred from pointwise convergence alone.
2. **The almost-everywhere subsequence is genuine.** Lines 139–150 first convert to extended L² norm convergence using `ofReal_lpNorm` with finite-norm hypotheses. Mathlib then gives convergence in measure and a strictly increasing subsequence converging almost everywhere. Strict increase supplies convergence of the subsequence indices to infinity, so the mass and energy limits survive restriction.
3. **The entropy integrand is nonnegative.** The proof uses `InformationTheory.klFun r = r*log r + 1-r` at nonnegative `r=f²`. Mathlib proves continuity and nonnegativity. In particular `klFun 0 = 1`; the zero convention is not incorrectly set to zero.
4. **Approximant entropy integrals are finite before use.** `smooth_compact_core_bound` (line 98) obtains boundedness of the smooth compact function and its actual derivative, proves integrability, and invokes the verified M4 theorem. It establishes
   `∫klFun(F_n²) ≤ 2∫(deriv F_n)² + klFun(∫F_n²)`.
5. **Fatou is applied in extended nonnegative integration.** Lines 165–200 apply `lintegral_enorm_le_liminf_of_tendsto` to the almost-everywhere limit. The right-hand bounds converge to the finite real number `L = 2∫h² + klFun(∫f²)`. This controls the extended integral of the limit by `ENNReal.ofReal L`.
6. **Integrability is a conclusion.** At lines 202–205, `integrable_of_tendsto` is applied only after proving the norm-integral liminf is finite. This proves `Integrable (klFun ∘ (f²))`. Real-integral identities for the limit are used only afterward.
7. **The real upper bound is not lost through truncation.** Lines 221–226 prove `0 ≤ L` before using `ENNReal.ofReal_le_ofReal_iff`. The proof does not extract a false real inequality from an `ofReal` inequality with a negative upper bound.
8. **Absolute entropy integrability is recovered before centering.** At lines 255–260, the identity `f² log(f²) = klFun(f²)-1+f²` combines the established `klFun` integrability, finite probability mass, and original square integrability. Only then does the proof use `klFun_integral_eq_entropySq` and cancel `klFun(∫f²)`.

The relevant Mathlib limit results are `TendstoInMeasure.exists_seq_tendsto_ae` in [ConvergenceInMeasure.lean:273](C:/OperatorDerivativeRewrite/.lake/packages/mathlib/Mathlib/MeasureTheory/Function/ConvergenceInMeasure.lean:273), and `lintegral_enorm_le_liminf_of_tendsto` / `integrable_of_tendsto` in [L1Space/Integrable.lean:1240](C:/OperatorDerivativeRewrite/.lake/packages/mathlib/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean:1240). These implement the substantive subsequence/Fatou argument, not an assumption that entropy is lower semicontinuous or integrable.

There is no claim that the entropy integrals themselves converge. Lower semicontinuity with a finite upper bound is what is proved and what the conclusion needs. The redundant intermediate `htop` at line 190 is harmless; the subsequently used finite-liminf proof independently supplies the required integrability premise.

**Zeros and constant 2.** No division by `f`, its square, or its mass occurs in the M6 limit argument. For `f=0`, the two `klFun(0)=1` normalization contributions cancel and entropy is zero. The M4 result used at [GaussianLogSobolevCore.lean:198](C:/OperatorDerivativeRewrite/Foundation/GaussianLogSobolevCore.lean:198) has constant 2: its proof combines `Ent(g) ≤ I(g)/2` with `I(f²+ε) ≤ 4∫(f')²`, then removes epsilon. M6 passes the actual energies to their limit without inflation, retaining exactly 2. The factors 2 in the M5 squared-error triangle inequality affect only errors tending to zero. No theorem proving optimality of the constant is established by this audit.

## 5. Exact legacy comparison and tested adapter

The actual legacy axiom is at [OperatorDerivative.lean:2354](C:/Operator/OperatorDerivative.lean:2354):

```lean
axiom bakry_emery_log_sobolev :
  ∀ (f f' : ℝ → ℝ),
    (∀ x, HasDerivAt f (f' x) x) →
    (∀ x, 0 < f x) →
    MeasureTheory.Integrable (fun x => (f x)^2)
      (ProbabilityTheory.gaussianReal 0 1) →
    MeasureTheory.Integrable (fun x => (f' x)^2)
      (ProbabilityTheory.gaussianReal 0 1) →
    gaussian_entropy (fun x => (f x)^2)
      (ProbabilityTheory.gaussianReal 0 1) ≤
    2 * gaussian_fisher f f' (ProbabilityTheory.gaussianReal 0 1)
```

The fully elaborated type was checked, rather than inferred from nearby section variables. It has **no** `Ω`, `P`, `IsProbabilityMeasure P`, abstract generator, curvature constant, or semigroup binder. All real typeclass arguments are concrete standard instances.

`gaussian_entropy`, [line 2284](C:/Operator/OperatorDerivative.lean:2284), is the same centered entropy applied to its argument. `gaussian_fisher`, [line 2291](C:/Operator/OperatorDerivative.lean:2291), is actually `∫(f')²`; its first argument is unused. Despite its misleading docstring, it is not `∫(f')²/f`. Therefore the new positivity corollary matches the **actual** legacy proposition exactly after unfolding these definitions and `GaussianCore.γ`.

The following body was checked against the unchanged original axiom type in a temporary file:

```lean
by
  intro f h hd hpos hf_sq hh_sq
  simpa only [gaussian_entropy, gaussian_fisher,
    OperatorDerivativeRewrite.Foundation.entropySq,
    OperatorDerivativeRewrite.Foundation.GaussianCore.γ] using
    (OperatorDerivativeRewrite.Foundation.GaussianLogSobolevFull.gaussian_logSobolev_of_hasDerivAt_pos
      f h hd hpos hf_sq hh_sq)
```

The probe retained the original declaration separately and compared the stored types using `Lean.Meta.isDefEq`: result **`EXACT_LEGACY_TYPE_MATCH`**. Its independent theorem had only the three standard axioms, even though the old axiom was present in that test environment. A second probe removed the axiom from the temporary prefix, installed this proof as a theorem named `bakry_emery_log_sobolev`, and compiled the unchanged immediate downstream `log_sobolev_1d` at [line 2366](C:/Operator/OperatorDerivative.lean:2366). Both then reported only the standard three axioms.

**Answer:** an exact-signature proved adapter can be supplied with no additional assumptions. The stronger entropy-integrability conclusion is available from the main M6 theorem even though the old signature does not expose it.

## 6. Dependency separation and circularity

The only project modules imported transitively by `Foundation.GaussianLogSobolevFull` are:

```text
Adjoint, LpProducts, GaussianCore, GaussianLocalSobolev,
GaussianSobolevCutoffs, GaussianSobolevSmoothApprox,
GaussianSobolevFixedSupport, GaussianSobolevPrimitives,
GaussianSobolevQuantitative, GaussianSobolevGlobalApprox,
GaussianMehler, GaussianMehlerTimeDerivative, GaussianFisherDecay,
GaussianEntropy, GaussianEntropyDissipation, GaussianSteinBounded,
GaussianRotationStein, GaussianEntropyDissipationProof,
GaussianLogSobolevCore, GaussianLogSobolevFull
```

All are under `Foundation`. The original monolithic source is absent. The independent environment check explicitly rejects the presence of `bakry_emery_log_sobolev`; it passed.

The substantive dependency direction is local Gaussian/Lebesgue comparison → cutoffs and FTC → corrected smooth primitives → global graph approximation, combined with the independently proved bounded-C¹ M4 inequality → Fatou extension. M5 does not assume entropy integrability or log-Sobolev. M6 does not assume graph density; it invokes the M5 proof. Helper lemmas with approximation hypotheses are instantiated with its actual witnesses. Neither final theorem concludes `True` or encodes its desired conclusion as a structure field.

## 7. Legacy and manuscript qualifications

These findings concern uncorrected legacy claims; they are not failures in the new M5–M6 proof chain.

- **The abstract curvature theorem remains unproved here.** The manuscript calls the axiom the general implication `Γ₂ ≥ κΓ ⇒ LSI(2/κ)` at [OperatorDerivative.tex:1375](C:/Operator/OperatorDerivative.tex:1375), and calls it a Bakry–Émery semigroup interpolation theorem at [line 1338](C:/Operator/OperatorDerivative.tex:1338). The actual axiom is just the concrete variance-one, one-dimensional Gaussian inequality. `ou_curvature_bound` at [OperatorDerivative.lean:2306](C:/Operator/OperatorDerivative.lean:2306) proves a square is nonnegative for arbitrary supplied functions; it does not connect a general generator, invariant measure, domains, and entropy dissipation. Replacing this axiom proves the concrete proposition, not a general curvature-dimension theorem.
- **The legacy Fisher docstring is inaccurate.** Its implementation is Dirichlet energy, not density Fisher information. The exact adapter succeeds because it follows the implementation, not the docstring.
- **The preliminary source sketch has normalization/sign errors.** The comment beginning at [line 2267](C:/Operator/OperatorDerivative.lean:2267) omits the entropy-centering term and omits `−∫fg'` in the product Stein identity. The semigroup sketch at [line 2319](C:/Operator/OperatorDerivative.lean:2319) gives `−2∫Γ(√u)` where the actual entropy derivative is `−4∫Γ(√u)` for this normalization, and reverses the subsequent bound for a negative entropy derivative. These comments were not used by the verified proof.
- **Other named legacy consequences are placeholders.** `log_sobolev_tensorization` at [line 2381](C:/Operator/OperatorDerivative.lean:2381) and `sobolev_embedding_from_hypercontractivity` at [line 2429](C:/Operator/OperatorDerivative.lean:2429) conclude `True`. They do not establish tensorization or a Sobolev embedding. The former also has an overbroad premise omitting necessary integrability hypotheses; it cannot simply consume the new theorem as written.
- **The asserted Gaussian `D^{1,2} ⊂ L⁴` is false.** The discussion around [line 2413](C:/Operator/OperatorDerivative.lean:2413) cannot be repaired merely by proving log-Sobolev. An analytic counterexample is `f(x)=exp(x²/8)`, with actual derivative `h(x)=(x/4)exp(x²/8)`: multiplying `f²` and `h²` by the Gaussian density gives integrable multiples of `exp(-x²/4)` and `x² exp(-x²/4)`, whereas `f⁴` times that density is a positive constant and has infinite Lebesgue integral. This counterexample is a mathematical check in this audit, not a new Lean declaration. Hypercontractivity of a semigroup does not bound its unbounded inverse by a first-order Sobolev norm.
- **Unrestricted pointwise L² multiplication remains impossible on the Gaussian space.** `brownianEnergySpace` at [line 3466](C:/Operator/OperatorDerivative.lean:3466) assumes total L² multiplication agreeing almost everywhere with products of arbitrary L² inputs. The same example has `f∈L²` but `f*f∉L²`. Its conditional construction is not a construction of the claimed Gaussian model. By contrast, the separate `L⁴ × L⁴ → L²` lemmas are mathematically valid; their current Lean errors are implementation issues, not counterexamples to Hölder.

No claim of finite-dimensional tensorization, an infinite-dimensional Gaussian LSI, arbitrary weak-Sobolev representatives, hypercontractivity, algebra closure, or general non-Gaussian Bakry–Émery theory follows from the public M6 statement alone. It is a full result for the requested **everywhere-differentiable real functions with Gaussian-square-integrable value and actual derivative**.

## 8. Untouched legacy compilation and safe replacement procedure

As an additional integration check, the complete original file was compiled from the pinned rewrite environment without edits. It failed at these existing locations:

| Location in `C:\Operator\OperatorDerivative.lean` | Declaration | Reported error |
|---|---|---|
| [3156](C:/Operator/OperatorDerivative.lean:3156) | `concrete_expect_constEmb` | `rewrite` pattern not found |
| [3272](C:/Operator/OperatorDerivative.lean:3272) | `concrete_mul_memLp` | Type mismatch in `MemLp.mul'`, including reversed product order |
| [3300](C:/Operator/OperatorDerivative.lean:3300) | `pip_memLp_one` | Invalid constructor notation for the expected finite-norm proposition |
| [3609](C:/Operator/OperatorDerivative.lean:3609) | `brownianEnergySpace` | `simp` made no progress |
| [3630](C:/Operator/OperatorDerivative.lean:3630) | `brownianEnergySpace` | `simp` made no progress |
| [3696](C:/Operator/OperatorDerivative.lean:3696) | `memLp_four_mul_of_memLp_eight` | Stuck `ENNReal.HolderTriple 8 8 ...` instance |
| [4456](C:/Operator/OperatorDerivative.lean:4456) | `memLp_two_mul_of_memLp_four` | Type mismatch in `MemLp.mul'`, including reversed product order |

Consequently the temporary prefix test establishes the exact adapter and its immediate consumer, but does not certify the whole legacy file. These failures were not induced by the new theorem or by this audit.

The narrowest safe future procedure is:

1. In the pinned Lake environment, import `Foundation.GaussianLogSobolevFull` into a reviewed integration copy of the legacy development. Preserve the existing `gaussian_entropy` and `gaussian_fisher` definitions and their mathematical meanings.
2. Replace only the `axiom` keyword/body at line 2354 by a theorem with the identical type and the checked adapter above. Do not leave a parallel axiom in place or weaken the signature.
3. Run fresh `#print axioms` for the replacement and unchanged `log_sobolev_1d`; require absence of the old analytic axiom and `sorryAx`. The temporary-prefix test already demonstrates this step.
4. Repair and recheck the unrelated legacy compilation failures separately before claiming a successful full-file integration. Do not interpret typechecking of the conditional `brownianEnergySpace` construction as proof of the impossible multiplication hypotheses.
5. In a separately reviewed documentation change, describe the result as the proved one-dimensional Gaussian LSI, correct the Fisher/entropy descriptions and source sketch, and retain explicit limitations for abstract curvature theory and the `True` placeholders.

**Recommendation:** proceed with the exact-signature theorem adapter as the smallest safe implementation milestone. M5 and M6 need no additional mathematical hypothesis or proof to discharge that concrete axiom. Full legacy compilation and the broader manuscript claims require separate work. No source replacement or commit has been performed by this audit.
