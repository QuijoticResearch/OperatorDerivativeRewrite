# Volterra and stochastic-volatility campaign: verified checkpoint

Date: 2026-10-12. Repository: `C:/OperatorDerivativeRewrite`.

Initial HEAD: `61548d19f1f0020b35942783b8056b8b4b826fe4`.
Final mathematical HEAD: `d84077b24aba4430093dad8f7ba9331d267c903b`.
This report is a subsequent documentation-only commit; the delivery message records the final repository HEAD.

The preceding Brownian campaign was committed, built, audited, and reported before this campaign began. Its remaining general nonlinear-cylinder Itô assembly is still open. The tracked tree was clean at the initial checkpoint. Twelve unrelated untracked documents have been preserved.

## Outcome

The source Brownian operator calculus gives a genuine random weighted representer for a concrete strictly positive stochastic volatility. The representer is proved not to coincide almost everywhere with any deterministic time function. Its energy is the actual source-gradient energy in the sigma-squared weighted measure. This verifies a substantive non-Gaussian-observable example without assuming a derivative formula or representing the derivative by independently prescribed data.

This is not a verification of the manuscript's whole Theorems D, E, or F. In particular, an intrinsic closed derivative on general volatility observables, general deterministic-representer rigidity, standard fractional Brownian realization, Gubinelli identification, and the proposed abstract functional-Itô transfer remain unproved. The example is positive and polynomial, but unbounded; it does not silently substitute for the requested bounded nonconstant Sobolev example.

## Verified commits and checks

| Commit | Result | Full Lake jobs | Transitive axiom checks |
|---|---|---:|---:|
| `8b236c4791d27c71d072f4236cf10013162315b0` | Actual predictable-volatility martingale and second moments | 4182 | 2866 |
| `cc9d460a3fffe926adec6545366a2bacd1f078bd` | Singular deterministic Volterra power kernels | 4183 | 2890 |
| `fb707578f1dba878952415a870dba8a7676d29dd` | Future-integral cancellation and rigidity step | 4184 | 2894 |
| `605efc5a7daacd5b62b4c7b377a4780f0309665b` | Bounded kernel covariance/derivative transfer | 4185 | 2906 |
| `87b6bc6f83e1a0f15f3915438dbcbd374716b347` | Positive random volatility, actual gradient, nonzero correction | 4186 | 2930 |
| `d84077b24aba4430093dad8f7ba9331d267c903b` | Weighted representer, energy, and nondeterminism | 4187 | 2951 |

Every full build and audit exited successfully. Every new public declaration has an audit entry (105 total new declarations). The union of reported transitive axioms is exactly `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, `admit`, custom axiom, or unsafe command occurs in the six new modules. Existing theorem bodies and statements were preserved. Nonblocking style warnings remain.

Reproduce: `lake build`; `lake env lean Foundation/AxiomAudit.lean`. Per-milestone logs and explicit elaborated-type checks are in `.lake/campaign-volterra/01-*` through `06-*` (ignored build artifacts). Definitions, statements, proofs, and audit commands are committed source, not dependent on those logs.

## Exact mathematical results and scope

All namespaces below have prefix `OperatorDerivativeRewrite.Foundation`.

### A. Actual stochastic-volatility processes

`GaussianVolatilityProcess.process U t` is the natural-filtration conditional-expectation representative of the actual integral `itoIntegral (predictableCut t U)`, for any `U : fullPredictable`. This domain was independently constructed before the campaign.

`process_ae`, `process_memLp`, `process_stronglyAdapted`, `process_condExp`, and `process_martingale` prove the representative's agreement with the actual integral, square integrability, adaptation, conditional martingale relation, and the actual Mathlib martingale property. No martingale conclusion is a structure hypothesis.

`process_product_integral` proves

    E[M_U(S) M_V(T)] = integral_(0,min(S,T)] U(r,omega) V(r,omega) dr dP.

`process_pair_integrable` justifies the product, and `process_isometry` is its diagonal specialization. `bounded_memLp`, `boundedField`, `boundedField_coeFn`, and `boundedField_lower` construct finite-horizon classes from raw predictably measurable uniformly bounded coefficients; a lower bound is an explicit independently checkable hypothesis.

**Not proved here:** conditional second-moment isometry, a continuous path version, quadratic variation for general sigma, or a bounded nonconstant coefficient in the full Malliavin Sobolev domain. The first-moment martingale relation is not mislabeled as conditional Itô isometry. Per-time AE representative equalities are not indistinguishability statements.

### B. Concrete source derivative and weighted random representer

For `0 < a < b`, `GaussianPositiveVolatility.volatilityField a b` is

    sigma = 1_(0,a] + (1+B_a²) 1_(a,b].

`volatilityField_sobolev` proves membership in the pre-existing independent predictable Sobolev domain. `volatilityField_lower` gives sigma≥1 on (0,b] AE. `volatility_integral` proves that its actual integral is

    J sigma = B_a + (1+B_a²)(B_b-B_a).

For `a≤b`, `volatility_derivative_graph` proves graph membership in the existing closed cylindrical derivative, with value

    fieldEmbedding sigma + 2 B_a(B_b-B_a) times the source direction 1_(0,a].

The second term is an actual vector-valued L² class. `sensitivity_norm_sq` gives its norm squared as `4*a²*(b-a)`. For `0<a<b`, `sensitivity_ne_zero`, `volatility_not_original_derivative`, and `volatilityField_not_deterministic` exclude zero correction, the false full-gradient identity `D J sigma = sigma`, and deterministic volatility, respectively.

`GaussianVolatilityRepresenter.gradientField_graph` identifies the same gradient as the embedding of an actual time-probability L² field. Its measurable `coefficient` extends sigma positively outside the finite horizon; the measure is explicitly restricted to (0,b], so the extension does not change the weighted problem. `coefficient_eq_field` proves this compatibility.

`quotient_memLp` proves that gradientField/coefficient belongs to the actual sigma²-weighted L². `representer_formula` gives

    kappa(r,omega) = 1 + 1_(0,a](r) * 2 B_a(omega)(B_b(omega)-B_a(omega))

as an equality of weighted almost-everywhere representatives. For `0<a<b`, `representer_not_deterministic` says that for EVERY `k : ℝ → ℝ`, this class is not AE equal to `fun z => k z.1`. It uses `correction_not_constant`, actual Itô centering, the nonzero sensitivity norm, equivalence of the weighted/base null sets, and AE Fubini on a positive-measure time interval.

`representer_sq_integrable` and `gradientField_sq_integrable` establish genuine finiteness; `coefficient_mul_representer` recovers the source gradient, and `representer_energy` proves equality of weighted representer energy and finite-horizon source-gradient energy.

**Scope:** this constructs a representer of a proved Brownian derivative. It does not define a new derivative operator by prescribing this formula. It does not establish a general intrinsic observable domain, smooth observable-cylinder graph density, or a general non-Gaussian integration-by-parts theorem.

### C. Weighted operators and full versus predictable adjoints

Existing `WeightedL2Transport.unitary`, `WeightedMeasurableTransport.measurableUnitary`, and `WeightedAdjointTransport.weightedOperator_adjoint_eq` already prove squared-density multiplication, its measurable-subspace restriction, and exact adjoint transport with inverse-image domains. They were inspected and reused instead of duplicated. Their hypotheses include measurable AE nonzero sigma; they do not require bounded reciprocal moments.

The new concrete weighted energy/gradient result is proved. **General stochastic operator identification remains open:** specify the time-coordinate source/target subspaces, prove the stochastic divergence realization with a dense independently described domain, and then instantiate exact adjoint transport. The time-field embedding is an isometry into the coefficient Hilbert space; surjectivity must not be silently assumed. An adjoint for the bounded predictable Itô isometry is not the full unbounded source derivative. Vanishing-volatility kernels/quotients require a separate treatment.

### D. Rigidity

`GaussianFutureRigidity.future_integral_past_zero` proves: if `predictableCut S u = 0` and `J u ∈ pastL2 S`, then `u=0`.

`deterministic_factor_zero` proves: if additionally `sigma ∈ pastL2 S`, `sigma≠0`, and `J u = c • sigma`, then `c=0` and `u=0`. Positivity is unnecessary for this cancellation step.

`parameter_deterministic_representer` proves the AE parameter-family version for actual Bochner-L² future integrands and past nonzero coefficients: `J(u_s)=(kappa_s-1)sigma_s` forces `u=0` and `kappa=1` AE. The future support and past membership are explicit hypotheses, not conclusions hidden inside an abstract derivative structure.

The positive example above supplies a concrete genuinely random representer. The full manuscript Theorem E still needs to identify a general volatility's actual jointly square-integrable causal sensitivity kernel and connect its vanishing to the independent source derivative. Observation horizons must reach the interval being tested. On an enlarged source, independent initial randomness is a mathematical obstruction to inferring determinism from a zero Brownian derivative; that enlarged-space counterexample is not formalized by this campaign.

### E. Gaussian Volterra realization and transfer

`GaussianPowerVolterra` constructs `K_beta(t,s)=1_(0,t](s)*(t-s)^beta` for every `beta > -1/2`. `kernel_memLp` proves actual time L² membership, including singular beta<0. `kernel_energy` proves `t^(2 beta+1)/(2 beta+1)` for every nonnegative t, including zero.

`value` is the existing actual deterministic integral. `value_law`, `value_covariance`, `value_isGaussianProcess`, and `value_derivative` prove its Gaussian law, overlap-integral covariance, Gaussian process property, and actual closed source derivative. `value_exponent_zero` recovers the existing Brownian value exactly. `normalizedVector_norm_sq` gives `t^(2H)` for H>0 after normalization sqrt(2H).

This is a Riemann–Liouville-type power-kernel family. Matching marginal variance does NOT make it standard fBM.

`GaussianKernelTransfer` treats an actual bounded linear map `K : E →L[ℝ] TimeHilbert`, with E a real inner-product space and completeness required only for adjoints on E. `realization = W ∘ K`; `realization_inner`, `realization_norm`, and `realization_zero_iff` transfer the inner product and exact nullspace. `realization_normal` proves `(W ∘ K)* (W ∘ K)=K* K`, `realization_covariance` identifies the covariance operator, and `realization_derivative` places its genuine source derivative in the existing closed graph. No injectivity, surjectivity, finite dimensionality, or covariance-square-root identification is assumed.

### F. Standard fBM: exact next analytic obligation

No full standard fBM realization was proved. A search of the pinned Mathlib Probability/Analysis sources for fractional Brownian/Volterra/Molchan/Decreusefond/Mandelbrot infrastructure found no directly reusable implementation under those terms. The existing isonormal realization is reusable once the correct deterministic Hilbert geometry is established.

A viable next construction is the two-sided stationary-increment kernel. For `-1/2 < beta < 1/2`, beta≠0, define `x_+^beta` to be x^beta for x>0 and zero otherwise, and

    k_t(s) = (t-s)_+^beta - (-s)_+^beta.

The exact missing first lemma is genuine L² membership of k_t on ALL real s, with a strictly positive finite norm for k_1. Local power integrability is already available; the negative-time tail requires a cancellation estimate of order |s|^(beta-1), not separate L² estimates for its two divergent terms. Translation/scaling identities would then give stationary-increment norm scaling, covariance by polarization, and an isonormal realization normalized by ||k_1||. Beta=0 is the separately verified Brownian case. This is a proposed proof route, not an established theorem in this repository. It also does not supply pathwise Hölder or controlled-rough-path regularity.

### G. Gubinelli, Leibniz, and functional calculus

The source polynomial calculus remains valid: `InfiniteGaussian.polynomialDerivative_product` is an actual domain/product theorem with proved moments. The concrete volatility integral is built from genuine polynomial source elements. These existing facts do not establish a smooth intrinsic M-cylinder chain rule on a closed non-Gaussian domain.

The manuscript's general closed-domain Leibniz proof still needs graph approximation with the required product integrability and closedness, rather than invoking D(FG) before domain membership. The full stochastic-observable graph core is missing. Gubinelli identification additionally needs genuine time-indexed transfer/projection, increment/remainder estimates and compatible versions; an L² projection identity alone is insufficient. No new general functional-Itô formula is claimed. The preceding Brownian campaign's unfinished general nonlinear-cylinder assembly remains unfinished here.

## Source audit and preservation

`VOLTERRA_VOLATILITY_DEPENDENCIES.md` gives exact original Theorems D/E/F locations and proof discrepancies. The archive inventory is `C:/Operator/ResearchAudits/NONCLASSICAL_ARCHIVE_SOURCE_AUDIT.md`, with the declaration index and file manifest beside it. All archive manuscript claims retain UNVERIFIED status until an exact corresponding Lean theorem is established. A verified related theorem does not change the status of a stronger source claim.

All 58 original files in `ARCHIVE_MANIFEST_2026-10-12.json` were rehashed at the end: zero changed or missing. In particular:

- `C:/Operator/OperatorDerivative.lean`: SHA256 `9B8BA956878B80F3C2AC8F239D335C0F49582C88D0693E63554F481ACBEBDF29`.
- `C:/Operator/OperatorDerivative.tex`: SHA256 `FCA841CCA43DC712AAD2FCF02CB04010ABD7CFCDA4A231022D58A3B23D3BB983`.

Lean remains `leanprover/lean4:v4.34.1`; Mathlib remains `d13f23b723b8a846827a245b89c10fc7d3f11612`. Git diff confirms no dependency-pin change. No push, package installation, original-manuscript edit, or deletion was performed.

## Recommended next checkpoint

For the stochastic-volatility branch, prove a bounded nonconstant smooth past coefficient belongs to the existing closed Gaussian derivative domain, with its actual derivative, then obtain a predictable step by tensoring. This closes a precisely identified gap in the requested bounded core without defining admissibility through the desired integral derivative conclusion. Follow with bounded past-event multiplication compatibility for the actual Itô integral; this is the key localization lemma for conditional second-moment isometry.

For the fBM branch, prove the two-sided kernel L² cancellation lemma above before introducing any fractional derivative/divergence name. Neither branch should revise the manuscript's claims until its remaining domain and regularity obligations are independently verified.

## Complete new declaration index

Every entry below is in `OperatorDerivativeRewrite.Foundation.<module>.<name>`, and every source path is under `C:/OperatorDerivativeRewrite/Foundation`. The module sections above specify the mathematical hypotheses; the source contains the exact Lean statement and proof, and the explicit elaborated-type logs provide an additional check.


### GaussianVolatilityProcess

| Declaration | Source line |
|---|---:|
| `value` | 13 |
| `value_mem_past` | 16 |
| `cut_cut` | 19 |
| `value_projection` | 24 |
| `value_condExp` | 29 |
| `process` | 37 |
| `process_ae` | 40 |
| `process_stronglyAdapted` | 44 |
| `process_memLp` | 48 |
| `process_condExp` | 52 |
| `process_martingale` | 58 |
| `process_centered` | 62 |
| `value_inner` | 67 |
| `process_pair_integrable` | 74 |
| `process_product_integral` | 78 |
| `process_isometry` | 95 |
| `bounded_memLp` | 102 |
| `boundedField` | 111 |
| `boundedField_coeFn` | 120 |
| `boundedField_lower` | 131 |

### GaussianPowerVolterra

| Declaration | Source line |
|---|---:|
| `kernel` | 13 |
| `kernel_measurable` | 16 |
| `kernel_sq` | 19 |
| `power_intervalIntegrable` | 29 |
| `kernel_sq_integrable` | 35 |
| `kernel_memLp` | 41 |
| `kernel_energy` | 46 |
| `vector` | 55 |
| `vector_coeFn` | 58 |
| `vector_norm_sq` | 61 |
| `vector_support` | 68 |
| `profile` | 73 |
| `value` | 76 |
| `value_law` | 79 |
| `value_derivative` | 86 |
| `vector_zero` | 92 |
| `vector_exponent_zero` | 97 |
| `value_isGaussianProcess` | 103 |
| `kernel_pair_integrable` | 107 |
| `value_covariance` | 111 |
| `value_zero` | 119 |
| `value_exponent_zero` | 124 |
| `normalizedVector` | 132 |
| `normalizedVector_norm_sq` | 135 |

### GaussianFutureRigidity

| Declaration | Source line |
|---|---:|
| `future_integral_past_zero` | 13 |
| `future_integral_eq_past_iff` | 20 |
| `deterministic_factor_zero` | 31 |
| `parameter_deterministic_representer` | 41 |

### GaussianKernelTransfer

| Declaration | Source line |
|---|---:|
| `realization` | 18 |
| `covarianceOperator` | 21 |
| `realization_inner` | 24 |
| `realization_norm` | 29 |
| `realization_zero_iff` | 33 |
| `realization_product_integrable` | 38 |
| `realization_centered` | 43 |
| `realization_covariance` | 46 |
| `realization_normal` | 53 |
| `covariance_energy` | 63 |
| `covariance_zero_iff` | 68 |
| `realization_derivative` | 81 |

### GaussianPositiveVolatility

| Declaration | Source line |
|---|---:|
| `polynomial` | 18 |
| `delayedField` | 20 |
| `coefficient_coeFn` | 23 |
| `coefficient_positive` | 28 |
| `delayedField_sobolev` | 35 |
| `delayed_integral_coeFn` | 39 |
| `coefficient_derivative` | 45 |
| `sensitivity_coeFn` | 55 |
| `sensitivity_eq` | 65 |
| `linearCoefficient_norm_sq` | 82 |
| `sensitivity_norm_sq` | 91 |
| `sensitivity_ne_zero` | 102 |
| `initialField` | 112 |
| `volatilityField` | 115 |
| `volatilityField_sobolev` | 117 |
| `initialField_coe` | 123 |
| `initial_integral` | 135 |
| `volatility_integral` | 143 |
| `delayed_derivative_graph` | 151 |
| `volatility_derivative_graph` | 160 |
| `volatility_not_original_derivative` | 171 |
| `volatilityField_coeFn` | 179 |
| `volatilityField_lower` | 202 |
| `volatilityField_not_deterministic` | 218 |

### GaussianVolatilityRepresenter

| Declaration | Source line |
|---|---:|
| `coefficient` | 17 |
| `coefficient_measurable` | 20 |
| `coefficient_lower` | 25 |
| `coefficient_ne_zero` | 31 |
| `horizonMeasure` | 35 |
| `correctionField` | 37 |
| `gradientField` | 41 |
| `gradientField_graph` | 44 |
| `coefficient_eq_field` | 50 |
| `correctionField_coeFn` | 64 |
| `quotient_memLp` | 84 |
| `representer` | 91 |
| `representer_coeFn` | 95 |
| `quotient_formula` | 99 |
| `representer_formula` | 115 |
| `correction_not_constant` | 124 |
| `representer_not_deterministic` | 157 |
| `representer_sq_integrable` | 180 |
| `gradientField_sq_integrable` | 185 |
| `coefficient_mul_representer` | 190 |
| `representer_energy` | 200 |
