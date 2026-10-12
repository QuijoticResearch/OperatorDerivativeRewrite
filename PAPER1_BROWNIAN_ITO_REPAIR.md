# Paper 1: focused Brownian Itô dependency map and repair

Audit against the unchanged original `C:/Operator/OperatorDerivative.tex` and `C:/Operator/OperatorDerivative.lean`, 2026-10-12. Campaign base: `00e5bd45681e45361c6fa0bfba6b47b8efb6f764`. This document records mathematical conclusions separately from Lean verification. The original files have not been edited.

## Verdict

**REVISE the original operator-functional theorem.** The new scalar result is a genuine Brownian theorem on a bounded-derivative C3 core. The stopped-observation theorem below is a restricted, independently specified path-functional extension. Neither establishes the manuscript's abstract operator-functional or Gaussian Volterra claim.

## Claim-by-claim dependencies

| Original claim/location | Exact verified replacement or related declaration | Discrepancy / obligation |
|---|---|---|
| TeX 254, operator derivative; 673, `thm:equiv` | `Foundation/GaussianPredictableAdjoint.lean`: `predictableAdjoint`, `predictableAdjoint_eq_projected_derivative`; `InfiniteGaussian.closedCylindricalDerivative` and `hilbertDivergence` | Full closed Malliavin D and bounded predictable J* are different operators. The identification J*=Pi D is only on dom(D). There is no transfer of the full Leibniz rule to all-L2 J*. |
| TeX 770--774, intrinsic bracket | `GaussianTimeProcess.wienerL2_sub_norm_sq`; `GaussianWeightedQuadraticVariation.weightedError_norm_sq` | The full Hilbert norm of D B_s=1_(0,s] is squared norm s, not 1. Integrating that norm in s would give T^2/2, not T. The instantaneous Brownian diffusion coefficient 1 must not be confused with the entire derivative time vector. Fix the time/field types before using the manuscript bracket. This observation is a mathematical type/normalization diagnosis, not a newly formalized universal bracket counterexample. |
| TeX 776--778, `def:ito_proc` | `GaussianPredictableFull.itoIntegral`, actual time truncations in `GaussianPredictableCutoff` | A process decomposition with an independently specified predictable coefficient is meaningful. The shorthand Pi D Y as a running coefficient requires a separate theorem and correctly distinguished time variables. It cannot be obtained just from endpoint PRP. |
| TeX 782, `lem:prod_rule`; 793, `prop:domain`; 809--810, `rem:domain` | `Foundation/LpProducts.lean`; `Foundation/MultiplierCore.lean`, `IsDivergenceMultiplier.mem_adjoint_domain`; actual Gaussian polynomial product theory | Domain membership and the identity must be proved separately. L2 times L2 is generally L1, not L2. Testing adjoint domain membership only on an ambient-L2 dense set is insufficient without a graph-core argument. Bounded multipliers/commutators or appropriate L4 estimates must be specified. No general closed-domain algebra is inferred. |
| TeX 826--844, `lem:skor_iso` | `GaussianPredictableFull.itoIntegral_norm`; `GaussianWeightedQuadraticVariation.weightedError_norm_sq`, `weightedError_tendsto_of_mesh` | Brownian J has an exact isometry. This does not establish an HS-square correction for arbitrary Skorokhod divergence. The displayed implication 2gamma+2H >= 2gamma+1 fails for H<1/2. The Volterra claim remains unverified. |
| TeX 850, `thm:ito`, Step 1 at 865 | Actual scalar derivatives in `GaussianTaylorRemainder.remainder_bound` and `GaussianSmoothIto` | The Brownian Taylor proof does not require a full-domain Malliavin smooth-chain theorem. Do not describe this as a proof of the manuscript's general abstract chain equivalence. |
| TeX 867--870, Step 2 (terminal projection replaced by running derivative) | `GaussianBrownianPRP.clark_ocone`; `GaussianCubicDiagnostic.cubic_projection_difference_norm_sq` | Clark--Ocone gives a terminal-variable predictable representer. It does not replace it by the running spatial derivative. The verified cubic discrepancy has squared product-L2 norm 3T^3. Cubic is NOT in C_b^3, so this is a polynomial diagnostic of the substitution, not a bounded-C3 counterexample to the entire stated theorem. |
| TeX 874--883, Step 3 and mean ODE | `GaussianTaylorRemainder.remainderSum_norm_sq`, `remainderSum_tendsto`; `GaussianLipschitzQuadraticVariation.error_tendsto` | New proof supplies genuine L2 Taylor and weighted quadratic-variation limits for Brownian increments. The original argument's moment/cross-term orders are not supplied by mere L2 Hölder continuity or an unweighted isometry. |
| TeX 885--897, Step 4 and `rem:ito_status` | `GaussianContinuousIntegrands.integral_step_tendsto`, `drift_sum_tendsto`; `GaussianSmoothIto.finite_taylor_identity`, `ito_of_lipschitz_derivatives` | Continuous-linear-map Bochner Fubini does not identify or absorb extra divergence terms into an already fixed stochastic integrand. The verified replacement passes to limits in an exact random-variable identity; it never promotes an expectation identity by assertion. |
| TeX 903--932, `thm:multi_ito` | `GaussianSmoothCylinders.cylinder_directional_hasDerivAt`, `cylinder_second_directional_hasDerivAt`, `stopped_cylinder_ito` | The new class is additive smooth cylinders of finitely many stopped observations, with diagonal Hessian. General nonlinear mixed cylinders require cross quadratic variation and a multivariate Taylor theorem. They are not established by applying scalar claims componentwise. |
| TeX 1255, Brownian square example | `GaussianQuadraticIto.brownian_quadratic_ito`; `GaussianScalarPolynomialIto.scalar_polynomial_ito` | The polynomial example is verified independently. x^2 is not bounded C3 and so was not literally an instance of the original C_b^3 theorem. Polynomial and restricted smooth theorems are separate verified results. |
| Original Lean 2081 `ItoProcess`, 2098 `ItoProcess.bracket`, 2118 `ito_formula_time_indexed`, 2141 `ito_formula_integrated` | New `GaussianSmoothIto.smooth_ito_ae` with the actual J and Bochner drift | The old time-indexed theorem assumes candidate fields `phi'Y`, `phi''Y` and their chain identity and concludes a divergence product identity, not the displayed stochastic change-of-variables formula. Its bracket is a terminal inner-product expression, not the manuscript time-integral definition. Old theorem names/builds cannot certify the new claim. |

All Foundation paths in the table are relative to `C:/OperatorDerivativeRewrite`; named Gaussian declarations have prefix `OperatorDerivativeRewrite.Foundation.`.

## Precisely corrected claims now implemented

1. Scalar: for C3 f with uniformly bounded actual first three derivatives, T>=0,
   `f(B_T)-f(0) = J(1_(0,T] f'(B_t)) + (1/2) integral_0^T f''(B_t) dt`.
   This is a Gaussian-L2 identity and an AE random-variable identity for each T. All integrability is proved. The time integral is Bochner in Gaussian L2. The actual running field is defined through the independent product-L2 isometry and shown predictable by convergence of adapted steps.
2. Conditional: `GaussianSmoothConditional.smooth_conditional_dynkin` proves
   `C_S f(B_T)-f(B_S) = (1/2) C_S(integral_S^T f''(B_t)dt)` for S<=T. `pastProjection_ae` identifies C_S with actual raw-past conditional expectation. `pastProjection_compensated` gives the exact conditional identity of the compensated process.
3. Restricted functional: fix any finite family of deterministic nonnegative observation times r_i and smooth functions f_i satisfying the scalar hypotheses. Define independently `F_T=sum_i f_i(B_min(T,r_i))`. `GaussianSmoothCylinders.stopped_cylinder_ito` proves
   `F_T-F_0 = J(U_T) + (1/2) sum_i integral_0^min(T,r_i) f_i''(B_t)dt`,
   where `stoppedIntegrand_slices` identifies `U_T(t)=1_(0,T](t) sum_i 1_(0,r_i](t) f_i'(B_t)` in actual product L2. The coordinate function is defined before the theorem; its first and second directional derivatives are proved by actual differentiation. Zero-dimensional families, zero and repeated observation times are allowed. With nonconstant functions at distinct stopped times, this class allows genuine dependence on observations before T; it is not restricted to terminal-only functions. Arbitrary nonlinear interactions between past observations are not included.

## Operator interpretation and next obligations

The Brownian J and its predictable adjoint J* remain bounded. Full D is the existing closed unbounded Malliavin derivative; delta is its full adjoint. The smooth proof uses J and Gaussian increment estimates and does not silently assert that each newly introduced functional has any unproved higher Malliavin-domain property. Existing Clark--Ocone retains its exact domain restrictions. Horizontal/vertical derivatives of a path-functional are separate notions; the proved finite-coordinate derivatives are not relabeled full Malliavin derivatives.

The shortest remaining extensions are: deterministic C1 time weights and then a genuinely nonseparable C1,2 theorem; a C2 approximation/localization theorem with simultaneous terminal/first-/second-derivative limits; mixed smooth finite-dimensional cylinders with correct covariance cross terms. General unbounded semimartingale coefficients, infinite-dimensional traces, and Volterra models require further analytic theorems. None can be supplied by changing the name of the present restricted theorem. Preserve the central intended contribution by stating the exact concrete Brownian theorem and keeping the abstract scheme explicitly open until its time types, domains, and correction mechanism are repaired.


## Subsequent verified time-dependent milestone

`Foundation/GaussianTimeWeightedSmoothIto.lean:152`, `time_weighted_ito_combined`, now proves the restricted time-dependent theorem for a(t)f(x), with a C1 and f in the stated C3 spatial core. Lines 167,170,173 prove its actual partial derivatives. `GaussianContinuousStochasticFubini.integrated_slices` proves the necessary kernel Fubini theorem with domination, and `weightedField` is independently defined by its actual running coefficient before its stochastic identity is proved. Thus deterministic C1 time weighting is no longer a missing obligation. General nonseparable C1,2, mixed nonlinear smooth cylinders, and the original abstract formula remain open.

The additional module `Foundation/GaussianSmoothHeatMartingale.lean` proves genuine nonpolynomial backward-heat martingales: `sin_heat_martingale` and `cos_heat_martingale`. These follow from the actual differential equations and the existing J, with no martingale assumption. The general `heat_martingale` remains restricted to the explicitly documented separable C1-in-time/C3-in-space class.

## Bounded smooth diagnostic for Step 2

The cubic caveat in the original table is now complemented by `Foundation/GaussianSmoothProjectionDiagnostic.lean`:
`sin_bounded_C3` (17) proves boundedness of sine and its first three actual derivatives. `sin_predictableAdjoint` (30) and `sin_predictableAdjoint_slices` (49) prove

    J*[sin(B_T)](t) = 1_(0,T](t) exp(-(T-t)/2) cos(B_t).

`sin_projection_ne_running_derivative` (69) proves this differs, for every T>0, from 1_(0,T]cos(B_t). Thus the terminal-adjoint/running-derivative substitution fails even for this bounded smooth function in the concrete bounded predictable-adjoint formulation. This theorem uses J*, not an undeclared value of the unbounded D. The existing J*=Pi D theorem can only be invoked on its established domain. A new smooth Malliavin-domain theorem is not assumed here, and the entire original ill-specified abstract theorem is not declared refuted solely by this calculation.

The corrected scalar Ito formula and the terminal representation are different identities: the former has the running derivative plus a random drift; the latter uses a conditional, terminal-horizon-dependent integrand. Erasing that distinction is precisely the unsupported step.

## Genuine C2 extension

`Foundation/GaussianC2Ito.lean:107` (`c2_ito`) and line 125 (`c2_ito_ae`) now remove the C3 assumption for scalar Brownian Ito: the exact hypotheses are C2 and uniform bounds on the first two actual derivatives. No bound on f, third derivative, or Lipschitz f'' is assumed. The explicit interval-average approximants converge in the terminal, predictable, and drift topologies. General time-dependent C1,2 and arbitrary mixed smooth cylinders remain distinct obligations.

## Corrected operator statement and mixed quadratic functional class

`GaussianC2OperatorCorrection.terminal_adjoint` proves the precise replacement J*f(B_T)=running f' +(1/2)J*(actual drift); `terminal_adjoint_eq_running_iff` proves the missing projected drift must vanish for the manuscript substitution to hold. `full_derivative_projection` invokes Pi D only under its exact, separately stated domain condition. The C2 Ito theorem itself has no such extra assumption.

`GaussianMixedStoppedIto.stopped_quadratic_ito` now treats arbitrary mixed quadratic functions of finitely many stopped Brownian observations, with actual directional derivatives, Hessian contraction, and correction sum_ij b_ij min(T,r_i,r_j). Its cross integrand is independently identified by `crossField_slices`. This is a genuine nonlinear functional repair beyond additive cylinders, but not the manuscript's abstract theorem or arbitrary smooth multivariate Ito.
