# Integer and conditional real-order stopping audit

October 21, 2026. Mathematical baseline: `41b8ca123a3571756a5cc3dce9f74b66b93352eb`.
This is a stopping audit of the focused integer/real-order investigation, not a
claim that every higher-order zero problem has been solved. The existing goal
remains active. The independent A(2) investigation opens only after this report's
checkpoint has passed its complete verification and exact private-backup gate.

## Actual objects and normalization

Write K for `RiemannQuarticKernel.kernel`, the repository's arithmetic theta
kernel, and use the existing measure `RiemannQuarticFlow.halfLine`. The actual
family is

F(a,t,z) = integral over u >= 0 of exp(t |u|^(2a)) K(u) cos(u z) du.

This is `RiemannRealOrderFlow.flow`, not a formal operator substitution.
`flow_eq_cosine_integral` identifies the genuine integral. `weighted_integrable`
and `integrand_integrable` discharge the domains for every a >= 0, every real t,
every complex z, and all natural polynomial moments. `jet_hasDerivAt` and
`flow_differentiable` establish spatial differentiation and entireness.
`actual_flow_zero_pos` gives positive mass at z=0. No probability law is assumed.

`RiemannRealOrderFlow.flow_nat` proves exact agreement with
`RiemannEvenFlow.flow` for every natural order. In particular a=2 is the frozen
quartic flow and a=3 is the sixth-order flow. The parameter a is the user's k;
the multiplier exponent is 2a. The cubic endpoint a=3/2 is not A(6).

`RiemannRealOrderLimit.locally_uniform_quadratic_limit_from_above` has target
`RiemannEvenFlow.flow 1 t` at the SAME fixed time t. Nonzero time is a quadratic
deformation, not undeformed Xi. The present audit does not supply a Lean theorem
identifying an externally normalized completed zeta function, its argument
scaling, or its multiplicative constant with this repository object. Those
identifications must be checked explicitly before any externally normalized
classical claim. No RH result is asserted.

## Requirement-to-theorem audit

All declaration names below are in `OperatorDerivativeRewrite.Foundation`.
Module names specify the namespace as well as the source file.

| Objective | Verified evidence and scope | Remaining boundary |
|---|---|---|
| Coherent integer hierarchy before real-order work | `RiemannEvenDomain.weighted_integrable`; `RiemannEvenEvolution.flow_iteratedDeriv`, `even_order_heat_equation`; `RiemannEvenEntireGrowth.jet_growth_bound` | This is an actual domain/jet/evolution/growth hierarchy, not global zero control at every integer. The post-private-gate reuse audit is recorded at checkpoint1226. |
| A(6) first generalization | `RiemannSixthTransitionSimpleZeros.eventually_all_zeros_real_simple` | Every sufficiently late time, every actual sixth-order zero is real and simple. No optimal sixth-order threshold or universal integer threshold relation follows. |
| Expanding integer windows | `RiemannEvenWindowZeros.actual_real_simple_window`, `eventually_real_simple_on_each_disk` | Each fixed positive integer order has an eventual real/simple window and each fixed disk eventually has only real/simple zeros. The quantifier order does not give one time controlling all disks. |
| Actual real interpolation | `RiemannRealOrderFlow.flow_nat`, `flow_differentiable`, `actual_flow_zero_pos` | Construction succeeds. It does not preserve global real-rootedness throughout the order parameter. |
| Local uniform order convergence | `RiemannRealOrderLimit.flow_order_tendsto_locally_uniformly`, `jet_order_tendsto_uniformly_on_ball`, `locally_uniform_quadratic_limit_from_above` | Fixed time, any positive limiting order, compact spatial regions; no global complex-zero conclusion from value convergence alone. |
| Uniform real-axis convergence | `RiemannRealOrderRealUniform.flow_order_tendsto_uniformly_real`, `uniform_quadratic_limit_from_above`, `joint_order_real_frequency_decay` | Whole real frequency axis at fixed time. This does not bound nonreal zeros. |
| Branch choices and density analyticity | `RiemannRealOrderBranchObstruction.no_analytic_half_integer_density`, `positive_half_line_density_extension`, `half_integer_fourier_entire_despite_density`; `RiemannRealOrderFractionalDensity.density` and its analytic derivative results | Real absolute-value powers need no complex branch. Positive-axis principal-power continuation is used only on its proved slit/kernel domain. At odd half-integer orders and nonzero time no holomorphic germ through zero matches the even density. This does not prevent the entire Fourier transform or all contour arguments. |
| Genuine fractional Fourier asymptotics | `RiemannRealOrderFractionalCoefficient.actual_flow_scaled_limit`; `RiemannRealOrderCubicEndpoint`; `RiemannRealOrderFourthAsymptotic.actual_flow_scaled_limit` | Third- and fourth-derivative reconstructions and actual L1 integration by parts, including the cubic endpoint. Higher derivatives of the old truncated Bell jet are not assumed. |
| Global fractional obstruction | `RiemannRealOrderQuarticLimitZeros.between_one_two_real_zeros_finite`, `between_one_two_nonreal_zeros_infinite`, `between_one_two_no_eventual_real_zeros`, `between_one_two_no_split_polynomial_limit` | Every 1<a<2 and every t != 0: finitely many real zeros, infinitely many nonreal zeros, no finite eventual all-real starting time, and no locally uniform split-real-polynomial approximation of the stated kind. The endpoint t=0 and orders above2 are excluded. |
| Uniform control as a approaches1 from above | `RiemannRealOrderUniformAsymptotic.actual_flow_uniform_scaled_limit`; `RiemannRealOrderTransitionRate.actual_absolute_error_uniform_rate`, `actual_relative_error_bound`, `actual_relative_diagonal_limit`, `real_zero_radius_bound` | Absolute error O(x^(-1/2)) uniformly on 1<a<=5/4 at fixed time. At nonzero time relative error <= C/((a-1)sqrt(x)) on a fixed right neighborhood. Constants are existential and time-dependent; the real-zero bound is not a nonreal-zero bound or a sharp escape rate. |
| Degeneration and counterexamples | `RiemannRealOrderFractionalCoefficient.leading_div_order_gap_limit`; `RiemannRealOrderRelativeObstruction.uniform_relative_error_unbounded`; `RiemannRealOrderCutoffConcentration.no_common_integrable_majorant`, `cutoff_lipschitz_tendsto` | The leading coefficient vanishes linearly at1. Relative error is unbounded on every full order/frequency tail rectangle touching1. The raw cutoff concentrates at0; dominated convergence cannot be justified by a nonexistent common L1 majorant. Uniform absolute convergence survives these obstructions. |
| Actual escaping nonreal zeros near1 | `RiemannRealOrderFractionalZeros.exists_approaching_escaping_nonreal_zeros` | Unconditional existence for every fixed nonzero time along explicit orders1+1/(n+3), selecting zeros of norm>n. This does not say every selected nonreal zero escapes. |
| Precise sufficient hypotheses for every selected zero to escape | `RiemannRealOrderZeroLimits.nonreal_zero_norm_tendsto_atTop`, `quadratic_nonreal_zero_escape` | The actual limiting flow must have only real and simple zeros. These assumptions are retained at the quadratic endpoint, not silently inferred. |
| Concrete escape with a real/simple limiting arithmetic flow | `RiemannRealOrderQuarticLimitZeros.eventually_quartic_selected_nonreal_escape`, `eventually_quartic_real_simple_with_escaping_fractional_zeros` | At sufficiently late fixed times, actual order2 has only real/simple zeros, explicit orders2-1/(n+3) have nonreal zeros, and any selected nonreal-zero sequence with orders tending to2 escapes every compact. No quantitative escape rate is established. |

## Fourier coefficient and endpoint safeguards

For 1<a<2 away from the cubic splitting point, the actual asymptotic coefficient
is L(a,t)=t K(0) Gamma(2a+1) sin(pi(a-1)); the cubic case is established
separately. The fixed-order identities are obtained from genuine density
derivatives, absolute integrability and endpoint integration by parts. The
new fourth remainder has finite one-sided limit K''''(0) at0; no assertion that
this constant is nonzero was proved or needed. Its cosine integration by parts
uses the vanishing sine boundary factor. Its actual derivative uses a separately
verified fifth Bell expression. The older exponential jet is defined as zero
above order4 and is never treated as the actual fifth derivative.

The asymptotic remainder bound near1 and the Gamma cutoff estimate yield an
absolute error uniform in order. Relative recovery is proved on moving regions
with (a-1)sqrt(x) tending to infinity. The divergent sufficient real-zero radius
does not prove actual zeros escape at that rate. Uniformity at order2, a sharp
transition scale, and uniform complex saddle estimates are not established.

## Stopping decision and open claims

Freeze this focused campaign after its audited private checkpoint. This is a
research stopping point with decisive constructions and obstructions, not a
claim of universal completion. The integer foundation, first A(6) generalization,
real interpolation, justified quadratic limit, uniform-control obstruction and
actual compact-escape question have concrete verified answers on the domains
above. All-order far-field classifications remain unresolved within the original
scope. This stopping decision preserves those obligations as open rather than
claiming exhaustive resolution; the queued independent A(2) audit can use the
verified results without assuming the missing classifications. Preserve these
explicit open problems:

1. Global eventual zero reality/simplicity, exit, and re-entry for EVERY integer
   order >=4; no universal classification follows from quartic and sixth-order
   cases or expanding windows.
2. Global zero classification for noninteger real orders >2, including a
   reusable all-order endpoint asymptotic and branch-safe contour estimates.
3. Sharp or effective transition constants, uniform complex localization near1
   or2, and quantitative rates for actual nonreal-zero escape.
4. Unconditional reality and simplicity of all zeros of the same-time quadratic
   limit in any claimed parameter regime; eventual absence of nonreal zeros on
   every fixed compact near1 without retaining the required hypotheses.
5. An explicit formal identification with the externally normalized classical
   Xi/de Bruijn-Newman convention before drawing conclusions in that convention.

No novelty claim is made. The source/reuse audits and manuscript inventories in
`A2K_INTEGER_CAMPAIGN.md`, `PROJECT_STARDUST_REPORT.md` and the frozen A(4) audit
remain part of the research record. This report is not a new literature survey
and does not certify unverified manuscript claims.

After the exact private gate closes, begin independent A(2) with a theorem-level
reuse and normalization audit, then verify the requested OpenAI paper/repository
and follow-up claims against their actual primary sources. Do not assume the
requested result exists or has the stated theorem. The final multichannel
pseudoprocess campaign remains afterward. October31,2026 is the hard stop; no
new campaigns are added.
