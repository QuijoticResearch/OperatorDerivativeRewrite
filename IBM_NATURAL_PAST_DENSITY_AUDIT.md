# Actual IBM natural-past density and adjoints — checkpoint 1304

IBM remains ACTIVE. This checkpoint discharges the finite-past density
obligation left open at checkpoint 1303, for every nonnegative horizon T,
including T=0. It also constructs the closed dense restriction of the existing
two-source intrinsic derivative to that actual past and its maximal adjoint.
It does not complete intrinsic IBM stochastic calculus.

## Exact density theorem and actual process

`IBMPastCoreDensity.core_closure_eq_past T` proves

    closure_L2(intrinsicCore ∩ past(T)) = past(T).

Here `past(T)` is the actual raw natural-filtration L2 space already defined
from the constructed IBM process, not a Gaussian scenery sector or a replacement
filtration. `intrinsicCore` is the existing actual IBM-observable intersection
of the clock and scenery derivative domains. The closure is strong scalar L2;
the theorem does not assert convergence of derivatives or graph norms.

The proof proceeds through the following verified connections:

1. `IBMPastEndpointCore.randomSource_zero` proves the native zero-time L2
   source class is zero from `GaussianTimeProcess.process_zero_ae` and the
   existing exact source-scenery norm identity. No everywhere-zero representative
   or pointwise normalization is silently assumed.
2. `point_mem_closure` includes t=0 as well as positive t≤T. Positive times
   use checkpoint 1303's left-sided actual averages; zero uses the zero class.
   Its `point_cylinder_closure` therefore covers bounded C1 tests with bounded
   derivative of any finite real weighted family with 0≤t_i≤T.
3. `IBMPastWeightedLaws.annihilator_point_fourier_moments` uses these actual
   cylinder approximations. Positive and negative parts of an L2 annihilator H
   define finite positive weighted measures. The existing generic
   `IBMFiniteWeightedLaws.finite_measure_eq_of_cos_sin` proves equality of their
   finite observation laws; no Gaussian law of IBM observations is assumed.
   `annihilator_finite_event` then annihilates every measurable finite event.
4. `PastTime T` includes precisely the NNReal times in `Iic T`.
   `natural_eq_pastSigma` identifies the generated observation sigma algebra
   EXACTLY with the previously constructed raw natural filtration at T, using
   Mathlib's `Filtration.natural_eq_comap`. Time zero is included rather than
   removed through an unproved sigma-equivalence or path modification.
5. A measurable-cylinder pi-system argument extends annihilation to every
   generated measurable event. The existing conditional-expectation uniqueness
   theorem then forces every past-measurable annihilator to vanish. Closed
   subspace orthogonality gives the asserted full density.

`past_le_intrinsic` consequently identifies every actual past L2 class as
all-time IBM-observable. `past_core_approximation` supplies an actual sequence
in the common past domain converging strongly to EVERY past L2 class.
`conditional_core_approximation` applies this to the genuine conditional L2
projection of ANY joint L2 input, including horizon-dependent terminal Doob
values. This is existential L2 approximation, not an explicit computational
sequence, uniform derivative estimate or projection/derivative commutation.

## Restricted derivative and genuine Hilbert integration by parts

`IBMPastIntrinsicOperators.pastSpace T` represents the actual past inside the
existing intrinsic Hilbert space. `pastSpace_covers_past` proves that it covers
EVERY actual natural-past L2 class; it is not a smaller substitute space.
`pastDerivative T` is the existing joint derivative restricted to this closed
subspace using `ObservableRestriction.derivative`. Its exact domain is the
same common past domain in the density theorem. Both closedness and density
are proved. `pastDivergence T` is its Hilbert adjoint on its natural maximal
domain, and is closed. `integration_by_parts` proves, with both domains explicit,

    <δ_T u, f> = <u, D_T f>.

The field space remains `IBMJointIntrinsicDerivative.JointFieldSpace`: the two
native Gaussian source fields, scenery and clock. This is an actual operator
identity on actual IBM past observables. It is NOT identification with a
physical-time predictable integrand, an Itô integral against raw IBM or a
temporal Clark–Ocone theorem. No new process or stochastic law was postulated.

## Verification, independent tests, and next obligations

Four independent Lean checks cover zero-horizon density, approximation of the
actual terminal Doob value E[Z_2|F_1], a signed-weight mixed zero/terminal cosine
cylinder, and a concrete native average in the restricted two-source domain.
The Doob approximation is consistent with the earlier proof that E[Z_2|F_1]
differs from Z_1. Full root build, complete safe-Foundation transitive axiom
audit, actual unabridged public-type/proof review, source manifests, archive
checks and exact private synchronization accompany the checkpoint; see
`STARDUST_IBM_NATURAL_PAST_VERIFICATION.json`. No toolchain, trust, compiler
resource or verification configuration changes are introduced.

Next connect this maximal past adjoint to the established actual ambient source
divergences, their projected sums and graph closures. Determine the exact
bounded/static reconstruction available for conditional terminal observables,
and which additional temporal causal or predictable convergence statements
remain necessary for stochastic integration and an intrinsic Itô formula.
Do not infer preservation of derivative domains by conditional projection from
L2 density, or infer natural-time adaptation from a restriction of observable
domains. Keep the actual F1/F2 correction terms and their proved topologies.

No manuscript was modified. The queue remains IBM → Bakry/fBM → Cauchy →
fractional diffusion → black noise → cumulative backlog, without an expiration
date. No queued campaign is activated by this intermediate IBM checkpoint.
