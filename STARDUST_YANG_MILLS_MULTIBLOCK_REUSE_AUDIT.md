# Yang–Mills multiblock: cross-domain theorem audit

October 31, 2026; checkpoint1838. Research audit, not publication maintenance.
Baseline: fully audited and both-remote-verified checkpoint1837,
`c83631b6cafb11c862a801c0b547c9ec7bbbbc94`.

## Conclusion

There is useful reusable operator geometry, but no audited theorem identified
here supplies the missing uniform nonlinear multiblock coercivity estimate.
In particular, neither signed Clark–Ocone reconstruction nor IBM covariance
completion converts the actual Wilson block problem into independent noise.
A new verified obstruction excludes transporting Gaussian closed operators
through the EXISTING Wilson Gaussian Gram feature map as a unitary map.
This excludes a specific mechanism, not all possible cross-domain transfers.
No assertion of nonexistence of another useful theorem or a Yang–Mills mass gap
is made. No continuum or infinite-volume construction is introduced as an axiom.

## Coverage and method

Every one of the 3036 Foundation Lean sources at baseline was read for a
syntactic declaration-signature, import, header and SHA256 index. The root
reaches 3035 of them; Foundation/AxiomAudit.lean is separately checked.
The index contains 30979 syntactic theorem entries, 7506 definitions, 416
abbreviations, 301 instances, 13 structures, one inductive and one lemma.
These are parser-index counts, not compiled-declaration or proof-review counts.
All source hashes were authenticated against the exact1837 approval manifest.
The ignored local evidence is `.lake/stardust-1838-library-index.json`.
Candidate original theorem statements and relevant proof/domain constructions
were then read selectively. This is NOT a fresh manual proof review of every
library declaration. Existing complete transitive axiom audits remain necessary.
The candidate search included Gaussian, Poisson, IBM, higher heat, Fourier,
Cauchy/fractional, Bakry, Hodge/Schur, SU(2), four-cube and periodic Wilson families.
No numerical experiment is being used as proof and no novelty claim is made.

## Exact theorem-level matches and rejected transfers

All names below are relative to `OperatorDerivativeRewrite.Foundation`.

| Existing declarations | Hypotheses and valid reuse | Missing Wilson connection / verdict |
| --- | --- | --- |
| `HilbertRepresentation.representationProjection_eq_self_iff`, `representation_norm_decomposition`, `representation_of_range_eq_orthogonal` | A genuine linear isometry from a COMPLETE integrand Hilbert space; orthogonal residual and reconstruction precisely on its closed range. | Abstract theorem transfers unchanged. Identifying the range with centered boundary observables requires a separate theorem. It gives no lower frame bound for spatial block fields. |
| `HilbertRepresentation.adjoint_domain_iff_pairing_bound`, `adjoint_domain_iff_core_pairing_bound` | Dense partial-operator domain; ambient-norm pairing bound; for core reduction actual graph-closure equality and closability. | Useful exact formulation of a Wilson divergence problem. A graph-dual functional is not automatically native L2 or a uniform multiblock estimate. |
| `AdjointUnitaryTransport.pullback_isClosed_iff`, `pullback_adjoint_domain`, `pullback_adjoint_eq` | Actual Hilbert UNITARY and a densely defined source operator, with the stated pullback domain. | Reusable without probability assumptions. Neither an arbitrary Hilbert isomorphism nor a Gaussian Gram factor identifies Wilson multiplication, boundary conditioning, derivatives or locality. The existing Gram factor fails the isometry hypothesis below. |
| `IBMConditionalL1Realization.conditional_pairing`, `realization_graph`, `conditional_memLp` | Actual IBM joint law and observed sigma algebra; integrable density; native realization additionally requires its conditional density in L2 and the full weak pairing. L2 source densities have the proved conditional L2 bound. | IBM-specific constants, initial germ and clock/scenery corrections cannot be substituted into a Wilson law. The abstract conditional-adjoint strategy survives, provided the actual Wilson score pairing and native norm bound are proved. |
| `IBMConditionalNativeCalculus.nonlinear_conditional_graph` | Actual IBM derivative/divergence graphs, chain-rule bounds and conditional L2 realization. | No identification with a Wilson boundary derivative or its adjoint has been proved. This is a missing domain/intertwining theorem, not a notational change. |
| `IBMMultichannelCompletion.finiteEnergy_actual`, `series_iff_energy_tails`, `fixed_range`, `fixed_reconstruction` | Actual IBM stochastic integrals and SIGNED cross-covariances retained in the Gram form; quotient by the integral kernel and completion in OUTPUT norm. The fixed-family range theorem is separately proved. | A comparable construction for block residuals would only complete their output span. It does not prove norm comparison with independent block inputs, closed range in a chosen physical norm, or uniform coercivity. Discarding cross-sector terms is invalid. |
| `IBMUniformStochasticReconstruction.gap_uniform`, `uniform_stopped` | Continuous compact parameter family and the proved IBM range/reconstruction and coefficient-energy convergence. | Compact-parameter uniformity does not cover unbounded beta, changing lattice dimension, volume or a continuum scaling regime. No uniform physical scale estimate follows. |
| `GaussianPolynomialStepCompletion.completedIntegral_norm`, `completedOperator_graph`, `completedOperator_isClosed` | Actual Gaussian elementary step isometry and its graph closure on the specified closed span. | Density and an isometry must be proved for Wilson integrands first; completion does not create either. |
| `GaussianPoissonChaosTransfer.finite_chaos_norm_transfer`, `poisson_square_first_inner`, `gaussian_square_first_inner` | Matching covariance/positive Poisson rate preserves chaos coefficient Hilbert norms. Squaring centered Poisson first chaos has first-chaos coefficient rate, whereas Gaussian squaring has zero first-chaos pairing. | Existing explicit product obstruction: a chaos isometry does NOT preserve ordinary products. Wilson words, nonlinear interactions and conditional laws cannot be transported by coefficient matching alone. |
| `GaussianDisplacementFromPoisson.displacement_derivative_graph`, `displacement_divergence_graph` | Actual source spectral unitary, positive rate and explicitly transported domains. | No Wilson spectral or multiplication intertwiner. Does not repair the preceding product obstruction. |
| `GaussianHalfDensityUnitary.unitary`, `forward_norm` | Actual linear Gaussian tilted law and square-root density, including AE equivalence and L2 domains. | This FILE is specialized to the Gaussian tilt. An actual Gibbs/Haar half-density unitary is a possible separate construction, but it would introduce nonconstant score terms and does not identify Gaussian derivatives with group derivatives. No new broad infrastructure is justified by the audit alone. |
| `HigherHeatBlockCoarsening.block_law`, `block_sum_law` | Independent finite signed heat increments, positive times and a LINEAR block-sum map; signed-measure Fourier uniqueness. | SU(2) word multiplication and boundary-weighted interacting Gibbs blocks do not meet these hypotheses. Gauge fixing does not establish independence or linearity. |
| `HigherHeatCompletedCausalProjection.completed_tower`, `completed_bound` | Nested dyadic past cuts on a particular analytic cylinder completion; bound exp(T), not a probability conditional contraction. | Overlapping spatial complement sigma algebras are not nested. No commuting spatial heat-bath or product conditional law is obtained. |
| `HigherHeatCompletedClarkOcone.clark_ocone` | All higher-order channels on the constructed analytic domain, reconstruction in its test dual with its proved coefficient and synthesis bounds. | Not probability L2, Wilson conditional expectation or a Wilson stochastic integral. A continuous intertwiner preserving derivatives, causal projections and synthesis is absent. |
| `HigherHeatClosedGenerator.domain_iff`, `operator_closed`, `domain_dense`, `graph_hasDerivWithinAt` | Closed complex L2 Lebesgue Fourier multiplier generator and its exact weighted domain. | Different measure, state space and spectral operator from a boundary-conditioned Wilson transfer. Taking a higher power of a nonnegative operator cannot by itself manufacture control near zero. No Wilson multiplier identification is established. |
| `SchurGaussianInnovation.completed_square`, `finite_minimum_attained`, `conditional_innovation` | Hilbert square completion, finite column span (dependent columns allowed); the CONDITIONAL conclusion further uses the actual Gaussian first-chaos embedding. | Quadratic minimization genuinely transfers when a quadratic form is identified. It is not exact elimination of a nonlinear Wilson block free energy. |
| `PeriodicHighActionSchur.completed_square`, `native_decomposition` and its low/high operators | Actual native periodic Wilson Hilbert splitting, high inverse and harmonic lift; the original operator and all coupling constants retained. | Genuine positive reuse of abstract Schur machinery ALREADY realized. Low Schur coercivity still must be proved; the winding obstruction survives the reduction. These action cuts are not spatial multiblock partitions. |
| `SU2BoundaryJointLaw.factorization`, `conditional_kernel`; `ConditionalResamplingKernel.update_law`, `invariant_iff_conditional` | Actual normalized boundary/interior joint law and actual conditional kernel; boundary marginal is partition-weighted. | Correct conditional interface. One-link/finite word identities alone do not establish the full 4D multiblock gluing law. Frozen boundary observables are fixed by the update. |
| `SU2BoundaryConditionedEntropy.no_strict_contraction` | Explicit actual boundary-conditioned stationary perturbation with positive finite relative entropy. | Existing decisive obstruction to GLOBAL strict entropy contraction for a frozen-boundary update. It does not forbid contraction of interior residuals or a sweep that updates the boundary. |
| `FourCubeBoundaryGibbsComparison.law_withDensity`, `law_integral`; `FourCubeBoundarySmoothPartition.actual_freeEnergy_contDiff` | Actual pinned four-cube full interior Gibbs law and smoothness for the specified boundary family at fixed coupling. | Supplies actual measure/domain data for a future score-covariance bridge. Fixed-coupling smoothness and density equivalence are not uniform estimates over beta or volume. |
| `FourCubeConditionalResponse.conditional_mixed_cubic`, `conditional_mixed_cubic_normalized_limit`; `FourCubeConditionalObstruction.no_uniform_quadratic_budget` | Actual one-retained-link Haar conditional, other31 retained interior links fixed at identity. Exact induced cubic, asymptotic coefficient4/5 after dividing by beta, and a failed quadratic budget. | Concrete nonlinear obstruction inside the real 4D geometry. It cannot be represented by a Gaussian Schur quadratic term alone. Do NOT identify this restricted conditional with the fully integrated32-link free energy. |
| `SparseBlockRelativeObstruction`, `SparseBlockGoodRegionObstruction`; `SU2MixedLinkBlocks` | Actual sparse Wilson Hessian budget counterexamples, including strict small-log caps; ordered derivatives retain commutator/gradient correction. | Smallness of a chart alone does not justify a fixed relative quadratic error or erase noncommutativity. |
| `PeriodicCoarseClosedReconstruction`, `PeriodicSingleBlockDecomposition`; `CubeSchurIntegral`, `CubeBoundaryKernelL2` | Linear closed-curl/Hodge decomposition, identified single-block Hessian, exact Gaussian chart integral and local-cutoff kernel convergence. | Valid linearized/quadratic tools. None identifies the full nonlinear Haar conditional block operator or gives global nonlinear scale transfer. |

## New actual-operator obstruction

`Foundation/PeriodicGaussianTransportObstruction.lean` uses the existing actual
periodic four-dimensional Wilson slice law, arbitrary actual ground data g,
and beta >=16777216. Let P be its native stationary transfer and N the unit,
centered, gauge-invariant local plaquette probe. Define the POINTWISE bounded
representative f of N and

    Q_g(f) = (g.value*g.normalizer)^(-1)
             * || integral dressed_g(U) f(U) Phi_beta(U) dHaar(U) ||^2.

`PeriodicGaussianTransferGram.native_gram` proves Q_g(f)=<PN,N>.
The new `probe_feature_loss` proves

    Q_g(f) + 3/(2401*PeriodicLogActionMoment.squareConstant) <= 1 = ||N||^2.

The constant is strictly positive. The new `no_isometric_gram_transport`
therefore excludes ANY linear isometry into ANY real Hilbert target whose
squared norm agrees with Q_g on the bounded measurable pointwise gauge-invariant
native core. Completeness or surjectivity of the target is not needed for this
negative result. Thus a Gaussian derivative/adjoint cannot be transported using
THIS feature map under the unitary-transport theorem's hypotheses.

This does not exclude a different true unitary or an operator intertwiner with
additional weights and domains. It also does not establish a gap on an invariant
plaquette sector: the witness is one probe and its iterates need not stay in that
sector. Global winding near-zero Dirichlet modes remain compatible with it.

## Concrete bottleneck and recommended next test

The useful transferable mechanism is an adjoint/residual formulation that keeps
actual boundary conditioning, not independent-noise reconstruction. For a fixed
finite boundary-dependent Wilson law mu_b proportional to exp(-beta*S_b) Haar,
the expected smooth-core identity is

    d_b E_b[f] = E_b[d_b f] - beta*Cov_b(f, d_b S_b).

This equation is a proposed NEXT bridge, NOT a newly proved theorem in this
checkpoint. Haar differentiation, quotient normalization and AE/L2 domains must
be established for the actual boundary variation. The generic bounded-tilt
`BoundedExponentialTiltResponse.expectation_hasDerivAt_zero` supplies an exact
covariance derivative for a bounded scalar tilt; it is usable only after the
actual score and domination hypotheses are checked, not by treating a nonlinear
boundary path as an affine tilt. The existing smooth actual partition and
nonlinear response results supply concrete tests.

The decisive remaining problem is quantitative: control the score-covariance
map or cross-block residual Gram operator in the ORIGINAL physical norms,
uniformly in admissible boundaries and through the intended scale/volume limit.
A quotient completed in its own output norm cannot supply that estimate. A
putative estimate must retain the known O(beta) cubic interaction or exhibit an
actual cancellation after full conditioning. Simply deleting that interaction,
commuting nonnested projections, replacing the native norm by a completion norm,
or importing Gaussian product identities fails this audit.

No existing theorem found in this audit resolves that bottleneck. Further work
should test this precise bridge or find a sharp counterexample to it, rather than
expand classical finite-volume estimates or build unrelated stochastic machinery.
All existing campaign priorities, original manuscripts and publication roles are
preserved. Verification and exact two-branch backup evidence are recorded in the
research ledgers and ignored checkpoint receipts.


## Follow-up1839: actual native conditional score and nonlinear Hessian bridge

The proposed score bridge above is now realized in
`Foundation/FourCubeConditionalScore.lean` on the EXISTING three-axis boundary
family, integrating ALL32 interior links against their actual normalized
product-Haar Wilson Gibbs density. This is not an arbitrary-boundary theorem,
a one-link restriction, or identification with the periodic stationary law.
For every real beta and parameters a,u in R^3, let

    D_u = fderiv(action)(a)[u],
    sigma_u = -beta*(D_u - E_a D_u),
    R_u(v) = <sigma_u,v>_{L2(mu_a)}.

The source is bounded by1 after dividing the action by144, so the existing
bounded exponential-tilt law supplies a genuine probability measure. Its
integrals are identified with the exact all32-link partition and expectation,
not a formal expectation symbol. The weight differentiates in the Banach
algebra of continuous observables on the fixed compact Haar state space.
There is no moving integration cutoff and no missing boundary flux term.

Exact declarations include:

- `expectation_hasDerivAt`, `native_derivative`, `nativeResponse_core`:
  directional differentiation of ACTUAL conditional expectations for continuous
  observables, and agreement with the bounded functional R_u on native L2.
- `moving_expectation_hasDerivAt`: a sup-norm differentiable observable family
  retains its DIRECT derivative E_a F'(0) as well as its score channel.
- `nativeResponse_norm`, `nativeScore_norm_square`, `native_bound_variance_iff`:
  the sharp ORIGINAL native norm criterion

      ||R_u||^2 = ||sigma_u||_2^2 = beta^2 Var_mu_a(D_u),
      |R_u(v)| <= C ||v||_2 for all native v
          iff beta^2 Var_mu_a(D_u) <= C^2       (C>=0).

  This is an exact criterion, NOT an established uniform bound. The score
  itself supplies an attaining test when nonzero. No induced covariance norm
  substitutes for the original L2 norm. No density theorem is silently used
  to claim a larger differentiability domain.
- `potential_mixed_covariance`, `actual_mixed_response`:
  the ordered integrated mixed derivative is

      d_v d_u F = beta E_a[D_v D_u action]
                  - beta^2 Cov_mu_a(D_u,D_v).

  The second variation is the actual derivative of the existing smooth action.
  No derivative interchange is assumed. `potential_eq_actual` identifies the
  unnormalized log partition with the pre-existing normalized boundary free
  energy up to a boundary-independent constant.
- `score_self_response`, `actual_diagonal_hessian`:

      d_u^2 F = beta E_a[D_u^2 action] - ||sigma_u||_2^2.

  The NEGATIVE score-energy correction is exact. Retaining only the quadratic
  geometry or importing an independent Gaussian completion would omit a real
  term unless another theorem established its cancellation or control.

This is classical score/fluctuation geometry instantiated and verified on the
actual nonlinear cell, rather than a novelty claim. It is the concrete positive
operator connection missing at1838; it does not undo the1838 nonisometric-Gram
obstruction. The previous report's proposed first-derivative bridge is now
proved on the stated continuous core. Uniform spatial/scale/volume estimates
remain OPEN, as does a physical mass gap.

Precise limits: R_u is a bounded functional on all native L2, agreeing with the
proved derivative on continuous tests. Differentiation for every arbitrary L2
representative along changing measures, a full closed boundary gradient and
adjoint, all boundary-link directions, a global conditional kernel for a larger
lattice, uniform physical-subspace frame bounds, and infinite-volume/continuum
limits are not established here. The sharp norm above is for the FULL native
L2 test space; the score is not asserted to lie in a specified physical
invariant sector. Fixed-coupling finiteness does not prove a uniform bound in
beta. Existing full-integral thermal Hessian/cubic obstructions remain intact.

Next substantive test: use the actual response/second-variation decomposition
to assess a physically scaled score-covariance estimate, retaining the existing
thermal nonlinear interaction. Check exact correspondence to the existing
mixed-Hessian direction convention before using those obstructions. Do not
infer score blow-up solely from Hessian blow-up: the direct second-variation
term also depends on beta and boundary data. Do not replace uniform estimates
with further formal identities or classical auxiliary infrastructure.

Next physical-domain test (UNPROVED): before demanding a full-native score bound, examine the score projected onto the relevant gauge-invariant observable space. At identity boundary, color-odd first source derivatives may cancel against invariant tests under the existing global SU2 conjugation/quarter-turn symmetries. Check this on the actual all32 law and stated boundary directions; do not assume the cancellation or infer a physical obstruction from an unprojected score norm. This is a concrete candidate for reuse of Hilbert residual/projection geometry, not a new campaign.


## Follow-up1840: actual invariant score projection at identity boundary

`Foundation/FourCubeInvariantScore.lean` resolves the symmetry candidate saved
at1839. For the actual all32-link conditional Gibbs family and EVERY real beta,
EVERY direction u in the existing three-source parameter space has

    Pi_H sigma_u(beta,0) = 0,
    R_u(beta,0)|_H = 0.

Here H is defined EXACTLY as the native L2 closure of the image of continuous
functions invariant under simultaneous global SU2 conjugation of the interior
links. It is not assumed to equal a full measurable invariant space or the
physical local-gauge sector. The proof does not claim a nonzero raw score norm.
For a continuous core test f with the stated invariance, the actual derivative
of E_{t u}[f] at t=0 is zero (`invariant_native_derivative`).

Exact mechanisms and declarations:

- `boundary_turn`, `fill_turn`, `action_turn`, `weight_turn` prove the
  quarter-turn transformation for the ACTUAL three-source boundary fill.
  No unproved identification with the older two-source construction is used.
- `weighted_turn`, `expectation_turn` use genuine product-Haar preservation,
  the existing actual action, and its normalized partition. They flip TWO
  parameter signs and keep the quarter-turn axis parameter fixed.
- `odd_response_zero` proves cancellation on an odd source plane;
  `coordinate_response_zero` covers each source coordinate. The actual smooth
  expectation's Frechet derivative and the existing finite-coordinate
  expansion extend it to arbitrary directions (`invariant_response_zero`).
- `invariantCore`, `invariantSpace`, `invariantSpace_le_kernel` specify the
  exact domain and extend the proved bounded response by continuity to its
  explicit closure. No missing density theorem is supplied as an assumption.
- `score_orthogonal`, `projected_score_zero` instantiate genuine Hilbert
  orthogonal-projection geometry on this native Wilson space. This is a valid
  reuse of the abstract geometry behind IBM conditional reconstruction; no
  IBM probability law, filtration, martingale, range-surjectivity theorem or
  Gaussian representation is transferred.

The independent checks include a nonconstant globally invariant continuous
trace observable (values1 and-1 on two actual states), zero actual derivative,
the ENTIRE restricted native response operator being zero on H, the actual
pair-flip expectation identity, invariance of xyz under those pair flips, and
coexistence with the existing POSITIVE full-interior thermal cubic limit
`FourCubeThermalMixedDifference.actual_scaled_third_difference_limit`.
The trace test is deliberately called globally invariant, not locally gauge
invariant; the existing endpoint-gauge obstruction to an open-link trace is
preserved. Thus H is not silently promoted to a physical-sector identification.

This is classical symmetry/selection geometry newly instantiated on the exact
conditional operator, not a novelty claim or a mass-gap proof. It refines the
quantitative target: an unprojected full-native score norm need not be the norm
relevant to invariant observations at the identity boundary. It does NOT say
that the raw score grows, vanishes, or has strictly larger norm; none of those
extra statements is proved here. First-order projected cancellation also does
not remove higher-order nonlinear interaction: simultaneous TWO-sign symmetry
permits xyz, and the previously verified nonzero thermal cubic remains.

Limits and next question: cancellation is at identity boundary for this
three-source family. Uniformity over beta at that ONE base point is not a
uniform boundary, scale-transfer or volume estimate. The functional R is a
BOUNDARY-VARIATION response, not the temporal stationary transfer P; no spectral
gap or zero Dirichlet energy follows. The actual changing-measure derivative
is proved on the continuous invariant core, while the bounded functional
vanishes on its specified closure. No arbitrary-L2 differentiability extension
or equality with a full physical gauge space is claimed. A boundary-dependent
observable F(t) still has the DIRECT derivative E[F'(0)] from1839's moving
formula, even when its base test is invariant and the score term cancels.

The next substantive problem is the surviving response away from identity in
physically justified boundary/observable domains and thermal normalization,
including moving Wilson observables and nonlinear mean second variations.
Reuse the known full-integral cubic/Hessian obstructions; do not infer a
physical obstruction from a raw, unprojected norm or a contraction theorem from
an isolated-base-point symmetry. No campaign transition or new gauge library.


## Follow-up1841: uniform native response on the thermal boundary scale

`Foundation/FourCubeThermalScore.lean` gives a quantitative positive transfer
beyond the identity-boundary cancellation. Write beta=1/t^2,
a_t=(t*x,t*y,t*z), e_y=the existing middle boundary direction, and let R be
1839's native response functional. For each fixed amplitude ball
x^2+y^2+z^2<=R0 there is a finite C_R0>0 and ONE punctured neighborhood of t=0
such that, simultaneously for all those amplitudes,

    ||R_(1/t^2,a_t,t e_y)||^2 <= C_R0.

`uniform_middle_response` is in the ORIGINAL L2(mu_(1/t^2,a_t)) operator norm,
not an output-induced completion or a supremum-only assertion. The common
neighborhood permits amplitudes depending on t within the stated ball.
`amplitude_derivative` identifies the functional with the actual derivative at
h=0 of E_(1/t^2,(t*x,t*(y+h),t*z))[f], for each continuous observable f.
The bounded functional is defined for every native L2 input; changing-measure
differentiation of every arbitrary L2 representative is not assumed.

The proof retains the nonlinear action and exact normalizers:

1. `exponential_partition` proves the actual all32-law identity

       E_(beta,a) exp((2/3)*beta*S_a)=Z_(beta/3,a)/Z_(beta,a).

   `scaled_action_mean` bounds beta E S by3/2 times this actual exponential
   moment. Continuous observables give genuine native integrability.
2. `moving_exponential_bound` uses the existing boundary action comparison,
   beta*boundaryCost<=216*R0, and the verified equality between the full32
   partition and the pole-reduced reference partition. It obtains

       E exp((2/3)*beta*S_a) <= exp(720*R0)*Q(t),
       Q(t)=Z_ref((1/9)/t^2)/Z_ref(3/t^2).

   `partitionRatio_tendsto` proves that Q has the finite positive limit
   (sqrt(1/9)^(-93))/(sqrt(3)^(-93)) using the EXISTING verified reference
   Gaussian partition asymptotics. No reference-law L2 identity replaces the
   actual native expectation. `uniform_scaled_action` yields a common bound
   on beta E_mu S over the amplitude ball.
3. `one_axis_control` proves the exact SU2 trace derivative bound through the
   genuine unit-quaternion representation and circle identity. Noncommutative
   products are only cyclically rotated inside the trace, not commuted as group
   elements. `ribbon_defect_le_action` places the chosen ribbon defect below
   the FULL nonnegative action. The exact residual-action identity then gives

       (D_y S_a(s))^2 <= 2*S_a(s)

   for EVERY interior configuration s, with all32 links arbitrary. This is
   NOT the older one-retained-link restriction with the other31 links fixed.
   Only the middle boundary source changes one ribbon; no factor2 estimate for
   the two cap-source directions is silently asserted.
4. `middle_thermal_score_bound` combines this pointwise inequality, genuine
   native integration, Var(D)<=E(D^2), and1839's exact score energy to prove

       ||sigma_(1/t^2,a_t,t e_y)||^2 <= 2*beta*E_mu S_a.

   Together with ||R||=||sigma|| this proves the uniform response estimate.

Independent checks cover the exact cosine trace derivative, direct actual-law
exponential integral, a common bound |R(v)|<=K||v|| for ALL original-native
inputs, and coexistence with the existing nonzero all-interior thermal cubic
limit. Thus bounded rescaled first response does not erase nonlinear boundary
interaction or contradict the unscaled Hessian obstructions.

Limits: C_R0 is coarse and fixed-cell dependent; neither C_R0<1 nor a
volume-uniform bound is proved. The power93 and the comparison factors are
specific to the verified reference cell. The boundary scale t=beta^(-1/2) is
justified by that Gaussian thermal analysis, not identified with physical
spatial distance or time. Only the middle source direction in the existing
three-axis family is covered; arbitrary boundary fields, all source channels,
block composition, infinite-volume/continuum limits and a physical mass gap
remain OPEN. A boundary-dependent observable still has the direct derivative
term from1839. Partition factors must also be retained: the existing
FourCubeScalarCalibration counterexamples already show that identical
normalized conditional laws do not determine free energy.

This is an actual operator-calculus/partition-asymptotic connection, assembled
from classical ingredients and existing verified cell machinery, with no claim
of mathematical novelty. It supplies regularity at the thermal normalization;
it does not settle multiblock coercivity. A concrete next test is whether it
controls genuine common-space distances between nearby boundary-conditioned
laws via their actual square-root Haar densities. Any such half-density/Fisher
or Hellinger bridge must be constructed explicitly; the old Gaussian Gram map
remains nonisometric, and scalar calibration still prevents recovering absolute
coarse free energy from normalized-law distances alone.
