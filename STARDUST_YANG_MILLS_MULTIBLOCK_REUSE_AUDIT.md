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
