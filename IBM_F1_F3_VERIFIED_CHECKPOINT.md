# IBM F1–F3 verified stopping point — discovery1107

The focused IBM F1–F3 campaign reaches its verified stopping point on October19,2026. This checkpoint preserves the actual stochastic constructions and records their exact domains and topologies. After its audited Git commit and private-backup verification, the queued A(4) campaign is released. Its first task is to read and inventory every file in `ResearchSources/a4` before starting new proofs. A(2) and the final multichannel pseudoprocess campaign remain queued afterward; October31 remains the research stopping date.

The preserved primary manuscript is `ResearchSources/ibm/EJP2605-044RA0.pdf`, SHA256 `5A91914A535AD19BDDF219D7A9AB9F8B5F20A52DD4EC6ED7333AA80B403182BE`. The requested Incoming filename with `(2)` was absent; identity with that unavailable version is not asserted. The available PDF has placeholder journal metadata. Manuscript assertions never supply Lean axioms. Its precise F1/F2/F3 targets were rechecked on pages12,19,22; the mollifier assumptions were checked on pages3–4. The original source is unchanged.

## F1: full continuum cross-sector dual closure

For every real Schwartz test g, shift a and finite horizon T, the actual full boundary/local-time-plus-curvature correction has a profile-independent limit in a genuine common dual norm. The profile may be any compact nonnegative mass-one C3 function; therefore all even compact smooth profiles allowed by the paper are included. The parameter is the entire positive-width filter, not merely a particular null sequence.

On the actual outer-clock/source-valued Gaussian L2 space, K=P0+N_clock^-1 is injective and self-adjoint with dense image. `IBMCommonClockDual.smoothing_denseRange`, `dual_bound`, `dual_attainment`, `dualNorm_le_iff` prove that norm(KF) is precisely the operator norm of the functional Kpsi -> inner(F,Kpsi) on the dense test image equipped with norm(psi). The preimage is unique. This is a verified dual interpretation, rather than an unsupported name for a weaker estimate.

`IBMDilatedPredictableLimit.field_continuum_tendsto` proves strong convergence of the ACTUAL regularized signed-slope integrands in the ORIGINAL `GaussianSourceClockIto.Domain T`. Its limit `fieldLimit g a T` has no profile parameter. `correction_continuum_tendsto` proves strong joint-L2 convergence of the ACTUAL K-smoothed full corrections to `correctionLimit g a T`, also independent of profile. `stochastic_reconstruction` identifies

    K endpointLimit = actualSourceClockIto(fieldLimit)+correctionLimit.

The finite stochastic identity, original predictable-domain realization, time-section identification, integrable uniform C_g/sqrt(t) energy bound and strong time-L2 convergence are proved, not assumed.

`IBMDilatedDualClosure.correction_uniform_rectangular_tail` proves the original raw correction's explicit rectangular source/clock chaos sums have uniformly small tails in this dual norm for all sufficiently small widths and independently large source and clock cutoffs. `correction_dual_uniform` gives convergence uniformly on the entire unit test ball. `raw_clock_projection_tendsto` and `raw_block_tendsto` give ordinary joint-L2 convergence for every fixed clock sector and every fixed source/clock block, with the exact inverse K-sector weights. These results meet OpenProblem7.1's request for a global cross-sector dual norm and limit. Its condition(4.2) subclass is covered by the stronger all-Schwartz statements.

This does not assert ordinary L2 convergence of the unregularized full correction summed over all clock sectors. Nor is an equivalence with the separate physical spatial H^-1 topology assumed or claimed.

## F2: literal boundary-layer random-functional L2 limit

Let U_rho be the actual Gaussian scenery convolution, V_rho=norm(U_rho)^2, and Q_j(rho,r)=E_source[g^(j)(a+U_rho(r))]. For every compact mass-one C2 kernel, `IBMCompactVarianceGeometry.variance_second` proves V_rho''=2rho globally. `IBMDilatedVarianceGeometry.covariance_bracket` proves the original Gaussian bracket equals rho. `IBMCompactOriginalBoundary.originalResidual_literal` identifies the ACTUAL two-term curvature expectation minus Q4/4, and `originalResidual_identity` derives its exact coefficient

    b_rho(r)=rho(r)*Q2(rho,r)+((V_rho'(r)^2-1)/4)*Q4(rho,r).

`IBMCompactSourceAverage` constructs each Q as a literal expectation on the actual source measure. Its shrinking-support error is verified. `IBMCompactWeightedBoundary.weightedClass_continuum_tendsto` proves the scenery-weighted occupation integral converges in ordinary clock L2. `IBMCompactBoundaryRemainder.integralClass_continuum_tendsto` proves the remaining bounded layer integral vanishes in that same topology, using the original Brownian zero-occupation theorem and actual time/sample dominated convergence.

For every compact even nonnegative mass-one C2 profile, every Schwartz g, shift a and finite horizon T, `IBMCompactOriginalBoundary.originalPathIntegral_continuum_tendsto` proves

    integral_0^T b_rho_epsilon(abs(Y_s)) ds -> g''(a)*BrownianTanakaResidual.mass(T)

in ORDINARY clock L2 over the entire positive-width filter. Both measurability and MemLp of this literal random time integral are verified. The mass is the already constructed Tanaka mass, with its original normalization; the curvature drift's prefactor1/2 must still be applied when this boundary layer is inserted into the full Ito identity. No spatial local-time density is postulated. This establishes the random-functional limit requested by OpenProblem6.4, including all manuscript profiles, rather than only its expectation or the old concrete bump subsequence.

## F3: dense maximal intrinsic core and actual adjoint

The manuscript's maximal core is IBM-measurable L2 intersected with the actual source and clock derivative domains. `IBMIntrinsicCoreDensity.core_closure_eq_intrinsic` proves its closure equals the actual IBM-observable L2 space. This uses genuine IBM-observable time averages and the established source/clock graph domains, not unproved measurability of mollified point observations.

`IBMJointIntrinsicDerivative.jointDerivative_closed` and `jointDerivative_dense` prove the actual joint intrinsic derivative is closed and densely defined. Its Hilbert adjoint `jointDivergence` therefore exists on its naturally determined domain. `ambient_pair_conditional_divergence` proves the manuscript's conditional projected-sum formula on the lifted ambient source-divergence domain. It does not identify that lifted domain with the entire intrinsic adjoint domain. The paper's suggestion of nondensity based on point-observation regularity is therefore not a proof of nondensity and does not survive this constructed core.

No claim is made that an individual unmollified IBM point observation has a joint clock-Sobolev derivative. A dense core does not require that assertion.

## Retained results and explicit limits of the freeze

The library's actual independent continuous scenery/clock construction, IBM composition, finite-mollifier full reflected stochastic identity, source-resolved projections, polynomial/Schwartz kernel tests and all pseudoprocess verification remain preserved. The distinct first-source physical Bessel-potential result `IBMSchwartzPhysicalReflectedIto.wholeClass_tendsto` proves convergence of its actual whole physical first-source kernel in clock-L2(H^-1) for the verified concrete bump sequence. This freeze does not silently enlarge that particular n-indexed physical-coordinate theorem to every profile, or equate it with the new common clock-number dual norm. The focused F1–F3 targets do not require such an equivalence.

The paper's additional directions—an unmollified distributional clock derivative, a general intrinsic chain/product rule, second intrinsic energy/PDE identification, and finer spatial tensor-dual sector estimates—are not asserted solved. They are deferred research directions, not hidden assumptions in the completed F1–F3 theorems. This is a stopping point for the focused campaign, not a claim that every sentence or future direction in the manuscript has been formalized.

## Verification and preservation

Pinned Lean4.34.1 full root build:5729 jobs passed. Root transitive axiom audit:31807 safe Foundation declarations passed, using only propext, Classical.choice and Quot.sound. All46 new public types in discovery1107 were printed and reviewed. The source manifest covers1675 Foundation/root Lean files. All107 archived manuscript hashes and43 Incoming files/42 distinct hashes remain unchanged. No manuscript, pinned dependency, goal state or unrelated draft is modified. The exact audited Git commit and verified private remote IDs are saved after commit in `.lake/stardust-1107-pending.json`; this document belongs to that immutable research checkpoint.
