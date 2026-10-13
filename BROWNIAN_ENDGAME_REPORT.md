# Brownian endgame: verified campaign report

Repository: C:/OperatorDerivativeRewrite. Date: 2026-10-12.
Starting HEAD: aaace0f09965d2f3b13b9ed6f536c836b8e1c49f.

## Verdict and strongest results

Substantial prerequisites for arbitrary nonlinear stopped-cylinder Ito are proved, including genuine common-mesh stochastic and Hessian convergence. The final arbitrary nonlinear stopped-cylinder Ito identity is NOT yet proved. The existing complete scalar C2, finite-rank C1,2, additive stopped-cylinder and mixed quadratic stopped-cylinder formulas remain unchanged.

All new coordinate families are arbitrary finite types; zero dimension, zero/repeated observation horizons and singular covariance are allowed. No independent-coordinate assumption is introduced. The new smooth fields require C2 Phi and bounds on the actual first/second Frechet derivatives. The new Taylor limit requires C3 Phi with an explicit uniform trilinear bound on the derivative of its actual Hessian. Neither integrability nor error convergence is assumed.

## Verified commits

1. e204a3bee012cb720b43504f59b30ddc3b0a7dbc: nonlinear stopped-coordinate L2 continuity and predictable approximation. Full build 4,172 jobs; 2,749 axiom checks.
2. b7d19ebe81771439250b554fb7bd09b7783e3ca1: genuine smooth fields and covariance-Hessian geometry. Full build 4,176 jobs; 2,785 axiom checks.
3. aef7b09a5a792f687d26bf25b94402c86be4abbe: mixed weighted stopped quadratic variation. Full build 4,177 jobs; 2,804 axiom checks.
4. 3c25968db6710409e13ed4117d95de3eb61cb329: multivariate Taylor and Gaussian remainder convergence. Full build 4,179 jobs; 2,829 axiom checks.
5. Commit containing this report: common refining meshes and simultaneous stopped gradient/Hessian approximation. Full build 4,181 jobs; 2,846 axiom checks. Its exact hash is in the final response and Git history.

Each milestone passed the complete Lake build, separate Foundation/AxiomAudit.lean execution, and explicit public declaration type checks. All 118 new public definitions/theorems are included in the audit. The only transitive axioms are propext, Classical.choice and Quot.sound. No earlier theorem body or statement was edited. New declarations have ordinary Lean proofs; no custom axioms, sorry, admit, or unsafe declarations were added. Existing style warnings remain nonblocking.

Lean 4.34.1 and Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612 are unchanged. Original OperatorDerivative.lean SHA256: 9B8BA956878B80F3C2AC8F239D335C0F49582C88D0693E63554F481ACBEBDF29. Original OperatorDerivative.tex SHA256: FCA841CCA43DC712AAD2FCF02CB04010ABD7CFCDA4A231022D58A3B23D3BB983. The twelve pre-existing unrelated untracked documents are preserved. No push.

## Objectives A--G

| Objective | Status | Precise scope |
|---|---|---|
| A. Arbitrary nonlinear stopped cylinders | PARTIALLY VERIFIED | Actual nonlinear L2 composition, adapted derivative fields, strict stopping-indicator identification, mixed weighted QV, C3 Taylor remainder control and same-mesh stochastic/drift convergence are proved. Final Ito assembly remains open. |
| B. Covariance-Hessian engine | PARTIALLY VERIFIED | Actual first/second derivatives, Hessian symmetry, positive semidefinite finite covariance and contraction sum_a H[k_a,k_a] = sum_ij H_ij C_ij. A stochastic Ito theorem for general deterministic L2 kernels is open. |
| C. General nonseparable C1,2 | OPEN beyond prior finite-rank result | GaussianFiniteRankTimeIto.finite_rank_ito remains the strongest complete time-dependent theorem. No simultaneous approximation for arbitrary C1,2 is claimed. |
| D. Corrected operator-functional Ito | PARTIALLY VERIFIED, general claim OPEN | Prior corrected scalar C2 and restricted cylinder formulas remain. Pure adjointness does not imply diffusion chain rules. New general operator-functional theorem not asserted. |
| E. Full D versus J* | VERIFIED prior restricted identities; extension OPEN | GaussianC2OperatorCorrection.terminal_adjoint retains the genuine drift projection. Full-D equality requires independent membership, explicitly present in full_derivative_projection. No new full-D cylinder-domain claim is inferred. |
| F. Second-order closure | OPEN | No closability of a separate functional Hessian or trace operator has been deduced from closability of D. |
| G. Nonclassical readiness | VERIFIED assessment only | Reuse boundaries and missing model-specific arguments below. No new nonclassical calculus theorem. |

## Exact remaining nonlinear-cylinder assembly

For Phi C3 with the first/second bounds of GaussianStoppedSmoothFields and third trilinear bound of FiniteTaylorRemainder:

1. Construct a monotone common sequence of partitions of [0,T] containing every min(T,r_i), with mesh tending to zero. Geometric existence remains to be formalized; it is not an assumed stochastic approximation.
2. Identify GaussianStoppedMeshFields.gradientSum and hessianSum with the first-order and covariance-weighted second-order terms in the finite Taylor sum on that partition. The capped sums sample at min(left,r_i) or min(left,r_i,r_j); verify that replacing these times by left changes no term when its stopped increment/cell length is nonzero, and that the remaining terms vanish.
3. Sum FiniteTaylorRemainder.taylor_identity along cells and telescope Phi(X_right)-Phi(X_left). Use the actual L2 endpoint class from GaussianStoppedComposition.value. Identify the residual as a finite sum of the actual rawMixedError terms plus remainderSum, with all representatives and coefficients checked.
4. Pass to limits using GaussianStoppedMeshFields.gradientSum_tendsto and hessianSum_tendsto, GaussianStoppedQuadraticVariation.rawMixedError_sq_tendsto, and GaussianStoppedTaylor.remainderSum_tendsto. This is the first missing complete Ito theorem; none of those separate limits is itself that identity.
5. Only afterward apply the bounded J* to derive the cylinder drift-projection correction. A projected FULL-D statement separately needs domain membership and actual derivative identification for Phi(X_T).

The natural initial class is arbitrary C3 with bounded actual first three derivatives (Phi itself need not be bounded). A C2 extension needs a simultaneous multivariate smoothing/limit theorem; the scalar Steklov proof is not automatically such a theorem. The general time-dependent extension needs simultaneous control of values, spatial derivative, time derivative and Hessian drift; finite-rank algebraic decompositions do not prove that density.

## Operator-first interpretation and counterdiagnostics

Foundation/GaussianPredictableAdjoint.lean:51 proves predictableAdjoint_eq_projected_derivative only on the genuine full derivative domain. Foundation/GaussianC2OperatorCorrection.lean:21 gives the actual scalar terminal identity J*f(B_T)=running f' + (1/2)J*(Hessian drift). Foundation/GaussianSmoothProjectionDiagnostic.lean:69 preserves the bounded sine counterdiagnostic. No terminal representer is substituted for a running derivative in the new proofs.

An abstract adjoint pair alone cannot imply a local diffusion chain rule. The already proved PoissonAdjoints.maximalDifference_adjoint_eq_maximalDivergence and maximalDivergence_adjoint_eq_maximalDifference coexist with PoissonPolynomialExamples.ordinary_chain_rule_fails (Foundation/PoissonPolynomialExamples.lean:153). For the centered count, D(X^2)=2X+1 and DX=1. The additional jump term is substantive. This is a verified counterexample to a universal ordinary chain rule based only on the adjoint architecture, not a defect in the Gaussian construction.

The new finite-coordinate derivatives are actual Frechet derivatives of Phi, while the full Malliavin derivative differentiates Gaussian noise and the bounded predictable adjoint represents terminal random variables. A path-functional calculus introduces further nonanticipative regularity and derivative structures. Cont--Fournie's [Functional Ito calculus and stochastic integral representation of martingales](https://arxiv.org/abs/1002.2446) explicitly develops path-functional directional derivatives and an associated representation; their [change-of-variable paper](https://arxiv.org/abs/1004.1380) treats nonanticipative functionals on path space. The present finite-cylinder prerequisites do not formalize that full path-space theory. No historical or mathematical novelty claim is made. A Dirichlet-form interpretation likewise needs a separately justified diffusion/locality chain calculus and correctly specified generator/energy domain; a closed adjoint pair by itself supplies neither.

## Readiness map (assessment, not new theorems)

| Track | Exact reusable infrastructure | Required model-specific proof before transfer |
|---|---|---|
| Fractional Brownian / Gaussian Volterra | GaussianDeterministicVolterra.volterraProcess_isGaussianProcess (123), volterraProcess_covariance (131), profileIntegral_derivative (72); actual isonormal and full Gaussian derivative infrastructure; FiniteCovarianceHessian.covariance_hessian_contraction | Construct and estimate the intended kernels in TimeHilbert; prove their covariance and regularity. The established Gaussian law/covariance theorem does not prove a martingale bracket, Brownian QV, or a semimartingale property. For a nonsemimartingale model, specify and prove the appropriate integration/chain theorem and correction rather than copying Brownian dt. |
| Gaussian OU / Bakry--Emery | GaussianFisherDecay.fisherInformation_decay (369); GaussianEntropyDissipationProof.hasDerivAt_entropy_dissipation (453); GaussianLogSobolevFull.gaussian_logSobolev_of_hasDerivAt (231); full Gaussian derivative/adjoint and Hermite theory | One-dimensional Gaussian entropy/LSI is already proved. A multivariate or abstract curvature-dimension theorem requires its actual semigroup, generator domain, invariance, Gamma/Gamma2 calculus and approximation. Neither Brownian Ito nor formal adjointness supplies those assumptions. |
| Hilbert stochastic convolutions / fractional SPDE | BochnerL2Fubini.integral_eq_of_slices; GaussianContinuousStochasticFubini.integral_weighted_field (147); finite covariance-Hessian contraction; independently defined predictable integral and Gaussian/Bochner L2 spaces | Establish the intended Hilbert-valued integral/noise, kernel Hilbert--Schmidt bounds and convolution integrability. Prove simultaneous finite-dimensional approximation and trace convergence for the actual Hessian. A finite covariance contraction is not an infinite-dimensional trace theorem or a fractional-SPDE existence proof. |
| IBM observable compression / singular correction spaces | General adjoint framework; GaussianPredictableAdjoint.representation_residual_orthogonal (73) and representation_norm_decomposition (77) for the existing predictable projection; explicit Gaussian drift-projection correction | No IBM-specific observable map, induced measure, compression projection, singular correction norm or compatible graph domain is constructed here. Specify these first, then prove representative independence and a compression/derivative commutator on an independent core. Prove closability or identify its failure in the chosen correction space. Existing predictable projections cannot be relabelled as IBM observable compression. |

## New declaration inventory

Paths below are relative to C:/OperatorDerivativeRewrite. Every name has prefix OperatorDerivativeRewrite.Foundation. followed by its module namespace. Definitions and helper lemmas are included for audit completeness; the preceding sections identify the substantive results.
### Foundation/GaussianStoppedComposition.lean

- Line 18: GaussianStoppedComposition.coordinates
- Line 21: GaussianStoppedComposition.vector
- Line 24: GaussianStoppedComposition.vector_coeFn
- Line 35: GaussianStoppedComposition.vector_continuous
- Line 41: GaussianStoppedComposition.coordinates_stronglyMeasurable
- Line 45: GaussianStoppedComposition.coordinates_past
- Line 53: GaussianStoppedComposition.coordinates_memLp
- Line 60: GaussianStoppedComposition.centered_lipschitz
- Line 66: GaussianStoppedComposition.value
- Line 69: GaussianStoppedComposition.value_coeFn
- Line 79: GaussianStoppedComposition.value_memLp
- Line 83: GaussianStoppedComposition.value_continuous
- Line 87: GaussianStoppedComposition.value_past
- Line 93: GaussianStoppedComposition.boundedValue
- Line 98: GaussianStoppedComposition.boundedValue_coeFn
- Line 103: GaussianStoppedComposition.boundedValue_continuous
- Line 129: GaussianStoppedComposition.boundedValue_past
- Line 136: GaussianStoppedComposition.boundedField
- Line 140: GaussianStoppedComposition.boundedField_slices
- Line 146: GaussianStoppedComposition.bounded_stochastic_sum_tendsto
- Line 152: GaussianStoppedComposition.bounded_drift_sum_tendsto

### Foundation/FiniteCovarianceHessian.lean

- Line 14: FiniteCovarianceHessian.direction
- Line 16: FiniteCovarianceHessian.partialDerivative
- Line 19: FiniteCovarianceHessian.hessian
- Line 22: FiniteCovarianceHessian.mixedPartial
- Line 25: FiniteCovarianceHessian.direction_norm
- Line 27: FiniteCovarianceHessian.coordinate_expansion
- Line 31: FiniteCovarianceHessian.differential_expansion
- Line 36: FiniteCovarianceHessian.hessian_expansion
- Line 50: FiniteCovarianceHessian.line_hasDerivAt
- Line 57: FiniteCovarianceHessian.line_second_hasDerivAt
- Line 71: FiniteCovarianceHessian.partial_contDiff_one
- Line 75: FiniteCovarianceHessian.mixedPartial_continuous
- Line 80: FiniteCovarianceHessian.partial_bound
- Line 86: FiniteCovarianceHessian.mixedPartial_bound
- Line 96: FiniteCovarianceHessian.covariance
- Line 99: FiniteCovarianceHessian.covariance_symmetric
- Line 102: FiniteCovarianceHessian.covariance_nonneg
- Line 126: FiniteCovarianceHessian.covariance_hessian_contraction
- Line 142: FiniteCovarianceHessian.partial_hasFDerivAt
- Line 148: FiniteCovarianceHessian.mixedPartial_eq_fderiv_partial
- Line 154: FiniteCovarianceHessian.mixedPartial_symmetric

### Foundation/GaussianStoppedSmoothFields.lean

- Line 21: GaussianStoppedSmoothFields.functionLip
- Line 24: GaussianStoppedSmoothFields.gradientValue
- Line 28: GaussianStoppedSmoothFields.hessianValue
- Line 32: GaussianStoppedSmoothFields.gradientValue_coeFn
- Line 36: GaussianStoppedSmoothFields.hessianValue_coeFn
- Line 40: GaussianStoppedSmoothFields.gradientValue_continuous
- Line 44: GaussianStoppedSmoothFields.hessianValue_continuous
- Line 48: GaussianStoppedSmoothFields.gradientValue_past
- Line 52: GaussianStoppedSmoothFields.hessianValue_intervalIntegrable
- Line 57: GaussianStoppedSmoothFields.gradientField
- Line 62: GaussianStoppedSmoothFields.hessianDrift
- Line 66: GaussianStoppedSmoothFields.gradientField_slices
- Line 81: GaussianStoppedSmoothFields.gradient_steps_tendsto
- Line 89: GaussianStoppedSmoothFields.hessian_steps_tendsto
- Line 104: GaussianStoppedSmoothFields.gradientField_slices_strict

### Foundation/GaussianStoppedQuadraticVariation.lean

- Line 18: GaussianStoppedQuadraticVariation.active
- Line 20: GaussianStoppedQuadraticVariation.stopped_increment
- Line 29: GaussianStoppedQuadraticVariation.stopped_time_increment
- Line 37: GaussianStoppedQuadraticVariation.active_mul
- Line 40: GaussianStoppedQuadraticVariation.min_aligned
- Line 48: GaussianStoppedQuadraticVariation.covariance_cell
- Line 56: GaussianStoppedQuadraticVariation.weight
- Line 60: GaussianStoppedQuadraticVariation.weight_measurable
- Line 65: GaussianStoppedQuadraticVariation.weight_bound
- Line 73: GaussianStoppedQuadraticVariation.weight_memLp
- Line 81: GaussianStoppedQuadraticVariation.weight_energy
- Line 91: GaussianStoppedQuadraticVariation.mixedError
- Line 97: GaussianStoppedQuadraticVariation.rawMixedError
- Line 103: GaussianStoppedQuadraticVariation.mixedError_coeFn
- Line 126: GaussianStoppedQuadraticVariation.mixedError_mesh_bound
- Line 133: GaussianStoppedQuadraticVariation.mixedError_tendsto
- Line 143: GaussianStoppedQuadraticVariation.rawMixedError_memLp
- Line 150: GaussianStoppedQuadraticVariation.rawMixedError_integral_sq
- Line 164: GaussianStoppedQuadraticVariation.rawMixedError_sq_tendsto

### Foundation/FiniteTaylorRemainder.lean

- Line 16: FiniteTaylorRemainder.line
- Line 18: FiniteTaylorRemainder.thirdDerivative
- Line 22: FiniteTaylorRemainder.remainder
- Line 25: FiniteTaylorRemainder.line_contDiff
- Line 29: FiniteTaylorRemainder.third_line
- Line 43: FiniteTaylorRemainder.third_line_bound
- Line 50: FiniteTaylorRemainder.remainder_bound
- Line 64: FiniteTaylorRemainder.remainder_continuous
- Line 75: FiniteTaylorRemainder.taylor_identity

### Foundation/GaussianStoppedTaylor.lean

- Line 18: GaussianStoppedTaylor.activeVector
- Line 20: GaussianStoppedTaylor.activeVector_norm_le
- Line 25: GaussianStoppedTaylor.vector_increment
- Line 33: GaussianStoppedTaylor.vector_increment_norm_le
- Line 44: GaussianStoppedTaylor.rawRemainder
- Line 48: GaussianStoppedTaylor.rawRemainder_measurable
- Line 54: GaussianStoppedTaylor.rawRemainder_bound
- Line 61: GaussianStoppedTaylor.rawRemainder_memLp
- Line 67: GaussianStoppedTaylor.remainderL2
- Line 69: GaussianStoppedTaylor.remainderL2_coeFn
- Line 72: GaussianStoppedTaylor.remainderL2_norm_sq
- Line 81: GaussianStoppedTaylor.remainderL2_mesh_bound
- Line 94: GaussianStoppedTaylor.remainderSum
- Line 99: GaussianStoppedTaylor.remainderSum_coeFn
- Line 113: GaussianStoppedTaylor.remainderSum_mesh_bound
- Line 126: GaussianStoppedTaylor.remainderSum_tendsto

### Foundation/GaussianRefiningPartitions.lean

- Line 10: GaussianRefiningPartitions.covers
- Line 23: GaussianRefiningPartitions.step_tendsto
- Line 52: GaussianRefiningPartitions.step_bound
- Line 64: GaussianRefiningPartitions.partition_tendsto
- Line 124: GaussianRefiningPartitions.drift_sum_tendsto
- Line 150: GaussianRefiningPartitions.predictableStep
- Line 156: GaussianRefiningPartitions.predictableStep_tendsto
- Line 167: GaussianRefiningPartitions.integral_step_tendsto
- Line 179: GaussianRefiningPartitions.integral_step_coeFn
- Line 193: GaussianRefiningPartitions.cap_mesh_bound
- Line 204: GaussianRefiningPartitions.cap_monotone
- Line 207: GaussianRefiningPartitions.capped_drift_sum_tendsto
- Line 221: GaussianRefiningPartitions.capped_integral_step_tendsto

### Foundation/GaussianStoppedMeshFields.lean

- Line 18: GaussianStoppedMeshFields.gradientSum
- Line 22: GaussianStoppedMeshFields.hessianSum
- Line 27: GaussianStoppedMeshFields.gradientSum_tendsto
- Line 40: GaussianStoppedMeshFields.hessianSum_tendsto
