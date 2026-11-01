# Cauchy operator campaign — initial source and reuse audit

ACTIVE by the user's November 1, 2026 instruction to move to the next objective.
The source is *The Stochastic Cauchy Operator: Operator Factorization Meets
Complex Analysis*, dated January2026. Its subject is a complex-Gaussian
projection operator, not a Cauchy-distributed Lévy process. The later generalized
Cauchy/stable-process campaign remains separately queued.

## Original source and review scope

`ResearchSources/cauchy/stochastic_cauchy_operator_v4.tex`,50050 bytes,
SHA256 `3154d5c35ac6c1a1c984847cda8f94d953e29ae783f4f4536933f8c973033e8c`.
This matches the preserved1292 inventory and new
`STARDUST_CAUCHY_SOURCE_INVENTORY.json`. No original bytes were changed.

Activation inspected the title/abstract, section/theorem labels, introductory
claims and the construction/decomposition/idempotence passages around original
lines379–501. It did NOT read every proof or certify the manuscript. Literature
and novelty audits remain pending; no novel result is claimed. This is
mathematical source-claim analysis, not publication or editorial maintenance.

## First central obligation: the operator identity and its domain

The manuscript defines C=delta_Z Pi^(1,0) Pi_A D_Z and claims an orthogonal
decomposition, idempotence, energy identities, analytic-functional and fBM
extensions, and conformal covariance. Original `thm:idempotent` near line469
uses “By Tier2, D_Z(delta_Z(u))=u for adapted u.”

The following existing VERIFIED theorems give a precise route to audit that
step. They do not yet constitute a formal repair of the entire complex source.

| Existing declaration | Exact reusable content / limitation |
| --- | --- |
| `GaussianPredictableAdjoint.predictableAdjoint_integral` | The actual bounded predictable adjoint is a left inverse of the actual real Gaussian predictable Itô isometry. It is NOT the unprojected closed derivative. |
| `GaussianPredictableAdjoint.predictableAdjoint_eq_projected_derivative` | Equality with the predictable projection of the closed derivative on its ACTUAL derivative domain. Retain that domain; do not erase the projection. |
| `GaussianPredictableDomainGap.representation_without_full_derivative`, `terminal_representation_without_full_adjoint` | Actual represented Brownian L2 targets can lie outside the full derivative/adjoint domain. A universal unprojected derivative-of-integral expression needs more than isometry. The complex/two-source embedding still requires its own exact realization. |
| `GaussianSensitivityGeometry.sensitivity_energy`, `correction_orthogonal_predictable` | On the stated predictable Sobolev graph, the true derivative has an extra orthogonal sensitivity contribution. It is not generally identified with the original integrand alone. |
| `GaussianProjectedDerivativeClosure.projectedGraph_closure` | Closure of the projected full derivative graph is the bounded predictable-adjoint graph. This is a candidate rigorous way to extend a projected reconstruction operator beyond the full derivative core. |
| `HilbertRepresentation.predictableAdjoint_isometry_apply`, `representationProjection_idempotent`, `representation_norm_decomposition` | Closed-range Hilbert projection and residual geometry for a genuine real Hilbert isometry. They neither construct a circular complex Brownian process nor identify stochastic direction projections with terminal holomorphic function spaces. |
| `ComplexL2Isometry.lift`, `norm_sq_parts`; `GaussianComplexHorizonIto.integral_norm`, `integral_trim_ofReal` | Verified norm-preserving complexification of the existing real Brownian integral. This is a complex-valued integrand integral against its original real noise, NOT automatically integration against two independent circular complex Brownian components. |

**Initial focus:** independently test the manuscript's unprojected identity,
then construct the strongest valid bounded adjoint/projection formulation with
its exact native domains and remainder. Test whether the asserted holomorphic
projection preserves the predictable subspace and the divergence domain.
Isometry alone must not be substituted for a full derivative inverse.

## Further exact questions, not conclusions

- The formulas Pi^(1,0)(u_X,u_Y)=(u_X-i u_Y)/2 and Pi^(0,1)=(u_X+i u_Y)/2
  need an explicit target embedding and induced Hilbert norm. The described
  eigenspaces contain PAIRS (h,-ih) and (k,ik). Audit normalization, signs,
  complex versus real scalar structure, actual orthogonality and domains.
- Distinguish a stochastic integral-direction range from a terminal holomorphic
  Gaussian/Hardy function space. No equality of these spaces is proved here.
- The introductory generic smooth-domain Cauchy/orthogonal-Hardy assertion,
  fBM Tier2 classification, covariance corrections, analytic examples and
  conformal-covariance theorem require separate mathematical/source/literature
  audits before adoption. None is certified by the title or analogy.
- Start from the cumulative library, including Bakry Gaussian and fractional
  domains and IBM closed-span/conditional-adjoint lessons, without resuming
  those paused campaigns or assigning their probability laws to a new process.

No new Lean theorem is asserted at activation. No Lean source, toolchain,
verification setting, manuscript or mathematical result was modified. Preserve
failed approaches, counterexamples and exact unresolved domains in this ledger.
Use the existing full verification, source-integrity and exact two-branch public
backup gates; never change repository visibility.
