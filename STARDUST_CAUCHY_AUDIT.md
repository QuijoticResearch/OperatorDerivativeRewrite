# Cauchy operator campaign — initial source and reuse audit

Current1880: actual complex Gaussian product/pushforward marginal and unbounded exponential L2 energies verified. EexpZ=1, centeredEnergy=exp(2v)-1; the paper exponential formula is false for EVERY positive time under BOTH its normalized and unnormalized conventions. Exact HasLaw transfer and native norms checked. Existing deterministic-test nonuniqueness and projected-versus-full derivative domain theorems directly audit the source foundation. Full complex Cauchy projection, true process/integral/source-domain realization, fBM and conformal claims remain OPEN; this campaign stays ACTIVE. See1880 below.

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

## Checkpoint1880 - corrected actual complex Gaussian energy; foundational Cauchy domain audit

**First Cauchy mathematical checkpoint; campaign remains ACTIVE.** The original stochastic_cauchy_operator_v4.tex is preserved at SHA2563154d5c35ac6c1a1c984847cda8f94d953e29ae783f4f4536933f8c973033e8c. Selective investigation now includes its real derivative/Riesz definition and Tier2 assertions (original lines168–232), direction projections/idempotence (379–501), and Brownian powers/exponential/modulus examples (603–663). It is a complex-Gaussian projection paper, not the later Cauchy-stable process campaign. No full-paper proof review, literature/novelty audit, complex Brownian construction, or completed stochastic Cauchy calculus is claimed.

**A central uniqueness claim is FALSE as written, by direct verified reuse.** Original def:operator_derivative tests E[F delta(u)]=E<DF,u> only for DETERMINISTIC u in the Gaussian energy Hilbert space, while declaring a UNIQUE RANDOM L2(Omega;H) gradient. `GaussianDeterministicAdjointDomain.quadratic_duality_not_unique` already proves two DISTINCT actual Gaussian random fields (the true nonzero quadratic Wick gradient and0) satisfy every such deterministic Gaussian pairing for the SAME quadratic observable. `deterministic_wick_other` identifies the deterministic-integration adjoint's first-chaos answer0; `deterministic_lift_not_closed_gradient` proves that constant lift is not the true closed-gradient graph value. The independent harness checks the exact original coefficient/random-field types. This refutes the stated real Gaussian building-block definition, not an imaginary sample-space analogy. A deterministic-test adjoint can be uniquely defined in its deterministic Hilbert codomain; it does NOT determine a random gradient there. A full random-field derivative requires a sufficiently rich dense random test domain and its actual adjoint graph.

**Tier2/idempotence: retain the projection and the domain.** The source asserts D(delta(u))=u for adapted u from isometry, then uses it in thm:idempotent. Existing `GaussianPredictableAdjoint.predictableAdjoint_integral` proves the genuine bounded inverse relation J* J u=u; `predictableAdjoint_eq_projected_derivative` identifies J* with Pi D ONLY on the ACTUAL closed derivative domain. The independent harness derives Pi D(Iu)=u with the explicit domain witness. `GaussianContinuousRigidity.rigidity_value` on its precise adapted completed graph says the UNPROJECTED full derivative equals the original field iff that field has a deterministic time profile; the non-deterministic case keeps its sensitivity correction. `GaussianSensitivityGeometry.sensitivity_energy` quantifies that correction. `GaussianPredictableDomainGap.representation_without_full_derivative` supplies actual represented Brownian L2 targets outside the full derivative domain, also checked independently. The correct bounded predictable inverse and the unbounded full derivative must not be interchanged. The manuscript's idempotence CONCLUSION may be repairable with a proper source projection and bounded adjoint; it is NOT declared false merely because its displayed proof uses an invalid inference. Full complex/two-source domain and projection hypotheses remain unresolved.

**New verified actual Gaussian law and corrected exponential.** `Foundation/StochasticCauchyGaussianNormalization.lean` constructs the ACTUAL product probability law N(0,v) x N(0,v) for every finite NNReal v, including0, and the measurable complex variable Z(x,y)=x+i y. `complexLaw` is its pushforward to C, `complexLaw_probability` verifies probability and `hasLaw_z` is literal law identification. This is a terminal MARGINAL, not an invented Brownian path or filtration. It matches the source's explicit independent equal-variance Gaussian marginal assumptions.

Measurability, integrability of the unbounded exponential and its squared norm, and actual complex MemLp2 membership precede Fubini/integral algebra. The existing Mathlib `complexMGF_id_gaussianReal`, `mgf_id_gaussianReal`, real variance and product integration are reused. The corrected results for every v>=0 are

    E|Z|^2=2v;  E exp(Z)=1;
    E|exp(Z)|^2=exp(2v);
    E|exp(Z)-1|^2=exp(2v)-1.

`z_second_moment`, `exponential_mean`, `exponential_second_moment`, `centered_energy` prove these in the actual product law. `exponential_mean_of_hasLaw` and `centered_energy_of_hasLaw` transport the equalities to ANY actual random variable Z on ANY measurable source with the stated `HasLaw` marginal. The process marginal is an explicit hypothesis, not an asserted constructed process. The independent harness checks the actual native complex L2 norms of both exp(Z) and its centered class, and uses the mean theorem to identify the centered integral as genuine variance under a supplied marginal law. These are classical Gaussian facts and exact corrections to the manuscript; no novelty is claimed for the moment formulas.

**The manuscript's displayed exponential energy fails under BOTH conventions.** Its Brownian examples first state Z=W1+i W2 but then use N_C(0,T) with real and imaginary variances T/2, and later use real variance T to compute exponential energies. Let M(T)=[exp(2T)-1]/2 be the ORIGINAL reported exponential variance.

- Under the stated NORMALIZED marginal v=T/2, the true variance is exp(T)-1. `normalized_energy` and `normalized_error` prove M(T)-trueVariance=(exp(T)-1)^2/2. `normalized_counter` proves strict failure for EVERY T>0.
- Under the UNNORMALIZED independent Brownian-component convention v=T, the true variance is exp(2T)-1=2 M(T). `unnormalized_energy` and `unnormalized_counter` prove the exact missing factor2 and strict failure for EVERY T>0.
- At T=0 all three are0; the proof keeps that degenerate corner. For v=T/2 the second moment is T; for v=T it is2T. Thus the two Gaussian normalizations cannot be silently interchanged. The source's mean E exp(Z)=1 remains valid under BOTH, so not every displayed identity is rejected.

These conclusions are law-level, independent of a disputed stochastic integral or a chosen Cauchy projection. The normalized powers calculation has a different convention; its general nth-moment formula is NOT newly proved here. Approximate quadrature also checks fourth moments, but those numerical checks are not a Lean theorem. A repaired integral energy must use the same covariance normalization as its actual integrator/source Hilbert norm. No repair of the entire stochastic representation follows merely from repairing the terminal variance.

**What remains OPEN.** Choose a coherent derivative/test/domain convention; construct or identify the actual required complex/two-independent-source process and predictable integral (complexifying a real-noise integral is not enough); supply correctly embedded and normalized (1,0)/(0,1) projections preserving the actual source/domain; identify bounded-adjoint reconstruction and the precise residual/range; distinguish stochastic direction ranges from terminal holomorphic/Hardy spaces. Audit the fBM projection boundedness, energy/covariance corrections and conformal claims against exact hypotheses and primary literature. Full abstract Hilbert projection theorems are already available and should be reused rather than re-proved as declaration accumulation. None of these central obligations is declared complete. No transition to iterated pseudoprocess or any other campaign is authorized by this partial correction.

**Verification and preserved repairs.** All191 final source lines,21 public proofs/five definitions/one abbreviation, five private proofs, and ALL27 unabridged public types reviewed. No new instances, axioms, placeholders, compiler/resource/toolchain changes or older mathematical-source edits. Five targeted-development logs retained: NNReal scope, explicit product-integral function arguments, typed pointwise integrability, real-part integral interfaces and exact arithmetic normalization were repaired at default resources. The first independent harness had wrong namespace qualifications of existing Gaussian objects; its log/time were preserved and only those references repaired. Nine independent Lean examples cover both second-moment conventions, degenerate probability/energy, normalized and unnormalized law-level counterexamples for arbitrary actual random variables, native centered/uncentered L2 norms, deterministic-test nonuniqueness, the correct projected inverse, the true full-gradient rigidity domain, and the actual Brownian full-domain gap.64x64 Gaussian-Hermite quadrature at five variance parameters and four positive times agrees below5e-14; approximate diagnostics ONLY, not Lean premises or a process simulation. No publication/manuscript, queue, goal, reflection or automation changes. Originals remain byte-identical.

Local closure1880: complete7303-job root build 39.4356919s; complete64406-declaration standard-only transitive axiom audit plus ALL27 unabridged public types 44.0932344s; nine independent Lean checks 27.2363029s; complete persisted AxiomAudit 54.0417979s, all PASS. All3079 Foundation signature/import/header/hash entries refreshed (3078 root reachable plus separately compiled AxiomAudit); authenticated unchanged entries reused, NOT a fresh manual review of every old proof. Authenticated3080-source snapshot preserves all older mathematics,3configs,113archive originals,21YM originals,the separately checked Cauchy original and both original numerical tools. Cauchy ACTIVE, Yang–Mills/Bakry paused and IBM deferred; every later queue priority and gate unchanged. Exact Git approval and guarded BOTH PUBLIC backup verification follow separately.
