# Campaign continuation after the archive inventory

2026-10-12. Research only; no Lean or dependency changes. All proposed results below are **UNVERIFIED** until Lean proves their exact statements. Source material is indexed in `NONCLASSICAL_ARCHIVE_SOURCE_AUDIT.md`.

The prior Brownian campaign attachment calls for a readiness map without automatically transferring Brownian results to nonsemimartingales. The latest request also prohibits changing the active repository. Accordingly this continuation develops concrete mathematical proof targets and inspects the pinned local APIs; it does not begin repository implementation.

## 1. First target: an actual singular deterministic Volterra kernel

For β>−1/2 and t≥0, define on R

    kβ,t(s) = 1_(0,t)(s) (t−s)^β.

Set the endpoints to zero; their values do not affect Lebesgue L². Prove measurable k, actual MemLp k 2 volume, support in (0,t), and

    ∫ kβ,t(s)² ds = t^(2β+1)/(2β+1).

At t=0, the interval is empty and both sides are zero since 2β+1>0. At t>0, reflect s↦t−s, use the power law for a nonnegative base, and integrate r^(2β) on (0,t). The strict condition 2β>−1 is the integrability argument, not an assumed L² hypothesis.

This constructs a `TimeHilbert` element for every time. For β=H−1/2, H>0, scaling by √(2H) gives variance t^(2H). Its covariance is still the overlap integral

    2H ∫₀^min(s,t) (s−r)^(H−1/2) (t−r)^(H−1/2) dr.

It is a Riemann–Liouville-type Volterra construction. **Matching one-time variance is not proof that this is standard fBM.** Do not rename it fBM or assert stationary increments without proving the two-time covariance identity. A standard fBM campaign needs its own actual kernel or positive-definite covariance construction.

Pinned Mathlib source APIs inspected:

- `Mathlib/Analysis/SpecialFunctions/Integrability/Basic.lean:47`: `intervalIntegral.intervalIntegrable_rpow'`, requiring exponent >−1 for Lebesgue interval integrability.
- `Mathlib/Analysis/SpecialFunctions/Integrals/Basic.lean:147`: `intervalIntegral.integral_rpow`, with the integrability/avoid-zero hypotheses explicit.
- `Mathlib/MeasureTheory/Function/L2Space.lean:52`: `MeasureTheory.memLp_two_iff_integrable_sq`, requiring AE strong measurability, and `MemLp.integrable_sq` at line 42.
- Set-indicator and affine change-of-variable APIs still need selection/elaboration for the proposed kernel proof. No claim that a scratch proof has compiled.

Existing repository proof bodies inspected in `Foundation/GaussianDeterministicVolterra.lean`, namespace `OperatorDerivativeRewrite.Foundation.GaussianDeterministicVolterra`:

- `positive_profile_predictable`: deterministic measurability and positive-time support imply membership in the actual full predictable space.
- `profileIntegral_eq_isonormal`: its actual Itô integral equals the isonormal embedding.
- `profileIntegral_derivative`: the integral and the constant embedded field belong to the closed cylindrical derivative graph.
- `profileIntegral_law`, `profileIntegral_pair_integrable`, `profileIntegral_covariance`: actual Gaussian law and covariance after supplying an actual L² profile.
- `causal_profile_mem`, `volterraProcess_isGaussianProcess`, `volterraProcess_covariance`: families of per-time L² causal profiles give Gaussian finite-dimensional laws and overlap covariance.

These results **do not** prove joint time measurability, continuous paths, kernel increments, fBM covariance, filtration equivalence, a Volterra Clark–Ocone formula, or an Itô formula for arbitrary nonlinear functionals. The first implementation milestone should finish only the concrete power-kernel construction, exact norm and its specialization to this existing integral.

## 2. fBM and curvature: keep three different questions separate

The archive's most developed `fbm` manuscripts concern a fractional-Laplacian symbol and finite covariance matrices, not a construction of a full fractional Brownian stochastic calculus.

**Kernel algebra target.** Define R_H(s,t)=(|s|^(2H)+|t|^(2H)−|s−t|^(2H))/2 and prove the same-sign symbol identity with γ=2H. This finite algebraic equality does not prove positivity on arbitrary families, process existence, or stochastic realization. In the Cauchy case, finite matrices M_k(i,j)=min(i,j)^k admit M_k=L diag(j^k−(j−1)^k)Lᵀ for one-based indices. Prove this by telescoping a finite sum before attempting spectral claims. Treat zero dimension and k=0 separately.

**Definition repair prerequisite.** The manuscript's complex Γ₂ must be Hermitian from its definition. The countercalculation in the source audit prevents using its literal unsymmetrized definition for an ordered curvature inequality. The covariance kernel identity itself does not depend on that flawed definition.

**Stochastic target.** Construct standard fBM only after proving its exact covariance, including dependent coordinates and H=1/2 recovery. `Foundation/GaussianHilbertProcess.lean` supplies `isonormalEmbedding`, `isonormal_covariance`, `isonormal_memLp`, `isonormal_isGaussianProcess`, and AE linearity for an actual separable real Hilbert space. It does not prove a proposed kernel has the fBM covariance. Keep the derivative in the covariance Hilbert space; do not change its norm to the derivative of the variance as the original manuscript does.

Acceptance boundary: no all-Hurst Itô, Gubinelli, Markov, rough-path, or curvature-dimension claim follows merely from a Gaussian covariance construction. The finite-dimensional deterministic adjoint in Part II is not the full random-field Malliavin derivative.

## 3. SPDE: first construct finite-rank Hilbert-valued Gaussian integrals

For a real Hilbert target E, orthonormal e₁,…,e_m and actual scalar time-L² profiles k_j, the natural first target is

    Z = Σ_j e_j W(k_j),       E‖Z‖² = Σ_j ‖k_j‖².

This needs actual E-valued L² embeddings, finite-sum integrability and inner-product expansion. No independence between W(k_j) is needed for this norm identity when the e_j are orthonormal. More generally retain the full Gram cross-terms. Use the actual scalar isonormal isometry and covariance results; do not introduce a structure containing the norm equality as an assumption.

Then an infinite orthonormal expansion may be constructed from a proved summable squared norm bound and L² completeness. That is a deterministic-kernel stochastic convolution milestone, not yet the manuscript's fractional SPDE. Joint-time continuity and a PDE solution concept are later obligations.

Before using the SPDE manuscript, resolve:

1. Its global L²(R) cylindrical white-noise Hilbert–Schmidt estimate is false for a nonzero translation-invariant convolution. Choose an explicit corrected model, rather than silently switching to a torus or a local state space.
2. Its Mittag-Leffler decay lemma must exclude α=2; the α>1 Laplace-transform argument and all constants need their own proofs.
3. For α>1, specify the second initial datum required by the time-fractional equation.
4. Prove the exact near-zero stochastic kernel integrability and temporal increment estimates. Do not infer path continuity from a single-time variance bound.
5. A fixed nonhomogeneous trace-class covariance generally destroys exact white-noise scaling.

A filename search of the pinned Mathlib found no purpose-built Mittag-Leffler, Volterra, Tanaka or Brownian-local-time module. This is a bounded search result, not proof that no useful declaration exists anywhere. Existing Gaussian and L² infrastructure should be reused before adding any dependency. The local revision remains Lean 4.34.1 / Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

## 4. IBM: closed pullback first, genuine stochastic compression later

The shortest independent operator lemma suggested by `EnergyFirst.tex:638–818` is this:

Let A:dom(A)⊆Hsrc→K be a closed linear operator and i:Hobs→Hsrc a continuous linear isometry. Define B on `{x | i x ∈ dom(A)}` by Bx=A(ix). Its graph is the inverse image of graph(A) under the continuous map `(x,y)↦(ix,y)`, so B is closed. This proves **no density** of dom(B).

If dom(A) and dom(B) are both dense, then for u∈dom(A*),

    u ∈ dom(B*) and B*u = i*(A*u).

Proof: test every x∈dom(B) and use the actual adjoint identities. If the energy target is restricted by an isometric inclusion J, the sufficient domain condition is Ju∈dom(A*), and the value is i*A*Ju. Do not claim the reverse inclusion; it requires an additional extension argument.

Reusable APIs inspected:

- `Foundation/Adjoint.lean`: `operatorDerivative`, `operatorDerivative_isClosed`, `operatorDerivative_adjoint_identity`, all in `OperatorDerivativeRewrite.Foundation`. Closedness and the identity have explicit dense-domain hypotheses.
- `Mathlib/Analysis/InnerProductSpace/LinearPMap.lean`: `LinearPMap.adjointDomain`, `adjoint`, `adjoint_isFormalAdjoint`, `adjoint_isClosed`; the latter proof uses closed orthogonal subspaces and continuous preimages.

The abstract pullback argument is useful but **does not verify IBM**. Next model-specific obligations are an actual independent scenery/clock product construction, pathwise random-time evaluation and measurability, a specified X(Y) or X(|Y|) convention, observable L² embedding/conditional expectation, and a dense observable derivative domain. The archive's mollified source functionals cannot be used to prove that density until their observable measurability is established.

For later correction-space work, preserve the first-chaos/full-chaos distinction. A claimed divergent first-chaos L² norm blocks a full L² correction limit, not a distributional dual limit. Brownian local time, its spatial Sobolev regularity, Tanaka's boundary term, and uniform moment bounds are substantial missing proofs. The expectation PDE is a separate, narrower target and cannot certify a random correction identity.

## Execution boundary

The next safe implementation is the explicit Volterra power-kernel L²/norm milestone in section 1, followed by its already-defined integral law, covariance and first derivative. This is concrete progress beyond assuming an arbitrary L² kernel, without relying on the problematic manuscript identifications.

Current work stops at read-only research because the user explicitly asked not to change the active repository. No Lean theorem, build, axiom audit, commit, dependency change or new campaign completion is claimed. All archive claims remain UNVERIFIED.
