# OperatorDerivativeRewrite

A small restart of the operator-derivative formalization.

## Pinned environment

- Lean: `leanprover/lean4:v4.34.1` (`lean-toolchain`).
- Mathlib: release `v4.34.1`; exact dependency revisions are recorded in `lake-manifest.json`.
- Project generated with the official `lake new OperatorDerivativeRewrite math` template.

With elan and Git installed, reproduce the build from this directory:

```text
lake exe cache get
lake build
lake build Foundation.AxiomAudit
lake env lean Foundation/AxiomAudit.lean
```

## Foundation

`Foundation/Adjoint.lean` extracts only the original densely defined operator-adjoint
foundation. It defines `operatorDerivative` using Mathlib's `LinearPMap.adjoint`
and proves `operatorDerivative_isClosed` and
`operatorDerivative_adjoint_identity`. Both theorems require a dense operator
domain; the identity explicitly uses elements of the two operator domains.

The namespace is `OperatorDerivativeRewrite.Foundation`. No energy-space interfaces
or chain rules are imported. No custom axioms are introduced.

`Foundation/LpProducts.lean` proves scalar-product, scalar–vector-product, and
vector-inner-product membership and Hölder estimates with their actual exponents.
It includes L² × L² → L¹, L⁴ × L⁴ → L², L∞ × L² → L², typed Lp operations,
integrated Cauchy–Schwarz, and bounded real multiplier symmetry on L².
`Foundation/AxiomAudit.lean` prints dependencies of every foundation declaration.
See [MATHEMATICAL_AUDIT.md](MATHEMATICAL_AUDIT.md) for original errors, the
counterexample, preserved fragments, and the proposed restricted interface.

The original `C:/Operator/OperatorDerivative.lean` and
`C:/Operator/OperatorDerivative.tex` are preserved unchanged.

`Foundation/OperatorDomains.lean` characterizes the actual adjoint domain, proves
whole-space domains for bounded operators and passage to limits for closed graphs,
and records the L⁴ value-and-output restriction without asserting closure or Leibniz.
`Foundation/MultiplierCore.lean` constructs continuous bounded multipliers and
proves a multiplier algebra for the given divergence using domain preservation and
bounded commutators. For centered densely defined divergences, its functions and
products belong to the actual adjoint domain. Admissible generators give the same
result for their generated algebra. No graph density or Leibniz rule is asserted.
See the domain reconstruction section of the mathematical audit for all hypotheses
and the remaining cylindrical/analytic obligations.

`Foundation/GaussianCore.lean` proves a genuine rank-one Gaussian polynomial core:
all finite moments, actual smooth derivatives and chain/product rules,
representation independence, and Gaussian integration by parts.
`Foundation/GaussianOperator.lean` constructs the actual derivative/divergence
operators on the polynomial L² domain, proves derivative closability and formal
adjointness, and connects actual cylinders p(W(h)) to that derivative.
The coordinate x is proved to fail the bounded-multiplier criterion; constants
satisfy it. The subsequent modules prove polynomial density and the full adjoint
identifications. This remains a one-coordinate polynomial milestone; the
manuscript's general bounded smooth cylindrical calculus is future work.

`Foundation/GaussianDensity.lean` now proves polynomial density in the whole
Gaussian L² space from exponential-moment determinacy, without any adjoint
assumption. `Foundation/AdjointClosure.lean` supplies general graph-closure and
formal-adjoint lemmas. `Foundation/GaussianAdjoints.lean` proves dense domains,
closability of divergence, closed-domain adjoint inclusions, and actual polynomial
values for both adjoints. The closed derivative preserves the genuine cylinder
formula. These inclusions are the starting point for the Hermite spectral argument.

`Foundation/GaussianHermite.lean` constructs the normalized probabilists' Hermite
Hilbert basis, proves Gaussian orthogonality and completeness using polynomial
density, and verifies the true derivative/divergence lowering and raising actions.
`Foundation/GaussianHermiteAdjoints.lean` proves full adjoint identifications by
explicit finite Hermite graph approximations:

- closure(D₀) = δ₀* = closure(δ₀)*;
- closure(δ₀) = D₀* = closure(D₀)*.

`Foundation/GaussianHermiteDomains.lean` gives the exact weighted coefficient
domains, output norms, graph norms, and graph cores of both adjoints. For
coefficients cₙ = ⟨Hₙ/√(n!), f⟩, membership in the common closed domain is
Σ n cₙ² < ∞ (equivalently Σ (n+1)cₙ² < ∞, since f is already in L²).
The squared derivative graph norm is Σ (n+1)cₙ²; the squared divergence graph
norm is Σ (n+2)cₙ². No graph-density assumption is used. The finite multivariate development below
extends this spectral method; the mathematical audit records its proof
dependencies and all declaration meanings.

`Foundation/FiniteGaussianCoordinates.lean` uses Mathlib's basis-independent
standard Gaussian on any finite-dimensional real Hilbert space. It proves
isonormal covariance, exact Gaussian marginals, all finite coordinate moments,
joint Gaussianity of arbitrary finite coordinate families, and their genuine
linear relations. Orthogonality or linear independence of the family is not
assumed. The ambient Gaussian's full support is proved from its product model.

`Foundation/FiniteGaussianCylinders.lean` defines actual multivariate polynomial
cylinders and verifies the Fréchet gradient Σᵢ ∂ᵢp(W(h))hᵢ, smoothness, a true
analytic product rule, and all finite scalar/vector moments. Its L² gradient is
proved independent of the finite representation, including correlated or
linearly dependent coordinate families on the same ambient space.

`Foundation/FiniteGaussianTensor.lean` reuses the verified one-dimensional
Hermites to construct an orthonormal tensor family in independent finite-product
Gaussian L². `Foundation/FiniteGaussianDensity.lean` proves multivariate
polynomial density by one-dimensional moment uniqueness and characteristic
functions. `Foundation/FiniteGaussianCompleteness.lean` proves tensor polynomial
spanning and constructs a complete orthonormal Hilbert basis in every finite
dimension, including zero, with actual cylindrical pullback compatibility.
Full multivariate adjoint identification and spectral domains are verified in the modules below.
A countable Gaussian product probability space is constructed below; no infinite-dimensional Malliavin operator is claimed.

`Foundation/FiniteGaussianIBP.lean` proves polynomial coordinate Gaussian
integration by parts. `Foundation/FiniteGaussianVector.lean` constructs actual
Euclidean-valued L² polynomial fields and proves their density.
`Foundation/FiniteGaussianOperators.lean` defines the genuine polynomial
gradient and Gaussian divergence, proves their dense domains and closability,
and constructs closed extensions with rigorous adjoint inclusions:

- closure(∇₀) ⊆ δ₀*;
- closure(δ₀) ⊆ ∇₀*.

The gradient is verified as the actual Fréchet derivative. Both closures
preserve their classical polynomial values. `Foundation/FiniteGaussianLadders.lean`
proves actual normalized tensor raising/lowering identities on these domains.
The subsequent verified spectral argument below proves the full adjoint equalities
and polynomial graph cores for the maximal adjoints. Correlated-coordinate derivative
results remain preserved; tensor orthogonality is used only on the independent
standard Gaussian product.

`Foundation/FiniteGaussianSpectral.lean` characterizes the actual full divergence
adjoint through combined coefficients, with genuine L² realization and Parseval.
`Foundation/FiniteGaussianTruncation.lean` constructs finite total-degree scalar
and vector polynomial projections. Their raising action preserves cancellations
between coordinates and proves closure(δ₀) = ∇₀*.
`Foundation/FiniteGaussianAdjoints.lean` proves the complementary gradient
approximation and closure(∇₀) = δ₀*, so both closed operators are mutual adjoints.
`Foundation/FiniteGaussianDomains.lean` proves coefficient realization, the exact
scalar domain Σα |α| |cα|² < ∞, and the vector divergence domain Σβ |bβ|² < ∞,
where bβ = Σᵢ:βᵢ>0 √βᵢ uᵢ,β−eᵢ. It also verifies squared Hilbert graph-error
convergence and the zero-dimensional case. No componentwise weighted divergence
domain or graph density is assumed. Classical polynomial values and all earlier
correlated-coordinate cylinder results are preserved. These results concern the
finite independent Gaussian model; no infinite-dimensional adjoint is claimed.

`Foundation/InfiniteGaussianProduct.lean` constructs the countable product
Gaussian probability space on real sequences, proves independent standard
Gaussian coordinate laws and all finite marginal laws, and embeds actual finite
polynomial cylinders isometrically into its L² space. These cylinders have every
finite moment; fixed-coordinate polynomial embeddings are injective, and finite
tensor Hermite orthonormality is preserved.

`Foundation/InfiniteGaussianFirstChaos.lean` proves coordinate centering,
second moments, and L² orthonormality. It constructs an injective linear isometry
from real ℓ² into product L² by actual unconditional sums of weighted coordinates,
preserving finite sums, norms, and inner products. The following modules complete
its isonormal Gaussian law. The sample space of real sequences remains distinct
from the coefficient space ℓ².

`Foundation/InfiniteGaussianLaw.lean` proves exact laws of actual finite weighted
coordinate sums and of every infinite L² limit W(h): N(0, ‖h‖²), including h = 0.
The proof explicitly passes from L² convergence to convergence in probability,
to convergence in distribution and characteristic functions, then uses
uniqueness of probability laws.

`Foundation/InfiniteGaussianIsonormal.lean` proves centering, exact covariance
Cov(W(h),W(k)) = ⟨h,k⟩, variance, and almost-everywhere linearity of actual
representatives. It proves joint Gaussianity of every finite family without
rank or independence assumptions, verifies Mathlib's Gaussian-process predicate,
and identifies finite-support correlated families with matrix pushforwards of
the existing finite Gaussian coordinate model. Thus the original first-chaos
isometry is now a genuine real isonormal Gaussian process over ℓ².

Full product polynomial cylinder density is proved by the modules below.
Infinite-dimensional derivative/divergence operators remain to be established.

`Foundation/InfiniteGaussianPolynomials.lean` constructs the actual L² evaluation
of algebraic polynomials indexed by ℕ, proves all finite moments and injectivity,
and identifies its image exactly with the union of finite polynomial cylinders.

`Foundation/InfiniteGaussianDensity.lean` proves that this actual union is dense
in the entire countable Gaussian product L² space. The proof combines the
verified finite Gaussian polynomial density theorem with an independent
measurable-cylinder π-system argument. It also proves that every L² variable
can be approximated in norm by one finite polynomial cylinder.

This completes the first scalar density milestone toward a Malliavin derivative.
Derivatives for arbitrary correlated W(h) cylinders, representation independence,
vector test-space density, Gaussian integration by parts, closability, and closed
operator/adjoint domains remain to be constructed. No such infinite-dimensional
operator is claimed here.
