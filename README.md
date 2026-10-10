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
norm is Σ (n+2)cₙ². No graph-density assumption is used. Tensor bases and
multivariate operators remain future work; see the mathematical audit for the
precise spectral proof and all declaration meanings.

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
Gaussian L². Tensor completeness and finite-dimensional polynomial density are
not yet proved. Multivariate Gaussian integration by parts, gradient closability,
divergence adjoints, and their spectral domains are subsequent milestones.
No infinite-dimensional Gaussian measure or Malliavin operator is claimed.
