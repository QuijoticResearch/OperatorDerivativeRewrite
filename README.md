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
