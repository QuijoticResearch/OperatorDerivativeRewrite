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

The namespace is `OperatorDerivativeRewrite.Foundation`. No stochastic calculus
interfaces, multiplication operations, chain rules, or custom axioms are included.
`Foundation/AxiomAudit.lean` prints the axiomatic dependencies of all three declarations.

The original `C:/Operator/OperatorDerivative.lean` and
`C:/Operator/OperatorDerivative.tex` are preserved unchanged.
