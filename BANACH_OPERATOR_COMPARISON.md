# Operator comparison across verified models

| Object | Actual type/domain | Verified role | Identification limit |
| --- | --- | --- | --- |
| Infinite Gaussian `D` | Closure of polynomial cylindrical `D₀` from scalar Gaussian `L²` to Hilbert-valued `L²`; see `Foundation/InfiniteGaussianOperators.lean` | Genuine Malliavin derivative from polynomial cylinders, densely defined and closed | Its Hilbert adjoint is a divergence, not a predictable Itô integral by definition |
| Infinite Gaussian `δ` | Hilbert adjoint `D*` with exact adjoint domain | Divergence; polynomial `δ₀` is included | Any predictable projection would be an additional operator/theorem |
| One-site Poisson maximal `D` | Weighted `L²(poissonMeasure rate)` partial operator with maximal forward-difference domain; see `Foundation/PoissonMaximalOperators.lean` and `PoissonAdjoints.lean` | Genuine add-one jump difference, closed; finite-support graph core | Hilbert geometry does not make its product rule diffusion-like |
| One-site Poisson `δ` | Weighted integrand `L²` to scalar `L²`, maximal backward weighted divergence | Adjoint to `D`, including full graph-domain identities | This is not yet a time-indexed predictable stochastic integral |
| B0 `boundedBanachDerivative δ` | `Lp ℝ q μ →L[ℝ] StrongDual ℝ H` for an **actual supplied** bounded `δ : H →L[ℝ] Lp ℝ p μ` | Hölder transpose; kernel is a range annihilator | The abstract `δ` is not constructed by B0 and the transpose is not automatically onto `H*` |
| C1 `adjoint T` | Partial map `StrongDual ℝ Y →ₗ.[ℝ] StrongDual ℝ X` for densely defined `T : X →ₗ.[ℝ] Y` | Exact ambient-norm adjoint domain, closed pairing graph | No automatic identification with `X` or `Y`; double-adjoint recovery remains open |

The shared abstraction is a densely defined linear map, its actual graph,
and a duality pairing with an adjoint-domain condition. This does not provide
a common chain rule: Gaussian cylindrical differentiation has the classical
Leibniz form, whereas Poisson forward differences have a jump defect
`D(fg) = f Dg + g Df + (Df)(Dg)` on their verified bounded domain.
`Foundation/PoissonQuadraticDefect.lean` verifies a nonzero quadratic defect.

A predictable Itô adjoint would be the dual of an **already constructed**
predictable stochastic integral. The raw Malliavin/add-one derivative acts
on all admissible perturbations; predictable projection, if defined, maps
those perturbations to the integrand class visible to a martingale integral.
Neither equality nor projection is automatic. A range theorem needs
surjectivity or a proven closed-range factorization; C2 only supplies the
closed range under a positive lower bound and a witnessed criterion for
elements outside it. No abstract implication here constructs a Gaussian,
Poisson, or stable stochastic model.
