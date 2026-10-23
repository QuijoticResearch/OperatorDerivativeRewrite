# Actual predictable change of integrator for IBM-observable martingales

Canonical manuscript: [LaTeX source](../../manuscripts/ibm-stochastic-associativity/main.tex)
and [compiled PDF](../../manuscripts/ibm-stochastic-associativity/main.pdf).
These Markdown notes are supporting exposition. Maintain substantive paper
changes in the LaTeX source and rebuild/review the PDF under the shared budget.
See the [manuscript index](../../manuscripts/INDEX.md) for freshness and status.

Working mathematical draft, grounded in checkpoint1373 and1374. This is not
a submitted paper, a novelty claim, or a completed physical-time IBM calculus.
The process being integrated is a terminal-observable martingale derived from
actual IBM; it is not the uncorrected IBM path. Original manuscripts are intact.

## Setting and statement

Work on the constructed independent scenery/clock joint probability space.
Let F be an original joint L2 channel. Its terminal-observable martingale is
P_tF in the existing right-germ filtration. Integrands use the existing raw
IBM predictable sigma algebra and finite predictable energy measure mu_F.
Write I_F:L2(mu_F)->JointL2 for the already constructed actual isometry.

**PROVED.** For every H in that ENTIRE original random predictable L2 space,
put Y=I_F(H). On the original predictable sigma algebra,

    mu_Y = H^2 mu_F.

For every K in ENTIRE ORIGINAL L2(mu_Y), the literal product HK is in L2(mu_F),
the product map is a linear isometry, and

    I_Y(K) = I_F(HK).

References: `IBMStochasticIntegratorEnergy.energy_change`;
`IBMStochasticProductAssociativity.product_memLp`, `product_ae`, `productIsometry`,
`actual_associativity`. All names have prefix `OperatorDerivativeRewrite.Foundation.`.

## Proof mechanism and domains

For a raw-past event A at s<=t, the previous actual rectangle pull-out theorem
identifies I_F(1_((s,t]xA)H) with 1_A(P_t-P_s)Y. Taking its genuine L2 energy
identifies the two measures on every adapted rectangle. Both are finite and
vanish at the origin; the existing ring partition and signed uniqueness extend
the equality to the entire predictable sigma algebra.

The withDensity integral identity then proves HK belongs to the original
input L2 space and preserves its norm. If representatives of K agree only
mu_Y-AE, their H-weighted products agree mu_F-AE. The H=0 locus is handled
explicitly; reverse absolute continuity is not used. Associativity holds on
original predictable cells by actual stochastic calibration, and original
dictionary density extends it to the entire output-energy domain.

**PROVED multichannel extension.** For EVERY existing completed family input z
and EVERY common bounded raw predictable g,

    J_F(M_g z) = I_(J_F z)(class_mu_(J_F z)(g)).

The corresponding completed input equals the existing nested stochastic lift.
Appending one original channel and applying the full signed joint multiplier
bound gives an output-comparison estimate. Existing self-representation of
completed outputs discharges the single-channel premise, and the preceding
single-channel identity finishes the proof.
References: `IBMCompletedBoundedAssociativity.comparison_bound`,
`actual_bounded_associativity`, `nested_identification`.

## Process-level convergence

**PROVED.** Every continuous curve in actual IBM-observable L2 has finite fixed-
channel reconstructions converging uniformly on compact parameter sets, and
uniformly over all causal horizons. Actual IBM and the existing bounded C1
nonlinear observation class instantiate the result. Its topology is sup_t of
L2 errors. Native transfers converge in the ORIGINAL divergence graph norm.
Reference: `IBMUniformStochasticReconstruction.uniform_actual`,
`actual_IBM_uniform`, `nonlinear_uniform`, `uniform_native_graph`.

## OPEN, and not supplied by the preceding results

No pathwise bracket, L2 of a samplewise time supremum, physical-time Ito–Tanaka,
or temporal conditional-gradient Clark–Ocone identity follows automatically.
An actual moving-terminal expansion has time-dependent coefficients and is
not automatically a martingale expansion in physical time. Arbitrary separate
channel multipliers g_i need not preserve full signed-energy null relations.
Rough point/sine observations remain outside the original joint derivative
domain despite their actual stochastic reconstruction. A future paper must
retain these distinctions, complete a literature/novelty audit, and select an
appropriate scope rather than claim all intrinsic IBM calculus is finished.

Verification and proof details: [associativity audit](../../IBM_INTEGRATOR_ENERGY_PRODUCT_ASSOCIATIVITY_AUDIT.md),
[uniform reconstruction audit](../../IBM_UNIFORM_STOCHASTIC_RECONSTRUCTION_AUDIT.md),
[blueprint](../../STARDUST_BLUEPRINT.md).
