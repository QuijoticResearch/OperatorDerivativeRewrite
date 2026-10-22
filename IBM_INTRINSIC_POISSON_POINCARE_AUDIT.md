# Intrinsic IBM Poincare and centered Poisson audit — checkpoint1336

IBM remains active. This checkpoint concerns the existing closed, densely
defined native source/clock derivative `jointDerivative` on the actual
IBM-observable `IntrinsicSpace`, and its existing Hilbert adjoint
`jointDivergence`. Neither operator nor the stochastic law is redefined.

## Established theorem contracts

`IBMNativeRecoveryContraction` uses genuine orthogonal Gaussian vacuum
projections and the exact product-field energy decomposition. The clock-first
ordered recovery from checkpoint1335 satisfies norm(Rf)<=norm(f), improving
its earlier sqrt(2) bound. The SAME bounded linear transfer from actual
raw-predictable L2(mu_F) consequently satisfies norm(B_F H)<=norm(H).
Its original native divergence identification and full-domain IBP remain valid.

`IBMIntrinsicPoincare` identifies the actual constant-one realizations and
reuses the existing constant graph. For EVERY f in the ORIGINAL domain of D,
norm(f-mean(f)*1)<=norm(Df), and Df=0 iff f=mean(f)*1.
Mean is the actual constant-one L2 pairing. The centered estimate follows
from actual adjoint duality with Rf and the recovery contraction; no cylinder
restriction or unproved core approximation is imposed. Constant one is nonzero
and has zero derivative, excluding uncentered coercivity. Constant1 is a valid
bound; optimality on the IBM-observable subspace is not established.

`IBMIntrinsicEnergyResolvent` instantiates the already verified closed-graph
energy construction with the actual D and its proved closedness and density.
J=(1+delta D)^(-1) maps into Dom(D), DJx belongs to Dom(delta), and
delta DJx=x-Jx. Testing its weak identity with constant one proves preservation
of mean. Energy plus Poincare gives norm(Jx)<=norm(x)/2 ONLY for centered x.
The independent constant-input test refutes extending this half bound globally.

`IBMIntrinsicPoisson` constructs the closed centered Hilbert subspace and the
actual contraction u -> J(x+u). Banach fixed point gives, for EVERY centered
intrinsic L2 target x, a centered solution u with u in Dom(D), Du in Dom(delta)
and delta Du=x. No derivative membership of x is assumed. Actual graph duality
proves uniqueness among centered original-domain solutions. Orthogonality to
the native divergence kernel proves norm(Du)<=norm(v) for EVERY original
divergence preimage v of x. Comparing with explicit R(x) proves
norm(Du)<=norm(x), and Poincare proves norm(u)<=norm(x). The actual fixed-point
iterates converge strongly in centered intrinsic L2, from every starting point.
This is not a claim of pathwise or uniform-in-physical-time convergence.

## Reuse correction and preserved results

The broader declaration search found that static centered intrinsic divergence
surjectivity and explicit recovery already exist in
`IBMNativeSourceRecovery`, `IBMGlobalVacuum`,
`IBMCenteredSourceRepresentation` and `IBMPastSourceRepresentation`.
In particular, `IBMNativeSourceRecovery.ordered_intrinsic_reconstruction`
and the centered representation use SOURCE-first recovery
(Rsource(f), Rclock(Psource(f))). The checkpoint1335 construction uses
CLOCK-first recovery (Rsource(Pclock(f)), Rclock(f)). Both are valid and all
old proofs remain unchanged. Static surjectivity itself is therefore not a new
discovery of1335. Its actual stochastic integration/native divergence and
gradient-adjoint bridge is preserved. This clarification supplements rather
than rewrites historical checkpoint records.

The new work reuses Gaussian minimal recovery, Bochner lifting, actual unitary
transports, old constant graph, closed-operator energy resolvent and Mathlib's
contraction theorem. No duplicate Gaussian or resolvent foundation is added.

## Scope and outstanding obligations

The energy operator delta D is a native Gaussian source operator on actual
IBM observables; it has NOT been identified with physical IBM time evolution.
Minimum norm here is among NATIVE divergence preimages, not among temporally
adapted stochastic integrands. The fixed-point solution is a genuine function;
a bounded linear Poisson solution operator has not yet been proved here.

Actual stochastic integral range/residual-zero, temporal adaptedness and causal
gradient identification, positive-time raw/germ comparison, old RAW-series
identification, physical-time versions/bracket and full native chain/product/
Itô and Clark–Ocone remain open. A native Poisson solution alone does not
prove actual stochastic range reconstruction or a universal noise. Existing
focused F1–F3 results remain verified on their exact domains.

## Verification and integrity

Fresh root build:6322 jobs,27.619s, terminal0. Complete transitive safe
Foundation audit:40515 declarations,38.221s, terminal0; only propext,
Classical.choice and Quot.sound. All49 actual unabridged new public types and
all410 final source/proof lines reviewed. Five independent Lean examples
passed first try in29.561s, including the constant obstructions and a NONZERO
actual observed IBM1 Poisson target without derivative-domain assumptions.
Stages ran serially. No proof-resource override or trust/configuration change.
The verification JSON contains exact hashes, commands, times and test code.
All2149 prior sources are preserved except exactly four appended root imports;
three configs and all113 immutable manuscript paths/hashes are checked.
Complete checkpoint closure still requires the explicit Git commit, exact-commit
receipt and verified PRIVATE main/research synchronization.
