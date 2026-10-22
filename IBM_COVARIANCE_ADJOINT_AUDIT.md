# Actual IBM integral adjoint and reconstruction scope — checkpoint1318

IBM remains active. The actual full deterministic stochastic integral I from
checkpoint1317 is a linear isometry from time L2(nu) into the original scalar
joint L2 space. Here nu is the actual expected-increment energy measure of the
constructed right-germ martingale r, under its explicit augmented filtration G.
This checkpoint connects that actual integral to the verified Hilbert adjoint
machinery. It does not identify the resulting adjoint with the native Malliavin
derivative or assert a full Clark–Ocone representation.

## Exact domain and actual interval duality

`IBMRightGermCovarianceAdjoint.covarianceAdjoint` is I*, an actual bounded linear
operator from ALL JointL2 into ALL time L2(nu). Existing Mathlib adjoint duality,
instantiated with the actual integral, gives

    inner(f,I*F) = inner(I f,F).

The proved interval identity is

    integral_(s,t] (I*F)(u) dnu(u)
      = integral_omega (r_t(omega)-r_s(omega))*F(omega) d jointMeasure,

for every actual joint L2 observable F and s<=t. This uses the actual time-L2
indicator/set-integral identity, the verified interval stochastic integral,
the L2 inner-product integral, and the actual scalar representative subtraction
bridge. It requires no smoothness, finite cylinder, hypothetical stochastic law
or deterministic conditional-variance assumption. Interval finiteness and the
L2 domains provide the relevant integrability. Thus the operator is a genuine
time-energy covariance density for the actual stochastic increments.

Its value on an actual martingale increment r_t-r_s is exactly 1_(s,t] in time
L2(nu). More generally, I*I f=f for EVERY f in the full completed time L2 space.
The adjoint norm on every input is bounded by the original JointL2 norm.

## Precise reconstruction and residual

Define reconstruction(F)=I(I*F) and residual(F)=F-reconstruction(F). Lean proves
idempotence of reconstruction, orthogonality of residual(F) to EVERY actual
deterministic stochastic integral, and the exact energy decomposition

    ||F||^2 = ||I*F||^2 + ||residual(F)||^2.

The actual complete-reconstruction condition is

    reconstruction(F)=F iff F belongs to range(I),

equivalently residual(F)=0. The range here is the actual range of the verified
full deterministic integral. It is not defined to contain every IBM observable.
No residual is discarded; no surjectivity or predictable representation property
is assumed. All genuine deterministic stochastic integrals are recovered exactly.

This supplies an actual operator/integration duality with an explicit residual,
rather than a formal adjoint on an uninstantiated process. It also pinpoints
what must be established before a stronger reconstruction claim could follow.

## Remaining mathematical work

The covariance adjoint is not automatically a native Gaussian-source/clock
Malliavin derivative. Their functional domains, causal projections and adjoints
require a separate proved identification, and a Leibniz rule is not claimed.
Random predictable integrands require their own actual weighted increment
energies and domain/control construction. The deterministic energy measure
must not be factored from those random energies without an applicable theorem.

A useful next test is whether centered actual IBM observables lie outside the
deterministic integral range. Global scenery-sign symmetry may distinguish
the quadratic-clock-derived r from actual odd-scenery IBM coordinates, but the
required transformation, filtration invariance and conditional-projection
equivariance must be proved; no such counterexample is claimed here. Existing
clock-sign symmetry alone does not establish that proposed test. Even a proved
deterministic-range obstruction would not exclude random predictable integral
representations or full Clark–Ocone with the correct channels.

Full random predictable integration, native derivative/adjoint compatibility,
Clark–Ocone, regular versions, bracket and unsmoothed actual IBM Itô remain open.
Original raw M/F and actual IBM Z are unchanged. Agreement r_t=M_t at positive
time remains exactly the unproved zero-jump condition. All F1/F2 correction and
K-domain hypotheses remain intact. The full intrinsic IBM campaign continues.

## Verification contract

`STARDUST_IBM_COVARIANCE_ADJOINT_VERIFICATION.json` records fresh full build,
complete transitive safe-Foundation axiom audit, all 13 unabridged public types,
81 source lines and complete proof review, four independent Lean checks,
unchanged prior sources/configuration, and all 113 immutable manuscript hashes.
Tests cover the actual increment's interval density, arbitrary actual scalar
interval covariance, full-domain exact recovery, and arbitrary-input residual
orthogonality/energy with its precise range condition.

Exact Git receipt and verified PRIVATE main/research synchronization close the
checkpoint separately. Precommit evidence claims no completed private backup.
Campaign order and source manuscripts are unchanged.
