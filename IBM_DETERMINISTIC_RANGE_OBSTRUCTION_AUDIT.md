# Actual IBM observable outside the deterministic integral range — checkpoint1319

IBM remains active. The proposed scenery-sign test is now proved for the actual
continuous IBM realization and its existing joint probability measure. The
time-one IBM coordinate is centered, nonzero and measurable in the time-one
raw observation past, but has zero covariance adjoint for the full deterministic
integral constructed through checkpoint1318. This is an obstruction to using
that single quadratic-clock-derived martingale with deterministic integrands
as a representation of all centered IBM observables.

## Actual global symmetry and past-space invariance

`IBMScenerySignSymmetry` reflects every Gaussian scenery coordinate and leaves
the independent clock sample unchanged. The product transformation S preserves
the actual joint law and is an involution. The verified first-chaos reflection
theorem makes each actual scenery coordinate odd almost surely. Existing
continuous scenery paths and a countable dense real sequence promote these
coordinate statements to ONE full-measure event on which the complete real
scenery path changes sign. Consequently the actual IBM path X_|Y_t| changes
sign at EVERY time on one joint full-measure event.

The induced L2 action U is an actual linear isometry, involution and self-adjoint
operator. Every raw IBM past L2 space is invariant under U. This is proved using
actual measurable factorization through the whole observed past: a coefficient
g(past) becomes g(-past). Canonical representative almost-sure identities are
transported under the actual measure-preserving map. The invariant-space claim
does NOT say that individual observables are fixed; actual IBM coordinates
provide explicit non-fixed members of those same past spaces.

For any projection space invariant under U, projection of a U-fixed input is
U-fixed. The proof uses Hilbert projection uniqueness, self-adjointness of U and
the actual space-invariance hypothesis. Clock-only quadratic inputs are fixed
by scenery reflection, so their actual raw conditional projections M_t are
fixed. The right-germ spaces are also invariant, by their verified intersection
of future raw L2 pasts. The constructed r_t is therefore fixed. No assumption of
raw-filtration right continuity or positive-time equality r_t=M_t is needed.

## Obstruction in the full completed deterministic domain

Finite actual deterministic stochastic dictionaries are fixed because every
r_t is fixed. The verified existence of dictionary approximations and strong
L2 convergence, together with continuity of U, shows that EVERY full time-L2
integral I(f) is fixed. This is a theorem on the full completed domain, not a
finite-grid-only calculation.

Let Z_t denote the actual JointL2 class `observed t` of IBM at time t. Its scalar
representative agrees almost surely with the existing actual IBM coordinate,
and Z_t belongs to the actual raw observation past at t. It is U-odd. Isometry
then gives inner(Z_t,I(f))=0 for EVERY deterministic time-L2 f. Actual integral
duality implies

    covarianceAdjoint(Z_t)=0,
    reconstruction(Z_t)=0,
    residual(Z_t)=Z_t.

The measure-preserving involution and oddness also prove E[Z_t]=0. All variables
are genuine L2 classes on the original probability space. At time one, nonzero
is established by reusing the existing verified strictly negative actual
increment pairing between times one and two: Z_1=0 would force that pairing to
vanish. This avoids inventing a new moment law or numerical nondegeneracy test.

Thus Z_1 is a centered nonzero ACTUAL observed variable outside range(I), and
there is NO f in the full deterministic time L2 space whose actual integral
equals the scalar IBM coordinate at time one almost surely. More precisely,

    ||Z_t-I(f)||^2 = ||Z_t||^2 + ||f||^2.

The error cannot be removed by choosing a different deterministic integrand,
partition, finite dictionary or completed-domain presentation. The scalar
almost-sure nonrepresentation theorem states this for the actual IBM function.

## What this does and does not resolve

This discharges the deterministic range-obstruction test proposed at1318. It
does NOT prove impossibility of random predictable integration against r, or
of Clark–Ocone using appropriate additional channels/integrators. A random
past-dependent coefficient need not be fixed by scenery reflection, so the
fixed-parity argument for deterministic integrands cannot simply be reused.
Nor does it contradict any prior finite-grid random-step result, whose exact
domains remain as recorded.

The next constructive direction is an odd-scenery intrinsic martingale channel,
or a rigorously constructed random predictable domain with the correct weighted
increment energies. For example, projection of a terminal actual IBM observable
onto the already verified right-germ spaces is a candidate channel; its full
martingale, parity, adaptation and terminal-recovery statements must be proved.
Do not equate a covariance adjoint with a native Malliavin derivative without
its domain/causal identification.

Full random predictable control/integration, native derivative/adjoint connection,
Clark–Ocone, regular versions, bracket and unsmoothed actual IBM Itô remain open.
Original M/F and IBM Z, all F1/F2 correction terms and K domains are unchanged.
Positive-time agreement of r and M remains the zero-jump question. The campaign
continues; this obstruction is not a stopping claim for intrinsic IBM calculus.

## Verification contract

`STARDUST_IBM_DETERMINISTIC_RANGE_OBSTRUCTION_VERIFICATION.json` records full
root build, complete transitive safe-Foundation axiom audit, every new public
type and complete source/proof review, four independent Lean checks, prior
source/configuration identity, and all 113 immutable manuscript paths/hashes.
Tests check actual centered nonzero past membership and zero adjoint, full-domain
scalar nonrepresentation, quantitative approximation error and orthogonality,
and the distinction between past-space invariance and a non-fixed past member.
Exact Git receipt and verified PRIVATE main/research backup close separately;
precommit evidence claims no completed private synchronization.
