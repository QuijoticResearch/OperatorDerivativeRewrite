# Checkpoint1347 — latent clock divergence and an actual observed martingale

Let B be the actual constructed Brownian clock of IBM, h_T its verified
isonormal time direction, and P_IBM the orthogonal projection onto the existing
entire IBM observable L2 space. In the ORIGINAL native divergence domain,

    delta(0, B_T h_T) = P_IBM(B_T^2 - T).

The actual coefficient identity is proved almost everywhere on the original
joint probability space. The output is NONZERO for T>0: its exact pairing with
the actual IBM observation X_T^4 is 6 T^2. This is a positive result beyond
checkpoint1346's observable-weight kernel. The latent odd coefficient B_T is
essential here: this field cannot equal lift_{0,k}(F) for ANY deterministic
k and ANY IBM-observable L2 weight F. No derivative-domain membership of the
point observation X_T is assumed.

## Exact reuse and original domains

`IBMClockLinearDivergence` starts with the existing actual mixed Gaussian
divergence graph for a times the first chaos in direction b. The established
Bochner adjoint inclusion, native clock unitary, and ambient-pair divergence
transport it into ORIGINAL jointDivergence.graph. The diagonal mixed target
equals the existing second Wick polynomial. Actual product/curry representatives
identify the original coefficient field with B_T h_T. Nothing replaces the
measure, derivative, adjoint, domain, observable space, or clock path.

`IBMQuadraticClockMartingale` instantiates the EXISTING observed-terminal
martingale and predictable integration machinery with F_T = B_T^2-T:

    M^T_s = P_{rightPast(s)} F_T.

This is a genuine square-integrable martingale in the verified right-germ
filtration, with right continuity in Hilbert L2. Projecting the new native
divergence output onto that past gives the same M^T_s, by projection geometry.
It is centered and scenery-even, hence orthogonal to every actual linear IBM
observation X_u. For s>=T its pairing with X_T^4 remains exactly 6 T^2.

For s<T, projection composition identifies M^T_s with the PREVIOUSLY verified
quadratic-clock rightLimitClass(s). That existing object's origin estimate
proves M^T_0=0 when T>0. Consequently the actual predictable indicator integrand
of (0,s] has stochastic integral M^T_s, rather than merely M^T_s-M^T_0.
For s>=T both its integral and its predictable-L2 integrand are nonzero.
In particular M^T_T != M^T_0. All these statements are Lean theorems.

## Scope that remains open

The integral is the existing genuine probability-space stochastic integral
against this terminal-indexed observed martingale, with its existing predictable
energy measure. It is not integration against physical-time IBM itself, a new
Brownian innovation, or a universal Clark–Ocone integrator. The target-indexed
construction was already verified; this checkpoint supplies its concrete native
clock-divergence realization and target-specific zero initial term.

The before-terminal comparison requires STRICT s<T. Equality with the old
rightLimitClass at s=T, raw/germ equality at positive times, and a stopped-channel
claim after T are not asserted. Right L2 continuity is not an almost-sure
continuous or cadlag version theorem. No assertion that the ENTIRE initial germ
is trivial follows from this target's zero initial value. Universal causal
Clark–Ocone, physical-time IBM Itô/Tanaka, local time, and the remaining full
intrinsic-calculus obligations remain open. IBM remains active.

## Verification and integrity

Read all262 final source/proof lines, all36 unabridged public types, and seven
printed actual definition bodies. Fresh complete root build and complete
transitive safe Foundation axiom audit passed. Six independent Lean tests check
actual coefficient/domain/output identity, nonzero output and observable-weight
obstruction, genuine martingale/L2/right continuity, nonzero actual integral and
integrand, exact fourth-power pairing/linear orthogonality/centering, and strict
before-terminal comparison/zero initial value/nonconstancy.

The first independent test pass failed on missing local completeness/open names
and a wrongly qualified L2 alias. Only the scratch tests were repaired; library
sources stayed unchanged after the successful full build and audit. First code,
log, and timing are retained. Final results and exact hashes are recorded in
STARDUST_IBM_QUADRATIC_CLOCK_DIVERGENCE_VERIFICATION.json.

All2180 prior Foundation/root sources remain unchanged except two appended root
imports. Three pinned configurations and all113 archive paths/hashes are checked.
ResearchSources is untouched and never staged. No proof-resource/trust/toolchain
override or weakened verification. Preserve the linear saved queue, research
ledger, exact-commit receipt, and verified PRIVATE main/research backup gates.
