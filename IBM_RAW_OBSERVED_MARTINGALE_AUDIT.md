# Actual nonconstant raw-observation IBM martingale — checkpoint1321

IBM remains active. This checkpoint proves that the ORIGINAL raw IBM initial
past is trivial modulo the actual joint law, and constructs an actual raw
observation martingale that starts at zero and recovers the nonzero time-one
IBM coordinate. It compares that process rigorously with the right-germ channel
from1320 while retaining the unresolved difference between their initial values.

## The raw initial past

`IBMRawInitialPast.observed_zero` reuses the verified zero-time source-class
theorem and the actual joint linear realization to prove observed(0)=0 in
JointL2. The actual scalar IBM coordinate at zero is consequently zero almost
surely. No claim of pointwise constancy on every sample is required.

If f belongs to the raw L2 past at zero, take its raw strongly measurable
version and apply the existing full-past factorization theorem. It equals
g(pastProcess(0)) almost surely. Every index in Iic(0) equals zero, so on the
actual zero-coordinate full-measure event the ENTIRE past process is the zero
path. Thus f equals the real constant g(0) almost surely. This applies to ALL
raw initial-past L2 members, not only cylinders, polynomials or bounded functions.

Every centered JointL2 variable F is therefore orthogonal to every raw initial
past member: its actual inner-product integral against an almost-sure constant
is that constant times E[F]=0. Hilbert projection uniqueness gives P_past(0)F=0.
This is a theorem about the raw initial sigma-algebra modulo the actual law,
not about its strictly-right germ or about a completed initial filtration.

## Genuine raw scalar martingale and dynamics

`IBMRawObservedMartingale` defines

    rawClass(F,t) = P_past(t) F,
    rawValue(F,t) = E[F | raw natural IBM filtration at t].

The L2 conditional-expectation theorem identifies rawClass with the ACTUAL
scalar rawValue almost surely. Conditional expectation supplies strong raw
adaptation, and the actual tower theorem gives the full Martingale predicate
for every F in JointL2. The scalar process is genuinely L2, and its mean is E[F]
at every time. This choice of scalar conditional-expectation representatives
avoids assuming canonical Lp representatives are pointwise raw measurable.

For F=observed(1), the raw scalar process starts at zero almost surely and
recovers the actual scalar IBM coordinate at EVERY t>=1. Its value at time one
cannot equal its value at time zero almost surely, by the previously proved
nonzero observed(1). Hence this is a genuinely nonconstant actual martingale
in the original IBM observation filtration. Its class is scenery-odd at every
time, using the established raw-past invariance and projection/action commutation.

This is a martingale of predictions of a fixed terminal observable. It does
not claim that the original IBM coordinate process itself is a martingale;
the earlier verified obstruction to that assertion remains unchanged.

## Exact right-germ comparison

For ANY fixed JointL2 terminal variable F and EVERY strictly-right cofinal
decreasing time sequence converging to t, the actual raw projection classes
converge STRONGLY in JointL2 to channelClass(F,t) from1320. The proof reuses the
existing decreasing-past projection convergence theorem and its exact cofinal
intersection identification. No bounded future horizon assumption is needed
for this fixed-terminal-variable result.

Projecting channelClass(F,t) back onto the raw present past gives rawClass(F,t),
by nested projections. In particular the concrete geometric approach to zero
converges to P_R_0 F, even when the raw time-zero value is known to be zero.
This limit is NOT silently replaced by the raw initial value. Triviality of G_0,
vanishing of the new odd channel's initial right-germ jump, and a modification
between the two scalar families remain unproved. Raw nonconstancy is established
independently of those unresolved regularization questions.

## Next obligations and preserved scope

Next use the actual nonconstant odd raw channel to develop controlled stochastic
integration, or obtain quantitative initial/right-germ control that justifies
a regular version and actual dynamic energy measure. Random coefficients must
retain their actual weighted increment energies. The deterministic even-channel
counterexample does not exclude random predictable or multichannel reconstruction.
Native derivative/adjoint compatibility, Clark–Ocone, regular paths/bracket and
unsmoothed actual IBM Itô remain open. Original M/F/Z and F1/F2 correction/K-domain
results are unchanged. This is not a full-calculus stopping checkpoint.

## Verification contract

`STARDUST_IBM_RAW_OBSERVED_MARTINGALE_VERIFICATION.json` records fresh complete
root build, complete transitive safe-Foundation axiom audit, all new unabridged
public types and complete source/proof review, four independent Lean checks,
prior source/configuration identity and all 113 immutable manuscript hashes.
Tests cover arbitrary raw initial-past constants and centered initial projection;
the actual nonconstant zero-start scalar martingale with IBM terminal recovery;
concrete strong origin-approach convergence to the UNREPLACED right-germ value;
and raw odd parity/mean preservation/present-past comparison. Exact Git receipt
and verified PRIVATE main/research synchronization close separately; precommit
evidence does not claim that backup has already completed.
