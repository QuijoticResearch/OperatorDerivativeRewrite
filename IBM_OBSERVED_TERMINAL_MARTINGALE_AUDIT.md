# Actual IBM terminal-observable martingales — checkpoint1320

IBM remains active. Following checkpoint1319's deterministic even-channel
obstruction, this checkpoint constructs actual terminal-observable martingales
in the SAME explicit IBM right-germ filtration G. In particular it constructs
a centered scenery-odd martingale whose terminal value is the actual nonzero
time-one IBM coordinate. Its initial germ is retained explicitly and is not
asserted to vanish.

## Actual probability space, process and filtration

For any F in the original JointL2 space define

    channelClass(F,t) = P_R_t F,
    channel(F,t,omega) = the canonical scalar L2 representative at omega.

R_t and G are the verified actual IBM right-germ past and the explicitly
ambient-null augmented, right-continued observation filtration. Their exact
L2-past identification and canonical-representative measurability were proved
at1314. No new measure, supplied stochastic law, hypothetical process or
replacement observation filtration is introduced here.

Projection membership supplies actual strong adaptation. The existing actual
conditional-expectation/projection identity and nested projections give, for
s<=t,

    E[channel(F,t)|G_s] = channel(F,s) almost surely.

`channel_martingale` is the FULL actual Martingale predicate on the original
joint probability space. Each value is genuinely L2, with norm at most ||F||.
Existing whole-neighborhood projection convergence proves strong L2 right
continuity at EVERY nonnegative time. Conditioning preserves the actual scalar
mean at every time. No smooth or finite-cylinder restriction is required on F.

If F belongs to the raw observation past at T, then F belongs to R_t for every
t>=T. Consequently the actual class channelClass(F,t) equals F, and its scalar
representative equals F almost surely, at EVERY later time. These are exact
terminal recovery statements, not convergence to a formal terminal operator.

## The actual odd-scenery channel

The verified scenery reflection preserves every R_t. Hilbert projection
uniqueness and self-adjointness of the actual reflection action now give the
full commutation identity U(P_K F)=P_K(UF) on invariant projection spaces K.
This generalizes the previous fixed-input projection result; it does not
mistake invariant subspaces for pointwise fixed subspaces.

Choose F=observed(T), the actual IBM coordinate class from1319. It is raw-past
measurable, centered and scenery-odd. Its entire channel is therefore centered
and scenery-odd. For T=1, the channel recovers the actual scalar IBM coordinate
at time one and at every later time. Its terminal class is nonzero by the
already proved observed_one_ne_zero theorem.

Every value of this channel has zero inner product with every value of the
scenery-even quadratic-clock right-germ channel r, at arbitrary pairs of times.
This proves an unconditional covariance separation of genuine actual channels.
It does not assert independence, independent increments, a product-martingale
property or strong martingale orthogonality. Those require further conditional
or pathwise results.

## Initial value and remaining calculus obligations

The new channel's initial value is exactly P_R_0 F by its definition. No theorem
here proves P_R_0 observed(1)=0 or triviality of G_0. The earlier fact that the
particular quadratic channel has value zero at zero does not establish either
claim for this different channel. Nonzero terminal value is proved; nonzero
terminal-minus-initial innovation is not inferred without controlling the
initial germ. A possible raw-filtration zero-origin argument would still need
a separate right-germ comparison or zero-one theorem for G_0.

Strong L2 right continuity does not establish a jointly measurable regular
version, right-continuous sample paths, a bracket, or stochastic integration
against the new channel. This is an actual additional martingale realization,
not a completed stochastic calculus or predictable representation theorem.
The deterministic even-channel obstruction is preserved and is addressed here
by constructing an odd terminal-recovery channel rather than declaring general
representation impossible.

Next determine the initial germ and genuine dynamic increment energy, or
construct the appropriate random predictable domain/control and native
derivative-adjoint connection. Full Clark–Ocone, regular versions/bracket and
unsmoothed actual IBM Itô remain open. All original M/F/Z, F1/F2 corrections,
K-domain restrictions and the existing campaign queue remain unchanged.

## Verification contract

`STARDUST_IBM_OBSERVED_TERMINAL_MARTINGALE_VERIFICATION.json` records fresh full
root build, complete transitive safe-Foundation axiom audit, all 18 unabridged
public types and complete 99-line proof review, four independent Lean checks,
prior source/configuration identity and all 113 immutable manuscript hashes.
Tests cover the actual Martingale predicate with scalar terminal recovery and
nonzero terminal class; arbitrary-terminal scalar conditioning; every-later-time
class recovery and actual L2 regularity/bound; and arbitrary-time centered odd
channel/covariance separation. No test assumes a vanishing initial germ.
Exact Git receipt and verified PRIVATE main/research backup close separately;
the precommit record does not claim private synchronization already occurred.
