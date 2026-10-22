# Actual IBM predictable ring content and finite stochastic realization

Checkpoint1331 constructs the finite algebraic part of the JOINT predictable
energy measure for the EXISTING right-germ terminal channel. IBM remains
ACTIVE. The result is an actual AddContent, not yet a countably additive measure.

## Exact process and measurable domains

Fix an actual F in JointL2 over the original independent scenery/clock product
law. G^F is the existing explicit augmented right-germ terminal martingale.
All rectangle events below belong to the ENTIRE RAW observed IBM past at their
left endpoint. This is the raw predictable sigma algebra used by the existing
coefficient type; it is not silently enlarged to all germ-predictable events.
Raw-past coefficients are eligible for G^F because the verified raw filtration
embeds in the germ filtration. No positive-time raw/G projection equality is
assumed. Nor is G^F the nonmartingale coordinate Z_t=W(abs(Y_t)); G^F depends on F.

## Verified semiring and ring, including the origin issue

IBMPredictableRectangles defines eligible sets R(s,t,A)=(s,t] times A, with
s<=t and A measurable in raw F_s. Any reversed or degenerate interval is also
represented correctly as an empty set by normalizing its right endpoint to
max(s,t); ordering is retained in the actual stochastic realization.

Intersection uses max of the starts, min of the ends, and A intersection B.
Difference is the union of three time pieces: before the second start with
event A; overlap with event A minus B; and after the second end with event A.
The overlap event is measurable at the LATER starting time by filtration
monotonicity. The three pieces are genuinely disjoint. This proves the actual
IsSetSemiring predicate, then Mathlib's isSetRing_supClosure supplies the
finite-union ring. Every member is raw predictable, excludes time0, and is
contained in (0,T] times the whole sample space for some finite T.

The FULL Mathlib raw predictable sigma algebra is proved to equal generateFrom
of this ring TOGETHER WITH all origin sets {0} times A for A in raw F_0.
The reverse inclusion uses the actual cofinal identity
(s,infinity) times A = union_n (s,n] times A. This matches Mathlib's concrete
Filtration.predictable definition in Probability/Process/Predictable.lean.
No equivalence with an unproved alternative definition is invoked.

The origin component matters: an independent Lean counterexample proves that
{0} times the whole sample space is NOT a member of the positive-time ring,
although it belongs to the generated full predictable sigma algebra. To obtain
a measure on that FULL sigma algebra, the zero-energy origin component must
still be adjoined or treated by a verified zero-origin extension. The ring
alone is not asserted to generate the full space.

## Actual finite stochastic integral, independent of presentation

IBMPredictableFiniteIntegral indexes ordered eligible rectangles by actual
time endpoints, sample events and their measurability proofs. Its process
map is the finite real linear combination of their ACTUAL indicators. Its
stochastic map is the corresponding finite linear combination of the ACTUAL
germ-channel steps from1330. A scalar AE theorem identifies every resulting
JointL2 variable with the genuine finite sum of indicator coefficients times
increments of the original channel representative.

The existing deterministic endpoint-charge identity proves a KERNEL INCLUSION:
if a finite rectangle combination is the zero time/sample function, its actual
stochastic integral is zero in JointL2. Mathlib's liftQ and quotKerEquivRange
then descend the stochastic map to the RANGE of the actual process map. The
map is linear, agrees with the finite sums, and realizes every rectangle basis.
This is finite presentation independence with a PROVED relation-respecting
map, not a definition of a continuum integral by an image norm. No analytic
completion, arbitrary bounded coefficient-domain equality or universal noise
representation is claimed. The finite range is the simple rectangle-process
domain; earlier full bounded-coefficient step results remain separately valid.

An independent nonzero finite coefficient relation, indicator(A)+indicator(Ac)
minus indicator(universe), has zero process AND zero actual stochastic integral.
Its coefficient vector is proved NONZERO by summing its coefficients. Thus
raw presentation coefficients are not injectively identified with processes.
The quotient is mathematically necessary; integrand injectivity is not assumed.

The actual integral also preserves sample support. If its finite time process
vanishes outside a sample set at ALL times, its actual L2 representative
vanishes there almost surely. The endpoint identity needs only the finitely
many time endpoints and the actual scalar bridges; no continuous or cadlag
version of the martingale is assumed.

## Constructed positive additive content and actual energy identity

For every ring set E, Mathlib's disjoint finite partition theorem represents
its indicator by eligible rectangle indicators. The descended finite integral
therefore defines I_F(E) independently of the chosen partition. Finite sums of
disjoint ring indicators map to finite sums of the ACTUAL integrals.

First, terminal pairing on each rectangle is its nonnegative squared energy;
partition linearity proves nonnegative terminal pairing on every ring set.
Define

    content_F(E) = ofReal(inner(F,I_F(E))).

The new object satisfies the FULL AddContent finite-additivity predicate on
the constructed ring, including the empty set and arbitrary finite disjoint
unions. Its value on each eligible rectangle is EXACTLY the already constructed
incrementMeasure F s t A, a true density measure under the original joint law.
It therefore agrees with the previous event/time slice values.

Pairwise-disjoint rectangles can overlap in TIME. If their time intervals
overlap, disjointness forces their sample events to be disjoint; their actual
stochastic steps then have disjoint sample support and inner product zero.
If their time intervals are disjoint, the existing martingale orthogonality
applies, with empty intervals treated separately. Consequently every disjoint
rectangle partition gives an orthogonal actual sum. This proves for EVERY E
in the ring

    inner(F,I_F(E)) = norm(I_F(E))^2,
    content_F(E) = ofReal(norm(I_F(E))^2).

This is genuine ring energy, including overlapping-time presentations, not
merely a positive functional given an unexplained energy label.

The content is uniformly bounded by ofReal(norm(F)^2) on the ENTIRE ring:
use its finite horizon containment, AddContent monotonicity, actual density
agreement on the containing full rectangle and the existing globally finite
germ time-energy measure. No initial germ projection is discarded.

## Support control on the actual ring and remaining countable obligation

For ANY ambient measurable sample event A with E contained in time times A,
the ACTUAL I_F(E) vanishes outside A. Reuse the existing actual indicator
terminal 1_A*F and the proved terminal pairing identity to obtain

    norm(I_F(E))^2 <= integral_A F^2.

A need not be adapted at any start time. No future-event pull-out is used.
The content obeys the corresponding bound. If ring sets E_n are supported
in measurable A_n which every sample eventually leaves almost surely, the
actual ring integrals tend STRONGLY tozero in JointL2 by the already verified
terminal-support dominated convergence theorem.

However E_n decreasing to the empty TIME/SAMPLE set does not by itself say
that projected sample supports eventually disappear. The remaining central
proof must construct compact closed-time-fiber approximants, control their
removed left-edge strips by1330's verified right-trim limit, construct their
projected support events measurably from FINITE rectangle data, and prove the
full continuity-at-empty argument. JOINT sigma-subadditivity and the actual
Caratheodory measure extension remain OPEN. The proved generation theorem
also retains the explicit zero-origin extension obligation above. No joint
countable additivity or continuum predictable L2 integral is declared.

## Verification and preserved scope

Three modules560lines and60 public declarations; full source/proof arguments
and actual unabridged public types reviewed. Five independent Lean checks cover
actual original-law rectangle density and finite bound; sample-event/complement
additivity with completely overlapping time intervals; a NONZERO coefficient
relation descending to an actual stochastic identity; the origin generator
counterexample; and an actual two-rectangle ring energy/support bound involving
a later IBM observation. Full fresh root build, COMPLETE transitive safe-
Foundation axiom audit and independent results are recorded in
STARDUST_IBM_PREDICTABLE_RING_CONTENT_VERIFICATION.json.

All2129 prior Foundation/root sources except exactly3 root imports, all3
configuration hashes and all113 archive paths/hashes must be unchanged.
No manuscript is modified or staged. Explicit Git, exact-commit receipt and
verified PRIVATE main/research synchronization follow full verification.

Focused F1–F3 remain verified in their exact1107 domains, including the actual
closed densely defined intrinsic derivative and Hilbert adjoint. Coordinate
initial-germ zero1329, support continuity1330, all original M/F/Z definitions
and existing theorem domains are preserved. Positive-time raw/G comparison,
regular versions/bracket, full native integration/adjoint-domain identification,
continuum closure and full intrinsic IBM calculus remain OPEN. IBM and the
indefinite goal stay ACTIVE; the campaign queue is unchanged.
