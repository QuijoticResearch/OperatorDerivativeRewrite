# Actual localized energy measures and the raw-filtration gate

Checkpoint1327, intrinsic IBM calculus ACTIVE. This constructs countably
additive localized energy objects and proves an exact obstruction criterion
for the usual raw increment-energy convention. It does not construct the
joint predictable measure or complete stochastic calculus for IBM.

## Genuine time and probability-space measures

`IBMTerminalEnergyMeasure` generalizes the existing quadratic right-germ
time-energy construction to EVERY actual JointL2 terminal F. The integrator
is the existing actual germ martingale G^F_t = P_(rightPast t) F under the
explicit `IBMRightGermFiltration.germFiltration`. Nested projection and the
verified strong L2 right-continuity make e_F(t)=||G^F_t||_2^2 increasing and
right-continuous. Its actual Stieltjes measure nu_F is countably additive
and FINITE on the entire nonnegative time axis, using the projection bound
e_F(t)<=||F||_2^2. For ordered endpoints,

    nu_F((u,t]) = ofReal ||G^F_t-G^F_u||_2^2
               = ofReal E[(G^F_t-G^F_u)^2].

The measure has no origin atom by the nonnegative-time Stieltjes convention.
This does NOT prove G^F_0=0. If F belongs to the raw past at T, its mass on
(0,T] is exactly ofReal(||F||_2^2-||G^F_0||_2^2). The initial germ projection
is retained in the theorem and is not silently discarded.

`IBMWeightedTerminalEnergy` reuses the existing bounded full-raw-past
Coefficient(s). It constructs the ACTUAL L2 terminal aF with its scalar AE
bridge. Actual conditional-expectation pull-out, using raw past_s <= germ
past_t for s<=t, proves G^(aF)_t = a G^F_t almost surely. Thus

    nu_(aF)((u,t]) = ofReal E[a^2 (G^F_t-G^F_u)^2], s<=u<=t.

`localizedMeasure` is nu_(aF) restricted to (s,infinity), a genuine finite
countably additive time measure. Exact weighted increment identification,
REAL-valued time additivity, and consistency when transporting the SAME
coefficient to a later anchor with the existing `later` are proved.
This is quadratic weighting a^2, not an independence-based factorization.

For every raw-past-s event A, `eventCoefficient` is its actual indicator;
`eventEnergy` is the corresponding localized time measure. Its increment
mass is ofReal E[1_A (G^F_t-G^F_u)^2]. Separately, `incrementMeasure F u t`
is an ACTUAL finite measure on the original joint probability space with
density ofReal((G^F_t-G^F_u)^2) against the original joint probability.
Square-integrability/integrability and its measure formula on all ambient
measurable A are proved. `event_time_agreement` identifies these two measures
on their common ordered/past-measurable rectangles. `event_countable_additivity`
proves countable additivity over disjoint past-s events by this actual density
measure. Time additivity/countable additivity is supplied by the actual
Stieltjes measure. No random bracket or cadlag version is assumed.

## Exact raw-measure obstruction

The original RAW terminal martingale is N^F_t=P_(rawPast t)F. Equality of
raw and right-germ projections is not known in general and the newly
constructed measures must not be relabeled as raw-martingale measures.
`IBMRawEnergyMeasureObstruction` proves a necessity statement even at ONE
fixed time s. If any time measure nu satisfies

    nu((s,t]) = ofReal ||N^F_t-N^F_s||_2^2 for every t>=s,

then G^F_s=N^F_s. Indeed (s,s+2^(-n)] decreases to the empty set; its first
mass is finite by the hypothesized increment formula. Genuine measure
continuity from above forces those masses to zero. The already verified
strong raw right-approach limit identifies the norm limit with
||G^F_s-N^F_s||_2^2. No pathwise version or uncountable AE intersection is used.

The precise `finite_raw_energy_measure_iff` theorem states that a finite
measure having the usual raw increment law on ALL ordered (s,t] exists
IFF G^F_s=N^F_s for EVERY s. Sufficiency is constructive: use the actual
finite Stieltjes nu_F already constructed and rewrite the projections.
`no_raw_measure_of_germ_gap` is conditional on a NONZERO gap; this checkpoint
does not prove such a gap exists. Nor does it prove the gaps vanish. In
particular, a raw law for the observed(1) terminal would force its currently
open initial odd germ to vanish, by the already proved zero RAW origin.

## Joint extension and other obligations still open

The existing Mathlib `MeasureTheory.OuterMeasure.OfAddContent` API constructs
an actual measure from a sigma-subadditive content on a generating set
semiring. Its `AddContent.measure`, `measure_eq` and induced-outer-measure
results require those hypotheses; they are not inferred from finite energy
identities. This checkpoint supplies actual consistent time/event slices
and countable past-event additivity, NOT an additive content on all eligible
predictable rectangles or its JOINT sigma-subadditivity/generation proof.
Separate countable additivity here is not claimed to discharge that extension.

The common G integrator is explicit and genuine; its comparison with the
earlier RAW stochastic sums remains gated by projection equality. This
distinction is now an exact theorem-level requirement, not a presumed transfer.
Next investigate coherent predictable rectangle content and joint extension
or prove the relevant raw-germ equalities. Actual continuum integrand domain,
closure/approximation, bracket/regular versions, intrinsic IBM derivatives and
adjoints, full Clark–Ocone and actual unsmoothed IBM Itô remain OPEN. Generic
terminal martingales are supporting objects, not full intrinsic IBM calculus.
Original M/F/Z and F1/F2 correction/K domains remain unchanged.

## Verification

Three modules317lines,37 public declarations; complete actual unabridged
types and proofs reviewed. Four independent Lean checks use actual sine
coefficients and weighted IBM endpoint recovery; the genuine event
{IBM_1<=0} with consistent finite measures on both axes; real weighted time
additivity and later-anchor agreement; and the conditional raw-law implication
for the actually open observed(1) initial germ. Fresh full root build, COMPLETE
transitive safe-Foundation axiom audit with only the same three standard
axioms, independent checks, all2117 prior source hashes except3 root imports,
all3 configurations and all113 archive paths/hashes are recorded in
`STARDUST_IBM_LOCALIZED_ENERGY_MEASURE_VERIFICATION.json`.
No manuscript is modified or staged. Exact-commit receipt and verified PRIVATE
main/research closure follow the audited commit. Precommit evidence does not
claim that backup has occurred. Queue and verification requirements remain.
