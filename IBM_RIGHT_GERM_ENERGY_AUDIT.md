# Actual IBM right-germ continuity and energy measure — checkpoint1315

IBM remains active. This checkpoint constructs a deterministic, countably
additive time-energy measure for the actual right-germ martingale constructed
at checkpoint1314. It does not construct a pathwise quadratic variation or
claim that the original raw martingale is its modification.

## Whole-neighborhood L2 right continuity

`IBMRightGermContinuity.rightPast_idempotent` proves

    intersection_{u>t} R_u = R_t,

where R_t is the verified intersection of strictly future actual IBM L2 pasts.
One inclusion is monotonicity. For the other, given v>t choose t<u<v, then
R_u is contained in the original L2 past at v. This uses density of nonnegative
real time, and does not assert right continuity of the original raw filtration.

For any fixed joint L2 variable f, the orthogonal complements R_u-perp increase
as u decreases to t. Existing Mathlib Hilbert projection convergence, indexed
by the order dual of the ENTIRE interval (t,infinity), gives convergence onto
the closed span of these complements. Subtracting from f, identifying the
orthogonal complement of that closed span, and using the intersection identity
proves `projection_right_continuous`:

    ContinuousWithinAt (fun u => P_{R_u} f) (Ici t) t.

The subtype atBot/right-neighborhood filter identity is explicit. This is
strong L2 topology over the whole right neighborhood, not just one grid or
monotone sequences, and not merely weak or test-probe convergence.

Locally choose a fixed future horizon T=t+1. For u<T, the previously verified
horizon theorem says r_u=P_{R_u} M_T. Thus
`rightLimitClass_right_continuous` proves strong L2 right continuity of the
actual martingale classes at every nonnegative time. Arbitrary sequences
approaching from the right inherit the result without a monotonicity assumption.

## A genuine expected-increment energy measure

`IBMRightGermEnergyMeasure.energy` is E(t)=||r_t||^2. Nested projections imply
E is increasing; strong L2 right continuity implies E is right continuous.
The existing Stieltjes construction therefore produces an actual Borel measure
`energyMeasure` on nonnegative real time, with

    energyMeasure((s,t]) = ofReal(E(t)-E(s)).

For s<=t, the martingale projection identity makes r_t-r_s orthogonal to R_s.
Pythagoras and membership of r_s yield

    E(t)-E(s) = ||r_t-r_s||^2
             = integral (rightValue t - rightValue s)^2 d jointMeasure.

The last equality uses the actual Lp representative subtraction identity and
the actual L2 inner-product integral, not a hypothetical covariance law.
The interval measure is consequently the exact actual expected squared scalar
increment. It is locally finite, zero on {0}, positive on (0,T] for every T>0,
and at most ofReal(2*T^2) there. Nontriviality and the bound reuse checkpoint1313.
No elapsed-time/Brownian variance normalization or increment independence is
inserted. Countable additivity comes from an actual Measure, not an interval
set function or a finitely additive placeholder.

The prior generic raw-martingale energy obstruction is not contradicted: that
example has a jump immediately after zero and lacks the right continuity now
proved for this explicitly constructed process. The original IBM raw M remains
distinct until its positive-time zero-jump condition is proved.

## Exact limitations and next obligations

This is the deterministic expected-energy measure of r. A random pathwise
quadratic variation, predictable bracket, random coefficient control measure,
and a full predictable-integrand isometry are not established here. The measure
provides the appropriate deterministic increment-energy input for constructing
deterministic step integrals and their L2 completion; arbitrary random
coefficients require their actual conditional/random increment energies.

Strong L2 right continuity does not prove almost-sure right-continuous or cadlag
sample paths, a jointly time/sample measurable modification, or equality of r
and the original raw M. Existing J_t=0 at the origin, and the positive-time
agreement iff zero-jump theorem, remain the exact status. A regular-version
construction must supply actual hypotheses and a common path event. Finite
common-refinement/continuum-domain, intrinsic adjoint, Clark–Ocone and actual
unsmoothed IBM Itô obligations remain open. All F1/F2 correction and K domains
and all manuscript/campaign gates are preserved.

## Verification contract

The checkpoint evidence file is
`STARDUST_IBM_RIGHT_GERM_ENERGY_VERIFICATION.json`: fresh complete root build,
complete transitive safe-Foundation axiom audit, every new public type printed
and read unabridged, complete source/proof review, four independent Lean checks,
prior source/configuration identity and all 113 archive paths/hashes.

Independent checks exercise arbitrary nonmonotone right-approaching sequences;
positive bounded actual interval mass and its scalar increment integral;
temporal additivity of actual expected squared increments; and vanishing of
actual expected squared increments over whole shrinking right neighborhoods.
The exact Git receipt and verified PRIVATE main/research backup are recorded
only after the audited commit exists and synchronization actually succeeds.
