# Actual IBM coordinate prediction at the initial right germ

Checkpoint1329 discharges checkpoint1328's specific odd-coordinate initial
projection obligation for EVERY nonnegative terminal time. IBM remains ACTIVE.
This is a theorem about the actual constructed IBM and its explicit augmented
right-germ filtration, not a conditional abstract model or an assumed zero–one law.

## Exact result and domains

Write Z_t = W(abs(Y_t)) for `IBMConstructedSources.ibmValue t` on the existing
joint Gaussian product probability space. Let G be the EXISTING filtration
`IBMRightGermFiltration.germFiltration`: ambient-null augmentation of the raw
observed IBM natural filtration, followed by right-continuous intersection.
For every t >= 0, the new Lean theorems establish

    E[Z_t | G_0] = 0 almost surely,
    channelClass (observed t) 0 = 0 in actual joint L2.

Equivalently, every G_0-measurable event A has actual integral of Z_t over A
equal to zero. No finite-coordinate or polynomial restriction on A is imposed.
This proves zero INITIAL projection of the actual observed linear coordinate;
it does not prove the whole initial sigma algebra is trivial, nor equality of
raw and right-germ projections at positive times for this or arbitrary terminals.

## Reused foundations and proof

`IBMBoundedGermFactors` applies the existing measurable factorization through
the ENTIRE raw IBM past to an L2 observable in that past. The representative
is factorized, then its measurable factor map is clipped by max(-C,min(C,x)).
If the original observable has absolute value <= C almost surely and C>=0,
this preserves its original realization almost surely and bounds the factor
on EVERY possible past path. This global bound matters when applying the map
to the clipped process: an AE bound under the original process alone would
not justify dominated convergence for the substituted process.

Every bounded initial-germ L2 observable has such a bounded measurable map
through each positive shrinking raw past, by verified rightPast_le_past.
The checkpoint1328 simultaneous early-path agreement gives almost-sure
convergence of its clipped realizations back to the original observable.
For ANY actual integrable scalar A, `localized_pairing_tendsto` justifies
convergence of the integrals against A by the explicit integrable dominator
norm(A)*C. This closes the needed convergence topology: actual real pairing
convergence under the original joint probability measure. Strong L2 convergence
of arbitrary unbounded substituted functionals is not assumed or asserted.

`IBMClippedForecastPairing.past_pairing` proves an ACTUAL joint-law identity:
for every bounded measurable functional a of the entire clipped past,

    E[Z_t * a] = E[W(min(abs(Y_t),delta)) * a].

Both joint products are proved integrable using boundedness and the existing
actual L2 coordinate domains. Product Fubini is applied only with this proved
integrability. For almost every fixed clock, the WHOLE clipped past is measurable
in scenery past through delta, and the verified actual conditional section
formula gives the forecast. Pull-out and integral preservation of conditional
expectation prove the section pairing; integrating these section equalities
proves the joint pairing. This is a joint integral theorem, without declaring
an unproved enlarged-filtration conditional expectation law.

Pass to shrinking original pasts for a fixed radius delta>0. The two dominated
pairing limits give, for every bounded initial-germ test f,

    inner(observed t,f) = inner(forecast(t,delta),f).

Now let delta decrease dyadically to zero. Checkpoint1328 already proves the
forecast tends STRONGLY to zero in actual joint L2, from its sqrt(delta) norm
bound. Continuity of the Hilbert inner product therefore makes every such
bounded test pairing zero. No interchange of unproved limits is used: first
the early-past limit at fixed radius, then the radius limit.

`IBMObservedInitialGerm` tests this identity on ACTUAL L2 indicators of every
G_0-measurable event. Their membership in rightPast0 follows from the verified
germPast_eq theorem, not from a guessed raw/germ identification. Their bound1
is proved. This gives all required zero set integrals. Mathlib's conditional
expectation uniqueness theorem then proves E[Z_t|G_0]=0; the existing actual
projection/CE bridge gives initial_channel_zero. No new density theorem or
source Blumenthal infrastructure is needed.

## Consequences for the existing operator and energy machinery

The existing raw projection of the germ gives rawClass(observed t)0=0.
Along ANY antitone strictly positive horizons tending tozero, the existing
strong raw-right-limit theorem now yields raw coordinate predictions ->0
strongly in actual joint L2. This resolves the initial coordinate gap only.

The EXISTING globally finite germ-channel energy measure for terminal
observed t now has exact mass

    energyMeasure(observed t)((0,t]) = ofReal(norm(observed t)^2).

Its initial projection deficit has been rigorously removed for these actual
terminals. At t=1 this mass is strictly positive by the verified nonzero IBM
coordinate. This remains the energy measure of the terminal-dependent G-channel;
it is not a pathwise bracket or a universal stochastic integrator for Z.

## Independent tests and verification

Four independent Lean examples test actual conditional zero and projection at
terminal1; a nonlinear sine of the actual clipped past paired with IBM at2;
zero set integrals on arbitrary measurable events of the completed initial
germ; and positive full terminal1 energy together with strong dyadic raw
prediction convergence tozero. All three new source modules, actual unabridged
public types and full proof arguments must be reviewed. A fresh complete root
build and COMPLETE transitive safe-Foundation axiom audit retain only propext,
Classical.choice and Quot.sound. No compiler/resource/trust settings change.
Exact results and timings are recorded in
`STARDUST_IBM_OBSERVED_INITIAL_GERM_VERIFICATION.json`.

## Precise remaining obligations

Full initial-germ triviality, arbitrary terminal initial projections, and
positive-time raw/germ equality remain OPEN. Checkpoint1327's finite RAW
energy-measure existence iff ALL-time projection equality is not discharged
by proving equality at time0 for the observed coordinate. Do not retarget
the existing germ measures to raw sums without their exact comparison gate.

Joint predictable rectangle extension, an actual continuum random-integrand
domain with closure/approximation, regular versions and pathwise bracket,
intrinsic IBM derivatives/adjoints, a universal Clark–Ocone representation,
and actual unsmoothed IBM Itô–Tanaka/F1–F3 completion remain OPEN. Native IBM
calculus is not complete. Original M/F/Z and F1/F2 correction/K domains are
unchanged. IBM stays active and the campaign queue is unchanged.

All2123 prior Foundation/root sources except exactly three root imports,
all3 configurations and all113 archive paths/hashes must be unchanged.
Manuscripts remain immutable and unstaged; unrelated drafts remain untouched.
After the audited explicit-path commit, require its exact receipt and verified
PRIVATE main/research synchronization. Precommit evidence claims no backup
closure. October31 remains review-only, with no research expiration.


## Preservation of the completed focused F1–F3 theorems

Checkpoint1107's focused F1–F3 results remain VERIFIED within their exact
domains: K-smoothed full cross-sector correction convergence and stochastic
reconstruction; the literal boundary-layer random-functional ordinary L2
limit; and a dense maximal intrinsic core with CLOSED densely defined joint
derivative and its actual Hilbert adjoint. See IBM_F1_F3_VERIFIED_CHECKPOINT.md.
The later broader intrinsic campaign does not reopen these completed theorems.

References below to open “intrinsic derivatives/adjoints” or “Itô–Tanaka/F1–F3
completion” concern the full native process calculus BEYOND those verified
domains: for example unrestricted unmollified corrections, native stochastic
integration/adjoint identification, domain equality, representation and closure.
They must not be read as declaring the existing F1–F3 theorems unproved.
The lifted ambient divergence domain is not assumed equal to the entire
intrinsic adjoint domain. No physical H^-1/common-clock-dual equivalence or
ordinary raw full-correction L2 convergence is inferred. Exact existing
theorem hypotheses and limitations remain unchanged. Current IBM campaign
and queue unchanged; checkpoint1329's initial-coordinate theorem stands.
