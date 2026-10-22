# Actual IBM scenery forecasting and shrinking-past localization

Checkpoint1328 advances the initial-germ obligation within the ACTIVE IBM
campaign. It does NOT prove the initial odd germ vanishes or finish the
raw/germ comparison exposed by1327.

## The actual process and reuse decision

The verified `IBMConstructedSources.ibmValue_eq` is
Z_t(omegaX,omegaY)=sceneryPath(omegaX)(abs(clockPath(omegaY)(t))). This is
W(|Y_t|), using the positive Brownian scenery branch. The source audit found
no matching ready-made initial-germ zero–one theorem in the inspected
Foundation and Mathlib BrownianMotion files. A full new Blumenthal theorem
is not introduced. Instead this checkpoint directly reuses the actual
positive-scenery Brownian law, `IsPreBrownianReal.indepFun_shift`, full natural
past factorization, Gaussian source L2 realization, constructed continuous
paths, and the existing joint product isometry.

## Whole spatial-past prediction

`IBMSpatialSceneryForecast` defines the natural filtration of the ACTUAL
positive scenery W_r=sceneryPath(r) on the original Gaussian factor. For
ALL r,delta>=0 it proves

    E[W_r | entire W past through delta] = W_(min(r,delta)) almost surely.

For r>=delta, the Brownian shift-independence theorem gives independence of
the following increment from the WHOLE coordinate past, not just a finite
family or covariance pairing. Zero increment mean and conditional expectation
then give the formula. For r<=delta the variable is already measurable.
The actual L2 projection is identified with the existing `sourceScenery`
class at min(r,delta). Its squared norm is exactly min(r,delta), hence <=delta.
No assumed Gaussian conditional projection is substituted for a proof on
the actual continuous-source natural filtration.

## Genuine clipped process and random-clock forecast

`IBMClippedSceneryForecast.actualValue delta t` is the actual process

    W(min(|Y_t|,delta)).

Every sample path is continuous, the process is jointly time/sample measurable,
and each time coordinate is genuinely L2. `sourceSlice` is the corresponding
clock-indexed existing Gaussian source class. `slice_projection` identifies
it with the whole-spatial-past conditional L2 projection of the IBM terminal
source section at EVERY fixed raw clock sample. `actual_section_prediction`
transfers this to the ACTUAL continuous path versions, for almost every clock
sample and almost every scenery sample. Its conditioning sigma algebra is
the scenery past, with the clock fixed; it is NOT the raw IBM observed past.

`field` is a genuine Bochner L2 clock field and `forecast` its actual joint
realization. The scalar AE bridge identifies forecast with actualValue,
and ||forecast(t,delta)||_2 <= sqrt(delta), uniformly in terminal t. Thus
for any radii delta_n->0, forecast(t,delta_n)->0 strongly in actual joint L2.
This is NOT a claim that Z_t itself tends to zero at a fixed positive t.

For every fixed clock sample, each clipped observation and EVERY measurable
functional of its complete time past is measurable in the positive scenery
past through delta. `past_functional_spatial_measurable` uses the entire
existing pastCoefficient domain (Iic T -> Real), without a finite-coordinate
or polynomial restriction. No joint enlarged-filtration conditional law is
asserted merely from the per-clock conditional statement.

## Simultaneous shrinking-past agreement

`IBMClockGermLocalization` first proves actual clockPath(0)=0 on ONE joint
full-probability event. Actual path continuity then proves: for ANY fixed
delta>0 and ANY sequence of nonnegative horizons tau_n->0, almost surely,
eventually n, EVERY r<=tau_n has |Y_r|<=delta. No monotonicity of tau is required.
Consequently the clipped process and actual IBM agree at ALL times in that
early interval simultaneously. This uses deterministic continuity on a single
source event, not an uncountable intersection of coordinate AE events.

The agreement transfers to arbitrary, even n-dependent, complete-past
functionals g_n. If their original IBM realizations equal a fixed function f
almost surely at every n, then their clipped realizations tend to f almost
surely. Only a COUNTABLE n-intersection is used. The conclusion is POINTWISE
almost-sure convergence. Uniform bounds/integrability and strong L2 convergence
of those arbitrary functionals are not inferred from it.

## Exact remaining initial-germ proof

The new results give the concrete localization inputs, but `channelClass
(observed T) 0=0` remains OPEN. A productive route is to factor a bounded
initial-germ test observable through every shrinking raw IBM past, clamp
the measurable factor maps to a common bound, and apply the proved clipped
past agreement. Prove strong L2 convergence (or justified dominated pairing
convergence), then use the WHOLE-scenery-past conditional forecast and Fubini
to identify its pairing with Z_T as its pairing with the clipped terminal.
The latter is bounded by sqrt(delta) times the test norm. Finally pass delta
to zero and use a rigorously proved dense bounded-test or indicator-set
conditional-expectation argument. These boundedness, integrability, product
measurability/Fubini, and final density steps are NOT asserted completed here.

Continuity of paths alone does not prove right-continuity/triviality of a
natural filtration. The1327 raw-energy existence criterion remains gated.
Joint predictable measure extension, continuum integrand domain/closure,
regular versions/bracket, intrinsic derivatives/adjoints, full Clark–Ocone and
actual unsmoothed IBM Itô also remain OPEN. Original M/F/Z, F1/F2 correction/K
domains and campaign order remain unchanged. No generic martingale-channel
construction is being labeled full intrinsic IBM calculus.

## Verification

Three modules303lines,38 public declarations; all actual unabridged types
and complete proofs reviewed. Independent Lean checks cover exact whole-past
prediction/energy for scenery at2 observed through1/2; genuine random-clock
forecast strong convergence and actual conditional sections; simultaneous
early-path agreement; and arbitrary measurable full-past functional spatial
measurability and conditional pointwise approximation. Fresh full root build,
COMPLETE transitive safe-Foundation axiom audit with the same three allowed
standard axioms, and independent checks are recorded in
`STARDUST_IBM_INITIAL_GERM_LOCALIZATION_VERIFICATION.json`.
All2120 prior sources except3 root imports, all3 configurations and all113
archive paths/hashes must remain unchanged. No manuscript is modified/staged.
Exact-commit receipt and verified PRIVATE main/research closure follow the
audited commit; precommit evidence does not claim backup has occurred. IBM
and the indefinite goal remain ACTIVE; the saved campaign queue is unchanged.
