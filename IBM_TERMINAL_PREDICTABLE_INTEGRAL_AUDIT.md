# Actual random predictable integration for IBM terminal martingales — checkpoint1322

IBM remains active. This checkpoint extends actual finite-step and finite-grid
integration to EVERY terminal-observable martingale constructed at1321. It
reuses the existing full raw-IBM-past coefficient type, predictable time
processes and sampled filtration. A proved horizon agreement connects it to
the previous quadratic-channel integral. This is not a completed countable or
continuum random predictable domain.

## Actual integrator and reused coefficients

For any terminal F in the original JointL2 space, N_t^F=rawValue(F,t) is the
verified actual scalar martingale E[F|raw IBM past at t]. Define the actual
stochastic step a*(N_t^F-N_s^F). The coefficient a is the SAME
`IBMIntrinsicMartingaleStep.Coefficient s` already in the library: a real
function strongly measurable in the ENTIRE raw IBM past at s, with its actual
almost-sure bound. No finite-cylinder, polynomial, deterministic or Gaussian
coefficient restriction is added.

The actual increment is L2. Bounded multiplication supplies genuine L2 for
the actual scalar stochastic step and its Lp class. The actual martingale
conditional identity gives zero conditional increment mean; conditional
pullout then gives zero conditional step mean. The step's L2 class belongs to
the raw past at t when s<=t and has zero projection onto the full raw past at s.
Thus it is orthogonal to EVERY L2 variable in that past. Ordered disjoint
stochastic steps are consequently orthogonal, even with random past-dependent
coefficients. No increment independence is used.

The existing predictable time process associated with the coefficient and
interval is reused and remains strongly predictable in the raw observation
filtration. It is associated here with the actual N^F stochastic step; the
observed process generating the past and the martingale integrator are kept
distinct. In particular N_s^observed(1) is NOT replaced with actual IBM Z_s.

## Actual sums and exact energy

For EVERY monotone time grid, including repeated times, and every sequence of
these bounded raw-past coefficients, finite sums are actual scalar random
variables with genuine JointL2 classes. They belong to the raw past at the
current grid time. The accumulated scalar sums satisfy the FULL Martingale
predicate under the existing sampled full raw filtration.

Orthogonality gives their finite isometry in actual increment energies:

    E[(sum_i a_i * Delta N_i)^2] = sum_i E[a_i^2 * (Delta N_i)^2].

Each expectation is the actual Bochner integral on the original probability
space. The coefficient and increment are retained TOGETHER inside it. There
is no substitution of elapsed Brownian time, deterministic conditional
variance, independent increments or a factored coefficient expectation.
The coefficient time sum is the existing actual predictable process.

Unit coefficients telescope exactly at the scalar-function level. On a monotone grid
starting at zero and ending at one, unit integration against the actual
zero-start odd terminal martingale N^observed(1) equals the actual scalar IBM
coordinate at time one almost surely. It uses the verified RAW zero start,
not an assumption that the augmented channel's initial germ vanishes.

## Compatibility with earlier verified integration

Choose terminal F equal to the existing quadratic martingale's L2 value at a
fixed horizon H. For every u<=H, the previously verified projection identity
and scalar bridges identify rawValue(F,u) with the original quadratic
martingale at u. Hence every stochastic step within H agrees with the earlier
actual quadratic-channel step integral, for the SAME random coefficient.
Finite-grid sums within H agree as actual JointL2 classes as well.

This is a proved reuse bridge, not an inferred retargeting of old results.
Prior mathematical sources and the original process M/F/Z are unchanged.
The new definitions provide the needed terminal parameter while reusing the
existing coefficient, predictability and filtration machinery.

## Remaining random-domain and calculus obligations

The proved objects are genuine finite stochastic sums indexed by specified
time grids and coefficients. This checkpoint does not define an integral on
all predictable processes or prove arbitrary cross-presentation consistency,
countable-grid convergence, a random control measure or continuum completion
for these new channels. Do not substitute a completion defined only by the
image norm and call it a verified process-domain integral.

Uniform energy control and countable orthogonal-series convergence are a
natural next use of the existing library. A continuum domain still needs the
actual time-process/presentation identification and proper weighted control.
The raw/right-germ initial distinction remains open; raw zero start alone
does not prove energy right continuity or augmented initial triviality.
Native derivative-adjoint compatibility, Clark–Ocone, regular versions/bracket
and unsmoothed actual IBM Itô remain open. Keep all F1/F2 correction and K
restrictions and the existing campaign order.

## Verification contract

`STARDUST_IBM_TERMINAL_PREDICTABLE_INTEGRAL_VERIFICATION.json` records a fresh
full-root build, complete transitive safe-Foundation axiom audit, every new
unabridged public type and complete source/proof review, four independent
Lean checks, prior source/configuration identity and all 113 manuscript hashes.
Checks use an actual sine-of-IBM random coefficient, the full sampled
martingale/weighted-energy identity, concrete two-cell unit recovery of actual
IBM1, and agreement with the earlier quadratic integral and its predictable
coefficient process. Exact Git receipt and verified PRIVATE main/research
backup close separately; the precommit evidence claims no completed backup.
