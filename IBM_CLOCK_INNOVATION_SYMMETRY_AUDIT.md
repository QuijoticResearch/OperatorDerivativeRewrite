# Actual IBM clock-sign obstruction and temporal reuse audit — checkpoint 1306

IBM remains ACTIVE. This checkpoint audits a concrete temporal realization gap,
following checkpoint 1305's native divergence identification. It proves that
the ACTUAL signed Brownian clock cannot be used directly as an integrator
adapted to IBM's raw natural filtration. It does not exclude all clock-driven
representations or all intrinsic martingales.

## What the existing F1 construction actually supplies

`GaussianSourceClockIto.Domain T` is the source-valued L2 space predictable for
`GaussianTimeProcess.naturalFiltration`, the Brownian CLOCK filtration. Its
source values live in the independent scenery Gaussian L2 space. Its integral
is the existing scalar Brownian Itô isometry lifted to those source parameters;
the factor order is explicit in `GaussianParameterizedIto.realIntegral`.
This definition does not assert IBM-natural predictability or measurability
of the signed clock in IBM's past.

`IBMSchwartzFullReflectedIto.endpointLimitClass_actual_sections` identifies the
UNSMOOTHED F1 endpoint with the actual function g(a+Z_T)−g(a), by actual scenery
sections of the constructed continuous paths. `IBMDilatedPredictableLimit`
proves convergence of the actual predictable source–clock fields, with an
integrable C_g/sqrt(t) time-energy majorant, and convergence of the original
correction family in the verified common clock-number dual topology. Its
`stochastic_reconstruction` retains the bounded clock-number smoothing K on
the endpoint. No theorem inspected here licenses dropping K, identifies its
compression with the identity on the IBM past, or makes its native fields
IBM-natural predictable. Preserve the F1/F2 corrected identities and topologies.

## Actual measure-preserving symmetry, including path null sets

`GaussianSampleReflection.reflect_preserving` constructs global coordinate
negation on the EXISTING countable Gaussian product sample. It preserves that
measure by Mathlib's `Measure.infinitePi_map_pi` and the actual centered Gaussian
reflection law. Its L2 pullback is a genuine linear isometry.
`reflection_firstChaos` proves that EVERY first-chaos class is odd, by mapping
the existing unconditional coordinate-series convergence through this isometry.
No independently postulated noise or reflection law is introduced.

`IBMClockSignSymmetry.process_reflect_ae` applies this to the actual Gaussian
Brownian clock. `clock_reflect_simultaneous` upgrades coordinate almost-everywhere
reflection to ONE probability-one set on which it holds for EVERY time. This
uses a countable dense time sequence and continuity of both actual clock paths;
it does not intersect uncountably many null sets.

`reflectClock_preserving` preserves the actual joint scenery/clock probability
law while leaving the scenery sample fixed. `ibm_reflect_simultaneous` proves
that the ENTIRE actual IBM path is unchanged almost everywhere under this map,
because its random scenery time is |Y_t|.

## Exact observation and clock-channel consequences

`IBMClockInnovationObstruction.observable_fixed` uses measurable
Doob–Dynkin factorization of representatives in the existing all-time
IBM-observable sigma algebra. EVERY such L2 class is fixed by the actual joint
reflection. Therefore EVERY reflection-odd joint L2 class is orthogonal to the
entire observable space. A nonzero odd class is not IBM-observable at all.
`odd_condExpL2_zero` projects any such odd class to zero in EVERY actual finite
natural past, using the verified inclusion of that past in the full observable
space and the actual closed-subspace projection characterization.

The existing `IBMClockConditionalCorrection.clockLift` transfers the Gaussian
clock classes into the actual joint probability space. Its reflection
intertwining is proved, rather than inferred from the name of a clock operator.
`clock_firstChaos_condExp_zero` gives zero for EVERY lifted clock first chaos.
`signed_clock_condExp_zero` translates this to the actual continuous clock:

    E[Y_t | F_T^IBM] = 0  almost everywhere, for EVERY t,T≥0.

For t>0 its L2 norm is nonzero, by the already verified Brownian increment norm.
Thus `clock_class_not_in_past` and `signed_clock_not_measurable` prove that Y_t
is not even almost-everywhere measurable in ANY finite IBM past, including
future horizons T>t. `signed_clock_not_stronglyAdapted` proves the corresponding
actual-process adaptation failure.

`IBMClockMixedSymmetry.mixed_clock_condExp_zero` extends the vanishing to
arbitrary scenery coefficients a in Gaussian L2 times ANY first-clock-chaos
class. `mixed_clock_orthogonal` makes this orthogonality valid against EVERY
actual IBM-observable L2 class. This is a precise source-resolved first-clock
channel constraint, not a separate chaos campaign or a claim about all sectors.

## Limits of the obstruction and the constructive next question

The signed clock is not an IBM-natural innovation process, and its conditional
projection is identically zero. Replacing it by that projection cannot recover
a nontrivial centered observable. This does NOT remove the clock derivative
or clock divergence from the proved two-source calculus. An odd clock-dependent
integrand can give an EVEN stochastic-integral terminal value. The independent
Lean check reuses the existing Hermite Itô representation to prove that
integral_0^1 Y_s dY_s=(Y_1^2−1)/2 is even under this reflection and has squared
L2 norm 1/2. The existing `BrownianSignIntegral.brownian_field_joint` identifies
that Hermite integrand with the actual clock field on (0,1]. The odd obstruction
does not apply to this nonzero genuine integral.
Its conditional projection into IBM's past is not determined by that check.

In particular, no absence of intrinsic martingales, no complete failure of
clock-driven calculus, and no nonsemimartingale theorem is claimed. Nor is
|Y_t| or the Lévy sign integral asserted measurable in IBM's past. The existing
`BrownianSignConditional` proves L2 conditional consistency/covariance for its
actual sign integral; those results alone are not a Brownian-law assertion.

Next investigate a concrete EVEN clock channel, such as the conditional
projection of the existing quadratic clock martingale, using actual one-time
scenery/clock moments and the verified clock conditional Itô machinery. Prove
nontriviality and the required temporal conditional consistency rather than
postulating a Gaussian innovation from covariance. Retain the correction terms
and operator domains needed for the full intrinsic IBM calculus.

Full root build, complete transitive safe-Foundation axiom audit, unabridged
public-type/proof review, independent Lean tests and archive/source hashes are
recorded in `STARDUST_IBM_CLOCK_SYMMETRY_VERIFICATION.json`. No new axiom,
toolchain, trust setting, proof-resource override or permanent configuration
change is introduced. Manuscripts and the campaign queue are unchanged.
