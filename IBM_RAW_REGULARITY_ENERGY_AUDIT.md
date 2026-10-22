# Raw-filtration regularity and energy-measure audit — checkpoint1312

IBM remains ACTIVE. This checkpoint proves a concrete obstruction to a proposed
general shortcut for continuum stochastic integration, and separately proves
the actual intrinsic IBM martingale's strong L2 continuity at zero. It neither
attributes the counterexample to IBM nor declares IBM calculus impossible.

## Fully constructed counterexample

ContinuousObservationFiltrationObstruction uses the existing countable Gaussian
probability space and its actual first coordinate xi, with mean zero and
variance one. On real time define

    Z_t = max(t,0)*xi,
    M_t = xi if t>0, and 0 otherwise.

observation_continuous proves every Z path continuous. filtration is its actual
raw natural filtration. filtration_before proves F_t is exactly the bottom
sigma algebra for t<=0. coordinate_adapted proves xi strongly measurable in
EVERY F_t for t>0, by recovering it as Z_t/t. coordinate_not_adapted_zero proves
it is not strongly measurable at zero. filtration_not_right_continuous proves
the actual Mathlib IsRightContinuous predicate fails, using the exact right-
continuation intersection. No prescribed marginal-law process or unproved
realization is supplied.

actual_martingale proves the full Martingale predicate for M in that exact
filtration. value_memLp proves square integrability at every time and value_mean
proves centering. Its positive-time law is the actual standard Gaussian law.
The existing fixed-law path obstruction therefore proves both failure of almost-
sure right continuity and absence of ANY almost-surely right-continuous
modification preserving every fixed-time random variable almost surely.
Changing representatives on null sets cannot repair this example.

## Countable additivity is not supplied by finite-grid energy

increment_energy proves E[(M_t-M_0)^2]=1 for EVERY t>0. All finite ordered
martingale steps still make sense, but their Ioc energies cannot automatically
be promoted to a time measure.

RawMartingaleEnergyMeasureObstruction constructs I_n=(0,1/(n+1)], proves it is
decreasing and has empty intersection. Measure continuity from above implies
no measure rho can satisfy rho((0,t])=1 for every t>0. Finiteness of just one
such interval suffices; no global finite-measure assumption is needed.
no_actual_increment_energy_measure applies this directly to the actual squared-
increment energies of the constructed martingale. Thus NO countably additive
time measure has those Ioc values.

This refutes the generic implication from continuous observations plus a raw-
filtration L2 martingale and finite-grid energy identities to an Ioc energy
measure or a regular martingale modification. It does not exclude different
interval conventions, changed initial laws or filtrations, or other stochastic
calculi. Such repairs would require their own precise statements and proofs.

## What is actually known for intrinsic IBM

The IBM martingale is the existing genuine
M_t^IBM=E[Y_t^2-t|F_t^IBM], under the original joint law. Its verified squared
norm bound <=2t^2 gives origin_norm_bound <=2t. IBMIntrinsicOriginContinuity.
origin_tendsto proves strong scalar L2 convergence to zero as t->0 in NNReal's
ordinary topology. No monotonicity of an approaching sequence is required.
This is stronger at the origin than checkpoint1310's from-below endpoint
result, which at T=0 only permits times equal to zero.

Consequently the specific origin jump of the counterexample is rigorously
ruled out for actual intrinsic IBM. Right regularity at positive times, a
cadlag/right-continuous version, and the needed countably additive predictable
energy measure remain unproved. Continuous IBM observation paths alone cannot
be cited as sufficient, given the verified counterexample above. Ambient null
augmentation preserves previously verified conditional expectations but is not
a theorem granting right continuity; do not silently substitute a right-
continued filtration or change the actual process.

## Tests and next obligations

Independent Lean examples check the actual continuous observation/L2 martingale
construction; raw-filtration and all-modification regularity failure; exact
energy one at the short interval1/1000 versus zero at zero, together with the
no-measure theorem; and genuine IBM strong L2 convergence along the concrete
positive sequence (1/(n+1)).toNNReal. This keeps the generic counterexample and
actual IBM conclusion separate on their actual probability spaces.

Next investigate the actual positive-time regularity/variance and predictable
energy-measure hypotheses, alongside common finite refinements and simple-
process equality. A finite-grid output closure alone is not a completed
continuum integrand domain. Preserve all prior actual countable integration,
cofinal endpoint and predictability theorems, F1/F2 correction terms, clock-
number smoothing, native derivative/adjoint domains and campaign gates.
Full IBM calculus remains open. The queue and all manuscripts are unchanged.

## Verification contract

Three new modules require the complete root build, complete transitive safe-
Foundation axiom audit, actual unabridged public-type/proof review, four
independent Lean checks and all113 manuscript path/hash checks. Exact source
counts, observed terminal results and reproducible tests are recorded in
STARDUST_IBM_RAW_REGULARITY_VERIFICATION.json after verification succeeds.
Git/exact-receipt/verified PRIVATE main and research backup remain separate
final gates. No toolchain, resource, trust or audit configuration change.
