# Mathematical commentary and opportunities

This is a synthesis of verified mathematics, not a chronology or novelty claim.
Exact Lean types and audited sources govern every assertion. IBM remains active;
the opportunities below do not change the [queue](STARDUST_CAMPAIGN_QUEUE.md).

## Why changing the energy measure solved an actual integration gap

At1372, raw adapted rectangles and finite sums were identified with actual
stochastic integrals, but arbitrary bounded predictable multipliers were not.
Uniform approximation by finite rectangle sums was unavailable: a general
measurable function need not admit that approximation in uniform norm. This
was a mathematical limitation of that route, not a Lean tactic failure.

At1373 the rectangle identities instead identified an ENTIRE original measure:
`IBMStochasticIntegratorEnergy.energy_change` gives mu_(I_F H)=H² mu_F.
It follows that every K in the ORIGINAL output energy space has an actual
product HK in the original input energy space. The product map is an isometry,
and original dictionary density establishes actual stochastic associativity.
The zero set of H matters: output-energy AE equality transports to input-energy
AE equality only AFTER multiplication by H. Reverse absolute continuity would
be false in general and is not required.

For many channels, append one original channel and apply the full signed
joint-energy bound. Equal actual outputs then have equal common-g-modified
outputs. Existing terminal self-representation discharges the single-channel
representation premise. This closes the old bounded-action gap without a
new integral definition or an assumed representation theorem.

References: [exact audit](IBM_INTEGRATOR_ENERGY_PRODUCT_ASSOCIATIVITY_AUDIT.md),
`IBMStochasticProductAssociativity.weighted_ae`, `actual_associativity`,
`IBMCompletedBoundedAssociativity.comparison_bound`, `actual_bounded_associativity`.

## The common role of null relations

Gaussian cylinders may have correlated/dependent coordinate descriptions;
IBM integral sums can cancel across channels; signed pseudo-channel synthesis
can have a nontrivial kernel. In each setting a presentation must be identified
by its ACTUAL mathematical null relation before claiming uniqueness.

The relationship is precise but not an identification of the three spaces.
`HigherHeatCompletedClarkOcone.synthesis_uniqueness` characterizes equality by
the synthesis kernel; it does not assert integrand injectivity. IBM instead
quotients the FULL signed joint energy and obtains an actual output isometry.
Neither permits replacing cross terms by independent component energies.

**Opportunity R1 — extraction, not a new external open problem.** For bounded
linear maps A:E->H and B:E->K, with K complete, C>=0 and ||Bx||<=C||Ax||,
B vanishes on ker(A) and
descends continuously to the closure of range(A). This standard mechanism
underlies IBM's common-multiplier comparison. Before creating any abstraction,
audit Mathlib and existing quotient/extension declarations. Extract a reusable
interface only if a SECOND concrete proof needs it. No new abstraction or
newly proved general theorem is claimed by this reflection.
The independent Lean test verifies the kernel implication; it does not by
itself formalize extension to the closure. Completeness of the target is an
essential extension hypothesis, not a consequence of the kernel calculation.

## Uniform convergence: a useful transfer and a precise obstruction

At1374 the fixed actual IBM stochastic expansion acquires an exact continuous
nonnegative Parseval tail. It decreases with finite channel sets and tends to
zero. Pinned Dini gives compact-parameter uniformity AFTER all those hypotheses
are proved. Existing causal contractions give uniformity over every horizon;
the native transfer then gives ORIGINAL divergence graph-norm convergence.

**Opportunity R2 — signed compact-family realization, UNPROVED here.** The
pseudoprocess stopping theorem already gives a jointly convergent signed
polynomial/grid diagonal for EACH completed observable. A stronger candidate
asks for common grid/degree choices approximating a compact set of observables
uniformly in all surviving coefficient L1 norms and reconstruction dual norm.
The target maps are bounded, but that alone does not give uniformly bounded,
presentation-consistent NATIVE approximants. Prove that missing bound or give
a counterexample before using an epsilon-net argument. IBM's positive Parseval
tail does not transfer to an indefinite signed pairing. This is an unresolved
Stardust obligation; external novelty/open-problem status is unchecked. Defer
it to the appropriate campaign rather than reopening frozen pseudo work now.

References: `IBMUniformStochasticReconstruction.error_sq`, `gap_uniform`,
`uniform_native_graph`; `HigherHeatSignedDiagonalRealization.completed_signed_realization`;
[precise pseudo domain](STARDUST_PSEUDOPROCESS_STOPPING_AUDIT.md).

## What compact convergence leaves uncontrolled

IBM's sup_t ||error(t)||_L2 is weaker than ||sup_t |error(t)| ||_L2. A new maximal
estimate would be needed for the latter; moving-terminal coefficients do not
make the finite diagonal approximants martingales. Their actual causal form
does not license a Doob inequality without its martingale hypotheses.

The analogous quantifier issue in Xi flows is that locally uniform function
limits do not confine all zeros to a common compact set. The existing real-order
zero-limit theorem assumes convergence of the zero locations. The quartic
global theorem succeeds by matching near and far estimates with one scale,
not by promoting a finite window to the whole plane.

**Opportunity R3 — active-campaign next step.** For actual IBM quartic variation,
the existing conditional fourth-moment and overlap double-sum identities give
an explicit variance target. Obtain uniform overlap-sum and clock-crossing
penalty estimates for a specified refining partition, then prove a genuine
random-variable limit in a stated topology. Finite expectation equal to a
time-scale expression is not that limit. See `IBMFiniteQuarticSecondMoment`,
`IBMConditionalQuarticPair`, `IBMJointQuartic` and `IBMClockOverlapEnergy`.
This is directly relevant to the active IBM calculus; no new campaign is opened.

## Experience worth retaining

- Dense observable cores do not require rough point observations to lie in the
  native derivative domain. The existing sine-of-IBM domain obstruction and
  uniform stochastic reconstruction coexist; one does not refute the other.
- A finite complex-noise construction is not the full signed pseudoprocess
  reconstruction. The actual signed laws, completed OBSERVABLE domain and
  convergence topology are substantive parts of the repaired theorem.
- Full adjoint identities need graph approximation/closure arguments. An
  abstract formal adjoint or equivalent reformulation does not discharge a
  missing core theorem.
- Lean heartbeat/elaboration limits and coercion failures are implementation evidence,
  not mathematical counterexamples. Preserve their details in exact audits,
  while retaining the mathematical obstruction or repair here.
