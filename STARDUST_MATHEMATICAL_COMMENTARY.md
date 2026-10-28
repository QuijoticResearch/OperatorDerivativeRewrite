# Mathematical commentary and opportunities

This is a synthesis of verified mathematics, not a chronology or novelty claim.
Exact Lean types and audited sources govern every assertion. Bakry Objective 2 is active;
the opportunities below do not change the [queue](STARDUST_CAMPAIGN_QUEUE.md).

## The three Fourier spaces that must not be conflated

The new Bakry bridge has three distinct levels. Finite covariance matrices
and actual pointwise Γₙ on trigonometric polynomials are positive for the
anisotropic fractional symbol when each weight is nonnegative and each
exponent lies strictly between0 and2 (`AnisotropicStableGamma`). The
diagonal multiplier also yields a closed, strongly continuous contraction
semigroup on the abstract coefficient Hilbert space ℓ²(ℤ³), for ANY
nonnegative rate (`WaveDiagonalSemigroup`). Neither statement by itself
constructs a physical Markov process.

The third level is the actual normalized three-coordinate torus integral.
`WavePhysicalFourierBridge.box_parseval_all` computes it exactly on EVERY
finite Fourier polynomial. `box_gamma1_energy` proves that the integrated
first Γ equals negative generator energy when the symbol vanishes at zero.
This specializes to the anisotropic rate and is a genuine physical finite-
core identity. It generalizes the earlier single-axis finite Parseval
calculation in `CauchyCenteredEnergy.axis_parseval`, but does not yet identify
the abstract ℓ² completion with physical Haar-L² functions.

There are two sharp cautions. A zero coordinate weight leaves a nonzero
stationary frequency, so the covariance theorem does not yield a positive
spectral gap. For the constant symbol ψ≡1, the zero mode has integrated
Γ₁=1/2 but generator energy1: the zero-normalization hypothesis cannot be
silently dropped. The viable next step is a proved isometric physical
Haar-L² Fourier map that intertwines the closed semigroup, followed by a
separate positivity-preservation test. This is standard Fourier/Dirichlet
mathematics until a more specific new consequence is established.

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

**Former opportunity R3 — RESOLVED on uniform grids.** The conditional fourth
moments, overlap sums and reflected-clock crossing penalties were combined into
`IBMUniformQuarticVariation.quartic_tendstoInMeasure`: actual quartic variation
tends to 3T in probability for ALL uniform N=n+1 grids. The stronger prefix
error maximum is controlled by `IBMUniformPrefixMaximum.maximum_tendstoInMeasure`.
This closes the former variance/partition-limit obligation in that exact scope,
not for arbitrary partitions or almost-sure full-sequence convergence. The
earlier moment-only calculations remain useful proof inputs, rather than the
final limit theorem.

## A calculus through cancellation, and the topology it actually reaches

Quartic tightness and compact spatial Peano control now turn the old variation
work into an actual stochastic quadrature theorem. Every sample has compact
range and vanishing mesh. Total absolute fourth-order error is eventually at
most epsilon times its quartic mass. `IBMActualSimpson.sums_tendstoInMeasure`
therefore requires only a global C3 one-form, not a fifth derivative, global
growth bounds or moment estimates. Its spatial midpoint is NOT evaluation at
a midpoint in physical time. This distinction belongs in every reuse.

`IBMActualQuadraticDivergence.first_identity` gives exact raw-rank cancellation
for z², while `quadratic_no_finite_limit` and `first_no_finite_limit` rule out
separate finite probability limits. One must preserve the combined prescription.
Simpson and lower Taylor prescriptions differ: quartic Taylor has the 3T
correction, whereas the derivative's Simpson sum telescopes exactly. This is
a useful counterexample to prescription-independent notions of integral.

One compact error modulus controls ALL prefixes, avoiding an N-dependent union
bound. Finite Abel summation then transfers prefix control to deterministic C1
time weights via the compact bound B+KT. `IBMTimeWeightQuadrature.rightSum_tendsto`
supplies the genuine time correction for every continuous path; no finite
variation of the IBM path is assumed. `IBMTimeWeightedSimpson.derivative_weighted_tendstoInMeasure`
is consequently a proved SEPARABLE spacetime chain rule, not general F(t,z).

The operator connection has its own exact topology. Explicitly clipped cosine
sums converge in observable L2, then in the ORIGINAL graph-dual norm and every
full adjoint-domain test pairing (`IBMSimpsonGraphDual.actual_pairing_tendsto`).
The sine target nevertheless stays outside the strong joint derivative domain.
`tracked_graph_escape` shows that any strong-domain approximation tracking those
actual sums must have gradient norms tending to infinity. Weak derivative
existence, strong-domain membership and causal stochastic integration cannot
be substituted for one another. No raw-sum L2 upgrade is established.

**Former opportunity R4 — RESOLVED in the deterministic smooth scope.**
`IBMTimeSpaceSimpson.sums_tendstoInMeasure` uses C1 time slices, C4 space slices
and joint continuity of the time partial/fourth spatial derivative. Its compact
Peano control is uniform in time, and the genuine time integral is proved.
`IBMUniformTimeSpace.maximum_tendstoInMeasure` controls all common-grid prefixes.
With joint continuity of F, `IBMContinuousSimpsonRealization.approximation_tendstoInMeasure`
gives Bernstein polynomial continuous-path approximants converging in probability
in supremum norm. Value-only separable approximation was insufficient; the
verified route supplied the missing derivative and quadrature estimates.
Bernstein coefficients use all grid prefixes, so this is not a causal or linear
interpolation theorem. Random coefficients and nonsmooth Tanaka remain separate.

## Three operations that must not be conflated

The original native grid outputs have divergent intrinsic Hilbert norms and,
by Banach–Steinhaus, no weak Hilbert limit or weak convergent subsequence at a
positive horizon (`IBMNativeWeakObstruction`). Later genuine Fourier
source-lowered actions nevertheless converge in clock L2 and clock L1
(`IBMFourierCylinderSeries.native_tendsto`, `source_native_tendsto`). This does
not contradict Hilbert escape: a smaller tested action and a different topology
were identified. The action limit is not the original observable.

A different operation averages the scenery source of the actual IBM observable
F. Its mean M involves exp(-Q/2), where Q is the actual folded covariance
variance. GaussianAbsoluteMinimumGraph supplies the ORIGINAL first derivative
of minimum through (f+h-|f-h|)/2, preserving collision and zero-level terms.
This closes the classical cusp obstruction to original clock-graph membership
of M. It supplies no second-derivative or divergence-domain theorem by itself.

With curvature summability,1519 proves the completed actual mean has original
gradient G. At1520, actual raw Brownian and finite-past measurability then let
the existing genuine Brownian Clark–Ocone theorem apply: the unique predictable
coefficient is U=predictableProjection G. The full-time and finite-horizon
stochastic identities hold; PRP and support require only sumabsw, not the
extra curvature hypothesis used to identify the full gradient.

Source averaging destroys information. For an exact single-frequency pi/2
example, F=-sin(Z_R), M=U=0 while F is nonconstant at every R>0 and remains
outside the original joint derivative domain. Combining the existing static
source recovery with the genuine predictable CLOCK field nevertheless gives
`IBMFourierHybridReconstruction.reconstruction`: original joint divergence
equals F-EF. The positive representation and negative strong-domain statement
apply to the SAME actual observable. Neither licenses dropping the source
channel or claiming full strong differentiability of F.

**Opportunity R5 — exact active IBM frontier, UNPROVED here.** For a proposed
OBSERVED-filtration coefficient K, prove membership in the original observed
predictable integral domain, identify that actual integral with the desired
physical prescription, and prove the residual F-EF-I_obs(K) vanishes in the
required topology. A nonzero residual would delimit the proposal. The current
U uses the hidden Brownian clock; the other channel is static source adjoint
recovery. No theorem says projection to the intrinsic observable space preserves
derivative domains or causal support. Audit existing stochastic-energy,
occupation and native/adjoint results before constructing another map.
This is an exact Stardust obligation, not a claim about an established external
open problem, a novelty assertion, or a change of campaign.

References and precise domains: [focused LaTeX/PDF note](manuscripts/ibm-clock-hybrid/main.pdf),
[updated signed Simpson draft](manuscripts/ibm-signed-simpson/main.pdf), and
checkpoints1515–1520 in the research ledger.

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
