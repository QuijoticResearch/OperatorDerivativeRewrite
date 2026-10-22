# IBM clock-section finite-energy obstruction — checkpoint 1353

IBM remains the active campaign. This checkpoint proves an obstruction for the
actual scenery-valued clock section, not yet nonmembership of a point IBM
observation in the original joint Gaussian derivative domain.

## Established mathematics

Write `F(r) = sourceScenery |r|`, taking values in the already constructed
Gaussian scenery L² space. This is exactly the function used by
`IBMRandomTimeHilbert.randomSourceClass`; it is not a new process model.
For nonnegative r,s its squared increment norm is |r-s|.

`Foundation/IBMClockSectionEnergyObstruction.lean` proves:

* A Bochner primitive with L² derivative g satisfies
  `‖∫_[a,x] g‖² ≤ (x-a) ∫_[a,x] ‖g‖²`.
* More generally, any Banach-valued curve with squared increments from a bounded
  interval's left endpoint bounded below by `c*(x-a)`, c>0, cannot have such a
  primitive. Shrinking intervals would each require at least c energy, whereas
  the integral of the integrable energy density tends to zero.
* For continuous curves, an almost-everywhere primitive representation with
  any integration constant is also impossible. Continuous representatives agree
  everywhere on the closed interval, using its dense interior and positivity
  of Lebesgue measure on nonempty open sets.
* These conclusions apply to F on every nontrivial nonnegative interval.
  Gaussian L² weighting of g cannot avoid the obstruction, by the existing
  positive-density local measure comparison.
* They also apply to `F(c*x)` for every c>0, both with Lebesgue almost-everywhere
  and Gaussian almost-everywhere equality. In particular c=sqrt(T) is permitted
  whenever T>0. The result retains both positivity and nontrivial-interval gates.

## Reuse and independent checks

The proof reuses `IBMContinuousScenery.sourceScenery_increment_sq`, the actual
isonormal scenery construction, `GaussianSobolevFixedSupport.cs_setIntegral`,
`GaussianLocalSobolev.exists_local_measure_comparison`, Mathlib's continuity of
integrable primitives, continuous almost-everywhere uniqueness, and absolute
continuity of Lebesgue measure with respect to a nondegenerate Gaussian.
It does not replace the original derivative or its domains.

Six independent Lean tests cover an exact unit spatial increment, arbitrary
Gaussian-energy candidates and primitive constants on [1,2], the positive-time
sqrt(T) scaling on [0,1], the admissible zero-scale constant curve, preservation
of the already verified actual unmollified scenery partial derivative graph,
and agreement with the original random source section.

The complete build, transitive safe-Foundation axiom audit, unabridged public
types, printed `folded` definition and all final source/proofs are reviewed at
the checkpoint gates. Exact commands, counts, timings and source hashes are in
`STARDUST_IBM_CLOCK_SECTION_ENERGY_VERIFICATION.json`. No verification setting,
toolchain, old mathematical source or manuscript is changed.

## Exact remaining obligation

To infer failure of ORIGINAL clock/joint derivative membership of the actual
point IBM observation, prove a necessity theorem transporting that closed
Gaussian derivative graph to a Gaussian one-dimensional, scenery-valued
finite-energy primitive along the normalized clock observation. Existing
`IBMClockObservationGraph.pullback_graph` supplies a scalar forward graph
transport, not this vector-valued converse. Existing `GaussianLocalSobolev`
requires an everywhere genuine scalar derivative; it is not a theorem about
sections of an arbitrary closed Gaussian graph. Neither result alone closes
the missing bridge. A proof must also connect the normalized clock pullback
to the actual Bochner clock/scenery representation, retaining AE identities.

The new obstruction excludes the target primitive representation rigorously,
including changes of representatives. It does not itself prove lack of a
weak derivative in any unspecified Sobolev space, failure of all intrinsic
calculus, nonmembership of mollified/averaged IBM, physical-time Itô or Tanaka
formulas, a universal Clark–Ocone representation, or completeness of IBM calculus.
The original unmollified SCENERY partial derivative remains verified.

No novelty claim is made. IBM → Bakry/fBM → Cauchy → fractional diffusion →
black noise → backlog remains unchanged; there is no expiration date.
