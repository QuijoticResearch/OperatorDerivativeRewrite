# Original Gaussian graphs and the IBM clock section — checkpoint 1354

IBM remains active. This checkpoint supplies the closed scalar Gaussian graph
to local primitive necessity missing from 1353, extends it to vector weak graph
tests, and applies it to the actual folded scenery curve. It does not yet
transport the original native infinite-dimensional clock graph to that curve.

## Original scalar graph: no pointwise derivative assumption

`Foundation/GaussianClosedDerivativePrimitive.lean` uses the ORIGINAL
`GaussianCore.closedDerivative`. Every pair (f,g) in this graph has a local
Lebesgue primitive representation `f(x)=c+∫_[a,x]g` almost everywhere on every
nontrivial compact interval. The representative g is the actual output of the
graph; there is no additional approximation, differentiability or domain
hypothesis on f.

The proof reuses the existing Hermite polynomial graph approximations. Mathlib's
`Lp.LpToLpOfMeasureLeSMul` and the already verified local Gaussian measure bound
give a continuous map to local Lebesgue L². Pairing with the local constant-one
class gives continuous local integral functionals. A common almost-everywhere
value subsequence and a point in its full-measure set fix the integration
constant; the polynomial FTC passes to the limit through those functionals.
This avoids unjustified evaluation of arbitrary L² convergence at an endpoint.

If F is a continuous representative on the closed interval, the primitive
identity holds everywhere, INCLUDING BOTH ENDPOINTS. This follows from positive
Lebesgue mass on nonempty open sets, the interval's dense interior, continuity of
the integrable primitive, and continuous AE uniqueness. No trace is assigned to
an arbitrary L² representative.

## Common vector derivatives: precise hypothesis

`Foundation/GaussianWeakVectorPrimitive.lean` proves: for a complete second
countable real Hilbert space E and actual f,g in Gaussian `Lp E 2 γ`, if EVERY
scalar pair `(⟨e,f⟩,⟨e,g⟩)` belongs to the ORIGINAL scalar closed derivative
graph, then f has an actual E-valued local Bochner primitive with derivative g.
The hypothesis requires ONE COMMON vector g. Independent scalar derivative
existence without a common finite-energy realization is insufficient.

Only countably many dense test vectors are needed in the proof, giving a common
AE set. Scalar constants cancel at a point in that set; inner products commute
with the integrable Bochner primitive. Dense inner-product separation identifies
the actual vector equality. This is a proved vector necessity theorem, not a
definition substituted for an existing derivative.

## Actual IBM section obstruction

`Foundation/IBMClockWeakGraphObstruction.lean` constructs the genuine Gaussian
Bochner L² class `sectionClass(c)(x)=sourceScenery|c*x|`. Its membership follows
from the existing exact scenery norm identity and Gaussian first absolute
moment; the representative is explicitly identified AE.

For EVERY c>0 there is NO common square-integrable scenery-valued g realizing
all scalar closed Gaussian derivative graphs of this class. The vector primitive
theorem and 1353's actual finite-energy obstruction prove the contradiction.
In particular c=sqrt(T), T>0 is covered. This strengthens a primitive obstruction
to a specific ORIGINAL scalar-Gaussian graph obstruction with a common vector
derivative. It does not claim that every scalar projection fails its graph.

## Verification and remaining bridge

The full root build, complete transitive safe-Foundation axiom audit, all
unabridged public types, actual definition bodies and all final source/proofs
are reviewed at this checkpoint. The verification JSON records exact commands,
counts, timings, source/configuration hashes and independent Lean tests.
All manuscripts and old mathematical sources are preserved.

Six independent tests exercise the primitive for actual nonpolynomial Gaussian
exponentials, their continuous-representative FTC including interval endpoints,
a nonconstant vector first-chaos curve with a genuine constant vector
derivative, the sqrt(T) obstruction for T>0, the valid zero-scale common
derivative, and preservation of the original unmollified scenery partial graph.
Development failures in the test's scalar/field coercions and zero-pair
packaging are retained; they do not change the final mathematical source or
weaken the test statements.

Still OPEN: transport from the original native infinite-dimensional clock
derivative of the actual IBM point observation to the normalized 1D scalar
graphs with ONE common scenery-valued finite-energy derivative. Scalar
`IBMClockObservationGraph.pullback_graph` is a FORWARD theorem; its converse and
the Bochner identification have not been proved here. A possible route is to
test the original full graph against normalized-clock polynomial divergence
fields, recover a scalar derivative via the pullback's adjoint, then verify
bounded assembly for the actual scenery/clock class. This route is a proposal,
not a result. No native point-domain nonmembership is asserted yet.

The unmollified scenery partial derivative remains valid. No physical-time
Itô/Tanaka formula, universal Clark–Ocone formula or completion of IBM calculus
is claimed. Campaign order and all private backup gates remain unchanged.
No novelty claim is made.
