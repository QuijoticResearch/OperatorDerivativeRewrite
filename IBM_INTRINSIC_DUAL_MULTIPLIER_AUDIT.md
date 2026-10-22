# Full intrinsic IBM graph-dual multiplication — checkpoint1359

The missing bounded graph-test action from1358 is now constructed, and its
transpose acts continuously on the ENTIRE intrinsic adjoint-graph dual. It
agrees with actual native multiplication on ordinary embedded fields. The weak
product identity is upgraded to an equality of full graph-dual elements with
a bounded correction operator whose pairings are the existing actual
two-channel stochastic contractions.

The coefficient class is unchanged: ORIGINAL intrinsic joint derivative domain,
essentially bounded coefficient, BOTH original native derivative channels
essentially bounded. No arbitrary bounded random coefficient, new nonconstant
admissible example, original derivative of a rough IBM point, or physical-time
integral is assumed.

## Full test graph action and its continuity

D and delta=D* remain the original full intrinsic two-channel derivative and
Hilbert adjoint. The test space is G(delta), with norm of `(v,delta v)` in the
Hilbert product. Every graph test corresponds to its actual original-domain
field v; `testField_injective` and `testOf_asDomain` prove the inverse
identification, using the original partial operator's single-valued graph.

The coefficient's existing native field multiplier N_f preserves the FULL
delta-domain by `IBMNativeWeightedDivergence.weighted_mem`. Thus the actual map

`L_f(v,delta v) = (N_f v,delta(N_f v))`

is defined on every full graph test. `liftLinear` verifies its linearity by
the injective field coordinate. No restricted test core replaces the full
adjoint domain.

`liftLinear_seqClosedGraph` proves its graph is sequentially closed. If tests
w_n->w and L_f w_n->z in the graph norm, continuity of N_f in the ordinary field
space implies field(z)=N_f field(w). Both z and L_f w are actual delta-graph
elements, hence their common first coordinate forces equality. The existing
Banach closed graph theorem, applied to the complete Hilbert graph, then
constructs the continuous `graphMultiplier` L_f.

Its operator norm is finite. No new explicit or sharp bound depending only on
the coefficient's declared scalar C, nor uniform control across coefficients,
is established. The quantitative statements retain the actual norm of L_f.
Closed graph continuity does not supply a claimed numerical constant.

## Action on the entire graph dual

`dualMultiplier` is continuous linear precomposition with L_f:

`M_f F(w) = F(L_f w)`.

It is defined for EVERY continuous graph-dual element F, not only generalized
derivatives or a chosen approximation range. It satisfies

`norm(M_f F) <= norm(F) * norm(L_f)`.

The original native multiplier is symmetric. Consequently

`M_f(embed V) = embed(N_f V)`

for EVERY ordinary joint field V. This identifies the operation with actual
native multiplication on the existing ordinary-field embedding. The operation
is defined as the transpose of the verified full test action; no assertion of
uniqueness among all possible extensions from a dense range is needed or
proved here.

For any strongly convergent graph-dual sequence, its multiplied sequence
converges strongly to the multiplied limit. For ANY original-domain u_n->g
strongly in intrinsic L2,

`embed(N_f D u_n) -> M_f(Dweak g)`

in full graph-dual norm, with

`norm(embed(N_f D u)-M_f(Dweak g)) <= norm(u-g)_L2 * norm(L_f)`.

In particular, this applies to1358's genuine observable-domain approximations
of the ACTUAL positive-time IBM point, whose unmultiplied ordinary gradients
have norms tending to infinity. No ordinary-field norm convergence or adapted
physical-time approximation is asserted.

## Bounded correction and full dual Leibniz identity

Let S_f be1358's actual intrinsic scalar multiplication. The continuous map

`R_f(w) = S_f(value(w)) - value(L_f w)`

is `correctionTest`. The prior full weighted-divergence value theorem proves
on EVERY original adjoint test v that

`R_f(v,delta v) = P[correction(Df,v)]`.

Here P is the existing intrinsic conditional orthogonal projection, and the
correction is the genuine original two-channel L2 contraction. This equality
identifies the bounded operator with the previously verified stochastic
object; it is not merely an unexamined remainder assigned to force Leibniz.

`correctionFunctional` is the bounded map g -> `<g,R_f(.)>`. On every actual
full test its value equals `<g,correction(Df,v)>` in the original joint L2
space. For g=actual IBM(t), this is EXACTLY the integrable expectation
`E[IBM(t)*correction(Df,v)]`, using the actual process representative and
unchanged joint Gaussian law. Integrability is reused from1358.

The verified equality in the ENTIRE graph dual is

`Dweak(S_f g) = M_f(Dweak g) + correctionFunctional(g)`

for EVERY intrinsic L2 observable g, without original Dom(D) membership of g.
The actual product S_f g is the original f*g random-variable class. The theorem
uses no undefined multiplication of a rough pointwise random slope with a
distribution, and no extension of the original partial derivative domain.

This checkpoint does not identify the correction functional with an ordinary
field embedding for every rough g, or prove a new original-domain product
closure theorem from that identification. Those are distinct further targets.

## Independent checks, preservation and remaining work

The checkpoint verification includes the fresh complete build, complete
transitive safe-Foundation axiom audit, unabridged public-type/definition/proof
review, and eight independent Lean examples. A concrete normalization test uses
the ACTUAL intrinsic constant-one graph, its zero derivative and its true
random representative to verify that the new multiplier is IDENTITY on EVERY
abstract graph-dual element. Other tests cover native embedding agreement,
full dual difference bounds, the actual nonrepresentable time1 IBM point's
product rule, stochastic correction/integrability, observable-domain multiplied
gradient limits, full weighted graph bounds and quantitative value-error control.

All previous sources/configurations and113 immutable manuscript paths/hashes
are preserved. Resource, trust and pinned dependency settings are unchanged.
Default-heartbeat elaboration failures were repaired by explicit typed equality
chains and local irreducibility, rather than increasing limits. No claim of
novelty or manuscript correctness follows from the construction.

The independent harness required four repairs before its final successful run:
qualification of the native coordinate, the correct zero-function lemma and AE
transport for the L2 zero representative, explicit canonical graph normed-group
and normed-space instances, and a typed subtraction equality replacing a costly
rewrite. The norm instances are EXACTLY those of the existing closed Hilbert
graph; no new norm or topology is substituted. A transparency-option diagnostic
did not solve the inference issue and is not used in the final harness. All
four failed test sources/logs/timings are retained with the final code. These
harness changes did not modify mathematical sources or require repeating the
already successful unchanged full build and complete audit.

Still open: useful nonconstant admissible coefficient constructions, ordinary
field realization of correction operators where justified, spatial Sobolev
transfer, physical-time Itô/Tanaka and adapted stochastic integration, and
universal intrinsic Clark–Ocone. No full IBM completion or campaign transition
is claimed. IBM stays ACTIVE under the existing linear queue and all gates.
