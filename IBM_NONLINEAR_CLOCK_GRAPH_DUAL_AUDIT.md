# Nonlinear multitime IBM clock-chain limits — checkpoint1357

Bounded C1 functions of every finite real linear combination of actual IBM
observations now have a verified nonlinear clock-chain approximation in the
continuous dual of the FULL original Gaussian clock-adjoint graph. Genuine
ordinary L2 chain fields are constructed at each mollification scale. Their
canonical embeddings converge in strong dual operator norm to a functional
with an integrable actual IBM expectation pairing for every original adjoint
test. The limiting scalar observable is in the existing intrinsic observation
space; membership of its original derivative domain is not asserted.

## Exact domain and construction

`IBMClockWeakChain.TestFunction` records a real function phi, its continuous
derivative phi', and GLOBAL bounds A and B for their absolute values. Both
bounds are finite real numbers; their nonnegativity follows from the bounds.
All new nonlinear chain results require these hypotheses. Unbounded functions,
nonsmooth local-time tests, polynomial growth and arbitrary measurable
functions are outside this theorem's scope.

The actual partial operator is unchanged:
`T = IBMFiniteAverageCore.partialDerivative`, the scenery-parameter Bochner
lift of the original closed Gaussian clock derivative. Test space remains the
Hilbert graph of its FULL adjoint, with norm of `(v,T*v)` in the Hilbert product.
The bounded generalized derivative is the checkpoint1356 functional
`v -> <f,T*v>`, while ordinary fields embed by `v -> <V,v>`.

`IBMClockWeakChain.chain_graph` REUSES
`GaussianClosedChainRule.bounded_product_chain_graph` on the original native
graph. For any genuine graph input `(clockUnitary f,V)`, its nonlinear output
is again in the same graph, with actual joint field
`phi'(f(omega)) * uncurryField(V)(omega)`. The field is in genuine joint L2,
by the bounded derivative and the original field's L2 membership. No measurable
selection of fiberwise witnesses or new derivative definition is needed.

## Actual multitime observations

For any finite number N of observations and real coefficients a_i, let

`Q = sum_i a_i * IBM(t_i)`

and let Q_n be the same linear combination of the existing spatially
mollified IBM values. Their actual native clock graph is obtained by sums and
scalar multiples of `IBMFirstSourceClockGraph.mollified_clock_graph`.
Approximation graph claims require EVERY t_i>0. The exact scalar observable,
expectation pairing and continuity statements allow all t_i>=0. N=0 and zero
coefficients are allowed; no distinct-time or independence premise is imposed.

The actual ordinary nonlinear field at scale n is

`H_n = phi'(Q_n) * sum_i a_i * D_clock IBM_n(t_i)`.

`chainGradient_actual_ae` identifies this as an equality of the original
actual joint L2 representatives. `value_actual_ae` identifies Q with the
finite sum of the ACTUAL constructed IBM process values, under the unchanged
joint Gaussian law. `nonlinear_value_intrinsic` reuses the original observation
subspace and continuous-composition theorem to verify intrinsic measurability
of phi(Q). It does not assume the mollified approximants lie in that subspace.

## Norm convergence and stochastic pairing

Original graph agreement, the bounded dual derivative, and the L2 Lipschitz
bound for composition give

`norm(embed(H_n) - weakDerivative(phi(Q)))`
`  <= B * norm(Q_n-Q)_L2`
`  <= B * sum_i abs(a_i) * sqrt(radius_n)`.

The sum is finite, B is fixed, and the actual mollifier radii tend to zero.
The theorem proves strong convergence in the full graph-dual operator norm.
It therefore controls every test in the graph unit ball simultaneously; it
does not merely assert weak convergence on selected probes.

The generic `chain_dual_limit` also applies to ANY sequence of genuine original
clock graph approximations with strongly converging values. No convergence or
boundedness of their ordinary gradient norms is needed. The limiting object
is independent of the selected approximation, for this precise topology and
fixed nonlinear test. This is not an assertion of independence from the
chosen derivative/test topology.

For every v in the full original adjoint domain, the limit pairs exactly as

`E[phi(sum_i a_i * IBM(t_i)) * clockUnitary.symm(T*v)]`.

The product is rigorously integrable. Both the scalar L2 transformation and
the original adjoint-test L2 class are explicitly connected to their actual
random representatives. The generalized derivative depends continuously on
the finite observation times, including zero times, in strong dual norm.

## Why no limiting product is claimed

Checkpoint1356 proved the positive-time point's mollified clock-gradient
norms tend to infinity, and1355 proved its exclusion from the original clock
and joint derivative domains. An L2 chain rule cannot simply be applied to
that point. The new construction keeps products at actual graph approximants
and passes to their canonical dual limit. It does NOT define a product of the
limiting generalized derivative with phi'(Q), assume stability of arbitrary
test multipliers, or show any ordinary-field representative for the limit.

The negative result for the original point is not transferred to every
nonlinear function of it. Constant functions, for example, require no such
obstruction. The theorem neither assumes nor proves original-domain exclusion
of every nonconstant phi(Q).

The space is Gaussian-source graph dual, not the manuscript's spatial Bessel
H^-1. Existing `IBMNegativeSobolevBounded.l2DerivativeCLM` differentiates
Lebesgue-L2 spatial kernels; `IBMNegativeSobolevRandom.randomDerivativeCLM`
lifts that spatial operator over Gaussian clock samples. Their input, output
and test variables differ. A transfer requires a proved test map, pairing
identity and norm/domain control. No equality or impossibility of transfer is
asserted by the current type comparison.

## Verification and remaining IBM work

The verification JSON records the fresh full root build, complete transitive
safe-Foundation axiom audit, actual unabridged public types, printed defining
bodies, full final source/proof review and seven independent Lean tests.
Tests include sine and cosine on mixed multitime observations, full-graph
uniform residual bounds, actual expectation and integrability, intrinsic
measurability, arbitrary approximation sequences, the empty zero cylinder,
and continuity in observation times. Development retained default resources;
two type-inference failures in the continuity addition were repaired with
explicit parameter types and unfolding, not increased limits.

The first independent-test run failed in the empty-cylinder harness: a zero
function had not been reduced at its argument, and the following anonymous
placeholder caused a default-heartbeat timeout. Explicit scalar equalities and
a fully typed congruence repaired that test; the mathematical sources and their
successful full build/audit were unchanged. The final seven-example run passed.
The failed first test source, log and timing are retained in the verification
record alongside the final test source and timing.

All earlier mathematical sources and113 manuscript paths/hashes are preserved.
Pinned versions, trust settings, full verification gates and private backup
requirements remain intact. No novelty claim or manuscript alteration is made.

Open: spatial transfer, justified multiplication on generalized test domains,
unbounded/nonsmooth nonlinear extension, observation-intrinsic adapted
integration, physical-time Itô/Tanaka and universal intrinsic Clark–Ocone.
An expectation integration-by-parts identity is not a chronological stochastic
integral. IBM stays ACTIVE and incomplete; no queued campaign is opened.
