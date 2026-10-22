# IBM clock-gradient divergence and graph-dual repair — checkpoint 1356

At EVERY positive time, the actual mollified IBM clock-gradient norms tend to
infinity. Nevertheless their canonical embeddings converge STRONGLY in the
continuous dual of the ORIGINAL clock adjoint's Hilbert graph. The limiting
generalized derivative is nonzero, has no representative in the original
ordinary L² field space, and has an actual integrable IBM expectation pairing
on EVERY original adjoint-domain test.

This is a Gaussian-clock generalized derivative construction. It does not
complete intrinsic IBM stochastic calculus, create a physical-time integral,
or establish the manuscript's spatial H^{-1} closure.

## Operator and topology

Let T be the existing `IBMFiniteAverageCore.partialDerivative`, with the native
scenery parameter outside and clock Gaussian parameter inside. Its input and
output spaces are the original Bochner L² spaces. Its closedness and dense
domain are reused from `BochnerClosedOperator`; its adjoint is the FULL Hilbert
adjoint. Equality with a separately prescribed fiberwise divergence domain is
not assumed.

The test space is the existing Hilbert graph `G(T*)` in `WithLp 2 (F × E)`.
An original test v in Dom(T*) is represented by the actual pair `(v,T*v)`.
The inherited norm is the Hilbert graph norm, incorporating BOTH the original
field norm and the original adjoint output norm. No finite test core or
restricted observable sigma algebra replaces this domain.

The bounded map `embed` sends an ordinary field V to the functional
`(v,T*v) ↦ ⟨V,v⟩`. The bounded generalized derivative sends an input f to
`(v,T*v) ↦ ⟨f,T*v⟩`. Both maps have norm at most one with these norms.
`embed` is injective when T is closed and densely defined, so ordinary field
representations are unique. On the ORIGINAL graph `(f,Tf)`, the two functionals
agree exactly. Moreover, the generalized derivative is representable by an
ordinary field if and only if f belongs to the original domain. The new map
does not extend, rename, or silently change that original partial operator.

## Why the L² gradient norms diverge

`ClosedOperatorEscapeEnergy` proves a general closed Hilbert operator theorem.
If graph inputs u_n converge strongly to f and output norms stay bounded
cofinally often, original adjoint duality gives an ambient-norm bound for
`v ↦ ⟨f,T*v⟩`. The existing
`HilbertRepresentation.adjoint_domain_iff_pairing_bound` and verified closed
bidual identity then imply f in Dom(T). Consequently, if f is outside that
domain, output norms tend to infinity, not merely fail to converge.

Applied to the actual IBM mollifier graph and 1355's actual point-domain
obstruction, this proves `clock_gradient_norm_escape`. No weak compactness,
new spectral basis, guessed mollifier asymptotic, or extra regularity
hypothesis is introduced. No numerical divergence rate is claimed.

## Genuine limit and quantitative convergence

`ClosedOperatorGraphDualDerivative` reuses the verified closed Hilbert graph
space, continuous linear precomposition and the existing Hilbert adjoint
machinery. Strong input convergence of ANY original graph sequence gives
strong operator-norm convergence of the embedded outputs to the generalized
derivative of the limiting input, with error no greater than input L² error.

`IBMClockGraphDualLimit.point` is the actual original IBM point class in native
clock/scenery order. Its `pointDerivative` is an explicitly constructed element
of `G(T*)'`. For the actual mollified clock gradients G_n(t), t>0,

`‖embed(G_n(t)) - pointDerivative(t)‖ ≤ ‖X_n(t)-X(t)‖_L² ≤ sqrt(radius_n)`.

This controls ALL tests in the graph unit ball simultaneously, not just one
probe at a time. The seven independent Lean examples also instantiate the
same divergence and convergence theorems for ARBITRARY original clock-domain
approximations of the actual point, not just the selected mollifier.

The limiting functional is not an ordinary original L² field, by the exact
representability/domain equivalence and the already proved actual point
exclusion. It is nonzero at positive times, zero at time zero, and continuous
in time in the strong graph-dual norm. These are statements about the
time-indexed generalized objects; no samplewise derivative version is asserted.

## Actual stochastic pairing and integrability

For EVERY v in the full original adjoint domain, the limiting functional equals

`E[ IBMConstructedSources.ibmValue(t) * clockUnitary.symm(T*v) ]`

under the original joint Gaussian probability law. The product is proved
integrable, using actual L² representatives and the verified
`joint_point_actual_ae` identity. The existing native `clockUnitary` fixes the
source/clock factor order. This connects the constructed functional to the
actual process and full original stochastic test pairing.

It is an expectation duality, not a chronological stochastic integral or a
physical-time Itô identity. The graph-dual space has not been identified with
the spatial H^{-1} space appearing in the IBM manuscripts. Such an identification
would require a separately proved transfer theorem.

## Gates and remaining research

Full root build, complete transitive safe-Foundation axiom audit, unabridged
public-type and final-source/proof review, actual old/new definition review,
seven independent Lean examples, and archive/configuration/source integrity
checks are recorded in `STARDUST_IBM_CLOCK_GRAPH_DUAL_VERIFICATION.json`.
Existing sources and all manuscripts are preserved. Default resource limits
are retained; one elaboration timeout was repaired by factoring the generic
nonzero argument, not by raising the limit. Native unitary reuse resolved
ambiguous product-isometry elaboration without changing mathematics.

Still open: intrinsic observation/adapted integration, nonlinear chain/product
identities on justified generalized domains, physical-time Itô/Tanaka formulas,
and a full intrinsic Clark–Ocone calculus for the actual process. The sourcewise
graph-dual construction is not completion of those tasks. Compare it with the
existing spatial negative-Sobolev and F1–F3 results by exact theorem reuse before
adding infrastructure; preserve the precise scopes already verified there.
No campaign transition or novelty claim is made.
