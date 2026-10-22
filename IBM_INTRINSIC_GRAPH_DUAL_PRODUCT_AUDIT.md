# Actual intrinsic IBM generalized derivatives and weak products — checkpoint1358

The generalized derivative is now instantiated for the ORIGINAL full intrinsic
two-channel IBM derivative, not only the ambient Gaussian clock derivative.
Every intrinsic L2 observable has original-domain graph approximations with
strongly convergent embedded derivatives. For every positive-time actual IBM
point, ALL such approximating ordinary joint-gradient norms tend to infinity;
its intrinsic graph-dual derivative is nonzero and has no ordinary original
joint-field representative. Existence of genuine observable-domain approximants
is proved, rather than assuming the spatial mollifications are observable.

Reusing the existing full intrinsic weighted-divergence theorem also gives
a weak product identity for an arbitrary intrinsic L2 rough factor, including
the actual IBM point. The coefficient must be in the original joint derivative
domain, essentially bounded, with BOTH native derivative channels essentially
bounded. These hypotheses are retained exactly; no arbitrary bounded random
coefficient or derivative of a rough IBM point is assumed.

## Exact operators, domains and topology

Let D be `IBMJointIntrinsicDerivative.jointDerivative`, with its existing
intersection domain in `IBMTimeAveragedObservable.IntrinsicSpace`. The field
space is the original Hilbert two-channel `JointFieldSpace`; channel0 is
scenery and channel1 clock. Let delta=D* be the FULL intrinsic Hilbert adjoint,
including any tests not represented by lifted ambient coordinate adjoints.
Closedness and dense domain are the original verified theorems.

`IBMIntrinsicGraphDual.Tests` is G(delta), with the Hilbert norm of `(v,delta v)`.
The existing checkpoint1356 construction supplies bounded maps

`Dweak(g)(v,delta v) = <g,delta v>`,
`embed(V)(v,delta v) = <V,v>`.

The derivative has norm at most the intrinsic L2 input norm. The field embedding
is injective; it agrees exactly with D on the ORIGINAL domain. Ordinary field
representability is equivalent to ORIGINAL domain membership. This defines a
separate generalized functional; D and its original domain are unchanged.
Convergence is the strong operator norm in G(delta)', not merely selected-test
pairing convergence, spatial Sobolev convergence, or pathwise convergence.

## Genuine observable-domain approximation of actual IBM

`domain_approximation` uses the EXISTING dense original derivative domain and
the standard metric closure sequence theorem. For each intrinsic g, it gives
u_n in ORIGINAL Dom(D) with u_n->g strongly in intrinsic L2. Original graph
agreement then gives

`norm(embed(Du_n)-Dweak(g)) <= norm(u_n-g)`.

For the actual g=intrinsicCurve(t), this is a genuine sequence of IBM-observable
classes with both original channel derivatives. It is not a claim that the
prior spatially mollified values belong to the intrinsic observation space.
The existence proof is nonconstructive and pointwise in the choice of g/time;
it does not provide an explicit formula, a jointly measurable family in time,
physical-time adaptation or simultaneous samplewise convergence.

For every t>0,1355 already proved g outside the ORIGINAL joint domain.
Consequently the generic closed-operator escape theorem proves
`norm(Du_n)->infinity` for EVERY such original-domain approximating sequence.
The dual limit still exists, is nonzero and has no original ordinary joint-field
representative. The time-indexed functional is continuous in strong dual norm.
No rate for the divergence or new ordinary derivative version is asserted.

For EVERY full intrinsic adjoint test v the pairing is the actual integrable
expectation `E[IBM(t) * delta(v)]`, under the original joint Gaussian law and
the original observable representative of delta(v). Time zero is included in
the pairing, integrability and continuity theorems; its functional is zero.

`ambient_pair_compatibility` reuses `ambient_pair_divergence`: on every verified
lifted pair of ambient source/clock adjoint tests, Dweak agrees with the pairing
against their ambient divergence sum. The conditional orthogonal projection
disappears from the pairing because the rough factor is intrinsic observable.
This is agreement on the EXISTING inclusion, not equality of the full intrinsic
adjoint domain with the lifted-pair domain, or equivalence of their graph norms.

## Weak Leibniz identity with a rough actual factor

For an essentially bounded intrinsic coefficient f, `scalarMultiplier` is the
bounded ambient multiplication followed by the original intrinsic projection.
Intrinsic measurability of f and g proves that this is the ACTUAL product f*g;
the projection introduces no change to the random-variable class. Its symmetry
is proved using the verified multiplier symmetry and projection pairings.

Now require f in ORIGINAL Dom(D), |f|<=C with C>=0, and both original native
gradient channels in L-infinity. The existing theorem
`IBMNativeWeightedDivergence.weighted_mem/weighted_value` ensures that N_f v
is in the FULL delta-domain for EVERY original v there and gives

`delta(N_f v) = P[f*delta(v) - correction(Df,v)]`.

The actual channel multiplier N_f and contraction are REUSED from
`IBMNativeFieldMultiplier` and `IBMNativeContraction`. In native joint random
coordinates, `correction_ae` identifies the contraction with the SUM of the
two channel inner products. No separately prescribed gradient or adjoint is
introduced, and no ambient-domain equality is assumed.

For EVERY intrinsic g in L2, without requiring g in Dom(D), the new theorem is

`Dweak(f*g)(v) = Dweak(g)(N_f v) + <g,correction(Df,v)>_L2`.

At g=actual IBM(t), the last term is exactly
`E[IBM(t) * correction(Df,v)]` and is rigorously integrable. The actual product
representative f(omega)*IBM(t,omega) is also proved. In particular, the rough
factor can be a positive-time point known NOT to belong to the original domain.
The smooth coefficient's domain/bounded-gradient hypotheses remain essential
to this theorem; this checkpoint does not construct a new nonconstant example
of that coefficient class or prove those hypotheses for arbitrary point tests.

This is an identity on every full intrinsic adjoint test. A bounded operator on
the ENTIRE abstract graph dual implementing multiplication, with quantitative
graph norm bounds, is not yet constructed here. Nor is multiplication by an
arbitrary rough limiting coefficient justified. All original weighted-domain
and native product results retain their exact prior scopes.

## Verification and open obligations

The verification JSON records the fresh complete build, complete transitive
axiom audit, unabridged public-type and printed-definition review, complete final
source/proof review and eight independent Lean examples. Checks include the
nonzero/nonrepresentable actual time1 point, time0, original-domain uniqueness,
actual full-adjoint pairing/integrability, observable-domain approximation with
energy escape, actual rough-point weak product, ambient-pair compatibility,
and the nonlinear two-time observable bridge from1357.

Elaboration repairs made existential transports explicit, kept large original
operator definitions locally irreducible, and replaced expensive rewrites by
typed equality chains. Default-heartbeat timeouts were NOT repaired by raising
limits. No theorem hypothesis, trust setting or pinned dependency was weakened.
All prior source hashes/configs and113 manuscript paths/hashes are preserved.

Still open: bounded graph-test multiplier extensions, explicit nonconstant
admissible coefficient constructions where needed, justified comparison with
spatial negative-Sobolev kernels, physical-time stochastic integration and
Itô/Tanaka, and universal intrinsic Clark–Ocone. Generalized source derivatives
and expectation IBP identities do not complete those tasks. No new physical-time
process law, pathwise derivative or observation-filtration martingale is claimed.
IBM remains ACTIVE; no queued research campaign is opened.
