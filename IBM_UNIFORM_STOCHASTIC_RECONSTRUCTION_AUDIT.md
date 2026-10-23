# IBM checkpoint1374: locally uniform stochastic reconstruction

IBM remains ACTIVE and incomplete. This checkpoint upgrades fixed-observable
stochastic reconstruction to locally uniform convergence for moving actual
IBM observations, with simultaneous control of every causal horizon. It also
connects that convergence to the ORIGINAL intrinsic divergence graph norm.
No physical-time Ito or temporal-gradient Clark–Ocone theorem is asserted.

## Existing objects reused

The fixed countable family, actual predictable integrands, full signed
multichannel completion, actual stochastic isometry J, initial right germ G0,
and causal stopping operators S_r are the existing verified objects. Each
basis channel e_i is an actual original integral I_(F_i)(H_i). Define

    L(f) = fixedHilbertEquiv^-1(f-G0 f),
    P_s(f) = sum_(i in s) embed_i(coefficient(f,i)*H_i).

The indices s range over ALL finite subsets of the fixed family, ordered by
inclusion. This is unconditional convergence and does not require a preferred
enumeration. The chosen Hilbert basis is not claimed explicitly computable.

`partial_actual` identifies J(P_s(f)) with the actual finite basis expansion.
`error_sq` proves its precise squared completed-input error:

    ||P_s(f)-L(f)||^2 = ||f-G0 f||^2 - sum_(i in s) coefficient(f,i)^2.

The right side is continuous in f, nonnegative, antitone in s, and tends to
zero by the existing exact Parseval theorem. These hypotheses are all proved
before invoking the pinned Mathlib Dini theorem. No abstract pointwise-to-
uniform implication is presumed.

## Uniform actual stochastic identities

For EVERY continuous curve u into actual IBM-observable L2 and EVERY compact
parameter set K, `uniform_input` proves P_s(u(t))->L(u(t)) uniformly for t in K.
The existing S_r are contractions, so `uniform_stopped` gives the SAME uniform
control simultaneously for EVERY r>=0, with no boundedness restriction on r.

`stoppedActual` is the literal finite sum of the EXISTING stochastic integrals

    sum_(i in s) I_(F_i)(cutoff_(F_i,r)(coefficient(u(t),i)*H_i)).

`stoppedActual_eq` identifies it with J(S_r P_s(u(t))). Its actual output lies
in the original right-germ past at r. `uniform_actual` proves, uniformly on
K and uniformly over ALL causal horizons r,

    stoppedActual(s,r,u(t)) -> P_r u(t) - G0 u(t)

in actual joint-source L2. The finite sums use the original predictable
domains and integrals, not newly defined outputs or surrogate processes.

The actual constructed IBM curve t->Z_t is already strongly L2 continuous.
Its terminal-past membership and G0 Z_t=0 are existing verified theorems.
`actual_IBM_uniform` therefore proves

    sup_(0<=t<=T) ||stoppedActual(s,t,Z_t)-Z_t||_L2 -> 0

for EVERY finite horizon T, including T=0. The source formula is causal at
each t. Coefficients depend on the moving observation t: these diagonal
approximants are not claimed to be martingales, nor is raw IBM made one.

## Nonlinear observations and the rough-domain test

Reuse the existing bounded C1 test-function class with bounded continuous
slope. `nonlinear_ae` realizes nonlinear(phi,t) as the ACTUAL phi(Z_t), and
`nonlinear_continuous` proves its strong L2 continuity. Its original raw-past
measurability is proved separately. `nonlinear_uniform` gives the corresponding
locally uniform stochastic reconstruction, retaining G0 phi(Z_t). No germ
triviality or automatic centering of nonlinear observations is asserted.

The independent sine test identifies this construction with the existing
sinePoint and verifies its ORIGINAL joint derivative domain exclusion at
every positive time. Thus process-level stochastic representation does not
assert ordinary Malliavin differentiability, even for bounded smooth phi.

## Original native divergence graph convergence

The original native transfer T maps every completed stochastic input into
the ORIGINAL joint-divergence domain, with delta(Tz)=Jz and ||Tz||^2<=2||z||^2.
Those are reused, not redefined. `nativeGraphDistance` is explicitly

    ||V-W||_original_field + ||delta(V)-delta(W)||_IntrinsicL2,

for V,W in that original domain. `native_graph_distance` proves the bound
<=3||z-w|| for the existing nativeTest(z),nativeTest(w). Consequently
`uniform_native_graph` proves convergence in this ORIGINAL graph norm,
uniformly for t in K AND simultaneously for EVERY causal horizon r.
Both the actual field and its original divergence converge. No derivative
domain enlargement, conditional-gradient identity or graph-dual-only
substitution is used.

## Exact limits and verification

The topology is uniform-in-time L2 (sup_t of L2 errors). It is NOT L2 of a
samplewise time supremum, almost-sure uniform convergence, a pathwise bracket,
a cadlag modification, finite-grid physical-time Ito or Tanaka, or a formula
for temporal Malliavin gradients. Existing F1/F2 correction topologies and
the nonmartingale/ordinary point-domain obstructions remain unchanged.
Full intrinsic IBM calculus remains OPEN; no campaign transition is released.

One new module contains266 final source/proof lines and30 public declarations.
The verification JSON records fresh full build and complete transitive safe
Foundation audit results, all unabridged type/printed-definition/source reviews,
eight independent Lean tests and113 unchanged manuscript paths/hashes.
Development diagnostics include five DEFAULT200000-heartbeat timeouts in
the native-graph elaboration/proof (attempts5–9). Existing nativeTest and an
explicit graph-distance definition bind the original domains once; typed
norm equalities avoid a generic rewrite exploring unrelated operators. The
final attempt passes at unchanged defaults. No new resources, trust or error
suppression is introduced. All ten exact development logs are retained.
Git's whitespace gate subsequently rejected an extra EOF blank line. The final
line now states the norm-topology caveat; all full gates were repeated for those
exact final bytes. The earlier successful gate logs/timings are also retained.

There is no novelty claim. Reuse of the exact verified operator and stochastic
objects, rather than attribution to a manuscript, supports these statements.
Manuscripts, the research queue and the pinned configuration remain unchanged.
