# A bounded smooth actual IBM clock-domain obstruction — checkpoint1360

For EVERY positive time, the ACTUAL bounded nonconstant observable
`sin(IBM(t))` lies outside the ORIGINAL native clock domain and ORIGINAL full
intrinsic joint derivative domain. It nevertheless has a genuine original
scenery derivative, whose ordinary L2 field is explicitly constructed from
the already verified actual point scenery gradient. At time zero it is zero.

This is an explicit mathematical obstruction to admitting all bounded smooth
point cylinders into these fixed original operator domains. It is stronger
than failure of a sufficient estimate. It does not refute other possible
calculi, ordinary chain rules on inputs already in their proper domains, or
the verified derivative-free L2 representations.

## Reuse and exact Gaussian projection

`IBMNonlinearFirstSource.first_adjoint` combines the EXISTING mixed regression
identity and diagonal Stein identity. For every actual Gaussian coefficient
direction u, including u=0, and every bounded real C2 function phi with bounded
first derivative, it proves

`E_first^*(phi(E_first u)) = E[phi'(E_first u)] * u`.

Here the input class is the original `IBMFirstChaosMixedStein.testClass`;
no prescribed Gaussian law or symbolic process replaces the actual first-chaos
random variable. A bound on the second derivative is not an extra hypothesis
of this first-moment theorem. Regression energy handles zero directions without
division by a nonzero norm.

The actual characteristic-function theorem gives
`E[cos(E_first u)] = exp(-norm(u)^2/2)`. Integrability of the complex exponential
and passage to its real part are justified. Consequently the bounded operator
P formed from the original first-chaos isometry and its adjoint satisfies

`P(sin(B_r)) = exp(-abs(r)/2) * B_r`,

where B_r is the ORIGINAL Gaussian-L2 Brownian scenery class `sourceScenery r`.
Its identification with the spectral Hilbert coefficient, norm-squared abs(r)
and actual sine representatives are proved. The sine class depends continuously
on the scenery coordinate in L2 and has norm at most one. This uses the exact
variance normalization of the genuine law, not a guessed heat coefficient.

Reuse includes `IBMFirstChaosDiagonalStein.first_diagonal`,
`IBMFirstChaosMixedStein.first_pairing/first_pairing_integral`,
`InfiniteGaussian.firstChaos_charFun`, the original isonormal scenery embedding,
and the existing norm/continuity and actual-realization theorems. No separate
chaos campaign or new probability space is introduced.

## Finite-energy obstruction in the normalized clock section

For c>0, let F_c(x) be the scenery-valued class `sin(B_abs(c*x))`. It is a
genuine bounded Bochner-L2 class under the original scalar Gaussian clock
measure. Its projected curve is

`P F_c(x) = exp(-abs(c*x)/2) * B_abs(c*x)`.

At x=0 this is zero. For x in [0,1], the exact source variance and monotonicity
of the exponential give

`norm(P F_c(x)-P F_c(0))^2 >= kappa_c * x`,
`kappa_c = exp(-c/2)^2 * c > 0`.

The EXISTING `IBMClockSectionEnergyObstruction.no_finite_energy_primitive_ae`
rules out a common finite-energy Bochner primitive with this lower bound.
This theorem already accounts for changing representatives and adding an
arbitrary primitive constant. The bounded projection commutes with each local
Bochner integral, and Gaussian positive-density comparisons transfer the
putative derivative to the Lebesgue interval. Thus projecting a putative
primitive of F_c produces the impossible primitive of P F_c.

The existing weak-vector primitive theorem then excludes a SINGLE common
Gaussian-L2 vector derivative realizing ALL original scalar Gaussian closed
graphs of F_c. This is not an inference from unrelated scalar derivative
witnesses. `IBMClockBochnerConverse.original_field_graph_recovery` supplies
exactly that common field from any actual native Bochner clock graph, so the
normalized sine section is outside the ORIGINAL clock domain.

No two-time Gaussian moment infrastructure or new inverse-weight calculus is
needed: the original energy obstruction already accepts the one-endpoint
lower bound. No divergence rate is inferred from that lower bound.

## Identification with ACTUAL IBM and its observation space

At t>0 the existing actual Brownian clock direction has norm c>0, and its
normalization has norm one. The verified measure-preserving Gaussian
observation, clock scaling and actual section identities show that the native
pullback of F_c realizes EXACTLY `sin(IBMConstructedSources.ibmValue t)` under
the original joint Gaussian law, with the correct source/clock factor order.
`jointRealization_ae_of_sections` justifies the actual product realization.

`sinePoint` is an element of the EXISTING intrinsic IBM observation space by
continuous composition with the actual point class. Its true random
representative, essential boundedness, strong L2 time continuity and time-zero
value are verified. No observability of spatial mollifications is assumed.

The native clock-domain obstruction therefore applies to that ACTUAL class.
The original intersection-domain characterization transfers it to the full
intrinsic joint derivative domain. At every positive time, sinePoint is not
equal to ANY real constant multiple of the actual intrinsic one class, since
all those constants belong to the original domain. It is thus a nonconstant
bounded actual observable, not a degenerate symbolic counterexample.

## Surviving scenery and generalized derivatives

The original actual point scenery gradient remains valid. The existing bounded
Gaussian product chain rule constructs `sineSourceGradient`, using cosine times
that gradient in the original native source coordinates. `sinePoint_source_graph`
identifies its actual source-unitary input and original Bochner derivative
graph; original scenery-domain membership holds at ALL nonnegative times.
This supplies a positive partial calculus alongside the clock obstruction.
This is the original Gaussian source derivative, not a pathwise derivative
of Brownian scenery in its spatial parameter. The clock derivative likewise
means the fixed Gaussian clock-source operator, not differentiation in physical
time. No essential boundedness of the surviving scenery gradient is asserted.

The existing full intrinsic graph-dual derivative applies to sinePoint. It is
continuous in time in that strong-dual space, nonzero at every positive time,
and has NO ordinary original joint-field representative there. For every full
intrinsic adjoint test v, it equals the integrable actual expectation

`E[sin(IBM(t)) * jointDivergence(v)]`.

There are genuine observable ORIGINAL-domain approximating sequences whose
embedded gradients converge strongly to that functional. EVERY original-domain
sequence converging strongly to positive-time sinePoint has ordinary joint
gradient norms tending to infinity. Existence is still nonconstructive for
each fixed input/time, as in1358; no jointly measurable or adapted family,
pathwise derivative or physical-time stochastic integral is constructed.

## Implications and verification boundaries

Scalar smoothness and boundedness do not establish ORIGINAL joint-domain
membership. In particular, positive-time sinePoint cannot be used as a regular
coefficient in1359's multiplier class, whose ORIGINAL Dom(D) premise fails.
It CAN still serve as the rough intrinsic L2 factor there. The bounded chain
rule remains valid on its proper ORIGINAL-domain inputs; the IBM point did
not satisfy that input premise. Generalized nonlinear limits from1357 and
derivative-free reconstruction from1337 are unaffected.

No analogous claim about cosine, every nonconstant smooth function, all
possible intrinsic derivatives, or impossibility of physical-time stochastic
calculus is proved. No spatial H^-1 identification, physical-time Itô/Tanaka
formula or universal intrinsic Clark–Ocone completion follows from this result.
No novelty claim is made without a separate literature audit.

The verification JSON records the fresh full root build, complete transitive
safe-Foundation axiom audit, unabridged public-type and defining-body review,
complete final source/proof review and eight independent Lean checks. Checks
include bounded C-infinity/nonconstant actual time1 domain exclusion, time0,
the genuine scenery graph, full intrinsic stochastic pairing/integrability,
unit-variance and zero-direction Gaussian projection normalization, the actual
section primitive obstruction, constant-function Stein calibration, and
observable-domain approximation with energy escape.

All previous mathematical sources, pinned configurations and113 archived
manuscript paths/hashes remain intact. No manuscript files are modified or
committed. Full build, axiom/type/proof audits, independent checks, research
ledger and exact PRIVATE main/research synchronization remain mandatory.
IBM stays ACTIVE and incomplete; no queued campaign is opened.
The first independent scratch run failed only on an ambiguous infinity notation
in its scalar C-infinity assertion: the scoped ENNReal infinity was inferred.
An explicit WithTop Nat-infinity smooth order repaired that test. All eight
final tests passed with the mathematical sources unchanged; both attempts,
terminal timings and the failed log are preserved in the verification record.
