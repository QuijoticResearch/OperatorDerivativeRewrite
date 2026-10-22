# Actual predictable covariance measures and mixed IBM stochastic energy — checkpoint1363

The existing scalar predictable energy measures now give a GENUINE SIGNED
cross-energy measure for every pair of actual IBM terminal channels. Exact
mixed stochastic energy is verified for arbitrary eligible finite predictable
presentations, including overlapping random steps, different grids and every
finite channel family. Cross pairings also have a unique strong limit on the
ORIGINAL completed single-channel predictable L2 domains.

This advances random multichannel integration beyond1362's scalar multiples
of a fixed family. It does not declare a completed general multichannel domain
or identify its null space without proof.

## Genuine objects and normalization

For the existing finite raw-IBM-predictable measure mu_F, construct

`nu_(F,G) = (mu_(F+G).toSignedMeasure - mu_(F-G).toSignedMeasure)/4`.

This is an actual Mathlib SignedMeasure on the ORIGINAL raw IBM predictable
sigma algebra, hence genuinely countably additive. Existing finite_measure
supplies finiteness, and pinned Mathlib `Measure.toSignedMeasure` performs the
finite-positive-measure conversion. No set function is merely named a measure.
The scalar1/4 is fixed by real Hilbert polarization with the original channel
normalizations. No new law, stochastic process, filtration or positive energy
measure is assigned.

The old weightedTerminal is identified EXACTLY with the existing bounded L2
multiplier for its actual adapted coefficient. This produces bounded linear
stepOperator, finiteOperator and ringOperator in the TERMINAL F. They are
identified with the ORIGINAL actual step/finite/ring stochastic integrals.
The ring operator's chosen finite presentation is justified by the existing
actual process representation/kernel theorem, not an assumed presentation
independence. In particular, terminal addition/subtraction identities hold.

For every elementary predictable set E,

`nu_(F,G)(E) = inner(I_F(1_E), I_G(1_E))`.

This identifies the signed measure with ACTUAL random stochastic integrals.
Its absolute cell mass satisfies the corresponding Cauchy-Schwarz bound.
The theorem is stated on the verified elementary ring. It does not identify
the old ringIntegral outside that ring with an arbitrary indicator integral.

## Mixed steps, overlaps and arbitrary finite channel families

Disjoint-time steps in DIFFERENT channels are orthogonal by the EXISTING
full right-germ conditional projection theorem and earlier-step measurability.
Disjoint sample events give zero products almost surely even when time
intervals overlap. Combining those facts proves mixed orthogonality of
disjoint predictable rectangles and then disjoint elementary-ring sets, using
the existing rectangle semiring partitions and actual ring additivity.

Decomposing E and H into their differences and intersection then gives

`inner(I_F(1_E), I_G(1_H)) = nu_(F,G)(E intersection H)`.

This generalizes the old same-channel finite isometry; its single-terminal
hypothesis could not simply be instantiated with two unrelated channels.
No refinement, null-event or overlapping-interval cases are silently omitted.

For arbitrary finite eligible presentations l and k, define mixedEnergy by the
literal finite double sum of their coefficients times nu_(F,G) evaluated on
rectangle intersections. The actual finite integrals obey

`inner(I_F(l), I_G(k)) = mixedEnergy(F,G,l,k)`,
`abs(mixedEnergy) <= norm(dictionary_F(l))*norm(dictionary_G(k))`,
`norm(I_F(l)+I_G(k))^2 = norm(dictionary_F(l))^2 + 2*mixedEnergy + norm(dictionary_G(k))^2`.

For EVERY finite family, the squared norm of its actual summed stochastic
integral is the full double sum of these mixed energies. The resulting finite
Gram energy is therefore nonnegative; off-diagonal entries need not be.
The theorem applies directly to1362's fixed countable channel family restricted
to any finite subset, with arbitrary eligible predictable presentations in
each selected channel. It does not impose identical integrands or a common grid.

## Closure in the existing completed domains

Let H be in ORIGINAL PredictableL2(mu_F) and K in ORIGINAL PredictableL2(mu_G).
If dictionary presentations a_n and b_n converge strongly in their respective
original spaces, their mixedEnergy converges to

`inner(actualIntegral_F(H), actualIntegral_G(K))`.

The original isometries and continuity of the Hilbert inner product prove this
for ALL such approximation sequences. Existing dictionary density independently
supplies actual approximants for EVERY H and K, so existence is not an extra
hypothesis left unresolved by the test. This proves completion-independence
of the mixed pairing. Old process-presentation independence is also tested.

This is NOT YET a theorem that arbitrary representatives H*K are integrable
against the total variation of nu_(F,G), or that their literal signed integral
is this completed pairing. That identification needs the appropriate signed
integrability/variation control. No false common measure or pointwise product
is inserted to bypass that obligation. The pinned signed/vector integration
API was located, not newly formalized here.

## Explicit actual counterexample to ignoring cross terms

Use the ACTUAL observed IBM1 terminal F and its negative G=-F. On the genuine
unit predictable cell (0,1] times the whole sample space, verified terminal
measurability and zero initial prediction give I_F(1_cell)=F. Therefore

`nu_(F,-F)(cell) = -norm(F)^2 < 0`.

The two actual finite stochastic sums cancel EXACTLY, while the sum of their
individual predictable L2 squared norms is STRICTLY POSITIVE. Thus unrestricted
multichannel energy cannot be the naive sum of diagonal channel energies.
This counterexample uses dependent opposite channels. It does NOT claim a
counterexample specifically for1362's distinct orthonormal basis terminals;
terminal orthogonality alone has not been proved to annihilate all localized
cross-energy measures for that family.

The independent tests also construct an ORIGINAL full native divergence-domain
preimage for a two-channel actual finite stochastic sum, reusing the existing
stochastic-native recovery and adjoint linearity. No ordinary point derivative
membership is assumed.

## Remaining calculus and verification obligations

General random countable-channel completion, its correct null-space quotient,
literal signed-integral identification on maximal channel domains, temporal
conditional-gradient/causal Clark-Ocone, pathwise brackets and physical-time
IBM Ito/Tanaka remain unresolved outside existing exact verified scopes. No
output-range closure is renamed a predictable integrand construction. IBM
stays ACTIVE and INCOMPLETE. Queue unchanged; no manuscript or queued campaign
is touched. No novelty claim is made without a separate literature audit.

The verification JSON records the fresh full build, COMPLETE transitive
safe-Foundation axiom audit, every unabridged public type and relevant printed
definition, all final source/proof lines, eight independent Lean tests and
all source/configuration/113-manuscript hashes. Complete Git, exact-receipt
and verified PRIVATE main/research synchronization gates remain mandatory.
