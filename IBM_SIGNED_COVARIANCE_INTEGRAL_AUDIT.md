# Global covariance control and literal signed stochastic pairing — checkpoint1364

The ACTUAL IBM predictable covariance now has a full-sigma-algebra variation
bound, global quadratic energy identities, and a literal signed-integral
identification for every pair of finite predictable inputs. The maximal
separate-L2-domain extension remains OPEN; the distinction below is essential.

## Full predictable measures, including the origin

The prior identities on the elementary ring are extended to the ORIGINAL raw
IBM predictable sigma algebra by pinned measure extensionality. An explicit
countable generator cover includes the time-zero origin and positive finite
horizons. The generator system is the existing one; its intersection closure,
predictable generation and finite-measure hypotheses are reused. This does not
assume equality of total masses or silently discard origin sets.

The following identities are proved as equalities of ACTUAL positive measures,
not only as set-function equalities on finite cells:

`mu_(F+G) + mu_(F-G) = 2 * (mu_F + mu_G)`,
`mu_(c F) = c^2 * mu_F` for every REAL c,
`mu_0 = 0`.

The coefficient in the last scaling statement is ENNReal.ofReal(c^2), with
its sign and zero cases intact. The proofs use exact terminal linearity of the
original actual ring integral, real Hilbert norm identities, and the verified
positive-measure generator extension. Origin contributions are verified zero
on the original time-zero sigma algebra. No filtration is completed or replaced.

Global diagonal normalization then proves

`nu_(F,F) = mu_F.toSignedMeasure`.

Thus the polarized covariance is calibrated to the original single-channel
energy on ALL predictable measurable sets, with the original one-quarter
polarization convention.

## Total variation and genuine finiteness

The actual signed covariance from1363 satisfies

`variation(nu_(F,G)) <= (mu_F + mu_G)/2`.

This is an inequality of positive measures on the FULL predictable sigma
algebra. The proof uses the existing variation_sub_le, variation_smul and
variation_toSignedMeasure theorems, followed by the new full measure
parallelogram identity. Real, NNReal and ENNReal coefficients are transported
explicitly; division by2/4 is not treated as field algebra on infinity.
The right side is finite, so the actual covariance variation is finite.
No conditional finiteness hypothesis remains for the constructed covariance.

## Literal finite signed integration

For ANY finite positive measure on this predictable measurable space, every
original finite processLinear presentation is in L2: it is an actual finite
linear combination of eligible rectangle indicators. This small generalization
reuses the existing MemLp indicator/finite-sum machinery. Apply it to the
actual covariance variation. Then for every finite l,k,

`p -> processLinear(l)(p) * processLinear(k)(p)`

is genuinely integrable against variation(nu_(F,G)). This is the precise
Mathlib VectorMeasure.Integrable condition, not merely existence of a signed
cancellation or a named dual pairing.

`signedPairing` is the LITERAL Mathlib signed/vector integral of this product
against nu_(F,G), using the scalar signed-measure integral notation. The
existing flipped scalar-multiplication bilinear map is used exactly as that
notation requires; it is not replaced by an unrelated pairing.

Rectangle-product integrands are actual indicators of intersections. The pinned
signed indicator integral theorem identifies their integral with the covariance
cell mass. Linearity, with every integrability premise discharged, extends this
to all finite presentations and proves

`integral H*K dnu_(F,G) = inner(actualIntegral_F(H), actualIntegral_G(K))`,

and equality with1363's exact mixedEnergy double sum. Both individual inputs
may be random eligible finite predictable processes and use different grids.
The signed measure is allowed to take negative values.

The independent checks include the ACTUAL IBM1/opposite-channel negative
signed pairing and diagonal norm normalization. They also verify that changing
one finite input on a null set for its OWN original energy measure does not
change this literal signed integral, using the old actual integral isometry.
For arbitrary inputs in the two OLD completed L2 domains, existing density
supplies finite approximants whose LITERAL signedPairing values converge to the
actual completed stochastic-output pairing. That statement concerns the
approximating signed integrals, not yet an integral of the pointwise limit.

## Exact remaining maximal-domain obligation

The half-sum variation bound does NOT by itself establish integrability of H*K
from only H in L2(mu_F) and K in L2(mu_G). Nor is a bound on
`abs(integral H*K dnu)` the same as a bound on
`integral abs(H*K) dvariation(nu)`.

The missing stronger result is the appropriate covariance/variation
Cauchy-Schwarz control on the full predictable sigma algebra, sufficient for
representative independence in the separate individual L2 domains, product
integrability, and identification of the completed stochastic pairing with
that literal signed integral. A full matrix-positivity/Radon-Nikodym argument
or a variation/Hahn-partition argument is a plausible route, not a proved
result of this checkpoint. No counterexample to that desired actual covariance
theorem is claimed, and no smaller common-control domain is declared a solution.

General random countable-channel completion and its null-space quotient,
conditional temporal-gradient/causal Clark-Ocone, pathwise brackets and
physical-time IBM Ito/Tanaka remain open outside their earlier exact verified
scopes. The current foundations are steps toward those objectives, not full
calculus completion. IBM remains ACTIVE; no queued campaign begins.

## Verification and preservation

Require fresh complete root build, COMPLETE transitive safe-Foundation axiom
audit, all unabridged public types and relevant printed definitions, all final
source/proof lines, eight meaningful independent Lean checks, every prior
source/configuration identity and113 immutable manuscript paths/hashes.
The JSON records terminal commands/times and honest development failures.
Preserve the ledger, explicit-path Git commit, exact-commit receipt and verified
PRIVATE main/research backups. No source manuscript, toolchain, trust setting,
operator domain, process law or research queue is changed. No novelty claim.
