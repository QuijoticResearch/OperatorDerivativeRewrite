# Actual IBM covariance variation — checkpoint1365

The signed predictable covariance now satisfies a Cauchy–Schwarz bound for its
TOTAL VARIATION on every measurable predictable set. This improves the1364
half-sum estimate and proves independence of representatives from the two
individual energy spaces. Arbitrary completed-product integrability and its
literal signed stochastic identity remain open.

## Objects and domains

Use the original ACTUAL IBM sample law, natural raw predictable sigma algebra,
actual observed terminal channels, positive finite energy measures `mu_F`, and
the1363 actual signed covariance `nu(F,G)`. No process, filtration, operator,
integral, norm or completion is replaced. The new module is
`Foundation/IBMCovarianceCauchySchwarz.lean`.

Signed-measure uniqueness on the existing predictable generators is proved
using an explicit increasing exhaustion: time-zero origin union `(0,n] × Omega`.
It is measurable, increases, and covers the entire space. Existing vector-measure
continuity from below establishes equality on the whole space before applying
the pinned generating-pi-system uniqueness theorem. Equality of total masses is
proved, never assumed; origin events are retained.

## Full covariance and variation identities

Full signed-measure bilinearity holds in both REAL terminal variables, with
symmetry, for arbitrary terminals, including zero and negative scalar cases.
It follows from the original actual bounded ring terminal operators and signed
uniqueness. For every predictable measurable E and real c, the energy polynomial is

`mu_(F+cG)(E) = mu_F(E) + 2 c nu(F,G)(E) + c^2 mu_G(E)`.

Positive finite masses are converted to real values with finiteness checked.
Nonnegativity for ALL real c and the pinned quadratic-discriminant theorem give
`nu(F,G)(E)^2 <= mu_F(E) mu_G(E)`.

The stronger estimate concerns variation, rather than absolute signed mass.
Apply1364's half-sum positive-measure bound to `(F,cG)`, use full covariance
bilinearity, variation scalar homogeneity, and positive energy square homogeneity:

`|c| |nu(F,G)|(E) <= (mu_F(E) + c^2 mu_G(E))/2`.

This is proved for EVERY real c, with no division by c or either energy.
All ENNReal-to-real transports justify finiteness explicitly. Since variation
is nonnegative and c <= |c|, the associated quadratic is nonnegative for every
real c. Its discriminant yields

`|nu(F,G)|(E)^2 <= mu_F(E) mu_G(E)`.

This is genuine total variation on the entire raw predictable sigma algebra,
including sets outside the elementary ring. No stochastic semimartingale bracket
or physical-time quadratic variation is identified by this statement.

## Separate-energy null sets and representatives

The last bound implies `|nu(F,G)| << mu_F` AND `|nu(F,G)| << mu_G`.
The proof first treats measurable null sets and uses pinned measure absolute
continuity extension to all sets. Neither energy need dominate the other.

Consequently, for ARBITRARY real-valued functions H,H',K,K', separate equalities
H=H' mu_F-almost everywhere and K=K' mu_G-almost everywhere imply
HK=H'K' variation-almost everywhere. The literal existing Mathlib signed integrals
are equal under these representative changes. No integrability assumption is
needed for this congruence theorem; it must not be mistaken for an integrability
theorem. Mathlib's undefined-integral convention remains unchanged. The independent
tests also verify equivalence of variation-integrability under such changes.

## Remaining maximal-domain obligation

For arbitrary H in the OLD L2(mu_F), K in the OLD L2(mu_G), still prove

`integral |H K| d|nu(F,G)| <= norm(H)_L2(mu_F) norm(K)_L2(mu_G)`.

Then prove literal signed integral equality with the inner product of the OLD
actual completed stochastic integrals, using genuine dictionary approximation
and justified L1(variation) product convergence. The setwise variation theorem
is a direct ingredient, but it is not asserted to prove this functional theorem
without further work. The representative-independence part is now discharged.
No smaller common-control domain substitutes for the original separate domains.
No counterexample to the desired functional theorem is claimed.

General random countable-channel completion/null quotient, causal temporal
gradient/Clark–Ocone and physical-time Itô–Tanaka remain open beyond their exact
earlier scopes. Full IBM calculus remains incomplete and active. Pseudoprocess
checkpoint1293 stays frozen; the saved subsequent queue is unchanged.

## Verification contract

The committed verification JSON records the fresh complete root build, complete
transitive safe Foundation axiom audit with only `propext`, `Classical.choice`,
`Quot.sound`, all20 final public types, four printed definitions and the entire
174-line final source/proof review. Eight independent tests address arbitrary
signed scalar normalization, PSD energy polynomials, square-root variation
control, null sets from either energy, variation-integrability invariance,
arbitrary null representatives, exact opposite-channel variation normalization,
and actual finite stochastic pairings under simultaneous representative changes.
All prior mathematical/configuration hashes and all113 immutable manuscript
paths/hashes are checked. No resource override, suppressed error, new axiom,
manuscript edit or weakened domain is introduced. Development scratch failures
are recorded separately from successful final gates. Git/private backup closure
requires the exact receipt and verification of BOTH remote branches.
