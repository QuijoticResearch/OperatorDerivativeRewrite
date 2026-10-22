# Completed actual IBM signed stochastic pairing — checkpoint1367

The maximal separate-energy product-integrability and literal signed-integration
identification left open in1363–1365 are now proved. For arbitrary H in the
ORIGINAL L2(mu_F) and K in the ORIGINAL L2(mu_G),

`integral |H K| d|nu(F,G)| <= norm(H) norm(K)`,

and the LITERAL pinned Mathlib signed integral satisfies

`integral H K dnu(F,G) = inner(actualIntegral_F H, actualIntegral_G K)`.

This extends the1364 actual finite signed stochastic identity. It does not
replace the original integrands, operators, process or filtration. It also does
not establish a physical-time semimartingale bracket, causal Clark–Ocone, or full
intrinsic IBM calculus.

## Exact original domains and genuine integrability

`Foundation/IBMCompletedSignedCovarianceIntegral.lean` proves `product_integrable`
for ANY functions H,K satisfying only MemLp H 2 mu_F and MemLp K 2 mu_G.
There is no premise of membership in L2(mu_F+mu_G), boundedness, common-grid
adaptation, smoothness, point-domain differentiability, or mutual domination of
the two energies. In particular, arbitrary chosen Lp representatives are covered.
Integrability is against the ACTUAL covariance VARIATION, rather than only a
bound on the absolute value of a signed integral.

The positive common control alpha=mu_F+mu_G is used internally for Radon–Nikodym
densities of the ORIGINAL measures. It is not a replacement integrand domain.
All three finite measures are absolutely continuous with respect to alpha.
Their actual measurable real RN densities are nonnegative and integrable;
set integrals recover the original real masses, with finiteness justified.

For each real c,1365's scaled variation Young bound becomes an alpha-AE density
inequality through pinned set-integral order comparison. Collecting this on
COUNTABLY MANY rationals first, then using rational density and continuity,
gives the inequality for all real c on a single full-measure set. The quadratic
discriminant proves v^2 <= f*g alpha-AE, where f,g,v are the two energy densities
and covariance VARIATION density. No uncountable intersection of AE events is
used, and no division by a density, energy or scalar is required.

An elementary scalar square-root/Young inequality gives

`v |x y| <= (f x^2 + g y^2)/2`.

Pinned RN integrability transport and original L2-square integrability show
variation-integrability first for strongly measurable representatives. The1365
separate-energy absolute continuity transfers each individual AE representative
equality to variation. This yields integrability for the ENTIRE original domain.

## Sharp functional estimate and convergence topology

The weighted product is integrable with respect to alpha by the proved RN
transport. Applying Young with cH,K, integrating, and transporting BACK to the
actual measures gives, for all real c,

`|c| integral |HK| d|nu| <= (c^2 integral H^2 dmu_F + integral K^2 dmu_G)/2`.

A second discriminant argument proves the square functional bound. Exact old
L2 inner/norm identities then give the stated sharp norm-product inequality.
No strengthened domain or conditional uniform bound is introduced.

For arbitrary old completed inputs H,H',K,K', the proved difference estimate is

`integral |HK-H'K'| d|nu| <= norm(H-H') norm(K) + norm(H') norm(K-K')`.

The function/coercion identities are transported through the individual AE
filters before using the algebraic product difference. Therefore ANY two strong
L2 sequences in the separate original spaces have products converging in genuine
L1(VARIATION). This is stronger than convergence only against selected test probes.

The pinned vector/signed integral norm estimate then gives convergence of actual
signed integrals. Its bilinear map is the existing flipped lsmul map, explicitly
typed over REAL scalars; no new integration convention or norm normalization is
assumed. Integrability of every input and limit is established before subtracting
integrals. The map's finite operator norm suffices for continuity.

## Identification with actual completed stochastic integrals

The old full predictable integral supplies genuine dictionary approximations for
EVERY original completed H,K. The preceding L1(variation) and signed-integral
limits apply to those approximations. Separate-energy AE representative invariance
identifies each dictionary signed integral with1364's LITERAL finite signed
stochastic pairing. The old actual isometries give strong convergence of stochastic
outputs and hence their inner products. Uniqueness of limits proves the full
displayed identity. No approximation sequence, density, convergence, product
integrability or signed-integral continuity obligation is left as a premise.

Independent tests also check diagonal squared norms, the completed two-channel
energy formula, the full finite-family completed Gram/signed energy, arbitrary
null representatives, and existence of actual finite approximations with both
genuine product-L1 convergence and convergence to the actual stochastic pairing.

## What remains open

This closes the previously isolated maximal separate-L2 signed covariance-product
gap. It does not by itself construct a general countable RANDOM multichannel
completion/null quotient, prove causal temporal gradient/Clark–Ocone identification,
or establish physical-time IBM Itô–Tanaka calculus or pathwise brackets. The
earlier verified F1–F3 domains, intrinsic rough-domain obstructions and valid
native adjoint/calculus results retain their precise scopes. Next use these
completed cross-channel energies to investigate the actual multichannel calculus;
do not claim that full IBM is complete or start a queued campaign prematurely.

## Verification and source integrity

Keep the fresh complete root build, complete transitive safe Foundation axiom
audit, all21 unabridged new public types, six printed old/new definitions, full
265-line final source/proof review, and eight independent Lean tests. Exact
terminal timings, logs, test code and development diagnostics are in the committed
verification JSON. The standard three axioms are the only permitted ones.
All2222 prior mathematical sources (except the one new root import), three
configurations and113 immutable archive paths/hashes are checked. There is no
new resource limit, suppressed check, toolchain change or manuscript edit.
Checkpoint closure requires explicit Git paths, exact receipt and successful
verification of BOTH private remote refs. The campaign queue is unchanged.
