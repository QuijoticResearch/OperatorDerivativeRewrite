# Ordinary intrinsic IBM correction fields and unbounded-factor products — checkpoint1361

The Leibniz correction from1359 now has an ORDINARY two-channel L2 field
representative for EVERY intrinsic L2 rough factor. The coefficient class is
unchanged: f is in the ORIGINAL full joint derivative domain, f is essentially
bounded, and BOTH original native gradients of f are essentially bounded.
This does not assert new nonconstant examples of that coefficient class.

For EVERY g in the ORIGINAL joint derivative domain, with NO boundedness
assumption on g, the actual product f*g belongs to the SAME ORIGINAL domain.
Its original two-channel derivative is f*Dg + g*Df. Both terms are genuine
square-integrable fields, with their actual random representatives verified.
This extends the previously bounded-both-factors product theorem. It neither
changes the operator nor assigns a replacement derivative to an excluded input.

## Genuine L2 realization of the correction

`IBMIntrinsicCorrectionField.vectorProduct` reuses `LpProducts.lpSmul` with
HOLDER EXPONENTS (2, infinity, 2). For a fixed bounded vector field v and ANY
scalar g in the actual joint Gaussian L2 space, it constructs g*v in vectorL2.
The map is linear and bounded in g, its AE representative is actual pointwise
scalar multiplication, and its norm is at most norm(v_infinity)*norm(g_L2).
No boundedness or new probability law is imposed on g.

`correctionField V hV` applies that construction in BOTH existing native field
coordinates and transports back by the ORIGINAL coordinate isometric
equivalences. It is a bounded map from joint scalarL2 to jointFieldSpace and
satisfies, for each channel i,

`coordinate_i(R_V g) = g * coordinate_i(V_i)` almost everywhere.

Each channel has the corresponding explicit infinity-times-L2 norm bound.
For bounded g this is EXACTLY the already verified native `multiply g V`.
For arbitrary g, it obeys the genuine full-field adjoint pairing

`inner(R_V g, u) = inner(g, correction(V,u))`.

This is proved directly by L2 inner-product integrals and pointwise inner
product algebra. Both sides are already legitimate L2 Hilbert pairings;
no unproved exchange of limits or unjustified triple-product integral is used.
No abstract Riesz witness substitutes for an actual random field construction.

For g equal to the ACTUAL IBM point, the correction's AE representative is
`IBM_t * coordinate_i(V_i)`, and its ordinary field depends continuously on
physical time in strong L2. This statement is multiplication by an actual
process value, not a physical-time stochastic integral or differentiation.

## Full intrinsic adjoint graph and original-domain closure

`correctionFunctional_embed` identifies1359's correction functional on the
ENTIRE original intrinsic adjoint graph dual with the embedding of R_(Df) g
for EVERY intrinsic L2 g. It uses the already verified full-adjoint stochastic
contraction identity and `testOf_asDomain`, so this is not equality restricted
to a hand-picked test core or ambient-coordinate tests alone.

For g in the original derivative domain,1359's full-dual Leibniz identity,
ordinary-gradient embedding agreement, and the new correction identification
give

`weakDerivative(f*g) = embed(f*Dg + R_(Df) g)`.

The existing `representable_iff_domain` theorem uses original closedness,
density and Hilbert bidual equality. It places the actual product in the
ORIGINAL domain. Embedding injectivity then identifies its original derivative.
The product is intrinsically observable via the already verified actual scalar
multiplier theorem; no observability of a spatial mollifier is assumed.

`productElement_gradient_ae` prints BOTH channels with actual native random
fields, and `productElement_actual_ae` identifies the actual scalar product.
`productElement_gradient_norm` bounds the ordinary gradient by

`norm(nativeMultiply_f)*norm(Dg) + norm(R_(Df))*norm(g)`.

These are the norms of the genuine bounded operators. This theorem does not
claim a sharp coefficient-only constant. `productElement_graph_limit` proves
strong L2 value AND strong original joint-field convergence whenever an
original-domain sequence has both corresponding strong limits. It does not
infer ordinary-gradient convergence from value convergence alone.

For EVERY full intrinsic adjoint test, `product_stochastic_IBP` gives the
actual integrable expectation of f*g*delta(v), equal to pairing the ordinary
product gradient with v. The companion theorem verifies the integrability;
g is still not assumed bounded. This is Gaussian-source/operator IBP, not a
chronological integral against physical-time IBM.

## Reuse, scope and counterexamples

Directly reused: `LpProducts.lpSmul_coeFn/lpSmul_norm_le`, original native
coordinate isometries and multipliers, `IBMNativeContraction.contract_ae`,
`IBMIntrinsicDualMultiplier.full_dual_leibniz/correctionFunctional_actual`,
full intrinsic graph-dual embedding injectivity and representability criterion,
and original source/joint operator closedness and density. No new foundational
measure, process, domain, topology or toolchain is introduced.

Checkpoint1360 remains essential: at every positive time, actual sin(IBM_t)
is bounded but outside the ORIGINAL clock and joint derivative domains.
The ACTUAL IBM point is also outside those domains. They can be used as rough
L2 factors in the correction field and full-dual Leibniz rule; they cannot be
inserted as original-domain factors in the new ordinary product theorem.
Ordinary representability of the correction alone does not make the entire
rough product derivative ordinary. No assertion that every bounded smooth
point function is an admissible regular coefficient follows.

The original derivative concerns Gaussian sources; physical-time Ito/Tanaka,
universal causal Clark-Ocone, chronological stochastic integration, spatial
H-minus-one identification and completion of full IBM calculus remain open
outside previously recorded exact verified scopes. No queued campaign begins.
No novelty claim is made without a separate literature audit.

## Verification record

The accompanying verification JSON records fresh full-root build, COMPLETE
transitive safe-Foundation axiom audit, unabridged public types and printed
old/new definitions, complete final source/proof review, independent Lean tests,
source/configuration identity and113 immutable manuscript paths/hashes.
Development failures and any scratch-test repairs are retained honestly.
Only after these gates may the explicit-path commit receive an exact-commit
receipt and verified PRIVATE main/research backup. ResearchSources remains
read-only and uncommitted. IBM ACTIVE, indefinite queue unchanged.
