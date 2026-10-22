# Checkpoint1341 — actual bounded native IBM products

The original closed joint derivative domain is closed under multiplication of
essentially bounded observables. If f,g belong to that domain, with actual
almost-everywhere bounds |f| <= C and |g| <= D for nonnegative finite C,D,
`IBMIntrinsicProductCalculus.bounded_product` produces F in the SAME domain
whose actual joint-measure representative equals f*g. Both original-coordinate
native fields obey D_i F = f D_i g + g D_i f almost everywhere.
`ProductResult` contains those three actual representative assertions and
original-domain membership. Its complete transparent body was printed and read.

## Proof and reused foundations

`IBMTruncatedSquare` constructs the ordinary primitive of 2*clamp_R, using the
existing GaussianSobolevFixedSupport primitive and fundamental theorem of
calculus. It is C1 with globally bounded derivative 2R and agrees with x^2 on
[-R,R]. The extension itself can grow linearly outside that interval. This is
why checkpoint1339's unbounded-value C1 theorem with bounded continuous
derivative, rather than a globally bounded-value chain theorem, applies.

`IBMIntrinsicBoundedSquare.bounded_square` proves actual f^2 membership for
essentially bounded f, both original-coordinate gradients 2f D_i f, and
norm(D(f^2)) <= 2R norm(Df). Its complete existing `ChainResult` body was also
printed and read. No globally bounded derivative of x^2 is assumed.

For the product, apply this square theorem to f+g and f-g, each bounded by
C+D, and form exactly (1/4)*((f+g)^2-(f-g)^2) in the original domain.
Scalar and coefficient-vector polarization identify actual values and fields.
The source field is transported back through the existing coordinate swap;
the clock field uses the existing uncurry isometry. A proof-local composition
of a linear field map with the original derivative avoids expensive elaboration
without introducing another derivative or domain.

## Verification contract

All 24 new public types, both complete result-definition bodies, and all 249
final source/proof lines were read. Fresh complete root build and complete
transitive safe Foundation axiom audit are required; only propext,
Classical.choice and Quot.sound are permitted. Five independent Lean examples
test full bounded-product scope, actual bounded squares, sine/cosine products
of arbitrary domain inputs, the true constant-one neutral factor, and actual
product-output stochastic integration by parts together with the existing
target-indexed reconstruction. Exact final code, timings, counts and hashes
are recorded in STARDUST_IBM_INTRINSIC_PRODUCT_CALCULUS_VERIFICATION.json.

Development failures were elaboration and explicit scalar/representative
identities, resolved by factorization rather than resource overrides. Failed
development logs remain under .lake/stardust-1341-target*.log. No new axiom,
trust setting, toolchain version, measure, process or stochastic integral.
All 2162 prior Foundation/root sources are preserved except three appended
root imports. All three configurations and all113 archive paths/hashes are
checked against their saved baselines; ResearchSources remains immutable.

## Remaining IBM obligations

This is native source-variable calculus for actual observables. It does not
prove a physical-time IBM Itô/Tanaka formula, a pathwise local time, or a
universal causal Clark–Ocone representation. The existing reconstruction
retains its full initial germ and its target-dependent integral channel.
No product rule for arbitrary unbounded domain inputs is claimed. No separate
product-gradient norm estimate is asserted by ProductResult.

The weighted divergence law remains open. Its proof must control actual field
multipliers, the correction term and adjoint-domain membership, with precise
L2 assumptions. Boundedness of a scalar factor alone does not bound its
gradient. Existing bounded graph approximants of arbitrary domain tests offer
a route from bounded-test Leibniz to full adjoint duality; that extension still
requires a proof. Full intrinsic IBM calculus remains active and incomplete.
The campaign queue and all private-backup gates are unchanged.
