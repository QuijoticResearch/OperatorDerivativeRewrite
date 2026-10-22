# Checkpoint1348 — informative clock integration by parts in the original domain

For every observable f in the FULL ORIGINAL jointDerivative.domain and every
T>=0, the actual clock B and its verified isonormal time direction h_T satisfy

    E[f (B_T^2-T)] = E[B_T <D_clock f,h_T>].

BOTH integrands are proved genuinely integrable. No boundedness of f or its
gradient, extra L2 condition on the scalar product, or point-coordinate
derivative membership is assumed. The clock gradient is the original native
clock coefficient field transported by the existing uncurry isometry.

## Proof and nonlinear extension

The existing ORIGINAL divergence graph for (0,B_T h_T), verified at1347, gives
the derivative-adjoint Hilbert pairing. The source coordinate is zero; the
actual clock coordinate identity converts the remaining L2-field pairing into
the right-hand integral. Its integrability follows from L2 times L2. On the
left, observable projection drops out when paired with observable f, and the
existing actual Wick representative is B_T^2-T. This proves equality of actual
probability integrals, with no replacement Gaussian process or derivative.

Reusing the previously verified FULL-domain unbounded C1 chain rule gives,
for any continuously differentiable phi with globally bounded derivative,

    E[phi(f) (B_T^2-T)]
      = E[B_T phi'(f) <D_clock f,h_T>].

Again BOTH sides are integrable. Phi itself need not be bounded. Exact Lean
hypotheses are HasDerivAt at every real point, continuity of the supplied
derivative, and a global finite real norm bound on that derivative. The module
does not silently allow an arbitrary unbounded derivative.

## Nonvacuity and the earlier kernel obstruction

For EVERY T>0 there EXISTS an actual observable f in the ORIGINAL domain such
that D_clock f is NONZERO and the right-hand Stein integral is NONZERO.
The proof uses original-domain density and the already proved nonzero native
clock divergence. If all such pairings vanished, its nonzero observable output
would be orthogonal to a dense domain and hence zero. A zero clock gradient
would force this pairing to vanish, completing the contradiction.

This is an existential domain witness, not an explicit polynomial cylinder or
a theorem that the point observation X_T lies in the derivative domain. The
independent test combines this witness with1346: ALL its deterministic scalar
clock contractions still have zero full IBM-observable projection. The gradient
can therefore be informative through an actual LATENT clock-weighted pairing
despite those first-direction projected contractions vanishing.

## Limits and open obligations

This is a SOURCE-VARIABLE intrinsic integration-by-parts theorem for actual
IBM observables. It does not integrate against physical-time IBM, identify a
Brownian innovation, supply an Itô time drift, or solve a universal predictable
Clark–Ocone problem. The existence witness is not an explicit formula. There
is no claim that observable projection preserves the original derivative
domain, that the entire initial germ is trivial, or that raw and right-germ
filtrations agree at positive times. No new derivative/conditional-projection
closure theorem is inferred from this weak pairing identity.

Physical-time IBM Itô/Tanaka/local time, versions/brackets, and the remaining
full intrinsic-calculus obligations remain open. The finite-horizon observed
martingale integral from1347 remains available with its exact target-dependent
scope; this checkpoint does not turn it into a universal integrator.

## Verification and preservation

All150 final source/proof lines, all14 unabridged public types, and the THREE
actual definition bodies are read. A fresh complete root build and complete
transitive safe Foundation audit pass with only the original three permitted
axioms. Six independent Lean examples test the full-domain integral with both
integrability clauses, sine, an UNBOUNDED affine phi, simultaneous informative
clock-gradient and projected-contraction-zero witness, zero-gradient pairing,
and the atomic constant-zero input. Exact code, terminal results, source
manifests and wall-clock timings are recorded in
STARDUST_IBM_CLOCK_STEIN_IDENTITY_VERIFICATION.json.

Two preliminary independent runs failed only in the constant-zero scratch test:
first an explicit uncurry map-zero identity, then its local coefficient-space
instances were needed. Both code/log/timing records are retained. Tests alone
were corrected; the library stayed unchanged after the successful root gates.

Development repaired scalar multiplication orientation, explicit zero-field
representatives, and a repeated-coercion elaboration timeout by factoring an
actual arbitrary-L2 scalar pairing lemma. No heartbeat/resource override,
weakened domain, toolchain change or suppressed failure was used.

All2182 prior Foundation/root sources remain unchanged except ONE appended
root import. Three configurations and all113 archive paths/hashes are checked.
ResearchSources remains untouched and unstaged. The existing linear queue,
indefinite IBM campaign, ledger and exact-commit/private backup gates remain.
