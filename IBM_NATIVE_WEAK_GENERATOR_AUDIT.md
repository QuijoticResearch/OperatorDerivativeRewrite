# Checkpoint1350 — full-domain weak L1 native calculus and a nonconstant clock potential

The previous strong chain rule required Gamma(f) in L2. This checkpoint removes
that hypothesis for a precisely stated WEAK L1 identity on the ENTIRE original
native generator domain. It does not silently weaken the conclusion of the
strong theorem or infer strong graph membership from weak integrability.

## Actual weak divergence density

For EVERY g in the original Dom(D) and u in the original Dom(delta),

    q(g,u) = g delta(u) - <Dg,u>

is a genuine integrable function on the existing joint probability space and
has integral zero. Neither bounded g nor a separate L2 contraction condition
is required for these two assertions: both scalar products are L2 times L2.
The coefficient contraction uses BOTH actual original-coordinate fields.

When g is bounded, for EVERY bounded v in the original Dom(D), the existing
native field multiplication and original adjoint/product rules give

    <g u,Dv> = E[v q(g,u)].

The integrand is genuinely L1. The statement does NOT put g u into Dom(delta)
unless a separate adequate strong representability condition is established.
It does not assume q is L2 or observable. The existing bounded product theorem,
actual field isometries, and total-contraction integral supply the proof.

## Nonlinear identity on the full original generator domain

Assume f in original Dom(D), (Df,y) in ORIGINAL delta.graph, and phi has
continuous globally bounded first and second derivatives. Phi itself may be
unbounded. Construct F in original Dom(D) with F=phi(f) a.e. Then

    w = phi'(f)y - phi''(f)Gamma(f)

is genuinely L1, E[w]=0, and for EVERY bounded original-domain test v,

    <DF,Dv> = E[v w].

Every weighted integrand is proved integrable. NO Gamma(f) in L2, L4 gradient,
bounded f, or additional hypothesis on the original Poisson solution is used.
The supplied HasDerivAt data, continuity and global derivative norm bounds
are explicit. The correct sign is that of the POSITIVE operator delta D.
For sine the density is cos(f)y + sin(f)Gamma(f).

`WeakChainResult` explicitly includes integrability, centering, the actual
original-domain composed observable, its a.e. representative, and ALL bounded
original-domain test identities. Its complete body is printed and reviewed.
The proof reuses the full C1 chain rule twice and the original weak native
divergence pairing. This is more than an expectation-level heat identity.

## Concrete actual IBM construction

For T>=0 take the existing actual clock target

    Y_T = P_IBM(B_T^2-T).

Its centering follows from its already verified ORIGINAL native divergence
preimage. Apply the existing centered Poisson construction to obtain a specific
observable U_T in original Dom(D) with (DU_T,Y_T) in ORIGINAL delta.graph.
For EVERY T>0, Y_T is nonzero, DU_T is nonzero, and U_T is NOT any constant
multiple of the true constant-one observable. These statements are verified.
The full sine weak identity applies to U_T with NO extra energy-L2 assumption.
This constructs a concrete family, through the existing fixed-point solution;
it is not an elementary closed-form formula, nor is sin(U_T) asserted nonconstant.

## Limits and next obligations

Weak L1 source calculus is not a physical-time IBM Itô/Tanaka formula or a
universal causal Clark–Ocone representation. The result does not establish
F in strong Dom(delta D), L2 integrability of w or its observable conditional
projection, observability of Gamma, or preservation of Dom(D) by P_IBM.
Test functions remain BOUNDED original-domain observables; no uncontrolled
extension to arbitrary unbounded tests is made. Strong closure under the
previous precise hypotheses remains valid, independently.

U_T is an actual IBM-observable Poisson potential, not the point observation
X_T. No point-coordinate derivative membership, innovation process, initial-
germ triviality, positive-time raw/germ equality, pathwise version, bracket,
or physical-time stochastic integral is inferred. Full IBM calculus is still
incomplete and active. The saved linear campaign queue is unchanged.

## Verification and integrity

Read all280 final source/proof lines and all27 unabridged public types. Print
and read seven complete definition bodies, including the new WeakChainResult
and reused full C1 ChainResult contract. Fresh complete root build, COMPLETE
transitive safe Foundation axiom audit and six independent Lean tests are
required. Tests cover arbitrary-domain weak-density L1/centering; the ALL-domain
sine weak identity with an arbitrary bounded test and correct sign; every
existing centered Poisson solution WITHOUT energy-L2; the concrete positive-
time clock potential's nonconstancy/nonzero gradient; UNBOUNDED affine phi;
and the actual nontrivial clock-potential sine conservation identity.
Exact code, results, source manifests and wall-clock timings are recorded in
STARDUST_IBM_NATIVE_WEAK_GENERATOR_VERIFICATION.json.

Four preliminary independent sine-test packagings reached the default
elaboration limit when reconstructing a large existential alongside the
expanded sign formula. The final test asserts the FULL universal weak contract
and separately verifies the scalar-integral sign expansion; it retains every
bounded-test claim. All four code/log/timing records are retained. A temporary
transparency heuristic did not help and is absent from the final test; no
resource limit was increased. Library inputs stayed unchanged after root gates.

Development made beta-reduced scalar inner-product multiplication orientation
explicit, supplied the original closed observable-space completeness instance,
and typed the original partial-map zero identity. Failed logs are retained.
No proof-resource/trust/toolchain override, replaced operator, or weakened
verification. All2184 prior Foundation/root sources remain unchanged except
THREE appended imports; three configurations and all113 archive paths/hashes
are checked. ResearchSources is immutable and unstaged. Preserve the ledger,
explicit Git checkpoint, exact-commit receipt and PRIVATE main/research gates.
