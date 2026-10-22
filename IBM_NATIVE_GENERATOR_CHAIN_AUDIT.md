# Checkpoint1349 — nonlinear closure of the original native delta D graph

Write D for the ORIGINAL full joint intrinsic derivative, delta for its ORIGINAL
Hilbert adjoint, and L=delta D with its positive sign convention. The new theorem
assumes f in Dom(D), (Df,y) in the original delta graph, and

    Gamma(f) = |D_source f|^2 + |D_clock f|^2 in L2.

Both gradients here are actual ORIGINAL-coordinate coefficient-valued random
fields on the existing joint probability space. For phi with continuous first
and second derivatives, both globally bounded, the theorem CONSTRUCTS F in the
original derivative domain and W in actual joint L2 such that

    F = phi(f) almost everywhere,
    W = phi'(f)y - phi''(f)Gamma(f) almost everywhere,
    (DF,P_IBM W) belongs to ORIGINAL delta.graph.

Thus phi(f) belongs to the original composed operator domain, with the asserted
second-order value. This is a strong ORIGINAL graph theorem, not a formal
identity of differential expressions or a new operator with a chosen domain.
Phi itself need not be bounded. Exact Lean hypotheses supply HasDerivAt for
phi and phi', continuity of both supplied derivatives, and finite global norm
bounds on those derivatives.

## Integrability and proof reuse

For EVERY f in the original Dom(D), Gamma(f) is nonnegative and genuinely L1,
and its actual integral is exactly ||Df||^2. The stronger L2 condition is proved
from L4 integrability of each actual coefficient gradient. Merely knowing
f in Dom(D), or f in Dom(L), is NOT here claimed to establish that condition.

The proof uses the existing full-domain C1 chain theorem twice, obtaining
original-domain F=phi(f) and g=phi'(f). Actual original-coordinate identities
identify DF with the existing native multiplication g Df and identify
<Dg,Df> pointwise with phi''(f)Gamma(f). The bounded second derivative and L2
energy density give the precise total-contraction L2 condition. The verified
full native weighted-divergence theorem then gives g Df in ORIGINAL Dom(delta)
and the stated projected product-minus-contraction value. Actual L2 multipliers
and the existing correction class construct W, with its full a.e. formula.
The original Poisson/resolvent graph machinery is reused rather than duplicated.

## Precise limitations

The positive source operator delta D is NOT identified with physical-time IBM
evolution. For this sign convention the second-order term is MINUS
phi''(f)Gamma(f). The sine test therefore has PLUS sin(f)Gamma(f).
The IBM-observable projection is retained. No claim that Gamma(f) itself is
observable, that this projection preserves Dom(D), or that projection can simply
be omitted has been made.

The theorem is conditional on its explicit regularity/domain hypotheses.
The Poisson-solution test retains Gamma(solution) in L2 as an assumption: the
existing Poisson construction does not automatically prove it. A concrete
nonconstant observable satisfying ALL these strong hypotheses has not been
constructed in this checkpoint. The informative nonzero Dom(D) witnesses from
1348 are not asserted to satisfy them. Point IBM coordinate derivative-domain
membership is not assumed. Gamma in L1 is established unconditionally on Dom(D);
extending the chain rule as a weak L1 identity is a separate possible step,
not an unproved conclusion smuggled into the strong graph result.

Physical-time IBM Itô/Tanaka/local time, appropriate versions/brackets and
universal causal Clark–Ocone remain open. The IBM campaign is not complete and
does not transition at this checkpoint. No novelty claim is made for the general
chain-rule pattern; the contribution is its actual verified original IBM
operator-domain realization, exact products, projection and integrability.

## Verification and preservation

Read all204 final source/proof lines and all16 unabridged public types. Print
and read the actual energyDensity body and the complete reused ChainResult
body appearing in a public theorem hypothesis. Require a fresh complete root
build, complete transitive safe Foundation axiom audit and six independent
Lean tests: L1/energy/norm/positivity, L4-to-L2 criterion, sine correction sign,
unbounded affine phi, compatibility with the existing actual Poisson solution
under its retained regularity assumption, and the true constant-one observable.
Exact terminal results, code and timings are saved in
STARDUST_IBM_NATIVE_GENERATOR_CHAIN_VERIFICATION.json.

Development factored representative and graph lemmas to avoid elaboration
timeouts, removed an ambiguous Gaussian/native coordinate name, used explicit
pointwise subtraction and typed real inner products. No heartbeat/resource,
trust, toolchain or mathematical-domain override. Preserve failed logs and any
independent test repairs. All2183 prior Foundation/root sources remain unchanged
except ONE appended import; three configurations and all113 manuscript paths
and hashes are checked. ResearchSources is immutable and unstaged. Keep the
ledger, exact-commit receipt and verified PRIVATE main/research backup gates.
