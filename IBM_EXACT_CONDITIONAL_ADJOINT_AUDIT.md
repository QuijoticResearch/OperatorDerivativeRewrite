# Checkpoint1352 — exact conditional adjoint domain and uniformly bounded native tests

The conditional-L2 criterion from1351 is now proved NECESSARY as well as
sufficient, under the same genuine L1-density and bounded-test pairing
hypotheses. Original operators and domains are preserved throughout.

## Uniformly bounded original-domain approximation

The scalar clipping function is constructed exactly as

    clip(x) = (|x+1|-|x-1|)/2 = max(-1,min(1,x)).

It is bounded by one, fixes every point of [-1,1], and is nonexpansive. The
existing FULL-domain shifted absolute-value theorem and the original linear
domain operations construct clip(f) in ORIGINAL Dom(D) for EVERY f in that
domain. No atomless law, boundary avoidance, smooth substitute or extra
derivative regularity is assumed.

Every IBM-observable L2 class F with |F|<=1 a.e. therefore has a sequence u_n
in ORIGINAL Dom(D), all with |u_n|<=1 a.e., converging strongly in actual L2 to F.
Start with original dense-domain approximants and clip them; nonexpansiveness
bounds the L2 error by the old error. This is VALUE approximation. No gradient
convergence or uniform derivative bound for these approximants is claimed.

## Observable L1 uniqueness: the missing limiting argument

For a genuinely integrable density a, the uniform bound permits an a.e.-
convergent subsequence of the L2 approximants and dominated convergence with
majorant |a|. Thus annihilation of bounded original-domain tests extends to
all observable unit-bounded tests at the actual integral level.

If a is ALSO measurable with respect to the IBM observation sigma algebra,
its actual sign has an observable L2 representative bounded by one. Testing
against that sign gives integral |a|=0 and hence a=0 a.e. Relative observation
measurability is explicitly retained. The proof constructs the sign through
its observation-strongly-measurable representative; ambient measurability alone
is insufficient. This is not an unsupported passage from L2 density to L1 duality.

## Exact ORIGINAL adjoint-domain theorem

Let U be an actual native field, q genuinely L1, and suppose EVERY bounded
ORIGINAL Dom(D) test v satisfies <U,Dv>=E[vq]. Then

    U belongs to ORIGINAL Dom(delta)
      iff the ACTUAL conditional expectation E[q|IBM observations] belongs to L2.

When U is in that domain, its ORIGINAL divergence equals this conditional
expectation a.e., and the actual conditional realization equals the original
adjoint value. For necessity, the observable L1 difference between conditional
q and delta(U) annihilates the unit-bounded domain tests. The new L1 uniqueness
theorem forces that difference to vanish. Sufficiency reuses1351.

The exact criterion applies to bounded original-domain multipliers g and
original u in Dom(delta), with density g delta(u)-<Dg,u>. It also characterizes
strong composed-domain membership of ANY original-domain representative of
phi(f) satisfying1350's weak chain contract. Equality of actual a.e. values
identifies that representative with the constructed weak-chain output.
The concrete clock-Poisson potential sine theorem is included as an IFF with
the actual conditional sine density's L2 integrability.

## What remains open

An exact criterion does not discharge its right-hand condition for every
nonlinear input or the sine clock potential. That quantitative regularity
problem remains open. No raw-L1 integral with arbitrary unbounded tests,
gradient convergence of the uniformly bounded approximants, or automatic
nonlinear strong-domain invariance is asserted.

The independent signed-clock negative control verifies that a NONZERO latent
clock-source first-chaos variable annihilates EVERY observable L2 test. This
shows why the observable-measurability assumption in L1 separation cannot
be removed. It does not provide a new innovation process or imply that all
clock information vanishes.

These are exact source-variable native operator-domain and uniqueness results.
Physical-time IBM Itô/Tanaka/local time, versions/brackets, universal causal
Clark–Ocone, point-coordinate derivative membership and raw/germ equality are
not established here. IBM remains active and incomplete; no queued campaign
starts at this checkpoint. No novelty claim is made for the generic clipping
or functional-analytic pattern.

## Verification and preservation

Read all294 final source/proof lines, all21 unabridged public types and SIX
printed complete definition bodies (clip, exact bounded weak pairing, weak
chain contract, both actual densities and the reused full C1 chain contract).
Fresh complete root build, complete transitive safe Foundation axiom audit
and six independent Lean tests are required. Tests cover clipping at endpoints
and zero with actual domain membership; uniformly bounded a.e.-subsequence
approximation of the actual clock potential's sign; actual clock native
divergence value recovered by NECESSITY; exact weighted-domain equivalence;
the actual clock-potential sine-domain equivalence; and the nonzero invisible
clock-source counterexample. Exact code, timings and terminal results are in
STARDUST_IBM_EXACT_CONDITIONAL_ADJOINT_VERIFICATION.json.

Development repaired only relative-sigma sign measurability using the actual
strongly measurable representative. Preserve all failed logs and test repairs.
The ordinary printer hides the sigma-algebra argument. A supplemental Lean
Meta gate inspects the actual measurability binder types of sign_observable
and annihilator_zero and checks their sigma argument by definitional equality
against the existing observationSigma. Both explicit checks passed and their
short output was read. An oversized fully explicit instance dump was superseded;
it is not used as that gate or claimed to have been fully reviewed.
No resource/trust/toolchain override or changed old proof. All2189 prior
Foundation/root sources remain unchanged except THREE imports; three pinned
configurations and all113 manuscript paths/hashes are checked. ResearchSources
stays immutable and unstaged. Preserve the ledger, explicit commit, exact audit
receipt and verified PRIVATE main/research backup gates.
