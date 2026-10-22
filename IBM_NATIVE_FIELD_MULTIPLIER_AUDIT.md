# Checkpoint1342 — native IBM multipliers and weak divergence calculus

For every real essentially bounded measurable scalar a on the actual joint
source probability space, `IBMNativeFieldMultiplier.multiply` is a continuous
linear symmetric operator on the ORIGINAL two-channel native field Hilbert
space. Its two original-coordinate representatives are exactly a times the
corresponding original-coordinate field. No differentiability or IBM-observable
measurability of a is needed for this field operator alone.

For bounded f,g in the full ORIGINAL joint derivative domain,
`IBMNativeProductOperators.bounded_leibniz` produces the actual product F in
the SAME domain with the Hilbert-space equality

    D F = M_f (D g) + M_g (D f).

For EVERY u in the original native divergence domain, the proved weak identity is

    <delta u,F> = <M_f u,Dg> + <M_g u,Df>.

Both identities carry actual product representatives, not an arbitrary symbolic
product. `LeibnizResult` and `WeakDivergenceResult` are transparent specifications;
their full bodies are printed and read in the complete final audit.

## Construction and direct reuse

The existing generic `MultiplierCore.boundedMultiplier` already constructs the
actual bounded scalar multiplication operator on coefficient-valued L2.
Its actual representative and symmetry theorems are reused directly.
The existing `vectorSwap` is proved involutive and packaged as an isometric
equivalence. Channel0 uses uncurry followed by that swap; channel1 uses uncurry
alone. Conjugating the existing multiplier by these coordinate isometries
constructs each native channel operator. The finite PiLp continuous equivalence
assembles them without changing the field norm or topology.

Actual representative identities from checkpoint1341, coordinate injectivity
and Lp extensionality establish the Hilbert-space Leibniz equality. Symmetry
moves the two multipliers across inner products. The ORIGINAL densely defined
joint derivative and its actual adjoint then give weak divergence. No assumed
`IsDivergenceMultiplier`, replacement derivative, projected substitute field,
new process or stochastic integral is used.

## Verification

All21 new public types, BOTH complete transparent specification bodies, and
all199 final source/proof lines are reviewed. Fresh full root build, complete
transitive safe Foundation axiom audit and five independent Lean examples are
required. Tests cover both actual original-coordinate channels for arbitrary
nonconstant multipliers; full symmetry; exact constant multiplication including
zero and negative constants; bounded Leibniz; and weak divergence instantiated
with the genuine field whose original divergence equals an actual predictable
stochastic integral. Exact final test code, counts, timings and hashes are in
STARDUST_IBM_NATIVE_FIELD_MULTIPLIER_VERIFICATION.json.

Development repairs concern explicit continuous-isometry coercions, the local
completeness instance of the existing closed observable space, and proof
factorization to avoid large expression elaboration. No new resource setting,
axiom, trust change or weakened domain hypothesis. Failed development logs are
preserved under .lake/stardust-1342-target*.log. All2165 prior Foundation/root
sources remain unchanged except two appended root imports; three pinned
configurations and all113 immutable archive paths/hashes are checked.

## Precise remaining strong-divergence obligations

The weak identity does NOT yet prove M_f u belongs to Dom(delta). Full adjoint
representability requires testing arbitrary, potentially unbounded g in Dom(D),
and an L2 representative of the correction functional. Existing bounded graph
approximants of identity can support that extension, but the estimates and
limits still need proofs. Scalar boundedness alone does not bound Df.

There is an additional observable-subspace issue: the pointwise contraction of
Df with an arbitrary native field u is an ambient joint-source function.
Observable measurability is not automatic. If it is L2, the intrinsic adjoint
formula must use its orthogonal/conditional projection unless actual observable
membership is proved. This is a domain obligation, not a proved counterexample
to every unprojected formula. No universal failure claim is made here.

The next substantive target is the strong weighted-divergence law with exact
integrability, projection and adjoint-domain conclusions. Full physical-time
IBM calculus remains open. Existing target-indexed reconstruction retains the
full initial germ; no universal causal Clark–Ocone formula is claimed. IBM
remains active; the saved linear campaign queue is unchanged.
