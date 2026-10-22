# Intrinsic IBM unbounded C1 chain rule — checkpoint1339

IBM stays active. The original joint derivative, adjoint, observable Hilbert
space and actual stochastic integrals are unchanged. This checkpoint removes
the global bound on phi from the1338 native SOURCE chain theorem. It retains
C1 differentiability, continuity of dphi and a global bound norm(dphi)<=B.

## Exact theorem and result definitions

`IBMIntrinsicUnboundedChain.unbounded_chain` proves `ChainResult f phi dphi B`
for EVERY f in the FULL ORIGINAL `jointDerivative.domain`. `ChainResult` is an
ordinary transparent Prop definition with this complete content: there exists
F in that same domain, F=phi(f) almost everywhere under the actual joint law;
the actual clock and ORIGINAL-coordinate scenery fields of DF equal dphi(f)
times their respective original fields of Df; and norm(DF)<=B*norm(Df).
There is no global value bound, no phi(0)=0 assumption and no bounded-input
restriction. `GraphResult` transparently records the actual joint graph and
the corresponding clock and swapped-coordinate source fields. Both complete
definition bodies are printed in the combined root audit and actually reviewed;
a predicate name is never substituted for inspection of its mathematical content.

## Actual construction and convergence

Use the existing positive widths e_n=1/(n+1) and define

    phi_n(x) = sin(e_n phi(x))/e_n,
    dphi_n(x) = cos(e_n phi(x)) dphi(x).

The approximants are bounded C1 functions; their derivative bounds are uniform
in n. The sinc identity proves phi_n(x)->phi(x), with norm(phi_n(x))<=norm(phi(x)).
Bounded derivative makes phi globally Lipschitz. Subtracting phi(0) and then
adding the actual constant proves phi(f) is genuine L2 even when unbounded.

`clippedValue_tendsto` proves actual strong JointL2 value convergence using
the EXISTING BochnerL2Approximation dominated-convergence theorem, with the
actual target as majorant. The native product-space multiplier is constructed
using the EXISTING L-infinity/L2 multiplication theorem. Uniform domination
by B times the original gradient norm and actual pointwise multiplier limits
give strong L2 convergence of BOTH native coefficient-valued product fields.

`bounded_approximants` reuses1338's full-domain bounded chain theorem to
produce actual domain elements. `approximation_values` and `gradient_limit`
identify their strong value and both gradient limits. `close_graph` transports
the latter through the verified onto L2 curry isometries, assembles the finite
two-channel convergence, and invokes the EXISTING closed joint derivative on
IntrinsicSpace times JointFieldSpace. This is strong Hilbert graph convergence,
not just weak convergence or convergence against test probes. It is not a
claim of pathwise, uniform-in-physical-time or physical quadratic-variation
convergence. The original-coordinate scenery formula reuses the1338 vector
flip lemma. The derivative bound reuses its already proved joint chain bound.

No new Gaussian law, measure, stochastic-integral completion or substitute
derivative is introduced. Scalar widths, Mathlib's continuous sinc, existing
bounded Gaussian product calculus, actual Lp multiplication, dominated
convergence, unitary transport and original graph closedness supply the proof.

## Tests, scope and open work

Independent Lean tests cover arbitrary UNBOUNDED affine maps a*x+c, identity
output equality in the ORIGINAL domain, the unbounded nonlinear map x+sin(x),
simultaneous strong actual value/source/clock approximations, and the nonlinear
output's actual native stochastic IBP and1337 target-indexed reconstruction.
The reconstruction retains the entire initial germ and target-dependent channel.

The proof does not establish arbitrary locally C1 functions with unbounded
derivative, nonsmooth Lipschitz contractions, general bounded-product Leibniz,
weighted-divergence product rules or a second-order generator chain formula.
In particular x^2 is outside the global bounded-derivative hypothesis; local
boundedness or stronger integrability would need an additional proof.
Physical-time IBM Itô, universal noise/causal Clark–Ocone, initial-germ
triviality, positive-time raw/germ comparison, versions/bracket and the full
intrinsic IBM calculus remain open. Existing focused F1–F3 exact-domain results,
native Poisson/Poincare and all previous verified work are preserved.

## Verification and integrity contract

Three modules,359 final source/proof lines,30 public declarations, including
both transparent result specifications. Full source/proof and unabridged public
type/body review, fresh root build, COMPLETE transitive safe-Foundation axiom
audit and five independent checks are recorded in the verification JSON.
The fresh root build passed6329 jobs in26.906s. All2157 previous mathematical
sources are unchanged except three appended root imports. Three configurations
and all113 archive paths/hashes are checked unchanged.

Development required explicit coercion equalities and factoring the large
existential result statements into the EXACT transparent specifications above.
An exploratory transparency-setting change did not solve the cost and was
reverted. Final proofs use the original resource settings; no heartbeat or
trust override, suppressed error, additional axiom or weakened hypothesis.
Failed development and diagnostic logs are retained. Full root/audit passes
are not replaced by targeted success or by synchronization receipts.
Explicit Git commit, exact-commit receipt and exact PRIVATE main/research
synchronization remain required before closure. Queue and archive stay intact.
