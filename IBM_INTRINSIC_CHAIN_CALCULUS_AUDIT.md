# Full-domain intrinsic IBM bounded C1 chain calculus — checkpoint1338

IBM remains active. The derivative and its adjoint, process law and stochastic
integrals are unchanged. The result concerns Gaussian SOURCE derivatives of
actual IBM observables; it is not a formula for physical IBM time evolution.

## Reuse and exact new theorem

`IBMFiniteAverageCore.bounded_chain` already proved preservation of the full
common domain by bounded C1 composition. Its proof called the verified actual
product Gaussian chain theorem twice but discarded the gradient witnesses.
This checkpoint does not claim domain preservation itself as a new discovery.
It reuses `GaussianClosedChainRule.bounded_product_chain_graph`, the existing
unitary transports and observable restriction, retaining BOTH actual gradients
and identifying them with the ORIGINAL `jointDerivative`.

For EVERY f in the full original joint domain, let phi be C1 with continuous
derivative dphi and global bounds abs(phi)<=A and abs(dphi)<=B. There exists F
in the SAME domain, F=phi(f) almost everywhere under the actual joint law.
`IBMIntrinsicChainRule.bounded_chain` gives both native derivative fields:
uncurrying the clock channel gives dphi(f) times the original clock field;
uncurrying the scenery channel gives dphi(swap(f)) times the scenery field
in its native SWAPPED product coordinates. No pointwise representative is
asserted outside the appropriate almost-everywhere equivalence class.

`IBMIntrinsicChainEnergy.bounded_chain_energy` translates the scenery field
back to the ORIGINAL sample coordinates. Thus both channels have the actual
multiplier dphi(f), with their respective actual fields. It proves

    norm(D F) <= B * norm(D f).

The proof uses genuine L2 multiplier domination on each channel and the exact
two-channel Hilbert norm identity. No conditional expectation or causal
projection is substituted for a derivative. The source-field coordinate flip
is the existing measure-preserving Lp composition isometry instantiated for
coefficient-valued fields; no new measure or Gaussian foundation is built.

The two partial chain constructions are glued by actual almost-everywhere
identity of their scalar outputs under the product swap. This verifies a common
intrinsic output and the true joint operator graph; it does not assume that
separately chosen fiber witnesses are jointly measurable. Measurable product
gradients come from the existing product chain theorem.

## Domains and limitations

The input domain is the FULL intersection of the original clock and source
derivative domains, not just polynomial cylinders or individual time averages.
Boundedness of phi and its derivative, continuity of dphi and the actual C1
derivative equation are explicit hypotheses. General unbounded Lipschitz
composition, nonsmooth normal contractions, bounded-product Leibniz rules,
weighted divergence product identities and second-order generator formulas
are not established by this checkpoint. No differentiability of an arbitrary
point IBM observation is assumed. No pathwise physical-time chain/Itô law,
universal stochastic noise, or causal Clark–Ocone theorem follows here.

The new fields and energy estimate can be paired with the existing native
adjoint and actual stochastic integral on all their verified domains.
Independent tests instantiate sine and cosine, check both original-coordinate
gradients and contraction bounds, test constant-input zero derivative, and
connect the nonlinear output to ACTUAL native stochastic IBP and the1337
target-indexed stochastic reconstruction. The latter retains the entire
initial germ and its target-dependent channel; it is not universal CO.

## Verification and preservation

Two modules,252 final source/proof lines,22 public declarations. The full
root build covers6326 jobs and passed in30.432s. The complete transitive audit,
all actual unabridged public types, final source/proof review, independent
tests and precise input hashes are recorded in the verification JSON.
All2155 prior sources are unchanged except two appended root imports; three
configuration files and all113 manuscript paths/hashes are checked unchanged.

Development exposed a missing finite-p exponent instance, a scalar-only swap
helper and elaboration limits. The final proof uses the appropriate existing
instances, the vector-valued measure-preserving isometry, typed graph
equalities and factored transport lemmas. No new proof-resource overrides,
suppressed errors, trust changes or mathematical hypothesis weakening.
Failed development logs are retained and are not verification evidence.

The first combined independent-test attempts were explicitly stopped after
measured expensive elaboration (315.173s and149.102s wall time). A diagnostic
copy with temporary per-example progress writes located the cost in the fifth
existential stochastic-reconstruction statement; the first four tests passed.
The final test uses a private proposition definition containing the EXACT same
reconstruction equality and hypotheses, then applies the already verified
identity to the nonlinear output. This preserves the test's mathematical scope.
The constant test also uses typed norm equalities. Diagnostics stay outside the
library and final test pass. No mathematical source changed after the successful
full build and complete audit; neither pass is repeated on unchanged inputs.

Complete exact-commit receipt and PRIVATE main/research synchronization remain
required before checkpoint closure. Focused F1–F3,1336 Poisson/Poincare and1337
actual target-indexed reconstruction are preserved. The queue, immutable
archive, no-expiration directive and every existing verification gate stand.
