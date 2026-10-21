# A(2) reuse and source audit

October21,2026. Independent A(2) opened only after the integer/real-order
stopping commit `492d5034b5b100ebfd83a601c1d606a6128964d8` passed its exact
receipt and PRIVATE main/research verification. The existing goal remains active.
The final multichannel campaign remains queued; October31 is the hard stop.

## Existing Xi identification: correction and direct reuse

The previous stopping report overlooked existing normalization declarations.
`RiemannXiNormalization.entireXi_eq_completed` proves

entireXi(s) = s(s-1) completedRiemannZeta(s)/2, for s != 0,1.

The entire definition uses completedRiemannZeta-zero with its poles removed;
`RiemannXiBridge.flow_zero_complex` proves throughout the complex plane

RiemannQuarticFlow.flow(0,z) = entireXi(1/2+I*z/2)/8.

Both complete source files were reread. This zero-time identification was
already proved, not a newly solved normalization problem. The stopping report
is corrected without altering its mathematical results or rewriting history.
Comparison with an external nonzero-time de Bruijn-Newman convention remains
separate. No time threshold is transported here.

## Verified transfer candidate at checkpoint1246

`RiemannQuadraticXiTransfer` directly reuses `flow_zero_time`, `flow_nat`,
`flow_quartic` and the existing Xi bridge. Its theorem `real_order_zero_time`
identifies EVERY real-order zero-time transform with normalizedXi, including
formal negative orders at time0; it makes no nonzero-time negative-order claim.

For s(z)=1/2+I*z/2 the proved coordinate formulas are
Re(s)=1/2-Im(z)/2 and Im(s)=Re(z)/2. Thus Re(s)>7/8 corresponds to
Im(z)<-3/4, with the boundary excluded. `zero_iff_completed` identifies actual
zero-time zeros with completed-zeta zeros away from s=0,1. It retains those
hypotheses because the completed formula has poles there.

`nonzero_of_zeta_half_plane` proves: IF actual `riemannZeta` is nonzero for
Re(s)>theta, THEN the actual zero-time arithmetic flow is nonzero for
Im(z)<1-2*theta. It handles the pole coordinates through existing imaginary-axis
nonvanishing, rather than dividing by a pole or assuming those points absent.
The proof uses Mathlib `riemannZeta_def_of_ne_zero`: a completed-zeta zero forces
a zeta zero there; it does not require a new Gamma nonvanishing theorem.

`zero_im_strip_of_seven_eighths` combines the conditional7/8 transfer with actual
conjugation symmetry to prove |Im(z)|<=3/4 for every actual zero-time zero and
every a>=0. The external zeta nonvanishing statement remains an EXPLICIT
hypothesis. This is neither an independent proof of quasi-RH nor an RH claim.
It is a concrete compatibility theorem between the two exact objects.

## Pinned OpenAI source discovery

The public repository exists. GitHub API inspection pinned its main commit to
`1581d4cbdd69a0faf34b2089614fe2a814316a6a` on October21,2026. Nine public files
were saved and hashed under `.lake/stardust-1246-openai-source`, outside the
read-only ResearchSources archive. The committed
`STARDUST_A2_OPENAI_SOURCE_INVENTORY.json` records every exact
path, immutable raw URL, SHA256, byte count and retrieval time. No upstream code
was executed and no dependency or toolchain was changed.

The [paper source](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/build/paper.tex)
has SHA256 `42a5ee0febca59fd1def55cfd6c6808c322ef4237d7726303ea52f711deac6a3`.
Its main theorem claims the7/8 zero-free half-plane for finite-order Hecke
functions over Q(sqrt(-3)) and Dirichlet functions, with principal poles allowed.
This audit read the abstract, introduction/main theorem and initial proof
overview, not the complete16,677-line proof. The overview uses cubic-theta
reflection, Poisson summation, reciprocal-L Mellin integrals, character moments
and large-sieve estimates. These are arithmetic families, not automatically the
quartic/sixth-order saddle integrals already in Stardust. No method equivalence
is inferred from theta terminology.

The [formalization scope note](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/docs/003.md)
states coverage of the7/8 zeta/Dirichlet/Hecke results and a logarithmic real-zero
gap; the paper's later applications are excluded. This is a statement of
upstream scope, not our independent verification certificate.

The [comparator configuration](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/ComparatorChallenges/QuasiRiemannHypothesis.json)
points from the challenge to solution module
`OAI.NumberTheory.DirichletL.Nonvanishing`, theorem
`OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re`, and permits only the same three
standard axioms as Stardust. Its challenge .lean file contains `sorry` as a
comparison template; that file alone is not the solution proof or evidence that
the solution is admitted. The comparator README describes how to compare them.

The [actual solution entry point](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/DirichletL/Nonvanishing.lean)
contains proof terms invoking
`OAI.SevenEighths.ProbeFinalAssemblyUnconditional.zeta_nonzero` and
`dirichlet_nonzero`. The directly inspected
[assembly](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/DirichletL/Detector/FinalAssemblyUnconditional.lean)
constructs `detector_certified_bands` using `terminal_certificate`; its imports
include `Energy.CertifiedExistence`, `Detector.FinalAssemblyCertifiedBands` and
`Moments.DetectorPlainSlotProfile`. Their transitive proofs have NOT yet been
audited or built independently here. Do not treat entry-point inspection as a
complete axiom audit or import its conclusion as an axiom.

The pinned [toolchain](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/lean-toolchain)
is Lean4 v4.34.1; its [Mathlib manifest](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/lake-manifest.json)
pins `d13f23b723b8a846827a245b89c10fc7d3f11612`, matching Stardust. This removes
an immediate version mismatch, but the upstream project lists many additional
dependencies. No assumption is made that its whole project can be imported or
verified by the existing Stardust build without a separate dependency audit.

## Next mathematical obligations

Continue the focused A(2) reuse audit: distinguish generic zero dynamics,
collision, Gaussian-mixture and Fourier-moment statements from hypotheses
actually established for this arithmetic quadratic flow. Audit the upstream
7/8 proof dependency chain and the paper's relevant estimates before adopting
any theorem, then examine the requested follow-up improvements. The11/12
companion listed in the collection has a weaker numerical half-plane boundary
than7/8; its status and dependencies still need direct review. No full paper,
follow-up, automorphic-method comparison or upstream independent Lean
verification is claimed complete in this first checkpoint.

The source-name/content search did not locate an existing general quadratic
de Bruijn strip-contraction theorem in Foundation. A zero-time vertical-strip
bound therefore does not yet supply a verified positive-time all-real theorem
or an A(2) threshold. That missing dynamical bridge must be audited separately;
do not apply the quartic far-field theorem to the quadratic flow.


Checkpoint1246 final verification: fresh full6096job root build TERMINAL0
(24.4318366s); complete37155declaration root/Foundation
transitive axiom audit TERMINAL0 (50.4781587s), only the
standard three axioms. All10 new public types actually read UNABRIDGED, all106
final production source lines/proofs/definition reviewed. SIX independent
coordinate/boundary/pole-cancellation/negative-order-time0/conditional-strip
tests TERMINAL0 (26.7970821s). First production build
needed real-field ring normalization; later conjugation wrapper needed scoped
ComplexConjugate, final source passed; no semantic weakening or audit bypass.
All1947 source hashes pinned; prior1946 unchanged except root import.
Archive107,Incoming43/42distinct,A4eleven/exactrecursivepaths unchanged.
Nine external public-source hashes are preserved in committed
STARDUST_A2_OPENAI_SOURCE_INVENTORY.json. No upstream proof execution or
independent upstream verification is claimed. Exact private backup pending;
current A2 remains ACTIVE; finalmultichannel queued; October31 hard stop.
