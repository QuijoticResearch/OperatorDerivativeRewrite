# A(2) reuse and source audit

> Current1247 correction: isolated replay66544 is TERMINAL1. It omitted the
> upstream project's required dependency patches and is not a faithful configured
> replay. The published PNT patch removes the two raw admitted decay lemmas.
> No target theorem or axiom audit was reached; no mathematical refutation follows.
> Preserve the log and raw hashes. Inspect/apply the pinned published patches in
> isolation before retrying; do not run upstream lake update in production.
> The reports/source inventory form a documentation-only checkpoint, with no
> upstream or scratch proof certification. Historical RUNNING entries below
> describe observations before this terminal result.


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

## In-progress checkpoint1247: complete source closure and isolated replay

The pinned source-import closure of the actual nonvanishing solution contains
2,924 OAI modules (25,009,201 bytes). The untruncated DirichletL Git subtree is
`1e340710a6e6220842ad878bb89a1de4b1989af4`. Every downloaded OAI source was
independently checked against its Git blob ID and its SHA256. The metadata is
`STARDUST_A2_UPSTREAM_IMPORT_INVENTORY.json`; this is a source inventory, not a
proof certificate. Two files in the subtree are outside the target's
import closure. An incomplete whole-repository API listing was rejected before
resolving this exact subtree.

The external mathematical dependencies are `PrimeNumberTheoremAnd.Wiener`
(repository revision `c39a751132c88b6e8080b74c74023fd95b3d8be0`) and
`RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.Rellich`
(`70f85d4c1bf99c6e7d61e8be4daa6f3664d08d23`). The former also imports the
Architect annotation package, pinned `468e8f58fb4ad6e6ad672a08da6d0d0531e95a97`.
Their required closure has30 source modules. All were saved and hashed in the
isolated scratch project. The OAI sources have no matched admission/axiom tokens
in the source scan; that scan is not an axiom audit.

The pinned Wiener source contains global declarations `prelim_decay_2` and
`prelim_decay_3` with `sorry` proofs. The compiler confirms those admissions.
Their presence in an imported module does not establish their occurrence in
the target's proof term. Neither target acceptance nor rejection is justified
until `Lean.collectAxioms` is run on the actual target. An exact-target audit
file is prepared and will fail on `sorryAx` or any nonpermitted transitive axiom.

The isolated replay is running with the same Lean4v4.34.1/Mathlibd13f23b and
references the existing nine package caches by path. Production Lake/Lean
configuration and all1947 mathematical source hashes are unchanged. Command:
`lake -d .lake/stardust-1247-upstream build OAI.NumberTheory.DirichletL.Nonvanishing`.
Its output is `.lake/stardust-1247-upstream-build.log`. It has NOT completed;
no upstream theorem is certified or imported into production. Do not run another
Lake build concurrently or restart this job merely because a poll times out.

The classical normalization check against
[Polymath, arXiv1904.12438v2, equations1--4 and Theorem3.2](https://arxiv.org/html/1904.12438)
matches the actual quadratic kernel, positive time sign and factor1/8.
Classically, its strip-contraction theorem would turn an initial3/4 strip into
an all-real starting time9/32. That is weaker than the paper's0.22 bound. This
is an external conditional deduction, not a new Lean threshold theorem or
numerical improvement. The general strip-contraction bridge is still missing
from the verified library.

## Further proof-development observations while replay runs

In the fetched auxiliary source, `prelim_decay_2` has no textual downstream use,
and `prelim_decay_3` is referenced only by `decay_alt`; the latter has no textual
use in the fetched closure. These observations are more precise than an
import-level warning, but do not replace proof-term axiom collection.

A direct Gaussian bridge has a concrete integrability route. For centered
Gaussian Y of variance2s, s>=0, the expected norm of
exp(t*u^2)K(u) exp(I*u*(z+cY)) equals the ACTUAL weighted domain at time
t+s*Im(c)^2 and linear tilt -Im(z), for u>=0. Its outer integral is finite by
the existing `RiemannEvenDomain.weighted_integrable`. The exact complex Gaussian
MGF then gives the candidate genuine identities E H_t(z+IY)=H_(t+s)(z) and
E H_t(z+Y)=H_(t-s)(z). The derivation and located Mathlib APIs are recorded in
.lake/stardust-1247-quadratic-gaussian-derivation.md; Lean implementation and
Fubini verification are still pending. No new verified theorem is claimed.

The sign matters: real Gaussian averaging of z^2-1 at variance2 gives z^2+1,
so ordinary positive convolution cannot be presumed to preserve real roots in
the growing-flow direction. For higher pure orders, Gaussian averaging adds a
quadratic frequency tilt instead of advancing quartic/sixth-order time. These
are direct structural tests, not a statement about actual Xi zero locations.

## Unverified implementation drafts and follow-up comparison

The actual Gaussian bridge now has a proof draft at
.lake/stardust-1247-quadratic-gaussian-candidate.lean. It includes the exact
Gaussian phase integrals, norm integral, product L1, Fubini, all actual jets,
flow integrability, and the general shift formula when c^2=delta is real:
E H_t(z+cY)=H_(t-s*delta)(z). Real and imaginary shift corollaries retain the
opposite time directions. It is NOT compiled, imported, committed or certified;
the live independent replay remains the only build. Fix elaboration and run
all production gates before any adoption.

The pinned Siegel comparator maps to `OAI.NumberTheory.SiegelZeros.Main`, with
targets `OAI.SiegelZeros.WeightedTorusJets.exists_absolute_real_zero_gap` and
`dirichletRealZeroBound_proof`. Its entry and two conclusion sources were read;
the first conclusion invokes a local-isolated-Bezout selection theorem, rather
than the inspected7/8 solution entry. Its full dependencies and independent
verification remain OPEN. Six exact source files and hashes are recorded at
.lake/stardust-1247-followup-source/inventory.json; no second replay was started.

The stated logarithmic-gap conclusion is a mathematical consequence of the
fixed7/8 bound: for q>=3 and beta<=7/8, monotonicity of log and positivity give
(1-beta)*log(q)>=log(3)/8>0. Thus an explicit c=log(3)/8 works under the stronger
Dirichlet nonvanishing premise, without primitive/real-character restrictions
on this elementary implication. This neither verifies nor refutes the
follow-up's separate method. A short conditional Lean draft is at
.lake/stardust-1247-siegel-gap-candidate.lean, likewise uncompiled/uncertified.

## Factorial-domain obstruction: mathematical argument and uncompiled draft

Direct source review sharpened the earlier domain caution.
`FactorialAnalyticDomain.H` is lp1 of the derivative coefficients, with
`sum_norm` proving absolute summability. `FactorialAnalyticFunctions.coordinate_recovery`
identifies the coefficients of its realized function with derivatives at0.
This is a substantive restriction, not a generic space of all entire functions.

For the ACTUAL arithmetic integer-order transform, the verified integral and
derivative identities give the mathematical formula
H_t^(2n)(0)=(-1)^n integral u^(2n) exp(t*u^(2m)) K(u) du.
On[2,3], the positive continuous base density has a positive minimum d. The
integral, and therefore the derivative norm, is at least d*2^(2n). It cannot tend
to0, so the full derivative-norm sequence cannot be summable. In particular
there can be no vector in the existing lp1 space whose coordinates equal all
these complex derivatives at0. This applies in particular to actual A2.

The six-lemma draft .lake/stardust-1247-factorial-obstruction-candidate.lean
implements the even derivative/moment identity, compact interval lower bound,
exponential derivative lower bound, nonsummability, and the precise absence of
a derivative-coefficient vector. It is UNCOMPILED/UNCERTIFIED. A stronger
real-function nonrepresentation statement would additionally need the matching
real/complex derivative bridge; the draft does not silently assume that step.
No general impossibility of analytic operator domains is claimed. The direct
Gaussian product-L1 proof avoids this particular lp1 membership problem.

## Existing critical-Gaussian reuse and documentation checkpoint

Entireness alone does not ensure imaginary-Gaussian integrability. For
f(z)=exp(-z^2/2), f(I*y)=exp(y^2/2). The existing verified
`GaussianCriticalExponential.critical_not_integrable` proves this real function
is not L1 under `GaussianCore.γ`, the actual standard Gaussian.
This is a direct mathematical counterexample to a
domain-free extension, not a new claim about Xi zeros. Scratch domain tests at
.lake/stardust-1247-gaussian-domain-tests.lean reuse that theorem and test that
(1+I)^2 cannot equal a real delta. The tests are uncompiled; the actual
theta-kernel product-L1 proof remains necessary.

The completed source inventory and this reviewed report are preserved in a
documentation-only checkpoint. It adopts no upstream result or scratch proof.
All1947 production mathematical sources and the Lake/toolchain configuration
must match audited/privatef38875b exactly before its receipt is recorded.
Under STARDUST_BUILD_OPTIMIZATION.md's explicit documentation-only rule, the
complete6096job build,37155declaration transitive axiom audit, actual10type/full
source review and six independent tests from1246 are retained on those EXACT
inputs; no partial check replaces them. The live upstream replay is not
interrupted to rerun an unchanged production build. The upstream axiom audit
and all draft verification remain OPEN and outside that certificate.


## Checkpoint1248: genuine Gaussian translation of the actual quadratic Xi flow

Within the active independent A2 campaign, RiemannQuadraticGaussian reuses the
verified arithmetic kernel, weighted integrability and Mathlib Gaussian MGF.
For Y with the actual probability law N(0,2s), s>=0 (including Dirac at s=0),
Lean proves product Bochner integrability BEFORE Fubini and, for every real t,
complex z,c and every Fourier jet j, actual Gaussian translation integrability.
If c^2=delta is REAL, E[jet_j H_t(z+cY)]=jet_j H_(t-s*delta)(z).
The same identity holds for the actual whole flow. Thus imaginary translation
advances time to t+s; real translation goes to t-s. The exact inner norm is
the existing weight at time t+s*(Im c)^2 and tilt -Im z. There is no restricted
bandlimit, assumed factorial-coefficient membership, or unproved Fubini step.

Scope: this is an actual integral realization on this arithmetic flow family,
not a zero-preservation/RH/threshold theorem, nor an all-entire-function domain.
The existing critical exponential counterexample gives an entire f(z)=exp(-z^2/2)
whose f(iY) is not integrable under standard Gaussian measure. Also (1+i)^2
is nonreal, so its integrability does not license a real-time-family identity.
No new foundational function space or campaign is introduced.

Fresh full6097job root build TERMINAL0 (41.2271903s);
complete37175declaration root/Foundation transitive axiom audit TERMINAL0
(35.7202334s), only propext, Classical.choice, Quot.sound.
All17 public types ACTUALLY READ UNABRIDGED; all203 final source lines, 14theorems,
2definitions and probability instance reviewed. TEN independent tests TERMINAL0
(25.8077150s): Dirac0, opposite time directions, odd
seventh jet/nonreal point, scaled imaginary shift, nonreal-square integrability,
canceled-pole coordinate, critical nonintegrability/entire counterexample, and
real-square restriction. First test run needed only arithmetic normalization of
(1/2)*4=2; final production bytes unchanged. No errors or audits suppressed.
All1948 source hashes pinned; prior1947 unchanged except root import. Archive107,
Incoming43/42distinct,A4eleven/exactrecursivepaths unchanged; pinned configuration
and Mathlib unchanged. Exact private backup pending at this precommit entry.

Upstream quasi-RH status remains unchanged: the raw isolated replay failed before
the target because our setup omitted published compatibility patches. The proper
patched/configured replay and exact-target axiom audit remain OPEN; this checkpoint
does not certify or refute that external result. Continue current A2 reuse/source
audit; final multichannel follows its stopping checkpoint. October31 hard stop.
