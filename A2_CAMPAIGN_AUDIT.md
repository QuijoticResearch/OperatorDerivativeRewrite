# A(2) reuse and source audit

> Current1251: the CORRECTED published-patch replay and exact-target audit are
> TERMINAL0. Actual zeta and Dirichlet entries independently passed standard3
> transitive axioms and full type review. See STARDUST_A2_UPSTREAM_VERIFICATION.json.
> Old raw-replay warnings below are historical; broad paper/followup review and
> A2 global strip contraction remain open. Pending scratch mathematics is uncertified.

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


## Checkpoint1249: actual Xi-flow obstruction to the factorial analytic domain

RiemannFactorialObstruction proves a precise incompatibility with the existing
FactorialAnalyticDomain.H = lp(real sequences,1), whose shift is bounded and whose
realization recovers all derivative coordinates at zero. For every natural order m
and every real time t, the ACTUAL integer-even arithmetic Xi flow has
D^(2n)H_t(0)=(-1)^n times its positive 2n-th Fourier moment. Positivity and
continuity of the actual weight on [2,3] give d>0 with EVERY n satisfying
norm(D^(2n)H_t(0))>=d*2^(2n). Its derivative norms are therefore not summable,
and no H vector can equal all complex derivative coordinates at zero.

The real/complex derivative bridge is ALSO proved, for every derivative order
and real point, using the existing symmetricJet derivative theorem. Consequently
NO u:H has FactorialAnalyticFunctions.realize u x = Re(H_t(x)) for every real x.
This is actual function nonrepresentation, not merely failure of a guessed vector.
In particular it applies to quadratic flow m=1 at every time and, at t=0, to the
already normalized entire Xi function. Polynomial realization remains valid.
This rules out this exact bounded-shift domain as a direct Xi realization; it does
NOT rule out other operator domains, unbounded generators, or the genuine Gaussian
integrals verified at1248. No zero-location, threshold, or RH conclusion follows.
The general m quantifier is direct reuse within A2, not reopening frozen campaigns.

Fresh FULL6098job root build TERMINAL0 (39.3869544s);
COMPLETE37186declaration transitive root/Foundation axiom audit TERMINAL0
(36.7959668s), standard3 only. All9 public types ACTUALLY READ
UNABRIDGED, all150 final source lines/proofs reviewed; no private helpers/defs.
EIGHT independent tests TERMINAL0 (26.0156850s): quadratic
zero/negative time, general quartic time, signed second derivative, fourth moment,
odd third real derivative at nonzero point, actual normalized Xi nonrepresentation,
and positive polynomial realization control. First draft needed explicit interval
volume and simplification before Nat injectivity; no resource increases or weakening.
All1949 source hashes pinned, prior1948 unchanged except root import. Archive107,
Incoming43/42distinct,A4eleven/exactpaths and pinned configuration unchanged.
Exact private backup pending at this precommit entry. Independent A2 remains ACTIVE;
next return to faithful published-patch upstream replay and concrete theorem reuse.
External quasi-RH proof remains unverified here, not refuted; previous raw setup
omitted required patches. Final multichannel follows A2; October31 hard stop.


## Checkpoint1250: corrected upstream configuration and A2 theorem-reuse audit

This is a DOCUMENTATION/SOURCE-METADATA checkpoint. All1949 production source
bytes and main Lake/toolchain/Mathlib configuration are IDENTICAL to fully audited
and exactly privately backed-up d1bd18a. The permanent explicit documentation-only
rule retains that complete6098job build,37186declaration standard3 transitive
audit, all9type/150lineproof review and eight tests on those EXACT mathematical
inputs. No partial check or external replay replaces them. Fresh archive107,
Incoming43/42distinct,A4eleven hashes and exact recursive paths are unchanged.

The corrected isolated upstream replay was observed LIVE on October21 at01:50EDT,
session18862/LakePID51120, compiling actual OAI/Rellich modules. Target completion
and exact-target axiom audit remain PENDING, not certified by this checkpoint.
Raw failed66544 remains TERMINAL1 and is not restarted. Its missing published
patches/options were our configuration error, not a mathematical refutation.

The30 raw support source files have been preserved separately. Nineteen effective
files match the published pinned PNT/Rellich patches; each hunk context/count and
old/new Git blob was checked. The effective import closure needs no new support
module:30 support and2924 byte-identical OAI sources. The actual pinned support
package configurations were read: OAI/PNT/Rellich autoImplicit=false; Architect
defaulttrue. The published PNT package patch moves its option to the main library
and removes prior extra global options. These choices are now matched in the
isolated target build. Production dependencies, versions and caches are preserved.
STARDUST_A2_PATCHED_SUPPORT_INVENTORY.json records raw/effective source hashes,
patch hashes/Git blobs, exact upstream pins, support configs and effective options.
The older source inventory remains the RAW inventory, not the patched certificate.

The actual entry/assembly, CertifiedExistence, FinalAssemblyCertifiedBands and
DetectorPlainMomentParameters were fully read; CappedAnalyticSuccessor was read
only through its first145lines. The terminal certificate uses finite certified-band
induction, a capped low stage, high/zero stages and radial transport. For the
detector, Delta=beta-7/8 and kappaPlain=3/4+2Delta=2beta-1. Arithmetic source,
character, inverse/marked/unmarked moment hypotheses remain essential. No generic
Gaussian-flow zero theorem follows just from that architecture. The generic
ContinuationShiftedGaussian source was fully read: its contour equality requires
holomorphy throughout the vertical strip and an actual polynomial-Gaussian bound.
Those hypotheses cannot be replaced by the word Gaussian or by formal operators.

Paper-source lines411--512 were selectively read. Its reciprocal-L Mellin argument
requires a positive saving epsilon chosen INDEPENDENTLY of the target character;
implied constants and thresholds may depend on that character. Separate endpoint
estimates give local uniform Mellin convergence, then Fourier inversion identifies
the reciprocal before continuation. This is an explicitly arithmetic route, not
an automatic consequence of Stardust's saddle or Gaussian-translation identities.
The full16,677-line paper, deeper estimates and follow-up proofs remain unaudited.

### Exact reuse map for the actual quadratic arithmetic flow

| Existing verified declaration | Actual A2 applicability and limit |
|---|---|
| RiemannEvenEvolution.even_order_heat_equation, m=1 | Actual time generator -D^2, same positive-time convention; no zero-preservation inference. |
| RiemannQuadraticGaussian.shifted_jet_average / shifted_flow_average | Actual Bochner domain and Gaussian identity, all Fourier jets; real-square coefficient restriction retained. |
| RiemannEvenEntireGrowth.actual_real_entire_nonzero_subquadratic, m=1 | Actual entire, real-on-real, nonzero at0, order<=3/2 bound for every real time; no root-reality hypothesis. |
| RiemannEvenWindowZeros.eventually_real_simple_on_each_disk, m=1 | For EACH fixed disk, eventually all its actual zeros are real/simple. Time threshold depends on disk; no single global threshold follows. |
| RiemannEvenWindowZeros.eventually_nonreal_zeros_outside_each_disk, m=1 | Existing actual large-time compact escape conditional on selecting nonreal zeros; does not assert such zeros exist. |
| RiemannRealOrderComplexZeros.actual_complex_zero_set_infinite, a=1, with flow_nat | Actual infinitely many quadratic complex-plane zeros at every time; says nothing by itself about nonreal zeros. |
| RiemannRealOrderZeroLimits.quadratic_compact_zero_stability / quadratic_nonreal_zero_escape | Varying ORDER at fixed time, requiring actual quadratic ALLREAL and SIMPLE hypotheses. They are not unconditional and do not vary time. |
| RiemannQuarticFrequencyBranch.scalar_ball_lower_bound | Generic local injectivity bound can be reused. QuarticThresholdCollision's global threshold/compactness conclusions cannot be specialized to m=1. |
| RealRootedLaguerreLimit.laguerre_nonneg_of_locally_uniform_split_polynomials_on | Requires actual split-polynomial approximants and locally uniform complex convergence. Subquadratic growth alone does not supply them. |
| RiemannFactorialObstruction.no_factorial_realization, m=1 | Actual quadratic flow outside this specific lp-one bounded-shift function domain, despite its genuine Gaussian realization. |

Classical comparison: [Polymath1904.12438v2](https://arxiv.org/html/1904.12438v2),
equations1--4, Proposition3.1 and Theorem3.2 match the normalization. Strip
contraction sends upper zero height y to sqrt(max(y^2-2s,0)). Conditional7/8
therefore gives y=3/4 and classical9/32, weaker than the paper's0.22. That global
contraction/threshold is NOT proved in Stardust Lean. Zero motion needs a
convergent interaction expansion; collisions and far-field control require
separate proofs. Gaussian averaging or per-disk eventual reality does not close
those obligations. No novelty/RH claim.

Next: let the existing corrected replay finish without duplication/interruption,
then run the prepared exact-target standard3 axiom/type audit if it succeeds.
Continue focused A2 reuse and decisive missing bridges; no campaign transition.
Finalmultichannel remains after the A2 stopping checkpoint; October31 hard stop.
Exact private backup pending for this documentation checkpoint; goal ACTIVE.


## Checkpoint1251: corrected upstream target replay and exact axiom audit PASSED

On October21,2026 at04:21EDT the corrected isolated replay completed ALL7059jobs,
TERMINAL0, in9561.4299975seconds. The exact-target audit then completed TERMINAL0
in46.6159779seconds. Both actual entries passed Lean.collectAxioms transitively:
OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re and
OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re. Each uses ONLY
propext, Classical.choice, Quot.sound. BOTH printed types were ACTUALLY READ
UNABRIDGED. They refer to actual Mathlib riemannZeta / DirichletCharacter.LFunction;
the Dirichlet principal-character pole exception is retained. The explicit example
checking the actual riemannZeta target also passed, with no surrogate replacement.

After replay, ALL2924 OAI source hashes, ALL30 effective support hashes, raw support
preservation and effective configuration hash were rechecked. Nineteen support
files match the pinned published patches. Native Lean4.34.1/Mathlibd13f23b and the
audited options remain unchanged. No upstream theorem is imported as an axiom.
STARDUST_A2_UPSTREAM_VERIFICATION.json preserves the exact scope, pins, timings,
log hashes, complete audit source/output and target types. The old raw failed
replay remains a setup error, not a refutation. Its two missing patch sets and
options were supplied before this successful corrected replay.

Scope is INDEPENDENT KERNEL REPLAY/AXIOM VERIFICATION OF THESE TWO TARGETS. It is
not a complete human review of the16,677-line paper, a separately audited Hecke
entrypoint, or independent verification of every followup claim. Selective method
and followup review remain open. This supplies the audited external hypothesis
for the existing conditional A2 zero-time transfer; it does not itself formalize
global strip contraction, a new A2 threshold, or RH. No dependency/version change
is made to production Stardust. The external actual conditional proof can now be
instantiated in an isolated integration check when useful.

This finite checkpoint contains ONLY reports and external verification metadata.
All1949 production mathematical inputs and main configuration are IDENTICAL to
fully audited d1bd18a. Under the explicit permanent documentation-only rule, its
COMPLETE6098job build, COMPLETE37186declaration transitive standard3 audit, all9
public-type/150lineproof review and eight tests are retained on those EXACT inputs.
Fresh archive107/Incoming43(42distinct)/A4eleven hashes and exact recursive paths
are unchanged. The three parabolic/Hermite/truncation scratch drafts and all new
limit arguments above remain UNCOMPILED/UNCERTIFIED, outside this certificate.
The executable files are not adopted into production or approved as mathematics.

The compiler is now FREE: upstream18862 and target audit88905 are TERMINAL0;
do NOT poll either completed handle or call them live. Next compile and repair
the three preserved A2 supporting drafts serially, then pursue the ACTUAL all-order
parabolic Fourier remainder, locally uniform Hermite collision limit and zero counts.
Do not stop at the supporting counterexamples or generic Hermite facts. Global
strip control still remains open in Lean. Current A2 remains ACTIVE; finalmultichannel
follows its stopping checkpoint; October31 hard stop. Exact private backup pending.


## Checkpoint1252: real and simple Hermite roots; actual upstream flow integration

Foundation/RiemannQuadraticHermite.lean directly evaluates the EXISTING
GaussianTimeSpaceHermite.polynomial 2 n on complex z. It proves the variance-two
recurrence Q_(n+2)=z Q_(n+1)-2(n+1)Q_n and the finite Christoffel-Darboux identity
Q_(n+1) conjugate(Q_n)-Q_n conjugate(Q_(n+1))=(z-conjugate(z))E_n(z), where
E_0=1 and E_(n+1)=|Q_(n+1)|^2+2(n+1)E_n>0. Consequently EVERY complex root of
EVERY Q_n is real. No consecutive polynomials share a root; actual complex
derivation lowers Q_(n+1) to (n+1)Q_n, so every root has nonzero derivative.
The private multivariate-evaluation derivative lemma is proved by polynomial
induction. These are precise supporting statements for parabolic zero splitting,
NOT the actual Xi-flow parabolic limit, zero counts or global strip contraction.
The exact all-order flow remainder and its zero-count application remain OPEN.

Fresh FULL6099job root build TERMINAL0 (39.1532037s),
COMPLETE37208declaration transitive root/Foundation audit TERMINAL0
(44.3278380s), ONLY propext/Classical.choice/Quot.sound.
ALL12 public types ACTUALLY READ UNABRIDGED, all110 source lines including two
definitions and the private helper ACTUALLY reviewed. EIGHT independent Lean tests
TERMINAL0 (23.2745665s): explicit Q2/Q3/Q4 coefficients,
degree100 real-root and simplicity specializations, consecutive-degree25 exclusion,
actual cubic root0 with derivative -6, positive energy at complex I. Separate exact
integer-coefficient CD checks through degree12 used independent closed Hermite
coefficients and closed energy sums; those finite checks are not the all-degree
certificate. Raw elaboration needed Pi function normalization and explicit eta
expansion, without resource increases, weakened checks or added axioms.
All1950 source hashes pinned; prior1949 unchanged except the root import. Pinned
configuration unchanged. All107 recursive ResearchSources paths/hashes preserved,
Incoming43/42distinct and A4eleven/exactpaths unchanged. Manuscripts were not edited.

The independently replayed upstream actual zeta theorem was ALSO instantiated in
an ISOLATED test with the existing RiemannQuadraticXiTransfer. Two complete proofs
now yield |Im z|<=3/4 for all actual zero-time flow zeros at every a>=0, including
actual quadratic m=1. Both integrated proofs passed transitive standard3 audit and
unabridged type/proof review, TERMINAL0 (42.4116798s).
STARDUST_A2_UPSTREAM_VERIFICATION.json preserves complete integration code/output.
An initial cast rewrite loop and then a non-definitional cast mismatch were repaired
using only Nat.cast_one and the explicit flow_nat identity; failed probes were NOT
certified. OAI artifacts were added ONLY to the child test process LEAN_PATH; no
production dependency, package or toolchain changed. This proves compatibility
with the ACTUAL flow, not just a similarly named analytic surrogate. No global
contraction, new threshold or RH follows. The known classical 9/32 consequence
would still require its separate global-flow theorem and is not a new bound.

Independent A2 remains ACTIVE, previous integer/real-order campaigns stay FROZEN,
final multichannel remains gated AFTER A2. Next compile the existing phase and
truncation-obstruction drafts serially, then prioritize the genuine all-order actual
parabolic integral remainder and zero-splitting connection. Preserve October31
hard stop. Permanent build optimization is already complete: original full-build,
thread, cache and complete-audit settings remain, only the preliminary type helper
has a measured23.19percent benefit. Exact private checkpoint backup is pending.


## Checkpoint1253: actual quadratic-flow double-zero parabolic limit

Foundation/RiemannQuadraticParabolic.lean proves a GENUINE actual Fourier-integral
expansion, with no assumed factorial analytic-domain membership and no infinite
Taylor/integral interchange. For every real t, complex z, Fourier jet j, real |h|<=1
and complex |w|<=R, the actual jet at (t+h^2,z+h*w) differs from
jet_j+h*w*jet_(j+1)+h^2*(w^2/2-1)*jet_(j+2) by at most C_j(t,z,R)*|h|^3.
The explicit finite budget is C_j=8 integral_halfLine weighted 1 j (t+2)
(norm z+2R). The EXISTING actual weighted-integrability theorem supplies its L1
domain. The actual integrand phase identity is proved first. Its second-order
remainder is genuinely integrable for ALL h,w; the uniform bound only needs |h|<=1.
For Q=norm a+norm b, factorial exponential estimates absorb polynomial factors
into 8 exp(2Q); this is exactly the time+2, tilt+2R enlargement above. Integrability
is established BEFORE integral linearity and remainder identification.

Pairing the two actual Fourier jets gives the ACTUAL symmetric flow expansion
H_(t+h^2)(z+hw)=H_t(z)+hw H'_t(z)+h^2*(w^2/2-1)H''_t(z)+E,
with norm E<=C_0*|h|^3. In particular, if H_t(z)=H'_t(z)=0, then
H_(t+h^2)(z+hw)/h^2 converges to (w^2/2-1)*H''_t(z), UNIFORMLY on EVERY fixed
complex disk, as real h tends to0 through h!=0. Both TendstoUniformlyOn and the
explicit error bound C_0*|h| are proved. A direct verified identity identifies the
limit with RiemannQuadraticHermite.value 2 w/2 times H''_t(z). The limit theorem
does NOT require H''!=0; that extra hypothesis would be needed for a nonzero
quadratic model and for a subsequent zero-splitting application. No existence of
an actual arithmetic double zero is assumed or asserted.

Fresh FULL6100job root build TERMINAL0 (39.4160129s);
COMPLETE37236declaration transitive root/Foundation audit TERMINAL0
(36.2564636s), standard3 axioms ONLY. ALL16 public types
ACTUALLY READ UNABRIDGED; COMPLETE271 source/proof lines including three definitions
ACTUALLY reviewed; no private helpers/instances. TEN independent Lean tests
TERMINAL0 (25.1651215s): exact phase/heat-sign algebra,
large-h integrability, budget nonnegativity even at negative formal radius,
actual w=0 flow sign, h=-1 with w=I, seventh-jet specialization, scaled w=0 bound,
w=sqrt2 Hermite-model cancellation, and the actual uniform Hermite statement.
Initial tests required explicit subtraction normalization; production mathematics
was unchanged. Draft repairs handled lexical spacing, namespace placement,
function-level Pi addition, exponent regrouping and a looping general neg_pow
simplification; no resource increases, disabled checks or new axioms.
All1951 mathematical hashes pinned; previous1950 unchanged except root import.
Pinned toolchain/Mathlib/configuration unchanged. All107 recursive manuscript
paths/hashes preserved, Incoming43/42distinct,A4eleven/exactpaths unchanged.

Independent finite quadrature of the literal arithmetic Phi kernel checked BOTH
positive and negative h, w=0/sqrt2/1+i, three grids1024/2048/4096. Correct normalized
errors decrease with |h|; the wrong heat sign stays around0.00142. Maximum grid
change 1.2821114e-13. This is EXPLORATORY ONLY: no
certified integral tail or roundoff bound; it is NOT used by any Lean proof.

The main A2 obligation remains higher multiplicity, then ACTUAL zero counts and
real/simple splitting, plus global strip contraction. The present double-zero
case is substantial actual-flow progress, NOT completion of arbitrary-multiplicity
collision analysis or the A2 campaign. Prior classical Proposition3.1 comparison
is retained; this is a formalization of the known local Hermite mechanism, not a
novel RH or de Bruijn-Newman bound. No global zero/RH conclusion follows.

Next all-order proof strategy, NOT YET LEAN VERIFIED: truncate exp(h*b+h^2*a)
at analytic degree N, expand each finite binomial, retain h-degrees<=N, and bound
the remaining terms by |h|^(N+1)*exp(Q). The analytic tail contributes
|h|^(N+1)*Q^(N+1)*exp(Q). Since Q^(N+1)<=(N+1)!*exp(Q), a proposed coarse bound
is ((N+1)!+1)*|h|^(N+1)*exp(2Q), with the SAME time+2/tilt+2R actual L1 mechanism.
Finite exact rational regrouping/Hermite closed-coefficient checks passed N=0..12,
not a general proof. Still needed: general finite reindexing, coefficient identity
with the EXISTING Gaussian Hermite family, actual all-order integral expansion,
then locally uniform finite-multiplicity scaling and zero-count/uniqueness results.
The preserved finite heat-truncation counterexample draft remains uncertified
and is deferred unless directly needed; do not replace the full exponential by
an unproved zero-preserving truncation or distract from actual all-order work.
Independent A2 ACTIVE; prior integer/real campaigns FROZEN; final multichannel
AFTER A2 stopping. October31 hard stop. All verification and private backup gates
remain unchanged; exact private backup pending at this precommit entry.


## Checkpoint1254: actual all-order expansion and every finite-multiplicity limit

Foundation/RiemannQuadraticAllOrders.lean proves the ALL-ORDER actual quadratic-flow
expansion and uniform Hermite scaling at EVERY finite multiplicity. It directly
reuses GaussianTimeSpaceHermite through RiemannQuadraticHermite.value, rather than
introducing an unrelated family with a matching name. Raising/lowering proves
D_q^n exp(q*w-q^2)=Q_n(w-2q)*exp(q*w-q^2), hence the n-th derivative at0 is Q_n(w).
Complex Taylor convergence gives the genuine generating HasSum for every complex
q,w. Scaling q=c*h identifies every coefficient c^n Q_n(w)/n!, without the formerly
proposed finite factorial reindexing. Hermite parity is also derived from this
verified derivative identity.

Cauchy's unit-circle derivative estimate gives, for EVERY n,c,w,
norm(c^n Q_n(w)/n!)<=exp(norm c*norm w+norm c^2). The geometric remainder estimate
then yields, for EVERY N and complex norm h<=1/2, a bound
2 exp(norm c*norm w+norm c^2)*norm h^(N+1). This is stronger than the previous
unverified factorial-dependent proposal and uses one majorant independent of N.
Only the SCALAR exponential phase uses complex h; no new complex-time Xi flow is
assumed. For ACTUAL flow integrals h remains REAL and time is exactly t+h^2.

With c=i*u, the actual integrand factor is proved exactly. Every finite remainder
is genuinely integrable for ALL h,w. For real |h|<=1/2 and complex norm w<=R its
norm is bounded by 2*|h|^(N+1)*weighted 1 j (t+1) (norm z+R) u on u>=0.
Existing actual weighted integrability supplies the L1 domain before integration.
Only FINITE sums are integrated. There is NO infinite-series/integral interchange.
Consequently the actual Fourier jet equals
sum_(n=0)^N h^n Q_n(w) jet_(j+n)(t,z)/n! + error,
with norm error<=B_j(t,z,R)*|h|^(N+1),
B_j=2 integral_halfLine weighted 1 j (t+1) (norm z+R).
Pairing +/- jets using verified Hermite parity gives the ACTUAL symmetric flow
H_(t+h^2)(z+hw)=sum_(n=0)^N h^n Q_n(w) D^n H_t(z)/n! + error
with the SAME budget B_0, for every real t and complex z. The budget is independent
of truncation order N, h and w within the fixed disk. This is genuine arithmetic
kernel integration, not merely a polynomial heat model or an assumed operator domain.

If ALL D^n H_t(z)=0 for n<m, then the scaled ACTUAL flow H_(t+h^2)(z+hw)/h^m
converges to Q_m(w)D^m H_t(z)/m!, UNIFORMLY on EVERY fixed complex w disk,
as real h->0 through h!=0, with explicit error<=B_0*|h|. The statement covers all
natural m, including vacuous m=0. Nonzero D^m is NOT needed for convergence; it is
needed for a nonzero limiting model. With nonzero multiplier d, all roots of
Q_m(w)d/m! are verified real and simple by direct reuse of the existing ALL-degree
Hermite theorem. This MODEL-root result is not a theorem about nearby actual zeros.

Fresh FULL6101job root build TERMINAL0 (39.0147886s);
COMPLETE37279declaration transitive root/Foundation audit TERMINAL0
(34.3704614s), ONLY propext/Classical.choice/Quot.sound.
ALL30 public types ACTUALLY READ UNABRIDGED, COMPLETE340 source/proof lines including
five definitions ACTUALLY reviewed, no private helpers/instances. TWELVE independent
Lean tests TERMINAL0 (36.7768136s): explicit cubic phase
derivative, generating sum at w=0, degree40 coefficient bound, large-h high-order
remainder integrability, nonnegative budget, m=0 base, exact agreement of N=2 with
the previously proved heat-sign formula, explicit cubic and quartic multiplicity
limits, m=0 uniform continuity, cubic center-model cancellation, and nonzero cubic
model derivative. The initial N=2 test needed ring normalization followed by simp;
production mathematics was unchanged. Draft repairs handled function eta/Pi
normalization, explicit Cauchy-center parameters and the disjunctive division-zero
lemma. No resources, axioms or verification settings were weakened.
All1952 source hashes pinned; previous1951 unchanged except root import. Pinned
Lean/Mathlib/configuration unchanged. All107 recursive manuscript paths/hashes,
Incoming43/42distinct and A4eleven/exactpaths preserved. Manuscripts were not edited.

Independent exact integer-polynomial recurrence/closed-coefficient checks passed
all degrees0..30. A further780 finite floating complex-phase checks through N=12
included positive/negative/imaginary h and several complex c,w; maximum observed
error/bound ratio 0.20897422. Floating checks are
NOT roundoff certificates and are not used by Lean. The general theorem is proved
by the kernel, not inferred from these finite controls.

This resolves the all-order expansion/coefficient-identity and finite-multiplicity
uniform-limit obligations left open at1253. It does NOT resolve ACTUAL zero
existence/counts, uniqueness or real/simple splitting near each model root; nor
does it resolve global strip contraction or produce any new threshold/RH claim.
For actual zero transfer, next use the existing Cauchy derivative bounds, scalar
ball injectivity and conjugation machinery; real sign-change/IVT or an equivalent
verified local argument must establish existence. Exact zero counts also need
an actual degree/root-count bridge for the existing Hermite polynomials. Do not
claim a zero theorem merely from convergence to a polynomial with real simple roots.
This is formalization of the known local Hermite mechanism under the prior
Polymath normalization audit, not a novelty claim. Independent A2 remains ACTIVE;
integer/real-order campaigns FROZEN, final multichannel AFTER A2 stopping; October31
hard stop and all complete audits/private-backup requirements remain unchanged.
The finite heat-truncation counterexample remains deferred and uncertified.
Exact private backup pending at this precommit entry.


## Checkpoint1255: ACTUAL local zero existence, uniqueness and real/simple splitting

Foundation/RiemannQuadraticZeroTransfer.lean transfers the verified all-order
Hermite limit to GENUINE zeros of the actual arithmetic quadratic flow. The key
reuse is the already verified, GENERIC complex-ball machinery in
RiemannQuarticQuantitativeSaddle.scalar_ball_surj / scalar_ball_injective and
RiemannQuarticFrequencyBranch.scalar_ball_lower_bound. Their names do not impose
quartic assumptions on their actual theorem types. Cauchy derivative bounds on
an inner disk transfer uniform function closeness on a buffered outer disk into
uniform derivative closeness. Ball surjectivity gives an ACTUAL zero; injectivity
gives uniqueness. No new fixed-point foundation, unproved Rouche/Hurwitz step or
assumed existence premise is introduced.

The generic close-function criterion is explicit: f,g entire, g(b)=0, d!=0,
model derivative within norm(d)/4 on radius r>0, and norm(f-g)<=epsilon on radius
2r, with epsilon<=norm(d)*r/4. It proves a UNIQUE zero of f in the inner CLOSED
disk, nonzero derivative at every such zero, and displacement<=2epsilon/norm(d).
This works over the COMPLEX plane and does not assume real coefficients.

For the ACTUAL quadratic flow at any real t and complex z, suppose all derivatives
below m vanish and D^mH_t(z)!=0. For EACH root a of the EXISTING Hermite Q_m,
there exist r>0 and C>=0 such that for every sufficiently small nonzero REAL h,
there is EXACTLY ONE w in closedBall(a,r) satisfying H_(t+h^2)(z+hw)=0.
Every actual zero in this disk has H'_(t+h^2)(z+hw)!=0 and norm(w-a)<=C*|h|.
The derivative conclusion concerns the ACTUAL spatial flow, not just a model
polynomial or the scaled function. Its affine-chain derivative is explicitly
verified, as is equivalence of scaled and actual zeros when h!=0. The physical
coordinate obeys norm((z+hw)-(z+ha))<=C*|h|^2 by a separate verified identity.
Thus the local actual zero has z(h)=z+h*a+O(h^2). Constants and the eventual
neighborhood depend on t,z,m,a; no global/uniform-in-all-roots threshold is claimed.
No analytic choice of branch as a function of h is asserted.

For an original REAL base point z=x, conjugation of the ACTUAL flow preserves
the scaled zero disk centered at real Hermite root a. Uniqueness forces w real,
and the PHYSICAL zero x+hw is explicitly proved real and simple. This reality
assertion is restricted to real original base points. At a complex original
base point the complex existence/uniqueness/simplicity theorem still applies;
no false real-zero assertion is made. These local results use forward time
exactly t+h^2, in the audited growing quadratic convention.

In addition, EVERY actual quadratic-flow zero has finite POSITIVE multiplicity:
there exists m>0 with precisely the required lower-derivative vanishing and
nonzero m-th derivative. Entire analyticity, existing strict positivity at0 and
the connected-domain identity theorem prove this; finite multiplicity is not an
extra unverified analytic hypothesis about the arithmetic kernel.

Fresh FULL6102job root build TERMINAL0 (38.4039775s);
COMPLETE37297declaration transitive root/Foundation audit TERMINAL0
(41.8011444s), ONLY propext/Classical.choice/Quot.sound.
ALL12 public types ACTUALLY READ UNABRIDGED, COMPLETE229 source/proof lines
including two definitions ACTUALLY reviewed, no private helpers/instances.
TEN independent Lean controls TERMINAL0 (24.7439798s):
complex translated linear zero, its explicitly nonreal location, simplicity/drift
for arbitrary small complex translation, h=1/4 cubic derivative factor16,
negative-h zero equivalence, automatic actual finite multiplicity, cubic-center
actual zero existence at arbitrary complex base, real double-zero branch at
sqrt2, the physical quadratic displacement identity, and the explicit nonreal
root i*epsilon of w^2+epsilon^2 for epsilon>0. The last control explains why a
multiple model root would not justify real-root transfer from closeness alone.
Initial test repair changed only the global norm_one lemma name; production
mathematics was unchanged. All raw generic/actual/real/multiplicity proofs passed
without increased resources, added axioms or weakened checks.
All1953 source hashes pinned; previous1952 unchanged except root import. Pinned
Lean/Mathlib/configuration unchanged. All107 recursive manuscript paths/hashes,
Incoming43/42distinct and A4eleven/exactpaths preserved. Manuscripts were not edited.

A separate120-case floating Newton control used polynomial perturbations
Q_m(w)+beta*h*Q_(m+1)(w), m=1..4, positive/negative h and real/complex beta.
Real cases stayed real; maximum residual 2.797762e-14; maximum
scaled displacement/|h| 0.52542112.
These are NOT arithmetic Xi zero computations or roundoff certificates; no
Lean proof depends on them. The actual-zero result above follows from verified
surjectivity and the genuine Fourier-integral remainder, not numerical inference.

What remains OPEN: exact degree/root counts for the existing Hermite family,
simultaneous distinct branches for all m model roots, and an EXHAUSTIVE cluster
statement excluding additional zeros in the remaining local region. A single
small disk around each model root does not by itself count the entire physical
cluster or control zeros outside every fixed scaled disk. Global strip contraction
and any new de Bruijn-Newman threshold remain open. No RH conclusion follows.
Next prioritize the actual degree/root-count bridge and simultaneous/exhaustive
local counting, reusing the verified univariate/multivariate polynomial machinery
and existing analytic finite-order tools. The local Hermite splitting mechanism
is classical under the prior normalization audit, not claimed as novel research.
Independent A2 remains ACTIVE; prior integer/real campaigns FROZEN; finalmultichannel
AFTER A2 stopping; October31 hard stop. All complete verification and exact private
backup requirements remain; backup pending at this precommit entry.


## Checkpoint1256: exact Hermite count, simultaneous actual zeros, joint remainder

Foundation/RiemannQuadraticCluster.lean closes the model root-count bridge by
DIRECT theorem reuse from the pure-order pseudoprocess/Appell library. The verified
Appell operator at p=2,a=1 is X*P-2P'. Mapping its polynomial to complex coefficients
and comparing the exact recurrence proves its evaluation equals the EXISTING
RiemannQuadraticHermite.value n w for every n,w. PureOrderAppellExpansion.
appell_monic_degree supplies the monic degree n result; it is not reproved for an
unrelated family. The actual Hermite derivative theorem then gives no repeated
polynomial roots. Algebraic closure plus the monic degree yields EXACTLY n distinct
complex roots, all real by existing verification. The finite root set is nonempty
for n>0. The signed-calculus/Gaussian operator foundation is thus connected by a
proved identity to the actual quadratic-flow zero analysis, with exact variance2
and sign, not by an analogy or an assumed naming convention.

The local actual-zero results are now simultaneous. At an actual order-m zero
(lower derivatives vanish, D^m!=0), for EVERY physical radius rho>0 and ALL
sufficiently small nonzero REAL h there is a FINITE SET S of cardinality m of
ACTUAL zeros of H_(t+h^2), all inside ball(z,rho) and all spatially simple.
When z is real, every selected actual zero is real. Finite simultaneous choice,
the proved convergence of scaled branches to the distinct Hermite roots, and
finite pairwise separation establish DISTINCTNESS. Multiplication by h!=0 makes
the physical points distinct as well. This is an actual m-zero LOWER count.
The cardinality m of the selected set is NOT an upper bound on every zero in the
physical disk. Exhaustiveness is deliberately not asserted.

A second advance addresses the gap outside fixed scaled windows. For EVERY N
and complex h,w satisfying norm h*(1+norm w)<=1/2, the scalar phase remainder
has norm at most 2 exp(norm c+norm c^2)*(norm h*(1+norm w))^(N+1). Rescale the
already verified Cauchy estimate with A=1+norm w, c'=c/A and h'=A*h; c'h'=ch
and all finite coefficients are unchanged. The exponent is now bounded independently
of w. With c=i*u this gives the ACTUAL jet and symmetric-flow remainder bound
B_j(t,z,1)*(|h|*(1+norm w))^(N+1), where the FIXED genuine L1 budget is
B_j(t,z,1)=2 integral_halfLine weighted 1 j (t+1) (norm z+1).
There is no growing tilt norm z+norm w hidden in this constant.

In PHYSICAL coordinates v=h*w, with h!=0 and |h|+norm v<=1/2, the lower-derivative
vanishing assumption gives the proved actual bound
norm(H_(t+h^2)(z+v)-h^m Q_m(v/h) D^mH_t(z)/m!)
 <=B_0(t,z,1)*(|h|+norm v)^(m+1).
The constant remains fixed when v/h grows without bound. This closes the actual
remainder-domain issue needed for an annular confinement proof. It does NOT by
itself prove confinement or exclude additional cluster zeros. All integration
uses existing weighted integrability and finite sums; no infinite exchange or new
complex-time Xi flow is assumed.

Fresh FULL6103job root build TERMINAL0 (42.7823671s);
COMPLETE37335declaration transitive root/Foundation audit TERMINAL0
(36.0755111s), ONLY propext/Classical.choice/Quot.sound.
ALL19 public types ACTUALLY READ UNABRIDGED; COMPLETE295 source/proof lines,
including two definitions, ACTUALLY reviewed; no private helpers/instances.
TWELVE independent Lean controls TERMINAL0 (25.4226521s):
exact quadratic polynomial, root sets at0/1, nine distinct real roots, sqrt2 root,
monic degree7, three actual distinct simple zeros at a complex base, two actual
real zeros at a real base, exact physical quadratic heat sign, scalar joint bound
with w=10000, negative-h seventh-jet joint bound, and actual existence of a real
root in degree17. Initial controls only removed an already-closed tactic and
normalized numerical casts; production mathematics was unchanged. Draft repairs
used the polynomial algebra-map identity, multiplication associativity, absolute-
value lexical spacing and explicit half-line membership types. No resources,
axioms or verification checks were weakened.
All1954 source hashes pinned; previous1953 unchanged except root import. Pinned
Lean/Mathlib/configuration unchanged. All107 recursive manuscript paths/hashes,
Incoming43/42distinct and A4eleven/exactpaths preserved. Manuscripts were not edited.

Independent exact rational Sturm-sequence controls gave n real roots and constant
terminal gcd for n=1..12. A further1040 floating joint-phase checks included
scaled coordinates up to 22360679.77499790; maximum observed
error/bound ratio 0.11660038. Floating controls
are NOT roundoff certificates, arithmetic Xi zero computations or confinement
proofs. The general degree/count and remainder claims are proved in Lean independently.

NEXT CONFINEMENT STRATEGY, NOT YET LEAN VERIFIED: set d=norm(D^mH_t(z))>0,
f=m!>0, B=B_0(t,z,1)>=0. Let M>=1 bound all existing Hermite root norms, and
R>=max(1,2M). The proved monic polynomial with exactly m roots should yield
norm Q_m(w)>=(norm w/2)^m when norm w>=R, by its product factorization.
For v=h*w in that annulus, norm v>=|h| and the joint error is bounded by
B*2^(m+1)*norm v^(m+1), while the leading term is at least
[d/(f*2^m)]*norm v^m. Choosing
 delta=min(1/4,d/(f*2^(2m+2)*(B+1)))>0
should make the error at most half the leading term for norm v<=delta and
|h|<=delta. A zero there is impossible. This would confine every zero in the
physical delta disk to norm v<R*|h|. Still required: FORMAL monic product norm
bound, exact constant/cancellation verification and the actual confinement theorem.

After confinement, use compact nonvanishing of the limiting model on the bounded
scaled disk outside the finitely many verified local zero neighborhoods. Uniform
convergence should put EVERY scaled actual zero inside one of those neighborhoods;
local uniqueness then makes it one of the selected m zeros. This compact-gap and
bijection/exhaustive argument also remains OPEN. Neither the selected cardinality
nor the joint remainder is being substituted for that proof. Global strip
contraction/new thresholds/RH remain open. This continues the classical local
Hermite mechanism under the prior literature/normalization audit; no novelty claim.
Independent A2 ACTIVE; prior integer/real campaigns FROZEN; finalmultichannel AFTER
A2 stopping; October31 hard stop. All full-build, axiom, type/proof, source-integrity
and exact private-backup gates remain; backup pending at this precommit entry.


## Checkpoint1257: actual annular confinement and EXHAUSTIVE local zero clusters

Foundation/RiemannQuadraticConfinement.lean proves the previously open upper-count
obligation for the ACTUAL quadratic Xi flow. The existing Hermite polynomial has
its exact finite monic root product. With M=1+sum(root norms), norm Q_m(w) is at
least (norm w/2)^m for norm w>=2M. This uses the exact m-root cardinality already
verified through the Appell bridge, including m=0, rather than a numerical root list.

At lower-derivative vanishing through order m-1 and nonzero D^mH_t(z), set
 d=D^mH_t(z), B=budget_0(t,z,1), k=norm d/(m!*2^m)>0,
 E=B*2^(m+1), R=max(1,2M), delta=min(1/4,k/(2*(E+1)))>0.
The joint actual integral remainder and product lower bound prove:
 h!=0, |h|<=delta, norm v<=delta, H_(t+h^2)(z+v)=0
 IMPLY norm v<R*|h|.
Indeed, in the opposite annulus norm v>=|h|>0, the leading norm is at least
k*norm v^m, while the error is <=E*delta*norm v^m<=k/2*norm v^m.
This is a genuine fixed-physical-disk confinement proof even when v/h is unbounded.
The chosen delta simplifies the previously proposed sufficient constant; all its
positivity, domain, factorial and norm-cancellation obligations are Lean verified.

EXHAUSTIVENESS follows without a new argument principle or assumed zero count.
Take the compact scaled disk of radius R outside the union of the finitely many
local Hermite-root neighborhoods. The limiting model is nonzero there, so the
existing IsCompact.exists_forall_le' gives a positive norm gap, including the
empty-compact case. Existing uniform convergence excludes every actual scaled
zero from that complement. Local uniqueness covers every remaining actual zero
by at most m physical points. The previously verified m distinct simple actual
zeros in the open physical delta disk then force equality of the finite sets.

actual_exact_cluster: for EVERY natural m, real t and complex z satisfying the
precise derivative conditions, there exists delta>0 such that for ALL sufficiently
small punctured REAL h there is S with card S=m and, for EVERY complex zeta,
 zeta in S IFF zeta in CLOSED ball(z,delta) AND H_(t+h^2)(zeta)=0.
Every such zero is spatially simple. If z.im=0, every such zero is REAL.
Thus this is an exhaustive count, not the previous selected-set lower count.
Every actual zero supplies a positive finite m by direct earlier theorem reuse.
Complex original zeros require no realness assumption and carry no false realness
conclusion. Both signs of h are included; the time increment is positive h^2.
The m=0 case gives an actual zero-free fixed disk near any nonzero value.

Fresh FULL6104job root build TERMINAL0 (41.0365026s),
COMPLETE37352declaration transitive root/Foundation audit TERMINAL0
(36.4519673s), only propext/Classical.choice/Quot.sound.
All NINE public types actually read UNABRIDGED and all223 final source lines
actually reviewed (eight theorems, one definition; no private helper or instance).
SIX independent Lean controls TERMINAL0 (25.6411309s):
empty product, exact quadratic heat sign, degree7 product lower bound, m=0 actual
zero-free disk, EXACT two actual simple real zeros at a real double-zero base,
and exhaustive positive finite cluster for an arbitrary complex actual zero.
Draft repair closed the identity z+(zeta-z)=zeta with ring; final cleanup removed
an unreachable tactic and used a local let for the finite instance. No resources,
axioms, theorem semantics or verification gates were weakened or suppressed.
All1955 production source hashes pinned; previous1954 unchanged except root import.
All107 manuscript hashes and EXACT recursive paths, Incoming43/42distinct and all
11 A4 files/exact paths preserved. Lean/Mathlib/build configuration unchanged.
Permanent optimized workflow was consulted and retained; only preliminary type
feedback has a measured speedup, not the complete build/audit. No cache deletion.

This closes the local finite-multiplicity collision mechanism. It does NOT give a
uniform delta across all zeros/times, global strip contraction, a new threshold,
RH, or a new novelty claim. NEXT: audit/reuse global polynomial heat zero-strip
control and the approximation/domain bridge to actual Xi. Do not replace this
bridge with a finite Euler/Taylor truncation, or infer global bounds from local
clusters. Independent A2 remains ACTIVE; prior integer/real-order campaigns remain
FROZEN; final multichannel only after A2's audited stopping checkpoint. October31
hard stop; all exact-commit receipt and private-backup requirements remain intact.
Private backup is pending at this precommit entry; closure is recorded locally.


## Checkpoint1258: finite heat-root strip mechanism and an actual upward branch

Foundation/RiemannQuadraticRootMotion.lean connects genuine polynomial heat
motion to the exact interaction mechanism needed for a global A2 strip proof.
For a finite set S of DISTINCT complex roots let P_S=product_(b in S)(X-b).
Mathlib logDeriv_prod gives P_S'/P_S=sum 1/(z-b) off S. Factoring out a root
and differentiating twice gives, for EVERY a in S,
 P_S''(a)/P_S'(a)=2 sum_(b in S erase a) 1/(a-b).
P_S'(a)!=0 is separately proved; the ratio is never certified through 0/0.

For a.im>0, conj(a) in S and EVERY b in S satisfying b.im<=a.im, the imaginary
part of this ratio is <=-1/a.im. The conjugate term is EXACTLY -1/a.im; every
other term is nonpositive. No full real-coefficient assumption is hidden: the
precise conjugate-member and uppermost hypotheses are explicit in the theorem.
The heat sign and factor2 agree with the ACTUAL quadratic flow convention H_t=-H_zz.

heat_factor_velocity differentiates a genuine time-dependent factorization
 P_s=(X-r(s))*Q_s
at FIXED spatial r(t). Under HasDerivAt r v t, the explicit differentiability
of Q_s(r(t)), the ACTUAL partial-time derivative -P_t''(r(t)), and P_t'(r(t))!=0,
it proves v=P_t''/P_t'. No unproved global root labeling is supplied by this lemma.
The root interaction then gives derivative[(Im r)^2]<=-2 along a differentiable
positive uppermost branch. Existing convex mean-value machinery integrates this:
 (Im r(t))^2 <= (Im r(s))^2-2(t-s).
The interval theorem states EVERY derivative, root membership, positivity,
conjugate membership, uppermost and velocity hypothesis for EVERY u in [s,t].
It is a BRANCHWISE strip estimate, not an unconditional global polynomial theorem.

A rigorous counterexample prevents a tempting incorrect extension. At t=0,
 P_0(z)=z^4+5z^2+4=(z^2+1)(z^2+4)
has simple roots +/-i,+/-2i, and P_0''(i)/P_0'(i)=i/3. Thus the INTERIOR root
has POSITIVE imaginary velocity, despite the real coefficients and conjugate pairs.
The example is realized by the GENUINE entire polynomial heat trajectory
 P_t(z)=z^4+(5-12t)z^2+4-10t+12t^2,
whose partial-time derivative equals -P_t'' at EVERY real t and complex z.
Set D(t)=9-80t+96t^2 and
 y(t)=sqrt((5-12t-sqrt(D(t)))/2).
Lean proves y(0)=1 in an independent control and HasDerivAt y (1/3) 0, plus
P_t(i*y(t))=0 under the TWO explicit square-root nonnegative-domain hypotheses.
Continuity proves those hypotheses on an ACTUAL neighborhood of zero, so this
is a genuine local root branch with upward height derivative, not merely a
formal velocity assignment or a finite Euler step. The universal all-root
height-monotonicity proposal is false. The uppermost-root estimate survives.
This concerns a degree4 polynomial under QUADRATIC heat, not the A4 Xi campaign.

Fresh FULL6105job build TERMINAL0 (42.0228765s),
COMPLETE37383declaration transitive root/Foundation audit TERMINAL0
(35.6751645s), only propext/Classical.choice/Quot.sound.
ALL20 public types ACTUALLY read UNABRIDGED; COMPLETE251 final source lines
ACTUALLY reviewed, including three definitions;17 theorems, no private helper or
instance. EIGHT independent Lean controls TERMINAL0 (26.0868219s):
empty root product, all-root simplicity, exact initial factorization, branch base i,
actual imaginary-height derivative1/3, actual neighboring root identity, explicit
failure of the interior downward bound, and a strictly bounded positive-branch
lifetime. The first factorization control needed the explicit polynomial C(1+4)
map-add identity; production proofs were unchanged. Exact rational controls for
162 finite symmetric imaginary-root configurations verify the top-root square-rate
bound and the interior1/3 velocity; no floating Xi zeros or external assumptions.
Draft repairs used logDeriv/Polynomial.deriv, exact complex numeral projections,
Pi function identities, Nat subtraction reduction and casts. A standard-heartbeat
elaboration timeout in the explicit branch proof was repaired by direct reuse of
Polynomial.hasDerivAt instead of a large convert expression. No resource limits,
axioms, checks or theorem semantics were weakened. A ring diagnostic within a
successful alternate branch is not being confused with an error; terminal codes,
complete root build and complete transitive audit all passed.
All1956 source hashes pinned; previous1955 unchanged except root import; pinned
Lean/Mathlib/build settings unchanged. All107 manuscript hashes and EXACT recursive
paths, Incoming43/42distinct and all11 A4 paths/hashes preserved; no manuscripts edited.

REUSE AUDIT / REMAINING GLOBAL OBLIGATIONS: the existing quartic canonical-product
approximation is stated for the ACTUAL quartic flow; it cannot simply be cited as
an A2 approximation. RiemannEvenEntireGrowth.exists_subquadratic_growth already
covers m=1 with exp(norm z*sqrt(norm z)) growth, and its uniform jet/spatial bounds
were reread. They are candidates for transferring the existing canonical estimates.
RiemannQuarticCanonicalPairs contains generic paired-denominator/opposite-product
identities, while RiemannQuarticActualPolynomialLimit and PolynomialFactors need
an exact theorem-level domain/reuse audit. No such transfer is certified here.
Still required: root collisions and changes of the uppermost branch for a GLOBAL
finite-polynomial maximum; actual Xi polynomial/canonical approximation, appropriate
heat-domain uniform control, and a justified limit preserving the strip bound.
The actual Gaussian L1 identity1248 and exhaustive local Xi clusters1257 remain
available; neither replaces these missing global steps. No global contraction,
new threshold, all-paper novelty claim or RH implication. Independent A2 ACTIVE;
prior integer/real campaigns FROZEN; final multichannel only AFTER the A2 audited
stopping gate. October31 hard stop. Exact receipt/private backup pending precommit;
terminal closure is recorded locally. Original permanent build configuration retained.


## Checkpoint1259: actual A2 divisor estimates and normalized canonical logarithms

The theorem-level reuse audit found that the quartic ACTUAL real split-polynomial
limit assumes all zeros real. It cannot be cited to prove A2 strip contraction
from an initial NONREAL zero strip. The Jensen and canonical logarithm proofs,
however, depend on explicit entire-function hypotheses already verified for A2.
They are now extracted into shared proofs, and the existing quartic public results
call those shared proofs. No quartic conclusion is silently applied to another flow.
All19 old public theorem headers across the three refactored modules are EXACTLY
unchanged; their names, domains and mathematical statements survive the refactor.

EntireSubquadraticZeroCounting: for an ACTUAL entire complex f with f(0)!=0 and
norm f(z)<=C exp(norm z*sqrt(norm z)), C>0, the ACTUAL disk DIVISOR multiplicity
count N_f(R)=sum_z divisor(f,closedBall(0,R))(z) is nonnegative and satisfies
 N_f(R)<=K R sqrt(R), R>=1, and N_f(R)/R^2 ->0.
Also 0<=sum_z multiplicity(z)*norm(z)^2/R^4<=N_f(R)/R^2 for R>0, so this
weighted divisor mass tends to zero. The count includes multiplicities and is
not an assumed enumeration of distinct or simple zeros. Bounds/nonnegativity
use the precise needed hypotheses; in particular some do not require f(0)!=0,
whereas finite-zero order, compact zero finiteness and Jensen normalization do.
No theorem for every entire function without a growth bound is asserted.

EntireDiskDecomposition uses actual compact zero finiteness to choose a zero-free
sphere r in (R,R+1), R>=0, and Mathlib exists_ecanonicalDecomp. The existing
EvenDiskLogRemainder constructs a genuine zero-free analytic remainder h and a
normalized logarithm g on the disk: exp(g(z))=h(z)/h(0), g(0)=0, and the exact
HasDerivAt g (h'/h) identity. EvenEntireCanonicalDerivative generalizes the actual
opposite-divisor and finite logarithmic-product cancellation: for ENTIRE EVEN f,
f(0)!=0, its canonical remainder h has h'(0)=0, hence the constructed g'(0)=0.
All multiplicities are kept; no real-root or simple-root assumption is introduced.
The chain rule at complex zero is explicitly typed; local analytic hypotheses
remain distinct from local root-membership witnesses and logarithm normalization.

Foundation/RiemannQuadraticDivisor.lean discharges ALL these hypotheses for the
ACTUAL flow RiemannEvenFlow.flow 1 t at EVERY REAL t, using existing analyticity,
RiemannEvenNormalizedCompact.actual_flow_zero_pos and
RiemannEvenEntireGrowth.exists_subquadratic_growth. Thus A2 now has ACTUAL
multiplicity counts, vanishing normalized/weighted mass, and canonical disk logs
with g(0)=g'(0)=0. Constants K depend on t; no uniform time or global zero strip is
inferred. Earlier actual Gaussian L1 identities and exhaustive local clusters remain.

Fresh FULL6109job root build TERMINAL0 (351.4603888s),
COMPLETE37414declaration transitive root/Foundation audit TERMINAL0
(33.9355979s), only propext/Classical.choice/Quot.sound.
ALL51 public types ACTUALLY READ UNABRIDGED:31 new and20 retained interfaces.
COMPLETE652 final source/proof lines across seven affected modules ACTUALLY READ,
including both new definitions and the retained quartic count definition; no new
private helper or instance. There are29 new theorems and2 new definitions, with
19 old theorem contracts preserved. FOUR new source modules, three refactored
prior modules, root import only otherwise. Full downstream build rechecked the
quartic threshold/canonical polynomial results and real-order branch results.
THIRTEEN independent Lean controls TERMINAL0 (28.5535195s):
constant count0 and normalized limit; explicit nonreal zeros of1+z^2; genuine disk
log with derivative0 for that polynomial; actual A2 count at t=-100; actual finite
zero set at t=0; normalized count limit at t=42; weighted mass nonnegativity;
actual radius0 disk logarithm at every t; failure of origin-nonzero for f=z;
zero-free exp with nonzero derivative0; exact divisor multiplicity3 for(z-i)^3;
and nonconvergence of the even normalized log family g_R(z)=z^2 to zero.
The last control shows that g(0)=g'(0)=0 and evenness alone do NOT prove the next
logarithm limit; a genuine growth estimate is indispensable. Exp(z) separately
shows zero-freeness alone does not give zero derivative. Test-only repairs used
7+1=8 normalization and the correct locally-uniform-on pointwise-limit interface;
production proofs were unchanged. Generic proof repairs addressed explicit section
hypotheses, shadowed analytic/origin witnesses and complex chain-rule typing.
No resources, axioms, errors or mathematical verification gates were weakened.

All1960 source hashes pinned; prior1956 unchanged except the three audited proof
extractions and root import. Lean/Mathlib/build settings unchanged. All107 archived
manuscripts and EXACT recursive paths, Incoming43/42distinct and A4eleven/exactpaths
preserved; no source manuscripts edited. Permanent build policy consulted. Because
shared imports changed, timings were rechecked at this natural proof break:
cached target 8.2245605s and cached full root 10.0008153s,
with fresh audit/type time above. The351.46s dependency-invalidating full build is
not compared as a performance regression against a cached build. No new speedup
or compiler/cache/thread configuration is claimed or adopted.

NEXT / REMAINING: transfer canonical remainder boundary/origin/growth estimates,
then use existing EvenDiskLogLimit for ACTUAL A2 local uniform remainder convergence.
Construction and g'(0)=0 do NOT by themselves prove that limit. Reconstruct the
actual zero product and real polynomial approximants with a justified NONREAL strip
domain, then establish the correct heat-domain convergence. The reviewed quartic
DenominatorLimit.denominator_error_bound proof uses no real-zero fact except the
phantom real-zero argument of denominatorProduct; its weighted-mass ingredient is
now verified for A2. Generic paired_denominator_ne_zero and
normalized_reciprocal_pair already allow complex roots. In contrast,
opposite_finite_product currently uses the real-zero premise to exclude Re(a)=0,
and numeratorPoly uses it for REAL coefficients. These must be generalized with
precise no-imaginary-axis/conjugation hypotheses, or another valid pairing scheme;
no circular all-real premise may be assumed. The quartic imaginary-axis positivity
proof was reread; its cosine/cosh positivity argument is a candidate for A2 reuse,
not yet an A2 zero-free-axis theorem here. Global polynomial collisions/switches
and actual Xi global strip contraction remain OPEN. No new threshold, RH result,
blanket order<2 theorem or novelty claim. A2 ACTIVE; previous integer/real stages
FROZEN; final multichannel only after A2 stopping. October31 hard stop; exact receipt
and PRIVATE backup pending precommit, terminal closure recorded locally.


## Checkpoint1260: ACTUAL A2 locally uniform canonical remainder and product limits

Foundation/EvenEntireCanonicalApproximation.lean extracts the existing quartic
remainder bounds, convergence and reconstruction into shared ENTIRE-function
proofs. All18 old theorem headers in four refactored quartic modules are EXACTLY
preserved. The retained inverseZeroProduct definition BODY is also byte-identical.
The old quartic theorems call the shared proofs; no old mathematical conclusion
is changed or silently reinterpreted as an A2 result.

For actual entire f with f(0)!=0, the finite canonical product has norm1 on its
zero-free boundary sphere and norm>=1 at0. Consequently the genuine canonical
remainder h satisfies norm h(0)>=norm f(0) and its closed-disk norm is bounded by
the proved boundary bound, using the maximum principle. If norm f(z)<=C exp(norm z
sqrt(norm z)), these estimates give for the normalized log on an intermediate
radius r in (2R,2R+1):
 Re g(z)<=A+6R sqrt(R), norm z<2R, R>=1.
The origin lower bound is proved BEFORE division; no uncontrolled quotient or
assumed inverse bound is introduced. Generic helper theorems state only their
needed analytic/nonvanishing hypotheses; evenness is used at the next limit stage.

For ENTIRE EVEN f with f(0)!=0 and that explicit growth bound, choose genuine
canonical h_R,g_R with g_R(0)=g_R'(0)=0 and exp(g_R)=h_R/h_R(0). The existing
EvenDiskLogLimit now applies with ALL hypotheses discharged, proving
 g_R ->0, exp(g_R)->1, h_R/h_R(0)->1
LOCALLY UNIFORMLY ON THE WHOLE COMPLEX PLANE as REAL R->+infinity. The witnesses
retain all radius, boundary-divisor, analyticity, derivative and real-part-bound
data. This closes the previously open convergence obligation, not merely the
construction of a finite-disk logarithm.

B_f(R,z)=product_a canonicalFactor(R,a,z)^(-divisor(f,ball(0,R))(a)) is an ACTUAL
finite reciprocal canonical product. Its reciprocal-factor rational identity and
nonzero denominators prove analyticity on the closed disk INCLUDING original
zero locations. Analytic uniqueness upgrades the canonical codiscrete identity to
 f(z)=B_f(R,z)*h(z)
EVERYWHERE on the closed disk, including the zeros. At valid radii B_f(R,0)!=0.
With the chosen r(R) in (2R,2R+1), normalized B_f(r(R),z)/B_f(r(R),0) converges
locally uniformly to f(z)/f(0); multiplying by f(0) converges locally uniformly
to the ACTUAL f, with its normalization restored. Multiplicities and complex zeros
are retained; no real-root or simple-root assumption is present.

Foundation/RiemannQuadraticCanonical.lean specializes BOTH complete quantified
limit statements to the ACTUAL H_t=RiemannEvenFlow.flow 1 t for EVERY REAL t,
using the verified analytic, positive-origin, even and subquadratic-growth facts.
Thus ACTUAL A2 now has the proved zero-free normalized remainder limit and a
proved finite rational zero-product approximation, uniformly on every compact
complex set. These are rational products analytic on growing disks; they are NOT
yet entire real-polynomial approximants or inputs certified for a global Gaussian
heat integral. No local-uniform-to-heat-limit interchange has been assumed.

Fresh FULL6111job root build TERMINAL0 (229.2174812s),
COMPLETE37436declaration transitive root/Foundation audit TERMINAL0
(35.2526738s), only propext/Classical.choice/Quot.sound.
ALL41 public types ACTUALLY READ UNABRIDGED (22new/19retained interfaces).
COMPLETE679 final source/proof lines across six modules ACTUALLY READ, including
the two new definitions and the unchanged quartic inverse-product definition;
20 new theorems, no new private helper or instance. TWO new source modules and
four audited proof extractions; root import only otherwise. Full build rechecked
all downstream quartic canonical/polynomial/threshold conclusions.
SEVEN independent Lean controls TERMINAL0 (25.6360142s):
reciprocal factor value0 AT its original zero; analyticity there; genuine generic
product approximation to3(1+z^2), explicitly proving its subquadratic growth and
restoring the NONUNIT origin scale3; ACTUAL A2 scaled product limit for all t;
EVERY actual A2 zero is an eventual exact zero of the finite products; actual
normalized remainder limit; and explicit nonreal root i of3(1+z^2). The private
control growth proof was reviewed. Test-only repairs used the explicit argument
of Real.pow_div_factorial_le_exp and the ring-multiplication norm identity;
production mathematics was unchanged. Draft transfer repaired a shadowed analytic
witness. The first generated A2 wrapper duplicated the growth binder and omitted
its namespace end; both syntax errors were corrected before the successful target
and full builds. Explicit quartic namespaces avoid accidental name resolution.
No resource settings, axioms, error checks or theorem semantics were weakened.

All1962 production source hashes pinned; prior1960 unchanged except four audited
proof extractions and the root import. Lean/Mathlib/build settings unchanged.
All107 archived manuscript hashes and EXACT recursive paths, Incoming43/42distinct,
A4eleven/exactpaths preserved. Post-import validation: cached target
7.4310564s, cached full root 9.8462918s, terminal0;
not a matched optimization comparison. Original permanent workflow retained.

SELECTIVE MANUSCRIPT / HEAT-DOMAIN AUDIT: ResearchSources/a4/ibm_laguerre_polya.tex, introduction lines78-97,
SHA256 EAF31754F5F993EF8EB33A1917484D70F6B62F5B37A907AD85F097C3C5589D96, reread without modification. Its LP definition uses
locally uniform polynomial limits, followed by a background backward-heat closure
claim. The prior critical-Gaussian domain obstruction remains relevant; this
checkpoint does not promote that unqualified assertion to an admissible-domain
theorem. In particular, the NEW rational local-uniform limit cannot alone justify
passing a heat operator through an approximation. A focused NEXT TEST is
 q_n(z)=(-1)^n n!/(2n)! z^(2n), heat time1.
Exact rational finite controls for n=1..30 verify the finite polynomial heat value
at0 equals1 and (n!)^2<=(2n)!, suggesting the disk bound R^(2n)/n! and local-uniform
q_n->0. The GENERAL locally-uniform theorem and identification with the GENUINE
imaginary-Gaussian integral are NOT YET Lean verified here. They must be proved
before claiming a topological obstruction. This test does not refute continuity
on a restricted canonical/strip-controlled sequence with uniform Gaussian domination,
or valid admissible-domain Polya theorems. No manuscript file was edited.

NEXT: form genuine REAL polynomial approximants without assuming all zeros real;
audit conjugation and imaginary-axis/pairing conditions, remove the rational
denominators with the verified weighted mass, and prove the heat-domain convergence
actually needed. Investigate the normalized-monomial test before any bare locally
uniform heat-continuity assertion. Global finite-polynomial maximum control across
collisions/switches and ACTUAL Xi global strip contraction remain OPEN. Existing
local clusters1257 and uppermost-branch1258 remain available. No new threshold,
RH implication or novelty claim. A2 ACTIVE; prior integer/real campaigns FROZEN;
final multichannel AFTER A2 stopping; October31 hard stop. Exact-commit receipt and
PRIVATE backup pending precommit; terminal closure recorded locally.


## Checkpoint1261: genuine Gaussian heat discontinuity and exact L1 obstruction

Foundation/GaussianHeatTopology.lean resolves the normalized-monomial test from
1260 for ALL natural indices, using existing genuine Gaussian moments and the
verified polynomial expectation calculus. Set
 q_n(z)=(-1)^n n! z^(2n)/(2n)!, p_n(z)=1+q_(n+1)(z).
The p_n are genuine even REAL-coefficient polynomials with p_n(0)=1. The proved
factorial inequality gives norm(q_n(z))<=R^(2n)/n! on each radius-R disk, hence
q_n->0 and p_n->1 LOCALLY UNIFORMLY on the WHOLE complex plane.

Every imaginary-Gaussian integrand is genuinely L1. Transport of standard N(0,1)
by sqrt(2) is proved equal to the existing time-one law N(0,2). For Y with that
POSITIVE probability law, integral q_n(iY)=1 and integral p_n(iY)=2 for EVERY n,
whereas integral 1=1. Moreover integral norm(p_n(iY)-1)=1 for EVERY n, and no
single integrable real function dominates all norm(p_n(iY)) almost everywhere.
Thus compact-uniform convergence plus individual Gaussian integrability is
INSUFFICIENT for heat convergence; the exact L1 distance identifies the missing
tail control. The common quadratic bound norm(q_n(z))<=exp(norm(z)^2) is proved,
but no uniform subquadratic or admissible Gaussian domination is inferred.

The pure-order p=2 algebraic expectation at parameter -1 of the actual polynomial
p_n equals2 and agrees with its genuine imaginary-Gaussian heat value. This is a
sequence-level connection to existing operator/pseudomoment machinery, not a
negative-variance probability law or a new higher-order stochastic realization.
The variance control independently distinguishes standard-Gaussian q_1 integral
1/2 from the heat-law integral1. No real-rootedness or fixed zero-strip hypothesis
is imposed on this counterexample sequence. It does NOT refute valid admissible-
domain Polya/de Bruijn results or establish failure for a properly controlled
actual Xi approximation. No novelty claim is made.

Source context remains the selective 1260 reading of
ResearchSources/a4/ibm_laguerre_polya.tex, introduction78-97, SHA256
EAF31754F5F993EF8EB33A1917484D70F6B62F5B37A907AD85F097C3C5589D96.
Its unqualified background heat-closure sentence cannot supply the missing
domain/limit theorem. The actual A2 canonical rational limits1260 remain valid;
they alone do not license a Gaussian integral interchange.

Verification: fresh FULL6112-job root build TERMINAL0,40.8507006s; COMPLETE37478
declaration transitive root/Foundation axiom audit TERMINAL0,38.3165691s, only
propext/Classical.choice/Quot.sound. ALL35 public types ACTUALLY READ UNABRIDGED;
COMPLETE262 final source lines reviewed,30 theorems and5 definitions, no private
helper or instance. SEVEN independent Lean controls TERMINAL0,26.6384087s:
explicit quadratic/quartic first polynomials; algebraic/actual integral agreement;
standard-versus-heat variance control; n=23 native-law integrability/integral/L1
distance; nonconvergence of L1 distances; and joint local-uniform/origin/heat
nonconvergence statements. A test-only nonexistent integral_div_const rewrite
was replaced by div_eq_mul_inv and integral_mul_const before the successful run.
Production proofs and mathematical inputs were unchanged after the full build.
All1963 source hashes pinned; prior1962 unchanged except root import. Exact107
recursive manuscript paths/hashes,43 Incoming/42 distinct and11 A4 preserved.
Toolchain/configuration/cache/resource settings unchanged. Permanent measured
build workflow retained; no redundant warm benchmark for this ordinary new leaf.

NEXT: genuine real-polynomial approximants to actual A2, without assuming all
zeros real, and the uniform growth/tail estimates needed for valid heat-domain
convergence. Reuse verified divisor mass and canonical remainder controls;
prove conjugation/pairing and denominator removal hypotheses. Global polynomial
maximum control across collisions/switches and actual Xi strip contraction stay
OPEN. No new threshold or RH claim. Independent A2 ACTIVE; integer/real stages
FROZEN; final multichannel AFTER A2 stopping; October31 hard stop unchanged.
Explicit checkpoint commit and exact PRIVATE receipt/sync close this checkpoint;
terminal closure is recorded in the local verification record.


## Checkpoint1262: actual A2 real-polynomial approximation with exact disk zeros

Foundation/EvenEntirePolynomialApproximation.lean proves the missing polynomial
step for an ACTUAL entire even f, f(0)!=0, conjugation symmetry, and explicit
growth norm(f(z))<=C exp(norm(z)*sqrt(norm(z))). It reuses the verified canonical
remainder/product approximation, actual divisor-mass bound, complex canonical
pair identities and finite power-product estimate. NO all-real or simple-zero
hypothesis is introduced. The finite numerator uses actual divisor multiplicities.

The selector Re(a)>0 OR (Re(a)=0 AND Im(a)>0) selects precisely one of a,-a for
every nonzero complex a. The former real-root pairing could not cover imaginary-
axis roots. The generalized finite-product identity works in ANY commutative
monoid. Pairwise canonical algebra yields P_R(z)=D_R(z) B_R(z)/B_R(0) on the
closed radius-R disk. The denominator is nonzero there, and its error is bounded
by exp(norm(z)^2 times the verified weighted closed-disk divisor mass)-1.
Hence D_R->1 locally uniformly, and the canonical rational limits1260 give
genuine complex-polynomial numerator convergence on the WHOLE complex plane.

Conjugation symmetry propagates through actual derivatives, iterated derivatives,
analytic/meromorphic zero orders, actual disk divisors and finite zero support.
An unpaired linear-factor identity proves the numerator polynomial is fixed by
coefficientwise conjugation. Taking real parts of coefficients then gives an
EXACTLY EQUAL genuine real polynomial after scalar extension; this is NOT merely
symmetrization that might alter zeros. A separate exact zero-set theorem proves
P_R(z)=0 IFF norm(z)<R AND f(z)=0 for EVERY z, retaining imaginary-axis and
nonreal roots and excluding spurious roots anywhere in C. Multiplicities occur
as the actual toNat divisor exponents in both proved paired/unpaired products;
no separate polynomial-multiplicity-equality theorem is asserted here.

The strongest combined theorem supplies r(R) in(2R,2R+1) for R>=1, r->infinity,
and a sequence of genuine EVEN real polynomials whose origin value equals the
ACTUAL f(0), whose zeros are EXACTLY the actual f zeros in the radius-r(n+1)
disk, and which converge LOCALLY UNIFORMLY to ACTUAL f on the WHOLE C.

Foundation/RiemannQuadraticPolynomial.lean discharges every analytic, origin,
evenness, growth and conjugation hypothesis for ACTUAL flow 1 t, for EVERY REAL t.
It proves that any explicitly supplied global zero-strip bound transfers to
EVERY approximating polynomial, together with origin normalization and full
compact-uniform convergence. This is a genuine link between actual Xi zero
geometry and finite real polynomials WITHOUT assuming RH or all zeros real.
The strip theorem is conditional on the stated bound; no stronger strip, heat
contraction, threshold or RH result is inferred. Generic approximation is not
claimed novel, and the earlier quartic split-polynomial results are preserved.

The Gaussian heat discontinuity1261 remains decisive: this checkpoint does NOT
justify passing Gaussian heat through the limit. Individual polynomial L1 and
compact-uniform convergence are insufficient. NEXT: prove a UNIFORM admissible
growth/tail budget for THESE actual divisor polynomials, before any heat-domain
convergence. A possible route is zero-count controlled paired products or
canonical disk estimates plus polynomial exterior bounds. Both require proofs;
no uniform subquadratic approximant bound is assumed from the limit function.
Global polynomial maximum control across collisions/switches and actual Xi strip
contraction remain OPEN. Exhaustive actual clusters1257, branchwise1258 and all
prior frozen campaign work remain intact.

Verification: targeted4616-job build TERMINAL0,38.3155218s; fresh FULL6114-job
root build TERMINAL0,25.0871194s; COMPLETE37538-declaration transitive root/
Foundation axiom audit TERMINAL0,37.7000228s, only propext/Classical.choice/
Quot.sound. ALL41 public types ACTUALLY READ UNABRIDGED; COMPLETE587 final
source/proof lines read across both modules:35 theorems,6 definitions, no new
private helper or instance (existing classical decidability is locally enabled).
EIGHT independent Lean controls TERMINAL0: imaginary-axis selector; finite pairing
of i,-i; actual polynomial root i for1+z^2; actual nonreal quartet root1+i for
4+z^4; EXACT real-coefficient recovery; repeated-root input (1+z^2)^2 with origin
excluded; actual A2 conditional-strip transfer; explicit nonreal source root.
The first control run needed test-only classical decidability and complex real/
imaginary simplification repairs. Production inputs unchanged after full build.

Draft repairs involved explicit section hypotheses, correct finite-product
division orientation, normalized polynomial C-power algebra, and renaming the
analytic witness to avoid membership-binder shadowing; a scratch text substitution
also misspelled halfZeroSupport and was repaired before the successful build.
No theorem weakened, axiom/resource setting changed or error suppressed.
All1965 source hashes pinned; prior1963 unchanged except root import. Exact107
recursive archive paths/hashes,43 Incoming/42 distinct,11 A4 preserved. No
manuscript edited. Permanent build optimization retained, no new setting adopted.
Independent A2 ACTIVE; prior integer/real FROZEN; final multichannel AFTER A2
stopping; October31 hard stop. Explicit commit/exact receipt/PRIVATE sync close
this checkpoint, with terminal status retained in the local verification record.


## Checkpoint1263: actual Xi inverse-square moments and annular Gaussian bounds

Foundation/EvenEntireInverseSquareTails.lean links the actual divisor polynomials
to derivatives of the actual entire function. Finite normalized polynomial jets
give P_R''(0)=-2*S_R, S_R=sum over the selected opposite-root representatives of
actual divisor multiplicity divided by a^2. Mathlib's holomorphic compact-uniform
derivative theorem is applied TWICE to the genuine polynomial approximants1262.
It proves S_r(R) -> -f''(0)/(2*f(0)), together with the SAME radii and SAME scaled
polynomial convergence. The proof does not exchange an infinite sum or Gaussian
integral with a derivative. The analytic and nonzero-origin domains are explicit.

For a!=0 with 2*abs(Im a)<=norm(a), Lean proves
 norm(1/a^2)<=2*Re(1/a^2),
including natural multiplicity weights. Under an EXPLICIT fixed zero-strip bound
abs(Im a)<=b, every root outside radius2b satisfies that inequality. Nested actual
disk supports have identical actual divisor multiplicities on common roots;
the difference of two actual S-values is exactly the annular finite sum. Thus
the ABSOLUTE annular inverse-square mass is at most twice the real part of that
complex difference, for outer radius>=inner radius>=2b. Complex cancellation
alone is not promoted to an absolute estimate: at a=i the geometric inequality
is explicitly false, and the two inverse squares at1+i,1-i explicitly cancel.

Consequently, for every epsilon>0, there is an index cutoff N such that ALL real
indices i,j>=N with r(i)<=r(j) have absolute annular inverse-square mass<epsilon.
The established finite product estimate then proves the actual annular polynomial
factor has norm<=exp(epsilon*norm(z)^2) for EVERY COMPLEX z. The cutoff is chosen
BEFORE z, not separately on each compact disk. The same witness retains expanding
radii, actual compact-uniform polynomial convergence and the inverse-square
moment limit. No real-root or simple-root assumption is used.

Foundation/RiemannQuadraticZeroProductTails.lean specializes the complex moment
limit to ACTUAL quadratic Xi flow H_t for EVERY real t. It also establishes the
UNCONDITIONAL CLASSICAL time-zero strip abs(Im z)<=1 at every actual H_0 zero:
direct reuse of Mathlib riemannZeta_ne_zero_of_one_lt_re, the existing exact Xi
coordinate/normalization bridge and actual conjugation symmetry. Source:
Mathlib/NumberTheory/LSeries/Dirichlet.lean, theorem at line326, pinned Mathlib
d13f23b723b8a846827a245b89c10fc7d3f11612. The exceptional completed-zeta coordinates
are already handled by the verified imaginary-axis bridge. This is the classical
width-one strip, NOT the external7/8 improvement and NOT a new zero-free theorem.
No external OpenAI formalization dependency or assumed RH is introduced.

That actual strip discharges the generic tail premise at timeZERO. Hence the
arbitrarily small Gaussian-growth annular bound is UNCONDITIONAL for actual Xi
time-zero divisor polynomials. This does NOT supply a strip for every later time,
an absolute infinite-series theorem, a whole-polynomial Gaussian majorant or a
heat-limit interchange. In particular, the fixed finite INNER product still must
be bounded uniformly and combined with the tail estimate. Gaussian integrability
and dominated convergence must then be proved for the actual shifted evaluations.
Counterexample1261 forbids skipping those remaining obligations.

Verification: target4643 jobs TERMINAL0,37.6227359s; fresh FULL6130 jobs
TERMINAL0,24.3066986s. COMPLETE37568-declaration transitive root/Foundation audit
TERMINAL0,37.8257757s; only propext/Classical.choice/Quot.sound. Initial
complete audit also passed (34.6574481s); final repeat was justified because the
type printer hid explicit analytic-witness arguments. The final output enables
pp.proofs, contains no ellipses, and ALL21 public types were ACTUALLY READ
UNABRIDGED. COMPLETE389 final source/proof lines read:20 theorems,1 definition,
no new private helper or instance. No source changed after the full build.
EIGHT independent Lean controls TERMINAL0,28.338232s: repeated paired-factor
second derivative -3/2; failure of cone estimate at i; valid estimate at2+i;
explicit inverse-square cancellation at1+i,1-i; empty product; actual classical
strip; actual nonvanishing at2i; and actual annular whole-plane bound with
epsilon=1/100. A test-only nonexistent numeral-imaginary lemma was replaced by
an explicit norm_num identity. Draft repairs used explicit function extensionality
for derivative functions, actual real-part sum mapping, section hypotheses and
correct finite-set difference identities; no axiom or check was weakened.

All1967 source hashes pinned; prior1965 unchanged except root import. Exact107
recursive manuscript paths/hashes,43 Incoming/42 distinct and11 A4 preserved.
No manuscripts edited. Original toolchain/build/cache/resource configuration and
permanent verification optimization retained. NEXT: finite inner-product bounds,
uniform arbitrarily small quadratic growth of the COMPLETE actual approximants,
then genuine Gaussian heat-domain convergence. Global polynomial collision/switch
control and actual Xi strip contraction remain OPEN. No threshold/RH/novelty claim.
Independent A2 ACTIVE; prior integer/real FROZEN; final multichannel AFTER A2
stopping; October31 hard stop. Explicit commit/exact receipt/private sync close
the checkpoint; terminal closure retained in the local verification record.


## Checkpoint1264: actual polynomial Gaussian L1 and heat convergence

Foundation/EvenEntireGaussianBudget.lean completes the missing finite-INNER
product step. For a fixed finite set S and multiplicities, every subproduct
T subset S has norm<=C_epsilon*exp(epsilon*norm(z)^2), with C_epsilon chosen
BEFORE T and z. The proof uses delta=epsilon/(1+sum multiplicities), factor
constants1+norm(c_a)/delta>=1, exponential domination and the nonnegative real
finite-product inequalities. Actual nested numerator factorization uses the
verified equality of divisor multiplicities on common roots.

Combining that with actual annular tails1263 gives the COMPLETE normalized
divisor-polynomial family, for every epsilon>0, one positive C_epsilon that
bounds ALL indices R>=1 and ALL complex z. The proof handles early indices and
later SMALLER radii using a common finite support at radius2i+1. It does NOT
assume the chosen radii are monotone. Exact real-coefficient recovery1262 gives
one sequence of genuine EVEN real polynomials with exact actual disk zeros,
actual origin normalization, compact-uniform limit f, and the full uniform
arbitrarily small quadratic-growth budget. Generic hypotheses remain entire,
even, nonzero origin, explicit subquadratic growth, fixed zero strip and, for
real coefficients, conjugation symmetry. No all-real-root premise is introduced.

Genuine integration: direct reuse of Mathlib
ProbabilityTheory.IsGaussian.exists_integrable_exp_sq (Fernique),
Mathlib/Probability/Distributions/Gaussian/Fernique.lean line163, pinned Mathlib
d13f23b723b8a846827a245b89c10fc7d3f11612. For ANY actual real Gaussian measure mu,
every fixed complex affine shift z+cY admits a COMMON INTEGRABLE majorant for
all approximants. The proof chooses epsilon from Fernique's positive coefficient
and norm(c), and uses norm(z+cY)^2<=2norm(z)^2+2norm(c)^2 norm(Y)^2. Each shifted
approximant AND its continuous compact-uniform limit are proved genuinely L1
BEFORE dominated convergence. Lean then proves both convergence of the actual
complex integrals and integral norm(F_n(z+cY)-f(z+cY))->0. Degenerate Gaussian
laws are included by the existing IsGaussian machinery; no density division or
positive-variance-only assumption is used.

Foundation/RiemannQuadraticPolynomialHeat.lean discharges EVERY premise for the
ACTUAL time-zero quadratic Xi flow, using the proved classical width-one strip.
The SAME real polynomial sequence preserves actual origin and exact initial disk
zeros, has every initial zero in abs(Im z)<=1, converges locally uniformly on
WHOLE C to H_0, and satisfies the uniform budget. For EVERY s>=0 and fixed z,c,
its actual shifted evaluations converge to H_0(z+cY) in L1 of law N(0,2s).
If c^2=delta is REAL, their actual Gaussian averages converge to
 H_(-s*delta)(z).
This uses the EXISTING independently verified actual Gaussian flow identity;
the integral/limit interchange is now rigorously justified for this sequence.
In particular c=i gives H_s, c=1 gives H_(-s), and c=2i gives H_(4s).
This is actual Gaussian integration, not a formal expectation functional or a
negative-variance probability construction.

The topology is PRECISE: local-uniform initial polynomial convergence; shifted
Gaussian L1 for each fixed s,z,c; POINTWISE spatial convergence of the resulting
heat averages. No spatially uniform heat convergence, global polynomial zero
contraction, new Newman threshold or RH result is asserted. Those remain proof
obligations before any Hurwitz/zero-transfer use. The Gaussian discontinuity1261
is preserved: an independent Lean control proves that its normalized monomial
FAMILY CANNOT satisfy the new uniform small-quadratic-growth hypothesis, since
it would contradict its proved lack of an integrable common majorant. A fixed
member DOES satisfy the budget, distinguishing individual polynomial domains
from a uniform sequence domain. No novelty claim is made.

Verification: successful target4646 jobs TERMINAL0,21.6600571s; fresh FULL6132
jobs TERMINAL0,25.1765504s. COMPLETE37582-declaration transitive root/Foundation
axiom audit TERMINAL0,35.0567498s, only propext/Classical.choice/Quot.sound.
ALL13 public types ACTUALLY READ UNABRIDGED, proof arguments visible and no
ellipses. COMPLETE400 final source/proof lines read:13 theorems, no new
definition/private helper/global instance. EIGHT independent Lean controls
TERMINAL0,29.1816547s: exclusion of the full counterexample family; admissibility
of its fixed first member; empty finite subproduct; imaginary shift clock+s;
real shift clock-s; zero-variance actual L1/integrability; arbitrary subproducts
with repeated factors; and doubled-imaginary shift clock4s. All production
inputs unchanged after the full build.

Draft repairs used explicit complex norm identities; correct nonnegative-real
product inequalities; spaces to avoid Lean's InitialSeg/PrincipalSeg notation;
the conjugation and NNReal scopes; and explicit constants/composition for the
L1 limit. The first actual target failed for a missing NNReal scope and was
fixed before the successful target/full/audit. No resource setting, semantics,
axiom allowance, error check or verification gate was weakened.
All1969 source hashes pinned; prior1967 unchanged except root import. Exact107
recursive archive paths/hashes,43 Incoming/42 distinct and11 A4 preserved.
No manuscripts edited; no Lean/Mathlib/build/cache configuration change.

NEXT: spatially local-uniform heat convergence and the exact finite polynomial
heat/operator identification, reusing existing machinery. Then global finite-
polynomial zero-strip contraction across collisions/switches and transfer to
actual Xi, with every hypothesis checked. Neither pointwise heat convergence
nor branchwise1258 alone supplies those theorems. Independent A2 ACTIVE; prior
integer/real FROZEN; final multichannel AFTER A2 stopping; October31 hard stop.
Explicit commit, exact audit receipt and private synchronization close this
checkpoint; terminal closure remains in the local verification record.


## Checkpoint1265: spatially locally uniform actual Xi heat convergence

Foundation/GaussianCompactHeat.lean supplies the previously missing compact-
uniform Gaussian limit theorem, using Mathlib's EXISTING Banach space C(K,C).
For each Gaussian argument y, the actual shifted map z|->F_n(z+c*y) is realized
as a continuous map on K. The proof verifies continuity in y via continuous
uncurrying and proves convergence in the compact-open topology from the given
local-uniform F_n->f. On compact K, the existing supremum norm is used; no new
function-space foundations or assumed uniform-integral interchange are added.

The Fernique majorant1264 is extended to ALL z in a bounded spatial disk: one
nonnegative integrable g(y) bounds EVERY n and EVERY z in that disk. The same
small-quadratic-growth hypothesis, with constants chosen BEFORE n,z, is retained.
Actual C(K,C)-valued shifted functions and their limit are strongly measurable
and genuinely Bochner L1 BEFORE dominated convergence. Dominated convergence
therefore gives convergence of their ACTUAL integrals in the supremum norm.
ContinuousMap.evalCLM and integral_comp_comm identify evaluation of each genuine
Banach-valued integral with the actual scalar Gaussian integral at z. This proves
uniform scalar convergence on K, hence local-uniform convergence on WHOLE C.

The generic theorem applies to any actual real Gaussian measure and continuous
F_n,f with the stated local-uniform limit and uniform small-quadratic budget;
analyticity is not silently required. Compact K may be EMPTY. The helper that
forms shifted continuous maps and its compact-open convergence do not require
K itself compact; the compactness premise is explicitly used for the Banach
supremum-norm integral step. A redundant M>=0 hypothesis was removed: the
majorant is valid for any real M, with its bound asserted when norm(z)<=M.
Degenerate Gaussian measures remain included. No uniformity over varying
Gaussian laws or heat times is inferred from this fixed-measure theorem.

Foundation/RiemannQuadraticUniformHeat.lean specializes this to the SAME
verified actual time-zero Xi polynomial sequence. It retains real even
coefficients, actual origin normalization, the initial width-one zero strip,
initial compact-uniform convergence, uniform Gaussian budget and genuine L1
of every shifted polynomial. For EVERY fixed s>=0,c and REAL delta with
c^2=delta, the actual Gaussian heat averages now converge LOCALLY UNIFORMLY
ON WHOLE C to actual H_(-s*delta). In particular the actual forward imaginary-
Gaussian averages converge uniformly on every compact complex set to H_s.
The chosen polynomial sequence is independent of s,c,delta and of the spatial
compact set. Cutoffs may depend on those fixed parameters, as the theorem states.
The previous merely-pointwise limitation1264 is now resolved for spatial limits.

This supplies the correct topology for a FUTURE Hurwitz/zero-transfer argument;
it does NOT establish its remaining finite-polynomial zero hypotheses. The
exact algebraic polynomial heat/operator identification and GLOBAL finite-
polynomial strip contraction across collisions/switches remain OPEN. The
existing uppermost differentiable branch result1258 is not promoted to a global
maximum theorem. No new Newman threshold, RH result or novelty claim is made.

Verification: target4648 jobs TERMINAL0,39.0039483s; fresh FULL6134 jobs
TERMINAL0,24.8037893s; COMPLETE37591-declaration transitive root/Foundation
axiom audit TERMINAL0,37.0383852s, only propext/Classical.choice/Quot.sound.
ALL8 public types ACTUALLY READ UNABRIDGED with proof arguments visible and no
ellipses. COMPLETE197 final source/proof lines read:7 theorems,1 definition,
no explicitly declared private helper or new global instance. EIGHT independent
Lean controls TERMINAL0,27.2007406s: exact compact-shift evaluation; forward
uniformity on every closed disk (all real radii, including empty disks); backward
real-shift local uniformity; doubled-imaginary clock4s; zero-variance local
uniformity; empty compact set; two-point compact set{0,i}; and zero spatial
shift at arbitrary Gaussian time. Production inputs unchanged after full build.
The scratch proofs passed; unused compactness/sign hypotheses on helpers were
removed before adoption. No axiom, setting, semantic or verification weakening.

All1971 source hashes pinned; prior1969 unchanged except root import. Exact107
recursive archive paths/hashes,43 Incoming/42 distinct and11 A4 preserved. No
manuscript edited; original toolchain/build/cache/resource settings retained.

THEOREM REUSE AUDIT for next operator step: PureOrderPolynomialTransport.lean
was selectively reread in full. Its transport2a, transport_eval, transport_add,
transport_derivative and transport_iterate_derivative are the existing finite
polynomial calculus. PseudoMomentGaussianBoundary.expectation_nonnegative_gaussian
and gaussianExpectation_eq_expectation identify actual N(0,2a) real moments
for a>=0. The next complex-shift identity must match transport2(s*delta) to the
actual Gaussian polynomial average when c^2=delta; forward Xi time c=i therefore
uses transport2(-s). This sign is a proposed next theorem, NOT proved here.
GaussianPolynomialHeat instead uses d_t+(1/2)d_x^2 and requires its clock to be
rescaled by2 for the present law. Do not duplicate these verified operators or
infer the complex-shift identity from a real expectation statement alone.

Independent A2 ACTIVE; prior integer/real FROZEN; final multichannel AFTER A2
stopping; October31 hard stop. Explicit commit/exact receipt/private sync close
this checkpoint; terminal closure retained in the local verification record.


## Checkpoint1266: exact complex Gaussian / finite-polynomial operator bridge

Foundation/ComplexGaussianPolynomialTransport.lean identifies GENUINE Gaussian
integrals with the EXISTING PureOrderPolynomialTransport.transport. For EVERY
s:NNReal, complex z,c, REAL delta with c^2=delta, and real polynomial P:
  integral P_C(z+cY) law_s = (transport 2 (s*delta) P)_C(z),
where law_s is the actual Gaussian N(0,2s), including its Dirac s=0 boundary.
Thus imaginary c=i gives transport2(-s), real c=1 gives transport2(s), and c=2i
has parameter -4s. The sign/variance are proved, not inferred from notation.

The proof reuses the existing real Gaussian expectation theorem through an
ACTUAL scaled-standard Gaussian law. All complex monomials and complex
polynomials are proved genuinely L1. A polynomial Stein identity is established
for actual complex integrals using the verified moment recurrence, and then
for arbitrary complex affine shifts. Every use of integral_add has actual L1
premises proved beforehand, including Y*P(z+cY), which is a polynomial in Y;
no invalid claim that products of arbitrary L1 functions are L1 is used.

The integral is realized as an actual real-linear functional on real polynomials.
An independent purely algebraic uniqueness theorem says equal-normalized real-
linear functionals with the SAME drift-Stein recurrence E(XP)=zE(P)+bE(P')
are equal, for arbitrary COMPLEX drift z,b. The existing transport is shown
to satisfy this recurrence by transport_eval, the old polynomial Stein identity
and derivative commutation. Strong induction on powers then monomial linearity
proves uniqueness. No positivity, extra measure or nonpolynomial completion is
assumed in that uniqueness statement. The conclusion identifies actual Gaussian
averages at complex z with the old transport on its precise finite domain.

Foundation/RiemannQuadraticOperatorApproximation.lean combines this exact
identity with1265. ONE actual real EVEN polynomial sequence has initial zero
strip1, actual H0(0), compact-uniform convergence to H0 and the uniform small-
quadratic growth budget. For EVERY FIXED s>=0, evaluations of the existing
transport2(-s) applied to that SAME sequence converge LOCALLY UNIFORMLY ON WHOLE
C to ACTUAL H_s. The sequence is chosen before s and the compact set. This is
an actual operator approximation to the Xi flow, not merely a formal moment
or expectation-level identity. No joint-time-uniformity is inferred.

The existing FactorialAnalyticHeat.evolution_polynomial supplies the bounded
operator interpretation for EACH FINITE polynomial. Its direct use is checked
in an independent example. It does not put actual Xi in its bounded factorial-
analytic domain: the derivative-growth obstruction1249 is preserved. The new
bridge uses compact-uniform limits of actual evolved finite polynomials instead.

EIGHT independent Lean controls pass: imaginary quadratic+1 gives z^2+1-2s;
imaginary quartic gives z^4-12s*z^2+12s^2; real quadratic gives z^2+2s;
doubled imaginary quadratic gives z^2-8s; arbitrary complex shift at zero
variance evaluates the original polynomial; operator approximations converge
uniformly on every closed disk (all real radii); genuinely nonreal quintic
shift is L1; and bounded factorial evolution on finite polynomials equals the
same old transport. Quadratic/cubic/quartic transport coefficients are separately
derived from the commutator for those tests. Scratch test failures from polynomial
coefficient casts and equality normalization were fixed; no production assumption,
semantic, toolchain, option or check was changed to make the tests pass.

Verification: target4683 jobs TERMINAL0,36.7766101s;
fresh FULL6136 jobs TERMINAL0,24.1884884s;
COMPLETE37619-declaration transitive root/Foundation axiom audit TERMINAL0,
34.8876305s, only propext/Classical.choice/Quot.sound.
ALL22 public types ACTUALLY READ UNABRIDGED, pp.proofs true, no ellipses.
COMPLETE286 final source/proof lines read:21 theorems and1 definition;
no explicitly declared private helper or new global instance. EIGHT independent
controls TERMINAL0,27.265415s. Source inputs stayed
hash-identical after the successful full build. Permanent optimization remains
a2846f7/502fb4d: original build/thread/cache/full-audit settings, selected-import
preliminary helper only. No fresh build speedup is claimed from these samples.

All1973 Foundation/root source hashes pinned; prior1971 unchanged except root
import. Exact107 recursive manuscript paths/hashes,43 Incoming/42 distinct and
11 A4 preserved. No manuscript changed or committed. Unrelated12 draft MDs and
tmp/ untouched. Explicit commit, exact receipt and PRIVATE remote verification
are required before this checkpoint closes; closure is in the local record.

NEXT OPEN: GLOBAL finite-polynomial zero-strip contraction under transport2(-s),
including collisions and changes of the uppermost root.1258 proves only a
simple differentiable uppermost branch estimate; its interior-upward-motion
counterexample remains. The new operator approximation closes the previously
missing analytic/algebraic identification but does not prove that global zero
theorem. Hurwitz transfer still needs those finite zero hypotheses. No new
Newman threshold/RH/novelty claim. A2 remains ACTIVE; integer/conditional-real
FROZEN; final multichannel ONLY AFTER A2 audited stopping. October31 hard stop.


## Checkpoint1267: global finite-shift strip contraction, with multiplicities

Foundation/SymmetricPolynomialStrip.lean independently verifies the finite-
polynomial symmetric imaginary shift argument. The operator is ACTUALLY
  S_h(P)(z)=(P(z+i*h)+P(z-i*h))/2.
For ANY nonzero conjugation-fixed complex polynomial (hence any nonzero real
polynomial mapped to C), h>0, and ANY real b such that ALL initial zeros satisfy
(Im a)^2<=b^2, EVERY zero of S_h(P) satisfies
  (Im z)^2<=max(b^2-h^2,0).
Constants are handled separately; no positive-degree premise is hidden in the
final strip theorem. The output remains nonzero and conjugation-fixed. Generic
b need not be nonnegative, since its square is the stated budget. The zero
polynomial is explicitly excluded, as the verified negative control requires.

The key exact identity for each conjugate root pair is the difference of the
products of squared norms at z+i*h and z-i*h:
  8*h*Im(z)*((Re(z)-Re(a))^2+Im(z)^2+h^2-Im(a)^2).
Above the target strip it is strictly positive. The proof multiplies comparisons
over the COMPLETE ROOT MULTISET, including repeated roots. Conjugation permutes
that multiset with ALL multiplicities, by the existing splitting/root-map
machinery. Pair products over the full multiset become squares of the original
norm products; nonnegativity justifies recovering the strict comparison. The
fundamental theorem of algebra supplies the exact polynomial/root product and
nonzero leading coefficient. The upper half-plane comparison forbids cancellation;
conjugation gives the lower half-plane. No root enumeration by time, simple-root
premise, discriminant premise, velocity or unproved collision continuation occurs.

The finite iteration theorem is GLOBAL: for EVERY natural n, S_h iterated n
times remains nonzero and conjugation-fixed, and every zero satisfies
  (Im z)^2<=max(b^2-n*h^2,0).
The proof carefully clips the budget at zero at each step; max(max(B,0)-q,0)=
max(B-q,0) for q>=0. This verifies all-real preservation after the budget is
spent. Repeated roots, switches of uppermost roots and arbitrary degrees are
included directly in this static finite-shift result.

For fixed REAL s>0, define scaledShift(s,n,P) using n+1 repetitions of
h=sqrt(2*s/(n+1)). The clock (n+1)*h^2=2*s is proved, with no zero denominator.
EVERY n therefore has the SAME bound max(b^2-2*s,0), remains nonzero and has
real coefficients in the exact conjugation-fixed sense. An explicit wrapper
instantiates actual real polynomials via coefficientwise complexification.
All roots are real when b^2<=2*s. These statements are about FINITE SHIFTS.
The s=0 identity is checked separately; positive-s scaling theorems do not
silently include that boundary through a false strict-positive shift premise.

The missing next theorem is STILL the scaling limit
  scaledShift(s,n,P) -> (transport2(-s)P)_C
locally uniformly on C for each fixed finite real polynomial P.1266 identifies
the RIGHT-HAND SIDE with actual Gaussian heat, but does not identify it with
each FINITE symmetric shift. An explicit checked quartic distinguishes them:
for P(z)=(z^2+1)^2, S_1(P)=z^2(z^2-4), hence S_1(P)(0)=0, whereas the genuine
imaginary Gaussian heat at s=1/2 has value2 at0. Thus finite-shift control cannot
be transferred to heat by an exact finite equality. No such equality or limit
is assumed here. Once the limit is proved, checked Hurwitz hypotheses still
must transfer zero exclusion, first to each evolved polynomial, then through1266
to actual Xi. Actual global heat strip contraction and a new threshold remain
OPEN; this checkpoint does not settle A2 or RH.

PRIMARY SOURCE/REUSE AUDIT: N.G. de Bruijn, The roots of trigonometric integrals,
Duke Math.J.17(1950),197-226, DOI10.1215/S0012-7094-50-01720-0.
Publisher PDF: https://pure.tue.nl/ws/files/1769368/597490.pdf . Selectively
rendered and VISUALLY READ pp.199-202; Lemma1 and Theorems3-5, pp.200-202,
contain the classical finite-shift comparison and strip contraction. The paper
uses stronger disk/ellipse localization and general phase combinations. The
present formalization proves the stated unweighted strip consequence, not those
stronger geometric/phase results. No novelty claim is made. PDF is scanned:
plain extraction gave no page text, so actual rendered pages were inspected.
The local ignored research-cache copy has SHA256
C538EFAF0CA02AED0AFCCA4060B0AB3D9324AC89BAE594B5E89E74DA105260E0.
Earlier TU Delft fetches timed out; the TU Eindhoven publisher copy succeeded.
No ResearchSources manuscript was created/changed by this external-source review.

NINE independent Lean controls pass: constants are fixed; zero-size shift is
identity; norm comparison reverses at a concrete point outside its hypotheses;
zero-polynomial counterexample to dropping P!=0; repeated-root quartic exact
shift z^2(z^2-4); ALL scaled iterates of that repeated-root quartic have only real
zeros at s=1/2; arbitrary all-real polynomial remains all-real under finite
iterates; finite quartic shift value0; genuine Gaussian quartic heat value2.
The last pair independently blocks a premature finite-shift/heat identification.
Scratch control coercion/tactic/syntax failures were repaired without changing
any production theorem or premise. All tests use actual algebraic/Gaussian objects.

Verification: target2949 jobs TERMINAL0,18.1515529s;
fresh FULL6137 jobs TERMINAL0,24.8390029s;
COMPLETE37648-declaration transitive root/Foundation axiom audit TERMINAL0,
35.3914777s, only propext/Classical.choice/Quot.sound.
ALL24 public types ACTUALLY READ UNABRIDGED, pp.proofs true, no ellipses;
COMPLETE254 final source/proof lines read:20 theorems,4 definitions, no explicitly
private helper or global instance. Nine controls TERMINAL0,
28.2807654s. Source inputs unchanged after full build.
Minimal mathematical imports use existing Mathlib polynomial/FTA/multiset results;
no new foundational system, axiom, toolchain, setting or verification weakening.
Permanent build configuration remains unchanged; no new speedup is claimed.
All1974 sources pinned; prior1973 unchanged except root import. Exact107 archive
paths/hashes,43Incoming42distinct and11A4 preserved; no manuscript committed,
unrelated12 draft MDs/tmp untouched. Exact Git receipt/private synchronization
required for closure and recorded locally afterward.

NEXT REUSE CANDIDATE (NOT PROVED): finite derivative-polynomial binomial expansion
of scaled shifts, truncating on fixed P by derivative nilpotence. Existing
ProbabilityTheory.tendsto_choose_mul_pow_atTop (Mathlib Probability/Distributions/
Poisson/PoissonLimitThm.lean55) already proves choose(n,j)*p_n^j -> r^j/j! if
n*p_n->r. This may identify the fixed finite sum limit with the existing bounded
FactorialAnalyticHeat.evolution_polynomial, used ONLY on finite polynomials;
actual Xi remains excluded from that bounded factorial domain1249. Avoid new
Banach/CLT infrastructure if finite nilpotence and this binomial theorem suffice.
A2 ACTIVE; integer/real FROZEN; final multichannel ONLY AFTER A2 stopping;
October31 hard stop. No campaign transition or RH implication.


## Checkpoint1268: polynomial-specific Euler limit in the existing jet norm

Foundation/NilpotentVectorEuler.lean proves a finite-vector Euler theorem using
existing Mathlib binomial asymptotics and Banach exponential. Let E be a complete
real normed space, A_n bounded operators with A_n->B in OPERATOR NORM, v a FIXED
vector, and D a FIXED natural such that (A_n)^D(v)=0 for EVERY n. Then
  (Id+A_n/(n+1))^(n+1)(v) -> exp(B)(v)
in the norm of E. Global operator nilpotence is NOT assumed. Neither mutual
commutation of A_n for different n, positivity, a new probability law, nor a
new function-space completion is required. D=0 is admitted and forces v=0.

The proof expands each finite power by the existing commuting binomial theorem
(only Id and A_n must commute), proves every power j>=D kills v, and truncates
the sum to the FIXED range D once n is large enough. The old
ProbabilityTheory.tendsto_choose_mul_pow_atTop gives
choose(n+1,j)/(n+1)^j -> 1/j!. Continuity of fixed powers and operator evaluation
therefore permits a FINITE sum limit. The limit B also kills v at power D,
proved by continuity and uniqueness of limits, not added as an assumption.
The genuine existing exponential series, mapped by continuous evaluation at v,
then reduces to that same finite sum. The preliminary finite-sum theorem needs
no completeness; completeness is used only for the exponential statements.

Foundation/PolynomialDerivativeEuler.lean instantiates this on EXISTING
FactorialAnalyticDomain.H and its already verified bounded derivative shift D.
For fixed natural N, real s, and natural n, its explicit bounded correction is
  A_(N,s,n)=sum_(j=0..N)
    [(-1)^(j+1)*(2s)^(j+1)/(2j+2)!]*(n+1)^(-j)*D^(2j+2).
No new derivative, transport, norm or foundational space is constructed.
The low-order term is EXACTLY -s*D^2; every other fixed term tends to zero,
so A_(N,s,n)->-s*D^2 in operator norm. The zero-scalar identity in this concrete
operator representation is proved coordinatewise when generic instance
rewriting does not match; no axiom, semantic or typeclass setting is changed.
Scratch elaboration failures were resolved before adoption.

A coordinate support theorem proves that if u(k)=0 for k>=M, then
(A_(N,s,n)^r u)(k)=0 whenever M<=k+2r. Thus for EVERY FINITE real polynomial P,
the common power natDegree(P)+1 kills polynomial(P) for ALL n. The generic
Euler theorem now proves, for EVERY fixed N, real s and finite P,
  (Id+A_(N,s,n)/(n+1))^(n+1) polynomial(P)
    -> polynomial(transport 2 (-s) P)
in ACTUAL FACTORIAL-JET NORM. The final identity directly reuses
FactorialAnalyticHeat.evolution_polynomial. Negative s and s=0 are included in
this algebraic norm-limit statement. No zero-strip assertion for negative time
is inferred. N=0 is allowed: it gives the ordinary finite-vector Euler scheme.
For N>=1 the first fourth-derivative coefficient in A is s^2/(6(n+1)); its
contribution in the one-step Euler operator is s^2/(6(n+1)^2), the expected
finite cosine coefficient at h^2=2s/(n+1). That coefficient agreement alone
is NOT treated as proof of the full shift identity.

EXACT REMAINING CENTRAL OBLIGATIONS: identify the correctly truncated finite
operator step with the ACTUAL symmetric polynomial shift S_h of1267, for each
finite P and an adequate fixed cutoff; prove the identity survives iteration
using a common degree bound; upgrade the resulting finite-polynomial jet-norm
limit to LOCALLY UNIFORM convergence on WHOLE C. The present norm theorem
alone is not stated as the scaledShift limit. In particular it does not yet
transfer1267's finite-shift zero control to actual heat. Checked Hurwitz
hypotheses must then give finite heat-strip control and the1266 actual Xi
transfer. These are still OPEN. Actual Xi remains EXCLUDED from the bounded
factorial domain by1249; only finite polynomial vectors are used here.

TEN independent Lean controls (nine examples and one explicit private coefficient
regression) pass: choose coefficient j=2 tends to1/2; the D=0 exponential case;
EVERY global power of shift is NONZERO, witnessed using X^D; nevertheless the
constant-polynomial vector meets the common annihilation premise with D=1;
N=0 correction is exactly -s*D^2 for arbitrary s,n; s=0 correction vanishes
for arbitrary N,n; the N=1,s=1/2,n=0 correction on z^4+2z^2+1 has origin value
-1; its full one-step Euler value is0; all individual jet coordinates converge
to those of the existing transported polynomial; and negative-time s=-1,N=4
on X^7 has the verified opposite transport clock. These explicitly test vector-
specific nilpotence, clock signs, zero boundaries and the first higher channel.
Initial regression coercion/coefficient simplification failures were corrected
without changing any production assumption or theorem. All use actual operators.

Verification: targeted3921 jobs TERMINAL0,22.7633922s;
fresh FULL6145 jobs TERMINAL0,25.9254745s;
COMPLETE37680-declaration transitive root/Foundation axiom audit TERMINAL0,
35.0485721s, only propext/Classical.choice/Quot.sound.
ALL13 public types ACTUALLY READ UNABRIDGED, pp.proofs true, no ellipses;
COMPLETE189 final source/proof lines read:12 theorems,1 definition; no explicit
private production helper or new global instance. Ten controls TERMINAL0,
25.0386543s. Sources unchanged after the full build.
All1976 Foundation/root hashes pinned; prior1974 unchanged except root import.
Exact107 recursive archive paths/hashes,43 Incoming/42distinct and11 A4 preserved;
no ResearchSources change/commit, unrelated12 MD drafts/tmp untouched. Original
compiler/thread/cache/full-audit settings retained; no new speedup claimed.
Exact commit receipt/private synchronization close the checkpoint afterward.

NEXT PROOF PLAN, NOT PROVED: existing Polynomial.taylor_eval, taylor_coeff and
finite eval_eq_sum_range give the complex Taylor expansion with Hasse derivatives.
Split a sufficiently long range into even/odd indices (a short finite induction
can avoid new infrastructure); odd imaginary shifts cancel and even terms give
real coefficients (-1)^j*h^(2j). The already available factorial_smul_hasseDeriv
and polynomial_iterate_derivative should identify their factorial jets with the
explicit Euler step above. Preserve a common finite degree bound under iteration.
For compact-uniform convergence, reuse existing C(C,C) compact-open machinery:
finite coefficient vectors evaluate jointly continuously as a finite polynomial
sum. ContinuousMap.continuous_of_continuous_uncurry and
ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn are already used
in GaussianCompactHeat; coordinate projections lp.evalCLM give all coefficient
limits from the proved H norm limit. This route need not construct a new global
complex analytic realization of H or a central limit theorem.
A2 ACTIVE; integer/real FROZEN; final multichannel ONLY AFTER A2 stopping;
October31 hard stop. No new Newman threshold/RH/novelty claim or campaign pivot.


## Checkpoint1269: ACTUAL scaled symmetric shifts converge locally uniformly to heat

The missing finite-shift/heat scaling limit is now proved. For EVERY finite real
polynomial P and EVERY real s>=0, set h_n=sqrt(2s/(n+1)) and take n+1 ACTUAL
symmetric shifts S_(h_n)(P_C)(z)=(P_C(z+i*h_n)+P_C(z-i*h_n))/2. Their evaluations
converge LOCALLY UNIFORMLY ON WHOLE C to (transport 2 (-s) P)_C(z). By1266 that
limit is the genuine imaginary Gaussian polynomial heat average at variance2s.
This is a limit theorem for actual finite polynomial functions, not an assumed
operator identity or a formal generating-series computation. The theorem includes
s=0, constants and the zero polynomial; no real-rootedness premise is used.

Foundation/SymmetricPolynomialTaylor.lean first proves the complex finite Taylor
formula using EXISTING taylor_eval, taylor_coeff and finite eval_eq_sum_range'.
A short finite induction splits a sufficiently long Taylor sum into even/odd
indices. Odd powers of the two opposite imaginary displacements cancel; even
powers give EXACT real coefficients (-1)^j*h^(2j). The real polynomial
  evenTaylor(h,N,P)=sum_(j=0..N) (-1)^j*h^(2j)*HasseDerivative_(2j)(P)
therefore complexifies to ACTUAL S_h(P_C) when natDegree(P)<2(N+1). The degree
of this real polynomial is <=natDegree(P), with no hidden nonzero assumption.
Thus the SAME sufficiently large cutoff is justified through EVERY finite
iteration, rather than being silently changed with the current polynomial.

The old factorial_smul_hasseDeriv and polynomial_iterate_derivative identify
its actual factorial jets with the finite derivative sum, including every
factorial. A real coefficient identity under h^2=2s/(n+1) matches this EXACTLY
to Id+correction(N,s,n)/(n+1) from1268 when evenTaylor's cutoff is N+1. Iteration
then gives the actual power of that existing bounded operator. No new derivative,
function-space completion, central limit theorem, assumed infinite-series
interchange or global nilpotence is introduced.

The selected actual real sequence scaledEvenTaylor(s,n,P) uses the fixed cutoff
natDegree(P)+1 and n+1 iterations. Its degree is bounded by natDegree(P) for
ALL n. Its complexification is EXACTLY scaledShift(s,n,P_C), for all real s.
For s>=0, Real.sq_sqrt justifies the clock, so1268 gives factorial-jet NORM
convergence to polynomial(transport2(-s)P). All necessary cutoff, iteration and
clock identities are proved before invoking that norm limit. The map identity
alone holds for negative s because both sides use the same real sqrt definition;
the heat-limit theorem correctly requires s>=0 and does not extrapolate it.

Foundation/SymmetricPolynomialHeatLimit.lean proves the compact-uniform step
using EXISTING C(C,C) with its compact-open topology. A finite real coefficient
vector a:Fin L->R evaluates to the actual continuous polynomial sum a_j*z^j.
Its dependence on a is continuous by joint continuity in (a,z) and existing
continuous-uncurry machinery. Finite coordinate convergence therefore gives
local-uniform convergence on WHOLE C through the established compact-open
characterization, with no unproved bounded-domain-to-global inference.

For actual real polynomials under a COMMON FINITE degree bound, this finite
vector is exactly their coefficient vector and its evaluation is exactly their
complexified polynomial. Each coefficient limit follows from the genuine
factorial-jet norm limit via lp.evalCLM and division by the NONZERO factorial.
The limiting polynomial's degree bound is inherited from the same coordinate
limits, not separately assumed for the application. These results combine with
the exact scaled Taylor realization to prove scaledShift_locally_uniform.
This closes BOTH remaining identifications from1268: actual shifts and complex
local-uniform topology. It does not claim a uniform error over varying polynomial
degrees or over time. Each finite P is fixed BEFORE its inner shift limit.

TEN independent Lean examples pass: exact quadratic shift z^2-h^2; a concrete
insufficient-cutoff quartic counterexample (truncated origin0 versus actual
shift origin1); zero-time local-uniform identity for arbitrary P; zero polynomial
limit; uniform convergence on every closed complex disk (all real radii);
empty finite coefficient vector; simultaneous exact real realization and degree
bound; the repeated-root quartic scaled-shift origin value tends to2 at s=1/2;
an explicit real Taylor degree control; and NEGATIVE-TIME counterexample.
For EVERY n, scaledShift(-1,n,X^2) has origin0, while transport2(+1)X^2 has
origin2. Thus dropping s>=0 would give a false heat-identification claim. The
positive-time quartic limit also preserves the earlier finite-first-step0 versus
Gaussian2 distinction; a limit, rather than finite equality, is now established.
Initial scratch rewriting, coercion and redundant-tactic errors were corrected
before adoption; no theorem hypothesis or semantics was weakened to pass tests.

Verification: target3927 jobs TERMINAL0,36.4297051s;
fresh FULL6147 jobs TERMINAL0,24.7868938s;
COMPLETE37717-declaration transitive root/Foundation axiom audit TERMINAL0,
35.4092755s, only propext/Classical.choice/Quot.sound.
ALL30 public types ACTUALLY READ UNABRIDGED with pp.proofs true, no ellipses;
COMPLETE312 final source/proof lines read:26 theorems,4 definitions, no explicit
private production helper or global instance. Ten independent examples
TERMINAL0,26.0459419s. Sources unchanged after the
successful full build. All1978 Foundation/root hashes pinned; prior1976
unchanged except root import, original toolchain/configuration unchanged.
Exact107 recursive archive paths/hashes,43Incoming42distinct and11A4 preserved;
no manuscript edits/commits, unrelated12 MD drafts/tmp untouched. Permanent
build configuration retained; no new performance speedup is claimed. Explicit
Git commit/exact receipt/private backup close the checkpoint afterward.

NEXT CENTRAL OPEN: transfer1267's GLOBAL strip bound of the actual scaled
polynomials through the just-proved limit, giving GLOBAL finite heat zero control,
then through1266's OUTER actual Xi polynomial approximation. These are two
separate limits: FIRST fix each finite initial polynomial and prove its heat
zero bound, THEN use the actual Xi approximating family. No uniform-in-degree
or diagonal interchange is assumed. No global actual Xi zero bound or new
Newman threshold is claimed at this checkpoint; no RH implication or novelty.

THEOREM REUSE AUDIT: RealRootedVerticalLimit.lean was read IN FULL. It already
proves real-rooted polynomial vertical-modulus monotonicity, preservation under
local-uniform limits and exclusion of nonreal zeros by analytic isolated-zero/
identity arguments. A promising directly supporting generalization is one-sided
vertical monotonicity ABOVE A FIXED ROOT STRIP: each linear factor grows with
y for y>=b when its root has Im<=b. Multiplying over the full root multiset
and passing to the limit yields the same monotonicity. A zero above b would
then force a vertical sequence of zeros approaching x+i*b, contradicting entire
nontriviality by the EXISTING analytic identity theorem. Negation handles the
lower half-plane. This remains a PROPOSED proof, not a verified global strip
closure theorem; it may avoid adding a new general Hurwitz foundation. Reuse
existing FTA/root-product and isolated-zero machinery, preserving multiplicities
and an explicit nonzero entire limit. The current local-uniform topology is
proved regardless of which valid zero-transfer proof is selected.
A2 ACTIVE; integer/real FROZEN; final multichannel ONLY AFTER A2 stopping;
October31 hard stop and all verification/private gates retained. No pivot.


## Checkpoint1270: GLOBAL finite heat strips and the ACTUAL classical Xi upper bound

The long-standing global zero-transfer obligation is now CLOSED for the stated
finite-polynomial and actual zero-time-to-forward-Xi domains. The new actual
RiemannQuadraticGlobalStrip.flow_zero_strip proves, with ONLY t>=0 and H_t(z)=0:
  (Im z)^2 <= max(1-2*t,0).
Here H_t is the ACTUAL RiemannEvenFlow.flow 1 t, not a surrogate polynomial,
assumed process, formal expectation or conditional zero-free object. The existing
exact zero-time Xi normalization and Gaussian/operator bridge are retained.
RiemannQuadraticGlobalStrip.real_zeros_after_half proves ALL zeros real at EVERY
real t>=1/2; classical_half_all_real specializes to t=1/2. These are the classical
coarse de Bruijn upper bound in the verified normalization. They are NOT an RH
proof, a new numerical record, an exact Newman threshold or an A4-to-A2 inference.
The printed theorem types contain no assumed RH, initial zero-strip or external
zero-free theorem. All such premises needed internally are mechanically discharged.

Foundation/PolynomialStripLimit.lean generalizes the existing verified vertical-
modulus method to arbitrary complex root strips. For each linear factor,
|x+i*a-r|<=|x+i*b-r| when Im(r)<=a<=b. Multiplication over the COMPLETE complex
root multiset, including multiplicities, and the exact leading-coefficient/FTA
factorization give the corresponding polynomial bound above any fixed root
strip. Its passage to the limit requires only ACTUAL pointwise convergence at
the two fixed evaluation points. No arbitrary integral/derivative interchange
or holomorphy of a merely pointwise limit is asserted.

The limit is EXPLICITLY assumed entire and nontrivial. If it had a zero above
height beta, the vertical bound forces zeros at
  Re(z)+i*(beta+(Im(z)-beta)/(n+1)),
which approach Re(z)+i*beta and are distinct from it. The EXISTING analytic
identity theorem then makes the entire function zero everywhere, contradicting
the nonzero witness. This proves upper-strip closure. Negating the polynomial
variable and the limit function proves lower-strip closure. Thus a nonzero
ENTIRE pointwise limit of polynomials whose zeros all satisfy |Im|<=b has the
same zero strip. Complex coefficients are permitted. This is a SPECIAL
polynomial-strip class argument, not a new general pointwise Hurwitz theorem.
Entire/nonzero hypotheses are explicit and independently checked in applications.

The existing transport group law and zero-time identity prove transport2(a)P
is nonzero for nonzero P, all real a. For s>0,1267 gives the global squared strip
max(b^2-2s,0) for EVERY actual scaled symmetric shift.1269 supplies its genuine
local-uniform heat limit; the new closure theorem transfers the bound to actual
(transport2(-s)P)_C. Nontriviality of that limiting polynomial comes from group
invertibility and polynomial evaluation, not an unproved limiting argument.
s=0 is proved separately from the exact transport identity. Therefore
PolynomialStripLimit.quadratic_heat_strip holds for EVERY finite nonzero real P,
EVERY s>=0, and ANY real b bounding the SQUARE of every initial root height:
  transported zero z => (Im z)^2<=max(b^2-2s,0).
All multiplicities, collisions and changes of the uppermost root are included;
no simple-root trajectory or discriminant-continuation hypothesis occurs.
quadratic_heat_real_roots gives real zeros once b^2<=2s.1258's interior upward-
motion counterexample is preserved; it does not contradict the GLOBAL bound.

Foundation/RiemannQuadraticGlobalStrip.lean applies this FIRST to EACH FIXED
actual finite polynomial from1266. Its nonzero status follows from the exact
actual H0(0) normalization and verified positive/nonzero origin value. Its
initial width-one strip comes from the existing independently verified classical
zeta nonvanishing Re(s)>1 construction1263. Each evolved polynomial therefore
has the same global bound max(1-2t,0). ONLY THEN does the1266 OUTER actual Xi
operator approximation pass to H_t, with its independently verified ENTIREness
and NONZERO origin. The new strip-closure theorem transfers the global bound
again. There is no uniform-in-degree or diagonal inner/outer limit interchange.
Actual Xi is never placed in the bounded factorial-analytic domain excluded by
1249. Genuine Gaussian domains, L1 before integration and compact-uniform heat
convergence from1264-1266 are preserved, not replaced by formal calculus.

TEN independent Lean examples pass: explicit failure of vertical monotonicity
below the root strip; zero-input-polynomial counterexample to dropping P!=0;
ACTUAL nonvanishing constant polynomials 1/(n+1) converging to the zero entire
function, showing why the NONZERO LIMIT premise is essential; a boundary root
at i for a complex-coefficient polynomial in the width-one closure theorem;
QUANTITATIVE SHARPNESS using initial z^2+1 with ALL initial roots in width1
and a genuine heat zero at s=1/4 with Im(z)^2=1/2 and Im(z)!=0; preservation of
real roots for arbitrary finite nonzero real P under forward heat; actual Xi
initial width1; actual Xi t=1/4 squared width1/2; actual Xi t=1/2 real zeros;
and actual Xi t=1 real zeros. The sharp quadratic is a GENERIC polynomial,
not the Xi function: it neither exhibits an actual Xi nonreal zero nor refutes
RH. It proves the universal width-only polynomial estimate cannot in general
force all-real zeros earlier. Additional Xi-specific information is required
for stronger arithmetic conclusions. Initial scratch coercion/evaluation and
rational simplification failures were fixed without production changes.

PRIMARY SOURCE CHECK: de Bruijn1950, The roots of trigonometric integrals,
Duke17,197-226, DOI10.1215/S0012-7094-50-01720-0, publisher PDF
https://pure.tue.nl/ws/files/1769368/597490.pdf . Existing ignored-cache copy
SHA256 C538EFAF0CA02AED0AFCCA4060B0AB3D9324AC89BAE594B5E89E74DA105260E0
was selectively rendered and VISUALLY READ at pp204-205. Theorem13 uses a
Gaussian multiplier with coefficient lambda^2/2 and narrows squared width by
lambda^2. Thus lambda^2=2t matches the verified clock. The general theorem has
weight hypotheses from Theorem10; this checkpoint independently proves the
stated finite-polynomial and actual-Xi instances, not its full arbitrary-weight
version. No novelty claim. The original archive and all manuscripts remain intact.

Verification: targeted4699 jobs TERMINAL0,41.7498331s;
fresh FULL6149 jobs TERMINAL0,24.4199383s;
COMPLETE37730-declaration transitive root/Foundation axiom audit TERMINAL0,
36.0429923s, only propext/Classical.choice/Quot.sound.
ALL13 public types ACTUALLY READ UNABRIDGED with pp.proofs true, no ellipses;
COMPLETE230 final source/proof lines read:13 theorems,0 new definitions, no
explicit private production helper or global instance. Ten examples TERMINAL0,
26.6084968s. Production inputs unchanged after full
build.1980 source hashes pinned; prior1978 unchanged except root import and
all configuration/toolchain unchanged. Exact107 recursive archive paths/hashes,
43Incoming42distinct and11A4 preserved; no manuscript edited/committed,
unrelated12 draft MDs/tmp untouched. Permanent build settings retained; no new
speedup claimed. Exact-commit receipt/private sync close the checkpoint afterward.

NEXT A2 TASK, not yet proved: audit reuse for actual contraction from an
ARBITRARY starting time t0 under an explicit initial strip b, then t0+s has
squared bound max(b^2-2s,0). This should directly reuse generic exact divisor
polynomials/zero tests, subquadratic Gaussian budgets and shifted_flow_average
at t0 rather than duplicating the zero-time construction. It would give actual
once-real-always-real and precise conditional transfer of any stronger initial
arithmetic zero strip. Compare with the already audited pinned OpenAI result
without treating its isolated replay as a new production import; preserve exact
theorem/dependency/domain boundaries. Exact Newman value, zero-time reality/RH
and stronger arithmetic estimates remain OPEN. Do not declare A2 stopped solely
from the classical1/2 theorem; a later explicit audited stopping checkpoint must
record the strongest proved transfer and the precise remaining obstruction.
A2 ACTIVE; integer/real FROZEN; final multichannel ONLY AFTER A2 stopping;
October31 hard stop and full verification/private gates retained. No pivot.


## Checkpoint1271: arbitrary-time actual Xi strip contraction and upstream heat transfer

Foundation/RiemannQuadraticStripEvolution.lean proves six actual-flow theorems.
For EVERY real starting time t (including negative times), an explicit GLOBAL
initial strip |Im z|<=b for ALL zeros of H_t yields at time t+s, EVERY s>=0:
  H_(t+s)(z)=0 => Im(z)^2 <= max(b^2-2s,0).
strip_between_times expresses the same result for arbitrary real t<=u.
real_after_strip_wait gives ALL zeros real at every u>=t+b^2/2.
once_real_always_real includes arbitrary real initial times; no initial t>=0
or simple-root, root-label, collision or bounded factorial-space hypothesis.
H is the ACTUAL RiemannEvenFlow.flow 1, with the established Xi normalization.

Proof reuses the GENERIC exact divisor polynomial approximation and Gaussian
growth budget at H_t, not only at time zero. The actual origin is nonzero for
every real t, so each approximating Pn is nonzero. Exact initial disk zero tests
transfer the GIVEN global strip to every finite polynomial. Actual Gaussian
integrability/domination/limit, the complex polynomial Gaussian transport
identity and imaginary_gaussian_average identify the pointwise transported
limit with ACTUAL H_(t+s). The1270 finite heat strip theorem and ENTIRE/NONZERO
strip-closure theorem then give the global result. No new infrastructure, no
uniform-degree assumption, diagonal limit or infinite Xi vector in H is used.
The NNReal-to-real clock coercion was repaired explicitly; failed scratch runs
were not certified. A transient unavailable Python launcher was a SETUP issue,
resolved by revalidating the bundled runtime before writes; not a math failure.

conditional_seven_eighths_strip keeps its exact arithmetic premise visible:
  forall w:Complex, 7/8<Re(w) -> riemannZeta(w)!=0.
The existing actual zero-time Xi transfer gives width3/4; hence squared width
max(9/16-2t,0), and conditional_seven_eighths_real_zeros gives all-real zeros
for EVERY t>=9/32. These are known classical transfer consequences, not RH or
a claimed new numerical bound. No equivalence to quartic/real-order stages.

The new ISOLATED integration actually supplies the previously independently
kernel-replayed OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re from pinned
OpenAI math1581d4cbdd69a0faf34b2089614fe2a814316a6a. BOTH resulting ACTUAL heat
theorems are UNCONDITIONAL in that isolated environment, with exact types and
transitive Lean.collectAxioms restricted to propext/Classical.choice/Quot.sound.
Both types and the full integration proof source were ACTUALLY READ UNABRIDGED.
STARDUST_A2_HEAT_UPSTREAM_INTEGRATION.json preserves code, exact output, hashes,
pins and domains. Only the child process LEAN_PATH adds existing OAI artifacts.
No production package/version/config/import change supplies the external theorem;
production retains the explicit conditional premise. All2924 OAI sources,30
effective supports,30 preserved raw supports and effective isolated config were
freshly hash-rechecked. The prior7059job replay1251 and1252 zero-time integration
remain intact; they were not rerun or falsely substituted for the fresh main build.
Mathlib's riemannZeta at1 is a nonzero junk value (Harmonic/ZetaAsymp
riemannZeta_one_ne_zero); the all-w arithmetic premise is not an accidental pole
contradiction. Broader human paper and follow-up method review remains open.

Verification: target4700jobs TERMINAL0,24.1808474s;
fresh FULL6150jobs TERMINAL0,25.0242793s;
COMPLETE37736-declaration transitive root/Foundation audit TERMINAL0,
36.9680841s, standard3 only. ALL6 new public types ACTUALLY READ
UNABRIDGED, pp.proofs true, no ellipses; ALL95 final source/proof lines read.
Six theorems,0 definitions, no explicit private helpers/global instances. Seven
examples TERMINAL0,28.0225714s: negative starting-time
strip wait, negative-time once-real preservation, zero elapsed time, exact
conditional t0 width9/16, t1/4 width1/16, t9/32 real boundary, and unconditional
classical real preservation to t2. Isolated integration TERMINAL0,
45.8554042s. All1981 production source hashes pinned;
prior1980 unchanged except root import. All build/toolchain/cache/resource settings
unchanged. Exact107 archive paths/hashes, Incoming43/42distinct and exact11A4
preserved; manuscripts/unrelated12drafts/tmp untouched. Exact private sync follows.

NEXT A2: theorem-level reuse for a GENERAL arithmetic half-plane parameter theta,
carefully retaining endpoint, pole/normalization and conjugation hypotheses; then
assess the precise remaining stronger-Xi estimate versus known external methods.
The arbitrary-time propagation and once-real obligations are now CLOSED, but
zero-time reality/RH, an exact Newman threshold and stronger Xi-specific arithmetic
estimates remain OPEN. Do not claim A2 stopped simply from known classical bounds.
An explicit audited stopping checkpoint is still required before final multichannel.
A2 ACTIVE; integer/real frozen; October31 hard stop; no priority change or pivot.


## Checkpoint1272: general arithmetic heat transfer, exact endpoint inputs and domain counterexamples

Foundation/RiemannQuadraticArithmeticHeat.lean proves seven theorems by direct
reuse of1271 and the prior actual completed-Xi/pole/positivity coordinate bridge.
Under the EXPLICIT actual arithmetic premise forall w,theta<Re(w)->zeta(w)!=0:
  zero_time_strip: ALL actual H0 zeros satisfy |Im|<=2theta-1;
  heat_strip: ALL H_t zeros satisfy Im²<=max((2theta-1)²-2t,0), t>=0;
  real_after_wait: ALL real at EVERY t>=(2theta-1)²/2.
These allow arbitrary real theta under the premise, without silently replacing
a negative initial strip width by its absolute value. No such arithmetic premise
is supplied by this module. At theta1 this matches classical1/2; theta11/12 gives
25/72; theta7/8 gives9/32; theta3/4 would give1/8, CONDITIONAL ONLY. The actual
external7/8 theorem and isolated actual-heat link remain precisely audited1271,
not a new production import. These are classical transfer statements, not novelty,
an improved numerical record, an exact Newman threshold or RH progress.

critical_half_plane_real_forward explicitly needs zero-free Re(s)>1/2.
asymptotic_half_planes_real_forward explicitly needs independently zero-free
Re(s)>1/2+epsilon for EVERY epsilon>0. It chooses epsilon less than a given gap;
no Hurwitz, time-limit, extrapolation of7/8, or k->1 flow claim. The substantive
strong arithmetic hypothesis is plainly visible in both printed theorem types.

polynomial_strip_sharpness proves the concrete initial real polynomial
P=X²+9/16 has ALL roots |Im|<=3/4, yet ACTUAL transport2(-1/4)P has nonreal zero
i/4. It saturates squared width1/16. Thus width3/4 alone cannot force general
polynomial heat reality by t1/4; stronger Xi conclusions need additional data.
This is NOT an actual Xi counterexample or RH refutation.
real_axis_exclusion_not_half_plane constructs f(z)=(z-1)²+1, entire AND conjugate
symmetric, nonzero on EVERY real argument, but zero at1+i with Re>7/8. This
refutes a generic real-axis-to-complex-half-plane inference, not a theorem about
the special Dirichlet L-function class. The witnesses and domains are printed.

STARDUST_A2_METHOD_TRANSFER_AUDIT.md records the selective HUMAN method audit:
pinned paper abstract/introduction/overview, opening and closure of the7/8 final
argument, full formalization note003, actual unconditional Dirichlet assembly,
and the follow-up's README/Main/conclusion. Exact read ranges, source pin and
prior verification scope are preserved. Nine initial external-source and six
follow-up source hashes freshly rechecked. No broad claim to have human-audited
all16,677paper lines, independently replayed the Hecke entrypoint or separate
SiegelZeros proof is made. Published scope distinguishes these targets.

The inspected arithmetic method uses completed cubic theta sums, Poisson/Mellin
reciprocal-L signals, prime compensation, asymmetric scales and matched moment
estimates with fixed exponent margins. Stardust supplies the DOWNSTREAM actual
Gaussian/operator/global zero transfer; it does not supply those arithmetic
estimates. No identity of the paper's arithmetic cubic theta object or auxiliary
Gaussian with the positive Xi density or actual probability law is assumed.
The real-zero/conductor logarithmic-gap follow-up, as STATED, is not a stronger
complex-zeta half-plane theorem. Its primitive/nonprincipal/real-character and
real-beta domains matter. The generic counterexample tests the logical domain
jump; the separate follow-up proof is neither certified nor refuted here.

Verification: target4701jobs TERMINAL0,23.6124477s;
fresh FULL6151jobs TERMINAL0,24.6779511s;
COMPLETE37743-declaration transitive root/Foundation audit TERMINAL0,
34.9110838s, standard3 ONLY. ALL7 new public types ACTUALLY READ
UNABRIDGED pp.proofs true/no ellipses, and ALL119 final source/helper/proof lines
read. Seven theorems,0definitions/no explicit private helpers/global instances.
Eight independent examples TERMINAL0,27.0092434s:
theta1/7/8/11/12/3/4 waiting/widths, critical endpointt0, EVERYepsilon premise,
polynomial nonreality and full entire/conjugate real-axis counterexample type.
Source1982 manifest pinned; prior1981 unchanged except root import; all config/
versions/resource/cache/check settings unchanged. Exact107 archivepaths/hashes,
43Incoming42distinct and11A4 preserved; unrelated12drafts/tmp untouched.
No manuscripts modified/committed. Exact private backup follows full audit.

NEXT: theorem-level reuse audit for closedness of the actual all-real TIME SET
and its boundary, using actual parameter continuity/local-uniform convergence
and a nonzero holomorphic limit. Do NOT assume an attained finite threshold;
do NOT infer holomorphic/no-zero limits from pointwise convergence without its
extra polynomial-strip or uniform hypotheses. The general transfer and exact
arithmetic/domain limitations are now documented. Zero-time reality/RH, exact
Newman threshold and stronger Xi-specific estimates remain OPEN. A2 ACTIVE;
explicit audited stopping still required before final multichannel. No pivot;
integer/real frozen; October31 hard stop and all private/verification gates hold.


## Checkpoint1273: actual all-real time sets CLOSED; exact finite-boundary obligation isolated

Foundation/RiemannEvenRealityClosed.lean proves CLOSEDNESS of the ACTUAL all-real
time set for EVERY natural integer-even order m, with no m>0, t>=0 or real-zero
assumption at the limiting time. This supports active A2 and reuses existing
general declarations; no frozen campaign is reopened. realTimes m is defined
literally as {t | forall z:Complex, flow m t z=0 -> Im(z)=0}.

upper_vertical_bound starts at an explicit all-real actual H_(m,t). The existing
generic real divisor polynomials have EXACT initial zero tests and actual local-
uniform convergence. Actual analyticity, nonzero origin, evenness, conjugation
and subquadratic growth discharge ALL input hypotheses for every m,t. Thus each
finite polynomial has only real zeros, and PolynomialStripLimit.limit_upper_bound
gives vertical modulus monotonicity above the real axis. No new split theorem,
new approximation construction, Gaussian budget or diagonal selection is needed.

For a convergent real time sequence s_n->t, the EXISTING even_order_heat_equation
gives true pointwise time continuity at each fixed complex argument. Every H_s_n
inherits the vertical inequality; passing the two norm limits preserves it for
ACTUAL H_t. The previously verified entire identity argument excludes zeros
above the real axis because H_t is entire and its origin is nonzero. Actual
evenness handles negative imaginary parts. Hence reality_of_time_sequence and
isClosed_realTimes hold. This is NOT a general pointwise Hurwitz theorem: the
global polynomial-derived modulus property is the essential additional structure.
No assertion of local-uniform time convergence is needed or made by this proof.
No root branch, simplicity, multiplicity bound or boundedness of approaching
zeros is assumed. The local-uniform DIVISOR approximation remains genuinely used.

For ACTUAL quadratic flow, once-real preservation gives quadratic_upper and
the unconditional classical half theorem gives quadratic_nonempty. IF the
all-real set is bounded below, quadratic_infimum_mem proves its infimum attained,
quadratic_eq_Ici identifies the entire set with that closed upper ray, and
quadratic_nonreal_before supplies an ACTUAL nonreal zero at EVERY earlier time.
The BddBelow premise is printed and has NOT been discharged. quadratic_dichotomy
is unconditional: either ALL real times are all-real, or the set is Ici A for a
real A<=1/2. quadratic_bddBelow_iff_nonreal_exists proves precisely that the
missing lower-boundedness is equivalent to one ACTUAL nonreal zero at some time.
This does not produce that witness or establish a finite Newman threshold.
No RH/exact threshold/numerical improvement or quartic-to-quadratic inference.

PRIMARY SOURCE: [Newman, Fourier Transforms with Only Real Zeros,
Proc.AMS61,245-251](https://sites.math.northwestern.edu/~auffing/papers/Newman.pdf).
Page247 was visually read. Its classification leads to a quartic density lower
bound incompatible with the Xi density's faster decay. This external theorem
is NOT Lean-verified or imported here. STARDUST_A2_NEWMAN_SOURCE_AUDIT.json records
the exact PDF/render hashes and scope. The paper uses a different time convention;
its normalization and all intervening analytic hypotheses still need verification.
No unverified finite-threshold theorem is silently substituted for BddBelow.

A promising NEXT INVESTIGATION, NOT A THEOREM: determine whether existing actual
Gaussian smoothing, canonical polynomial products and density derivatives can
prove the NEEDED lower-bound consequence directly, without formalizing the full
measure classification. Required links include actual even-density realization,
Gaussian approximate identity for needed derivatives, a uniform quartic lower
bound under the all-negative-time reality hypothesis, and contradiction with the
verified superexponential arithmetic tail. Each is presently an obligation; a
formal density/expectation or unchecked normalization will not close it. Start
with theorem reuse and read the relevant classification proof before choosing
the shortest valid route. Keep actual-existence and conditional thresholds distinct.

Verification: target4702jobs TERMINAL0,22.6494436s;
fresh FULL6152jobs TERMINAL0,23.9231951s;
COMPLETE37758-declaration transitive root/Foundation audit TERMINAL0,
49.4433188s, ONLY propext/Classical.choice/Quot.sound. ALL11
new public types ACTUALLY READ UNABRIDGED with pp.proofs true, no ellipses; ALL100
final source/proof/helper lines read. Ten theorems and1definition; no explicit
private production helper/global instance. TEN examples TERMINAL0,
28.4037483s: closedness m1/m3/m0; conditionalnegative
constant-time sequence; decreasing t+1/(n+1) boundary; conditional attained
infimum/nonreal earlier point; unconditional dichotomy; actual nonreal witness
implies BddBelow; actual vertical bound. Initial scratch repaired generic argument
order and the explicit local-uniform-on-univ conversion; no false weakening.
Source1983 hashes pinned; prior1982 unchanged except root; configs/toolchain/
resource/cache/full gates unchanged. Exact107archive paths/hashes,43Incoming
42distinct,11A4 unchanged; unrelated12drafts/tmp preserved. The external PDF is
only an ignored cache source; no manuscript edited/renamed/deleted/committed.
Private exact-commit receipt/sync complete the checkpoint afterward.

A2 ACTIVE; no stopping from this conditional boundary theorem. Exact finite
lower bound, stronger Xi estimates, exact Newman value and zero-time RH remain
OPEN. Integer/real frozen; finalmultichannel ONLY AFTER explicit audited A2
stopping; October31 hard stop and all verification/private gates unchanged.
