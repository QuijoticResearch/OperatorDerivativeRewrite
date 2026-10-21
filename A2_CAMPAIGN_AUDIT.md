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
