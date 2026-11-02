# Iterated/time-changed higher-order pseudoprocess calculus — active audit

Activated November2,2026 via the standing automatic-next instruction after A2's
fully verified stopping checkpoint1951. Full mission remains in
STARDUST_ITERATED_PSEUDOPROCESS_QUEUED_RESEARCH.md. This is a distinct signed
composition campaign, not reopening the completed1293 calculus or IBM priority.

## Source evidence at activation

Cinque and Orsingher, Higher-order fractional equations and related time-changed
pseudo-processes, arXiv2402.13691v2,12November2024:
https://arxiv.org/html/2402.13691v2 . Authors/version/abstract and introduction,
Definition1.1 and opening hypotheses of Section2 selectively read. The abstract
URL returned cache miss; the versioned HTML is available. This is NOT yet a
complete proof/publication-version comparison or a novelty audit. Publisher
S0022247X2400948X remains the supplied publication anchor; inspect its actual
version before claiming equivalence of statements.

Definition1.1 sets (f diamond g)(t,x)=integral_(s>=0) f(s,x)g(t,s)ds when convergent.
The accompanying boundedness discussion invokes bounded f and bounded integrated
g. For signed g the appropriate general bound must involve integral|g|, not
only signed mass. This is the first CONCRETE claim to independently test; it is
not a declaration that the paper's conditional main PDE theorem is false.
The paper itself requires additional Fourier/Laplace and boundary hypotheses.

PREPROOF candidate: clocks on nonnegative operational times with
 g_t(s)=(1+t)1_[0,1)(s)-t*1_[1,2)(s), t>=0.
Their signed mass is1 but variation is1+2t. A bounded observable1_[0,1)(s)
would have composition1+t. Verify actual measurable Lebesgue integrals or an
explicit signed-measure realization in Lean before recording a formal theorem.
The finite two-atom version (1+t)delta0-t*delta1 similarly separates mass and TV.
A genuine contractive scalar semigroup test exp(-lambda*s) also detects growth.
This is a test of composition continuity, not a path-space probability model.

Second possible obstruction to audit, NOT yet proved here: for fractional time
order2, a positive-time heat-clock representation would have Laplace multiplier
cos(t*sqrt(lambda)). A finite signed clock supported on[0,infinity) has Laplace
transform converging to its atom at0 as lambda->infinity, whereas that cosine
oscillates. Check the source's exact order/sign, inverse-clock and transform
hypotheses before drawing a consequence. A distributional/analytic-dual clock
may survive even when finite-TV clocks do not.

## Precise existing foundations to reuse next

The old STARDUST_PSEUDOPROCESS_STOPPING_AUDIT.md was read through its completed
observable-domain reconstruction and native signed-approximation contract.
HigherHeatCompletedClarkOcone.clark_ocone gives the FULL p-1-channel formula on
the EXISTING analytic cylinder Banach domain, in its continuous test dual; do
not confuse this with unrestricted pseudo-L2 or a finite signed path measure.
HigherHeatSignedDiagonalRealization.completed_signed_realization supplies a
joint actual polynomial/mesh approximation. Its domain and probe pairing must
be matched before any random/signed clock substitution.

HigherHeatL2, Schwartz/tempered and Fourier-path semigroups are available with
positive operational times, exact signs and original topologies.
HigherHeatRealizationClassification excludes probability/finite-signed full
path realization at natural m>=2 for its cylinder family. IBM's observed
filtration/domain/residual theorems remain source-specific; their hypothesis
match is still to audit, not assumed from terminology.

NEXT: inventory exact existing signed integral/TV/composition declarations;
prove the sharp bound or obstruction for a genuine signed clock functional;
then determine an admissible clock/domain for actual operator composition.
Audit polynomial cylinders, mass/variation, time support and Fubini conditions
before derivatives, adjoints, Ito channels or completed reconstruction. No new
foundational library is justified merely by the existence of a formal PDE formula.

No new mathematical claim or theorem is certified by activation. Original
ResearchSources and all completed/paused proofs are preserved. All full-build,
transitive axiom/type/proof/independent checks and guarded exact BOTH-branch
backup requirements remain, repository visibility never changed.

## Checkpoint1953 — genuine signed-clock composition and continuity obstruction

VERIFIED: Foundation.SignedClockComposition (130 lines; 13 public proofs and
4 definitions). Reuses SignedDensityIntegral.integral_density to identify an
ACTUAL signed-measure integral, not an assigned moment functional.
On nonnegative operational times let g_t=(1+t)1_[0,1)-t1_[1,2).
Each density is measurable and integrable; its actual finite SignedMeasure has
mass1. The fixed measurable bounded observable f=1_[0,1) has actual signed
integral1+t. Thus constant signed mass does not bound these compositions, even
essentially in t: an independent Lean example rules out every AE constant bound
by a positive-measure unit interval beyond it. Joint measurability is checked.
Negative-time support vanishes; endpoint membership and negative density are
independently tested. No positivity is assumed or inferred from mass1.

The production composition_bound proves |integral f*g| <= M integral |g|
for integrable g and AE strongly measurable f with pointwise |f|<=M, including
product integrability. Uniform L1 control therefore supplies a valid uniform
bound; signed mass alone does not. law_mass and signed_observable_composition
prove the exact signed-measure realization. This corrects the general signed
boundedness discussion after Definition1.1 in Cinque-Orsingher,
https://arxiv.org/html/2402.13691v2 (12 November2024).
It does NOT refute Theorem2.1: the counterexample has not been shown to satisfy
its separate clock PDE, boundary and initial conditions. Sections2 and3 and
Eq3.17 were selectively inspected, not every proof or the publication version.

Full root build7372 jobs passed49.502815s; complete transitive audit66565
declarations passed54.123333s, standard three axioms only. All17 canonical types
and complete source proofs reviewed. Fourteen independent Lean examples passed
26.667883s; persisted complete AxiomAudit passed62.068732s. Failed initial test
normalizations and an unqualified test lemma were repaired only in tests; their
logs remain. Five exact rational clocks and125 bounded coefficient tests passed
as consistency checks, not substitutes for continuous signed-integral proofs.
The rational variation value1+2t is not a newly formalized TV equality.

Source integrity authenticates prior1952 approval and all3148 Foundation/root
sources: only the new leaf, root import and axiom ledger differ. All older
mathematics,3 configs,113 archived originals,21 YM originals, Cauchy original,
both old numerical tools,1947 probes and4 paused1945 scratch copies preserved.
Receipt: STARDUST_SIGNED_CLOCK_COMPOSITION_VERIFICATION.json. Exact commit and
both-branch PUBLIC remote confirmation are recorded separately at closure.

NEXT concrete question (UNPROVED): source Eq3.17 at fractional order2 suggests
operational Laplace multiplier E_(2,1)(-lambda*t^2)=cos(t*sqrt(lambda)).
A finite signed clock supported on[0,infinity) should have a Laplace transform
converging to its atom at0 as lambda grows. Prove that limit and the incompatible
cosine subsequences with exact hypotheses before asserting any impossibility.
An analytic-dual or distributional clock may remain valid. Distinguish such a
clock from a finite signed measure, a process, and an operator cosine family.
Do not return to A2 or launch broad infrastructure; actual iterated calculus,
channel identities and completed-domain convergence remain unresolved.


## Checkpoint1954 — finite signed inverse-clock obstruction at time order2

VERIFIED Foundation.SignedClockLaplaceObstruction:155 lines,12 public proofs,
3 definitions, no private declarations or trust/resource changes.
The actual vector integral L_nu(q)=integral exp(-q*s) dnu(s) for a finite signed
measure on NONNEGATIVE operational times satisfies
 L_nu(q) -> nu({0}) as q->positive infinity.
Proof uses existing VectorMeasure dominated convergence with bound1 against
finite total variation, including the atom at0; origin_eq_atom identifies the
limit exactly. The signed mass nu(univ) is NOT substituted for that atom.
The working Laplace domain is q>=0, on which these bounded observables are
integrable. Totalized definitions at negative q assert no integrability there.

inverseTwo is the ACTUAL series sum_n (-q*t^2)^n/Gamma(2*n+1).
inverseTwo_hasSum proves convergence for all real t and q>=0 using the verified
Gamma-factorial and cosine series; inverseTwo_eq_cos proves cos(t*sqrt(q)).
No assigned transform or unsupported Mittag-Leffler library is introduced.
For every t>0 no finite SignedMeasure NNReal has that Laplace transform for
ALL q>=0. The proof reparametrizes q=(x/t)^2, so any such measure would force
cos(x) to have a limit; natural even/odd phase sequences give1 and-1.
At t=0 an explicit Dirac0 clock DOES work. The exceptional endpoint is retained.

This applies DIRECTLY to actual HigherHeatL2.symbol2, with its verified2*pi
frequency normalization: no single finite signed operational clock can integrate
even its real multipliers into inverseTwo(t,(2*pi*xi)^4) for every real xi.
The fourth-root substitution xi=sqrt(sqrt(q))/(2*pi) proves that the actual
spectral rates cover EVERY q>=0, including zero. inverseTwo_biharmonic identifies
the transformed multiplier as cos(t*(2*pi*xi)^2).

The scalar addition formula has the exact negative sine-product correction.
inverseTwo_not_semigroup gives the positive-time witness s=t=pi/2 at rate1:
C(s+t)=-1 while C(s)C(t)=0. Hence scalar semigroup/independent-increment results
cannot simply be reused. The sine channel is a positive algebraic repair, not
a completed stochastic calculus, natural filtration or closed-operator theorem.

Source comparison: Cinque-Orsingher arxiv2402.13691v2,12November2024,
https://arxiv.org/html/2402.13691v2 Section3 after Eq3.17, asserts operational
Laplace multiplier E_(nu,1)(-q*t^nu). The nu=2 specialization cannot be an
ordinary finite-TV signed clock. This is a rigorous restriction on that
interpretation, NOT a blanket refutation of the paper's conditional PDE results
or a generalized analytic-functional interpretation. Other fractional orders,
publication-version comparison and novelty remain open. No original modified.

Full root7373-job build passed45.204554s; all66598 transitive declarations
passed51.699472s with standard propext/Classical.choice/Quot.sound only.
All15 canonical types and full155-line source proofs reviewed. Fifteen independent
Lean examples passed26.285282s; complete persisted axiom ledger passed62.979829s.
Independent tests include Dirac endpoints, a mass1 signed clock with limit atom2,
actual Gamma-series summability, normalized biharmonic frequency and semigroup
counterexample. One initial test required norm_num for2-1=1; its failed log/time
are preserved, mathematical sources unchanged. Forty-nine Decimal/cosine and30
phase/frequency numerical consistency checks passed; they are NOT universal
proofs. Receipt: STARDUST_SIGNED_CLOCK_LAPLACE_VERIFICATION.json.

Authenticated exact1953 approval:3149 Foundation/root source hashes, only new
leaf/root/audit changed; all older mathematics,3configs,113 archived originals,
21YM originals,Cauchy original,old tools,1947 probes and4paused1945 scratch copies
preserved. Exact-commit approval and independent BOTH-branch PUBLIC backup
confirmation recorded separately at closure. Campaign and goal remain ACTIVE.

NEXT: construct an admissible analytic-functional/operator composition using
existing FactorialAnalyticDomain/Heat/Functions and signed cylinder machinery.
Candidate, NOT PROVED: Phi_t(f)=sum_n t^(2*n)*f^(n)(0)/(2*n)!, realized on an
explicit derivative-controlled domain. FactorialAnalyticDomain.H is l1 of
UNSCALED derivative jets: exp(-q*s) belongs only for |q|<1. Do not claim all
spectral rates belong to that fixed domain; scaled derivative bounds or another
already verified domain must be matched. A bounded two-component operator
exponential using the existing shift might realize the even series and its
velocity channel without a scalar clock measure. Prove its norm/domain,
polynomial transport and convergence before any signed Ito/Clark-Ocone claim.
No ordinary tempered-distribution clock is inferred merely from failure of
finite measures. A finite spatial signed law for cos(t*xi^2) is ALSO not decided
here; test uniform continuity of Fourier-Stieltjes transforms before claiming
one-time realization. Preserve this distinction between clock and output.


## Checkpoint1955 — constructed analytic clock and actual signed polynomial composition

VERIFIED Foundation.AnalyticInverseClock:336 lines;40 public proofs,7 definitions.
Reuses L1BoundedSynthesis and the existing FactorialAnalyticDomain/Heat/Functions;
no new foundational Banach space, probability assumption or clock measure.
H is l1 of UNSCALED real derivative jets u_n, faithfully realized by an actual
smooth function f_u with a globally convergent factorial series and f_u^(n)(0)=u_n. A contractive even-coordinate embedding
J has (Ju)_(2n)=u_n and (Ju)_(2n+1)=0. Define
 Phi_t(u)=FactorialAnalyticHeat.mean(1,t)(Ju).
This is an ACTUAL continuous linear functional with norm<=exp|t| and the proved
convergent derivative series sum_n f_u^(n)(0)*t^(2n)/(2n)!.
It is not merely a prescribed collection of moments. The t=0 value is u_0,
initial velocity is0, and Phi_t is C^n for every finite n for each u.
Even-coordinate intertwining proves d_t^2 Phi_t(u)=Phi_t(Du).

On actual polynomial functions Phi_t(s^n)=n!*t^(2n)/(2n)!.
The nonnegative actual square (s-t^2/2)^2 has value -t^4/6, so Phi_t is NOT
positive for t>0. This is a separate exact positivity obstruction, not a
finite-signed-measure assertion. The previous1954 global finite-clock
impossibility remains preserved. The new functional uses a stronger analytic
norm, not sup norm on arbitrary bounded measurable functions.

The exponential domain is EXACT, not assumed: an H-realization of exp(-q*s)
exists iff |q|<1. For0<=q<1 the constructed functional equals the ACTUAL Gamma
series inverseTwo(t,q)=E_(2,1)(-q*t^2)=cos(t*sqrt(q)). At q=1 the exponential
already lies outside this fixed domain. No all-frequency clock representation
or continuity beyond the proved domain is inferred.

For every positive integer p and |c|<=1 the contractive heatJet map sends
u_n to c^n*u_(p*n). Its faithful function realization is EXACTLY the existing
operator mean s->mean(p,c*s)(u), including all real s as the canonical analytic
extension. For the physical sign c=(-1)^(m+1),p=2m and polynomial P, its values
at every positive operational time s agree with the ACTUAL signed higher-heat
kernel expectation via FactorialAnalyticHeat.actual_mean. This is a genuine
one-time signed-kernel connection, not a moment-only surrogate.

C_t=Phi_t composed with heatJet is a bounded H->R dual mean, norm<=exp|t|,
with convergent series sum_n c^n*u_(p*n)*t^(2n)/(2n)!.
It is the unique continuous extension of its polynomial action, and
H-norm approximation gives UNIFORM convergence for |t|<=T, with quantitative
error <=exp(T)*norm(u-v). For every u this is a smooth classical solution of
 d_t^2 C_t(u)=C_t(c*D^p u), C_0(u)=u_0, d_t C_t(u)|_0=0.
Smoothness is explicitly proved; no totalized-derivative shortcut is used.
C_t is a DUAL FUNCTIONAL, not a claimed full H->H operator cosine family.
General H kernel-integral agreement is NOT yet proved: actual signed integrals
are identified on polynomials, with the unique analytic extension thereafter.

Independent concrete biharmonic tests, p=4,c=-1, prove
 C_t(x^4)=-12*t^2 and C_t(x^8)=1680*t^4,
as well as normalization, clock positivity obstruction, q=1 exclusion, actual
q=1/2 exponential evaluation, even/odd coordinates, smoothness, physical generator
sign, initial conditions, actual kernel agreement and compact-time convergence.
Twenty independent Lean examples passed27.831549s after initial test-only
arithmetic/coefficient/sign normalizations; failed logs/times remain. The
mathematical sources were unchanged after the full build/audit passed.
Exact rational checks on18 degree12 rational polynomials,5 positive orders,
4 coefficients and4 times passed1440 compositions and360 time-second versus
spatial-generator identities, plus4 negative-square checks. These finite checks
are consistency evidence, not proofs of the completed-domain statements.

Full root7374-job build passed46.298754s; complete66666-declaration transitive
axiom audit passed48.007787s with propext/Classical.choice/Quot.sound only.
All47 canonical types and complete336-line source proofs reviewed; persisted
complete axiom ledger passed56.946566s. Receipt:
STARDUST_ANALYTIC_INVERSE_CLOCK_VERIFICATION.json. Exact3150-source/root identity
authenticates1954 and changes only new leaf/root/audit; all old mathematics,
3configs,113 archive originals,21YM originals,Cauchy original,old numerical tools,
1947 probes and4paused1945 scratch copies preserved. Exact commit and guarded
BOTH-ref PUBLIC confirmation recorded separately at closure.

Interpretation and remaining bridge: this rigorously repairs ONE-TIME analytic
composition at source time order2 (Cinque-Orsingher arxiv2402.13691v2,
https://arxiv.org/html/2402.13691v2), not its entire stochastic theory. Classical
analytic/transmutation facts are distinguished from any unestablished novelty.
The univariate H is NOT the old HigherHeatAnalyticCylinderDomain.Domain.
No multitime clock law, consistent time-changed cylinders, natural filtration,
causal projection, adjoint integral, Ito or Clark-Ocone theorem follows yet.
Do not substitute independently chosen clock marginals or a finite-scale
complex-noise representation for those missing hypotheses.

NEXT concrete audit: identify a justified multitime signed-functional composition
and its relationship to the source inverse-clock claims, or isolate the precise
consistency obstruction. Alternatively match a useful state-space/two-channel
lift to the existing analytic operator calculus if it resolves that obligation.
Preserve the finite-clock impossibility; do not stop at re-proving scalar PDE
formulas or add unrelated infrastructure. Campaign remains ACTIVE.


## Checkpoint1957 — genuine complex Brownian realization and the observable phase obstruction

VERIFIED Foundation.BiharmonicGaussianBranches:324 lines;41 public theorems,
13 definitions,1 abbreviation and2 probability instances; all57 types and all
source proofs reviewed. No private declarations, resource/trust changes or new
foundational stochastic process library. Reuses the actual continuous Brownian
clockPath from IBMConstructedSources, finite probability integration, original
ComplexGaussianPolynomialTransport integrability/Stein/moment results and1955
analytic composition. Earlier proofs and the current queue are preserved.

Construct sigma as one fair independent sign and set Z_t=(1+i*sigma)B_t on the
ACTUAL product probability space. The sign is selected ONCE, not refreshed each
increment. The path map into C(nonnegative time,complex) is measurable, paths
are continuous and evaluation is jointly measurable. Its actual pushforward
path law is a probability measure. This constructs a genuine COMPLEX process
at all times, stronger than a finite-scale complex-noise representation.
It is NOT a real signed path measure or a nonnegative inverse clock.

For every real polynomial P, integrability of its holomorphic complex extension
P^C(Z_t) is proved before Fubini and integral algebra. The full polynomial
functional, not merely selected moments, satisfies
 E[P^C(Z_t)] = (AnalyticInverseClock.composed(4,-1,t)(polynomial P):complex).
Proof establishes the phase cancellations and exact Gaussian moments, then
identifies the two real-linear polynomial maps. Degree4j gives
 (4j)!*(-1)^j*t^(2j)/(2j)!, with all other degrees zero.
Thus the analytic clock's biharmonic means have an actual continuous complex
probability realization on polynomial observables. It does not identify the
source paper's multitime inverse-clock composition, which is still undefined
in the required completed domains. Polynomial agreement does not prove a
completed-H or all-entire-observable integral representation.

The variance normalization is essential: the branch Gaussian law is
RiemannQuadraticGaussian.law(t/2)=normal(0,t), and phase is1+/-i. Their squares
are+/-2i. The existing average_eq_transport/actual_gaussian_transport requires
a REAL delta, so it was explicitly REJECTED for these phases. Instead actual
complex polynomial moments and average_mul_X supply valid integration by parts.
The old ComplexFourthRootNoise.root_fourth proves the exact fourth phases;
its finite-noise realization is not mistaken for the new continuous process.

Let A be the fair average and B its sign contrast, each built from actual
Gaussian integrals. The verified paired Stein identities for EVERY polynomial:
 A_t(XP)=2*i*t*B_t(P'),   B_t(XP)=2*i*t*A_t(P').
These are genuine terminal polynomial IBP identities. They are not yet a closed
Malliavin derivative, time-chronological integral or Clark-Ocone theorem.
A_t(X^2)=0 but B_t(X^2)=2*i*t. More sharply the actual Brownian-source conditional
branch averages satisfy integral_w Z_t(b,w)^2=2*i*t*sign(b), and for t>0 they
cannot BOTH vanish. Any future reconstruction requiring branch-conditional
centering must keep this nonzero branch information; unconditional centering
alone cannot supply that hypothesis. No unsupported representation theorem is
asserted from this necessary obstruction.

Observed-domain result: Re(Z_t)=B_t and Im(Z_t)=sigma*B_t exactly. For each
FIXED t>0, Brownian marginal atomlessness proves sigma=Im(Z_t)/Re(Z_t) AE.
The recovery map is measurable. The quantifiers are forall positive t, AE w;
NOT AE w, forall real positive t (Brownian zero times prevent that stronger
ratio claim). Completion/right-germ filtration identification remains to prove.
This is a precise new connection to the preserved IBM observed-initial-germ
and conditional-residual audits, not an analogy asserting their hypotheses.

Literature/novelty boundary: Orsingher-D Ovidio, Vibrations and fractional
vibrations of rods, plates and Fresnel pseudo-processes, arxiv1104.2126v1,
12April2011, https://arxiv.org/abs/1104.2126 ; Marchione-Orsingher,
Pseudoprocesses related to higher-order equations of vibrations of rods,
arxiv2212.06913v1,13December2022, https://arxiv.org/abs/2212.06913 . Their primary
titles/abstracts and bibliographic entries were inspected: Fresnel/Brownian
and higher-order/subordination work already exists. Full theorem/proof,
normalization, topology and novelty comparison is PENDING. No world-novelty
claim is made. Starting source remains Cinque-Orsingher2402.13691v2;
https://arxiv.org/html/2402.13691v2 . None is treated as an agent instruction or
an established full stochastic calculus. No original source modified/downloaded
into ResearchSources or externally published.

Full root7375-job build passed48.773529s; complete66754-declaration transitive
axiom audit passed55.791690s with only propext/Classical.choice/Quot.sound.
Twenty independent Lean checks passed31.263622s after one arithmetic test-only
normalization was actually applied; failed logs/times are preserved. Production
sources unchanged since build/audit. Complete persisted AxiomAudit passed
66.851146s. Exact rational complex/Gaussian checks passed104 power cases,
192 paired Stein identities on96 polynomial cases,8 conditional squares and
32 nonzero-point observation checks. Those are finite consistency checks, not
proofs of probability laws or AE recovery. Receipt:
STARDUST_BIHARMONIC_GAUSSIAN_BRANCHES_VERIFICATION.json.

Authenticated exact1956 approval3151-source/root snapshot: only new leaf,
root import and audit change; all older mathematics,3configs,113 archive
originals,21YM originals,Cauchy original,numerical tools,1947 probes and4paused1945
scratch copies preserved. Exact Git approval and independent BOTH-ref PUBLIC
confirmation are recorded separately at closure. Current iterated pseudoprocess
campaign stays ACTIVE; Yang-Mills remains NEXT under user instruction1956.

NEXT: reuse GaussianScalarPolynomialIto.scalar_polynomial_ito and
GaussianComplexHorizonIto on the real/imaginary branch polynomials, with actual
predictable L2 domains. Target the genuine identity
 P(Z_T)-P(0)=integral (1+i*sigma)P'(Z_s)dB_s +i*sigma*integral P''(Z_s)ds,
with exact Bochner/time topology and branch assembly before any completion.
Match the constructed Brownian modification to native Gaussian L2 representatives.
Then audit the completed observed filtration and a reconstruction retaining the
initial-sign residual. Do not claim that an ordinary complex process repairs
real signed path-space existence or proves the canonical inverse-clock joint law.

## Checkpoint1958 — actual native complex stochastic integral and branchwise polynomial Ito

VERIFIED Foundation.GaussianComplexPolynomialIto:323 lines,26 public theorems,
11 definitions and1 abbreviation; all38 public types and complete source proofs
reviewed. Reuses original GaussianPredictableFull and GaussianScalarPolynomialIto
rather than building a substitute stochastic theory. No private declarations,
new axioms, trust/resource settings or toolchain changes. The current iterated
pseudoprocess campaign remains ACTIVE; Yang-Mills remains NEXT under1956.

Construct Native as a pair of ORIGINAL real fullPredictable Gaussian L2 fields,
and integral as the complex combination of their actual Brownian Ito integrals.
The exact identity is ||integral U||^2=||field U||^2 for field U in COMPLEX
L2(time x probability). It is NOT an isometry for the default product-supremum
norm on Native: equal unit real/imaginary components give squared field norm2
versus squared product norm1. Both the distinction and diagonal norm formula
are explicitly tested. No false product-Hilbert assertion is introduced.

For every complex polynomial Q and horizon T, value(T,Q) is an actual complex
Gaussian L2 class, AE equal to Q(B_T) for the continuous Brownian clockPath.
It is norm-continuous in time and its second-derivative drift is genuinely
Bochner interval-integrable in Gaussian L2. The verified unique native integrand
has real/imaginary scalarCurry fields equal AE-time to the horizon-indicated
polynomial derivative values, and
 value(T,Q)-constant(Q(0)) = integral U + (1/2) integral_0^T value(s,Q'')ds.
Uniqueness concerns the integrand with the specified derivative field, using
original injective scalarCurry, not an unproved arbitrary-filtration theorem.

For each FIXED sign b, let Z_b=(1+i*sign(b))B and evaluate real P by its
holomorphic complex extension. The chain rule verifies phase^2=2*i*sign(b),
so the ACTUAL STOCHASTIC identity in complex Gaussian L2 is
 P^C(Z_b(T))-P(0) = integral U + i*sign(b) integral_0^T (P'')^C(Z_b(s))ds.
The unique U has complex time slice phase(b)*(P')^C(Z_b(s)) on(0,T].
This is stronger than an expectation-level heat formula. All drift terms are
actual Bochner L2 integrals. For original predictable past-step coefficients
A+iB at s<=t, the constructed integral agrees AE with the genuine product
(A+iB)*(Brownian_t-Brownian_s). The original natural-filtration measurability
and L2 hypotheses are retained. Every native integral has ordinary complex
expectation zero.

This yields a sharp ACTUAL-domain obstruction: for every T>0 and either branch,
P=X^2 has mean2*i*T*sign(b), so branchValue(T,b,X^2) is NOT integral U for any
Native U. The T=0 exception is verified. This does not rule out reconstruction
with the branch mean/residual, and does not rule out a multichannel theorem.
The quartic phase cancellation is also independently verified:
 branchPolynomial(b,X^4)=(-4)*X^4.
The distinction suggests branch-conditional polynomial reconstruction via the
existing backward Gaussian polynomial martingale, with an explicit sign residual,
as a productive next route. Such reconstruction remains UNPROVED here.

Reuse audit: coefficient extraction uses only the unrestricted finite-polynomial
realPolynomial_coeff from EvenEntirePolynomialApproximation and map_eval_real
from RealRootedLaguerreLimit. Their original Xi/zero-control applications are
not hypotheses of this proof; no A2 campaign is reopened or RH consequence
claimed. The complex Ito extension is classical mathematical machinery transferred
rigorously to the1957 analytic biharmonic process, not a novelty claim. Earlier
Fresnel/rod-vibration references and pending full normalization/novelty comparison
in1957 remain preserved. No new external literature theorem is assumed.

Still open: completed observed-filtration/right-initial-germ identification;
conditional residual/Clark-Ocone reconstruction; completed analytic-H actual
probability L1/L2 agreement; and canonical source inverse-clock multitime
identification. A continuous COMPLEX probability realization and its branchwise
calculus are not a real signed path measure or full signed stochastic composition.
The1954 signed-clock obstruction and1955 analytic-domain restrictions remain.

Verification: full7376-job root build, complete66820-declaration transitive
standard-three axiom audit, persisted Foundation/AxiomAudit.lean, all38 canonical
types/full proofs,21 independent Lean examples all PASS. Independent exact rational
checks cover240 branch drift/expectation cases,528 coefficient chain cases and75
complex step norm cases, plus an explicit product-norm counterexample; these
finite checks supplement rather than replace stochastic proofs. Failed test-only
namespace/simp attempts are retained locally; two evaluation checks were repaired
by pointwise AE transitivity and eval_X_pow. Production sources were unchanged
through those test repairs, so their successful full build/audit remains exact.

Integrity: authenticated prior approved1957 source snapshot;3152 Foundation/root
files,3151 Foundation modules,3150 root-reachable (only AxiomAudit unrooted).
Only the new leaf/root import/persisted audit change mathematically. All older
source bytes,3 configurations,113 archive originals,21 Yang-Mills originals,
Cauchy original, numerical tools and paused1945 scratch remain unchanged.
ResearchSources is immutable and uncommitted; no manuscripts/PDF/README changes.
Exact Git approval, guarded two-branch synchronization and independent remote
confirmation are recorded separately. Repository is PUBLIC under exclusive user
visibility control; never change it. Previous goal-turn classification: PROGRESS
in1956 queue update and1957 actual-process construction; the brief confirmation
turn added no mathematical change, and this turn resumes the unfinished1958
test/verification checkpoint. No new goal, session or automation.
