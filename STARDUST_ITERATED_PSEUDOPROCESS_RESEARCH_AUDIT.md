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
