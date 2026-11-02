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
