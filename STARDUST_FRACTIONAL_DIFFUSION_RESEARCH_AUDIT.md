# Fractional diffusion — ACTIVE research audit

Checkpoint1964, November2,2026: explicit user transition from Yang–Mills.
Full objective remains in STARDUST_FRACTIONAL_DIFFUSION_QUEUED_AUDIT.md.
Read-only inventory confirms ResearchSources/fractional_diffusion/main.tex,
70018 bytes, SHA2564726071a1433b7645d2c2504188c3f41dc65b9073ea3ee20d22fd11ca53cb130.
It agrees with the original1292 inventory. No claim is verified by inventory.

First research obligation: selectively extract title/abstract/main claims and
compare exact operator domains, covariance/process hypotheses, fractional
kernels and convergence against existing Lean declarations. Reuse earlier
Cauchy, IBM, pseudoprocess, closed-integral and Gaussian results only when all
hypotheses hold. Prioritize a substantive theorem or decisive counterexample.
No new fractional-diffusion theorem is claimed at activation. Do not create,
revise or compile publication drafts/PDFs; original research sources stay intact.

## Checkpoint1965 — a genuine noising-transfer repair and two source-level calibration failures

Fractional diffusion remains ACTIVE. Previous goal turn is PROGRESS: user
transition1964 committed at115681d972395e419ab876c9eed69426b12b75f2 and
independently verified on BOTH PUBLIC branches. Yang–Mills is PAUSED/INCOMPLETE;
its46 locally archived draft/evidence files and every earlier return point
remain unchanged. No campaign reorder or publication-agent work occurred.

The immutable source is ResearchSources/fractional_diffusion/main.tex, SHA256
4726071a1433b7645d2c2504188c3f41dc65b9073ea3ee20d22fd11ca53cb130.
Selective review covered title/abstract/standing assumptions, A–D statements,
linear-factorization argument, transfer lemma, OU corollary, GFDM kernel and
convergence proof sketch, and the formalization-status section. The source
correctly distinguishes a matching-marginal auxiliary from a pathwise fBM
reversal and explicitly labels its concrete Lean theorems unformalized. Those
qualifications are retained. Source text is evidence, never agent instruction.

1. The claimed equivalence between Wiener-integrand transfer and the ordinary
L2 adjoint of the path Volterra operator is FALSE literally (source lemma
volterra-transfer, lines522–540). At H=1/2, Kf(t)=integral_0^t f(s)ds. Its
ordinary adjoint kernel applied to 1_(0,T] is (T-s)1_(0,T], whereas the actual
Brownian Wiener transfer of 1_(0,T] is 1_(0,T]. The scalar unit pairing is
1/2 versus1. Foundation.FractionalNoisingTransfer proves both functions in
actual Lebesgue L2, and transports them through the EXISTING isonormal source.
The mistaken replacement produces the actual Bochner time integral of the
constructed Brownian motion, not its endpoint. In genuine observable L2:
 ||wrong(T)-W_T||^2 = T^3/3-T^2+T >= T/4.
Thus they differ at EVERY positive time, including horizons where their
variances might happen to agree. At T=1 their variances are1/3 and1.
The lemma's displayed compensated transfer formula is not refuted by this:
the false part is its identification with the ordinary path-operator adjoint.
No new bounded full Volterra operator on L2 is constructed; the kernel and
literal scalar-adjoint pairing test supply the decisive counterexample.

2. The GFDM alpha normalization drops c(t) between source remark gfdm-rep
and equations gfdm-solution/alpha-def (lines510–520). The original cited
Nobis et al. arXiv2310.17638v3 Proposition4.2, equations12–13 and A.3,
equations39–40, put c(t) OUTSIDE the Brownian integral. Their variance is
c(t)^2 integral alpha^2. To compare with the source's already scaled beta,
use alpha_tilde=c(t)*alpha, or retain the outside c(t) consistently. This is
not a discrepancy resolved by citing Ito isometry. Lean normalization_energy
proves actual Gaussian energy scales by c^2; at c=2 the variances are4 and1.
Primary comparison: https://arxiv.org/html/2310.17638v3#S4 and Appendix A.2.
No novelty is claimed for this classical normalization or the adjoint test.

Positive repair, reusing existing GaussianHilbertProcess,
GaussianDeterministicIntegral and FractionalForcingKernel, without duplicating
stochastic foundations: for a time-Hilbert kernel curve k_s and weights f,q,
set a=f(T)k_T-integral_0^T q(s)k_s ds. Explicit Bochner interval integrability
is required. The actual observable f(T)W(k_T)-integral q(s)W(k_s)ds equals
W(a), has the proved centered Gaussian law with variance ||a||^2, and belongs
to the ORIGINAL closed cylindrical derivative graph with derivative a tensor1.
When q=f' and k_0=0 this is the appropriate integration-by-parts construction;
the generic theorem itself does not assume or prove a pathwise stochastic
integral identification, nor actual C1 weighted Type-II domain membership.

For TWO curves on the SAME Gaussian source, with uniformly bounded kernel
error epsilon on[0,T] and |q|<=M, the observable error is at most
 (|f(T)|+T*M)*epsilon.
weighted_convergence proves actual observable L2 convergence from those exact
hypotheses and epsilon_n->0. This is a rigorous sufficient topology, not a
claim that terminal-only L2 error or a marginal-law coupling suffices. The
GFDM approximation hypotheses and cited rates still need independent checking.

The Gamma-normalized Type-II constant-noising variable is the EXISTING actual
fractional response at alpha=H+1/2. typeII_energy verifies for every H>0:
 E[B_T^2]=T^(2H)/(Gamma(H+1/2)^2*2H), and typeII_brownian identifies H=1/2
with the original Brownian variable. No stationary-increment Type-I covariance
or uniform-in-H estimate is imported into the Type-II problem.

Verification:258 lines,30 public theorems+4 definitions; all34 canonical types
and complete proofs reviewed;7379-job complete root build, full namespace
transitive standard-three axiom audit,20 Lean boundary checks and persisted
AxiomAudit passed. Independent exact rational diagnostics:48 Brownian pairing/
energy tests,240 polynomial power-kernel integration-by-parts tests,60 singular
power cancellation tests,18 normalization tests (366 total). These diagnostics
do not prove stochastic convergence or general singular integration. Earlier
failed elaboration logs are preserved; no resource/trust options were changed.

Remaining substantive obligations: identify the corrected C1 Type-II Wiener
integral on its actual native domain, prove weighted-kernel convergence under
the actual GFDM norm/rate assumptions, prove a concrete Gaussian-mixture score
with data/driver independence and differentiation domains, and audit the
nonlinear predictable projection/Clark-Ocone claims. Existing stationary-fBM
obstructions cannot be instantiated as Type-II counterexamples without a new
covariance/domain bridge. The source's SA8 superposition/time-reversal and
endpoint hypotheses remain hypotheses, not a completed sampler construction.
No fractional-diffusion campaign completion is claimed.

Integrity:all3155 Foundation/root source hashes accounted for; only the new
leaf, root import and persisted audit changed.3154 Foundation modules,3153
root-reachable; only AxiomAudit is unrooted. All3 configurations,113 original
archive entries,21 Yang–Mills originals, Cauchy original, fractional original,
paused Cauchy/pseudoprocess/Yang–Mills artifacts and earlier tools preserved.
Exact audited BOTH-branch backup is required; completion is recorded in the
local terminal receipt only after independent remote verification.

## Checkpoint1966 — the actual noising convergence topology; adapted counterexample and direct domain reuse

Fractional diffusion remains ACTIVE. Previous goal turn is PROGRESS:1965 was
fully verified, committed atd62a6db7d9488f8935567ae99b608471a154fdfe and
independently backed up on BOTH PUBLIC branches at19:08:56.218597Z. Preserve
all Yang–Mills/pseudoprocess/IBM/Bakry/Cauchy pauses and unresolved A2 status.
No campaign priority or original source changed.

VERIFIED Foundation.FractionalNoisingTopology,162 lines,14 theorems and3
definitions, reuses1965's actual isonormal realization rather than constructing
another stochastic foundation. Write e_s=k_s-l_s for two deterministic kernel
curves coupled through the SAME original Gaussian source. For their actual
integration-by-parts observables A_k,A_l, with q=f' when used for C1 noising:
 ||A_k-A_l||_2 <= |f(T)|*||e_T|| + ||q||_{L2(0,T)}*||e||_{L2(0,T;TimeHilbert)}.
The hypotheses explicitly retain interval integrability of both q*k and q*l,
MemLp q2 on(0,T], and MemLp e2 on(0,T]. This is weighted_L2_bound. The
new same_source_error theorem identifies the last energy with the actual
time-integrated Gaussian observable mean-square error; it is not a comparison
of arbitrary marginal couplings. weighted_L2_convergence proves actual
observable L2 convergence when BOTH endpoint error and integrated-time RMS
error tend to zero. No new smoothness assumption is silently inferred.

This directly sharpens the1965 sufficient uniform-kernel topology toward the
norm used in the cited GFDM optimization: Nobis et al. arXiv2310.17638v3,
Proposition3.3/equation8 optimize integral_0^T E|B_t-Bhat_t|^2 dt.
Primary source: https://arxiv.org/html/2310.17638v3#S3. This objective alone is
not an endpoint estimate. The source manuscript main.tex Proposition
alpha-convergence, lines571–590, does not specify a process norm in its
L2(P) shorthand or derive the needed endpoint/control bridge. Its SA9 weighted
estimate applicability remains an assumption. We do NOT refute the specific
optimized MA-OU sequence, nor claim its cited convergence rate. A valid repair
must establish both terms for that actual sequence or prove a different
sufficient theorem exploiting its special kernel structure.

A concrete negative result uses the ACTUAL constructed Brownian process:
 E_t=(1-t)*B_t.
errorProcess is proved IsGaussianProcess and strongly adapted to the ORIGINAL
Brownian natural filtration; errorL2 has the actual AE coordinate realization
and energy (1-t)^2*t. E_1=0. Its f(t)=t integration-by-parts error functional is
 F=-integral_0^1 (1-t)*B_t dt.
weightedError_actual_integral identifies F with the ORIGINAL predictable Ito
integral of -integratedHermite(q=1-t,n=0,T=1), an actual member of the existing
closed predictable domain. No hypothetical stochastic integral is assumed.
The proof uses the previously verified stochastic-Fubini/Bochner identity;
weightedError_pairing proves <B_1,F>=-1/6, and weightedError_norm_lower gives
||F||_2>=1/6. Thus no finite real C can bound this weighted error by C*||E_1||_2.
This rules out terminal-only control for general genuine adapted Gaussian
noising errors. It is not a counterexample restricted to MA-OU errors. The
Lean declaration proves the integration-by-parts functional and its actual
predictable Ito representation; it does not introduce a separate semimartingale
integration theory for integrating arbitrary weights directly against E.

Direct existing theorem reuse also resolves a separate literal domain error
in main.tex lines286–290. The paper defines D as the FULL closed Skorokhod
adjoint but states F=E F+delta(Pi D F) for every terminal L2 F. At H=1/2,
1965.typeII_brownian identifies the actual Brownian model. Existing
GaussianPredictableDomainGap.terminal_representation_without_full_adjoint
provides an actual terminal-measurable L2 F OUTSIDE that full adjoint domain,
with a genuine predictable representation. no_full_adjoint_pair excludes even
a graph representer. These exact statements are included in the independent
Lean boundary checks; no duplicate counterexample was constructed.

The precise positive repair at the Brownian endpoint is ALREADY verified:
GaussianProjectedDerivativeClosure.projectedGraph_closure proves that the
closure of Pi*D's graph is the bounded original predictable-adjoint graph;
bounded_extension_unique proves uniqueness. Restrict literal Pi*D to its real
full-derivative domain, or explicitly use this completed projected derivative
for all L2. Do not call the extension the original full derivative. The
source's deterministic linear first-chaos factorization is not refuted by
this all-L2 obstruction. No corresponding nonlinear Type-II closure theorem
for H unequal1/2 is inferred, and stationary-Type-I fractional counterexamples
cannot be transplanted without covariance and domain identification.

Complete gates:7380-job root build, whole namespace transitive standard-three
axiom audit, all17 canonical types and entire162-line proofs/definitions,
20 independent Lean checks (including the exact old domain/closure theorems),
persisted AxiomAudit, and source-integrity checks passed. Independent exact
rational diagnostics passed400 polynomial Holder/weighted-error inequalities,
32 Brownian triangular covariance tests, and41 terminal-bound constant tests
(473 total). The candidate exact variance1/20 is a diagnostic only; the new
Lean theorem proves the nonzero pairing and norm lower bound, not that full
triangular-kernel identification. Targeted elaboration repairs, including
standard real-module instance conversion, are retained; no trust/resource
settings, versions or original mathematical results were changed.

All3156 Foundation/root sources accounted for:3155 Foundation modules,3154
root-reachable, only AxiomAudit unrooted. Only the new leaf/root/persisted audit
changed.3 configurations,113 archive originals,21 Yang–Mills originals,
Cauchy/fractional originals, all46 archived Yang–Mills artifacts and earlier
paused work/tools are byte-preserved. ResearchSources stays uncommitted.

Next substantive bottleneck: for the actual common-Brownian MA-OU convolution
kernel error e(u), time-integrated process error corresponds formally to
integral_0^T (T-u)*|e(u)|^2 du, whereas endpoint error is integral_0^T |e(u)|^2 du.
The weight degenerates near u=T. Prove the exact stochastic-Fubini identities
and determine whether the actual optimized exponential sums supply the missing
endpoint control; no conclusion from these formal expressions alone. Preserve
the remaining native C1 Type-II integration, Gaussian-mixture score/data
independence, GFDM rate, nonlinear projected closure, weak auxiliary/time
reversal and endpoint obligations. No campaign completion or novelty claim.
Exact audited BOTH-ref backup is recorded only after independent verification.

## Checkpoint1967 — actual MA-OU/Type-II interior convergence; endpoint obstruction retained

Fractional diffusion remains ACTIVE. Previous goal turn is PROGRESS:1966 was
fully verified, committed at106c375ab7195aebdb18f4feb172cd41f5bbeaa1 and
independently BOTH-branch backed at19:25:32.170831Z. No paused campaign resumed.

The new Foundation.FractionalMAHorizon gives a concrete positive repair to
the manuscript's GFDM kernel-convergence argument, rather than extrapolating
the generic1966 counterexample. Use the ORIGINAL common-Brownian variables
Y_t^gamma from GaussianExponentialMarkovPrediction.value and the actual
Gamma-normalized Type-II variable from FractionalNoisingTransfer.typeII.
For every finite number n, every REAL weight vector w, every NONNEGATIVE rate
vector gamma (including the Brownian zero-rate limit), and every H>0, define
 E_t=sum_i w_i*Y_t^(gamma_i)-B_t^H.
actual_error proves this exact identity on the existing Gaussian product.
No independent OU coordinates or fitted covariance surrogates are substituted.
For0<H<1 this is the precise Type-II normalization in the source manuscript.
The larger H>0 range is valid for the already constructed RL kernel; it does
not extend stationary-increment fBM claims beyond their actual range.

The explicit L2 lag error is
 e(u)=sum_i w_i*exp(-gamma_i*u)-u^(H-1/2)/Gamma(H+1/2).
errorVector_coeFn and error_energy prove, with actual integrability,
 ||E_t||_2^2=integral_0^t e(u)^2 du.
The error is centered. Its deterministic positive-time input belongs to the
ORIGINAL fullPredictable space; error_native_integral identifies its actual
Ito integral with E_t. error_source_derivative proves membership in the
ORIGINAL closed Gaussian source derivative graph with the exact kernel tensor1.
This is Brownian SOURCE calculus, not an identification with intrinsic D_BH.

Consequently the actual squared error V(t) is NONDECREASING. This is a
special convolution structure; the earlier arbitrary adapted counterexample
E_t=(1-t)B_t need not have it. Time integrability of V is proved from monotonicity,
not assumed. Positivity and averaging now give the useful quantitative bridge:
 (S-t)*V(t) <= integral_0^S V(s)ds, for0<=t<=S;
 V(t) <= [integral_0^S V(s)ds]/(S-t), for t<S.
The bound is uniform over0<=t<=t0<S with denominator S-t0. It is uniform
pointwise mean-square control, NOT an L2 norm of a sample-path supremum.
actual_interior_convergence proves strong actual Gaussian L2 convergence of
the errors from time-averaged mean-square convergence, for ANY sequence of
finite weights/rates satisfying that explicitly stated premise. No geometric
grid, positivity of weights, optimality or convergence rate is presumed.

weighted_actual_interior_convergence reuses1965's verified same-source
weighted-observable transfer. Under its explicit Bochner integrability domains,
bounded q on[0,t], and averaged driver convergence on the LARGER horizon S>t,
the actual integration-by-parts noising observables converge in Gaussian L2.
For C1 noising q=f', this is the correct deterministic filter. The native
Type-II stochastic-integral identification and automatic discharge of those
Bochner domains for the manuscript's full C1 class remain separate obligations.
The result does not construct a Markov auxiliary, reverse SDE or path-space limit.

Primary-source calibration: Nobis et al., arXiv2310.17638v3, Proposition3.3/
equation8 uses time-integrated mean-square approximation error. AppendixA.1,
equation22 and the Type-II restriction after it use the same Gamma prefactor
in the positive-time Brownian integral. Exact sources:
https://arxiv.org/html/2310.17638v3#S3 and
https://arxiv.org/html/2310.17638v3#A1.
The new bridge rigorously transfers that TYPE of error to strict interior
times. It does not prove the specific Daems optimal coefficients have vanishing
averaged error or the manuscript's quoted exponential rate. To use the endpoint
T in the source's evaluation interval[epsilon,T], either establish approximation
on a genuinely larger horizon S>T or supply an additional terminal estimate.
The factor1/(S-T) is visible; no endpoint limit in this constant is taken.

A verified obstruction shows why the strict boundary cannot simply disappear
from an averaging-only argument. Reuse GaussianPowerVolterra to construct
 Z_n(t)=sqrt(2n+1)*W((t-s)^n*1_(0,t](s)).
The spike declarations prove endpoint energy1, averaged unit-horizon energy
1/(2n+2)->0, and failure of EVERY finite uniform endpoint-energy comparison.
These are actual Gaussian L2 variables on the original source. This is a
counterexample in the LARGER higher-integrated Gaussian Volterra class, not a
counterexample specifically to the optimized MA-OU sequence or fixed-H fBM.
It strengthens the trace obstruction without discarding the positive interior
result. No optimality claim is made for the interior comparison constant.

Verification:285 lines,23 public theorems and8 definitions; all31 canonical
types and entire proofs reviewed.7381-job complete root build, full namespace
transitive standard-three axiom audit,22 Lean boundary checks and persisted
AxiomAudit passed. Tests include empty MA sums, all actual domains/native graphs,
strict/non-strict horizon cases, and exact H=1/2 Brownian normalization.
Independent diagnostics:64 exact rational power-energy checks and144 ordinary
floating checks of OU/RL covariance, derivative, monotonicity, averaged-Fubini
and interior inequalities (208 total). The maximum covariance/derivative/
averaging discrepancies were about2.7e-13/5.4e-11/2.1e-12. Floating diagnostics
are not interval certificates or proofs of rates. mpmath was unavailable;
the original failed diagnostic was preserved and standard-library Simpson/
Taylor calculations used without installing packages or changing the environment.
The double-time Fubini identity was numerically tested; the positive Lean bridge
uses the proved one-time energy identity and monotonicity instead, so does not
rely on an unformalized Fubini claim. All failed elaboration/check logs retained;
no compiler/trust/resource/version or verification settings changed.

All3157 Foundation/root source hashes accounted for:3156 Foundation modules,
3155 root-reachable, AxiomAudit only unrooted. Only the new leaf/root/audit
changed; all3 configurations,113 archive originals,21 Yang–Mills originals,
Cauchy/fractional originals,46 archived Yang–Mills artifacts, earlier tools
and paused work unchanged. ResearchSources remains immutable and uncommitted.

Remaining central obligations: actual optimal-coefficient averaged consistency
and valid rates; exact original finite-GFDM alpha identification with the corrected
weighted construction including c(t); native C1 Type-II transfer and its Bochner
domains; actual Gaussian-mixture score with data independence; nonlinear causal
closure away from H=1/2; conditional weak auxiliary/reverse-process and endpoint
assumptions. Next prioritize automatic native domain/transfer identification
or actual coefficient consistency, not unrelated infrastructure. This is a
classical analytic mechanism with a concrete verified application; no novelty,
complete manuscript repair or campaign completion is claimed. Exact audited
BOTH-ref backup is recorded separately after independent remote verification.

## Checkpoint1968 — actual Type-II weighted domains and finite-horizon native integration

Fractional diffusion remains ACTIVE. Previous goal turn is PROGRESS:1967 was
fully verified, committed ate51993bd97311d70218f5794e4e2d30f4a51be19 and
independently BOTH-branch backed at19:50:30.983268Z. Every paused campaign and
original source remains preserved; no priority or publication-agent change.

Foundation.FractionalConvolutionDomains discharges a substantial domain gap
in1967: actual Type-II and finite MA-OU kernel curves are continuous in the
ORIGINAL Lebesgue time L2 space, and weighted Bochner integrability follows
from CONTINUITY ON THE FINITE WORKING INTERVAL. Neither global continuity of
the weight nor uniform pointwise domination of a singular kernel is assumed.
The rough-kernel singularity near the diagonal is handled in L2.

The precise general hypothesis is an EXISTING family K_t in TimeHilbert with
AE profile1_(0,t](x)*k(t-x), for a fixed real lag function k. This AE convolution
hypothesis is an explicit parameter of convolution_continuous and all generic
weighted theorems; continuity is not smuggled into it. On t<=S, the proved
convolution_projection identity is
 K_t=P_positive[translate_(S-t) K_S],
where translation acts as f(x)->f(x+S-t), and P_positive is the ORIGINAL
orthogonal projection onto the closed supportedL2(Ioi0) subspace. Pointwise
AE support and orthogonality prove the identity, including t=0. Existing
Mathlib Continuous.compMeasurePreservingLp, actual Lebesgue translations and
bounded projection then prove L2 continuity; localize S=t0+1 to cover all
nonnegative times. No new covariance or stochastic law is postulated.

Actual typeII_vector_continuous and ma_vector_continuous instantiate the
1967 AE profiles, for every H>0 and every finite real weight/nonnegative rate
vector. typeII_observable_continuous transfers continuity to the EXISTING
Gaussian L2 realization. These are mean-square continuity results, NOT proofs
of sample-path continuity or equality of observed filtrations.

For every q continuous ON uIcc(a,b), q(s)K_(s.toNNReal) is actually Bochner
interval integrable. The concrete Type-II and finite MA versions retain those
local domains. On a nonnegative horizon T, the profile
 A=f(T)K_T-integral_0^T q(s)K_s ds
belongs to the ORIGINAL closed supportedL2(0,T] space: finite-horizon causality
is proved, not just positive-time support. Its deterministic tensor with the
original gaussianOne belongs to the ORIGINAL fullPredictable input space.
convolution_weighted_native_integral identifies its actual original Ito
integral with f(T)W(K_T)-integral q(s)W(K_s)ds. The original closed SOURCE
Malliavin derivative graph has the exact profile tensor1. No new derivative,
projection or integral was defined to force these equalities.

For genuine C1 noising, use q=f' on[0,T]. The construction itself permits
arbitrary deterministic endpoint function f and interval-continuous q; it does
not claim q=f' automatically. Agreement with the original Type-II deterministic
stochastic Riemann–Stieltjes STEP limit remains a separate obligation. Nor is
the Brownian source derivative identified with intrinsic D_BH. These scope
limits preserve the earlier full-D all-L2 obstruction and causal-space issues.

weighted_interior_convergence_continuous removes ALL extra Bochner-domain
and bound hypotheses from1967's weighted theorem, using only local q continuity
and the actual finite MA/Type-II curves. Its remaining substantive convergence
premise is vanishing time-averaged driver error on a LARGER horizon S>t.
That premise for the specified optimized coefficients and its rate are still
open. The theorem does not cover t=S, reverse-SDE convergence, a path-supremum
norm or a completed repair of every manuscript claim.

Verification:210 lines,18 theorems+2 definitions; all20 canonical types and
entire definitions/proofs reviewed. Complete root build and whole namespace
transitive standard-three axiom audit,20 Lean boundary checks and persisted
AxiomAudit passed. The generic convolution-profile assumption is present in
the canonical printed types; the concrete application types carry no irrelevant
section parameters. Boundary checks include H=1/4, zero horizon, constant
noising and a weight with a jump OUTSIDE the evaluation interval, which is
properly admitted by local continuity. Independent diagnostics:672 exact
rational support/argument translation identities plus64 scalar floating L2
continuity/weighted-energy tests (736 total); worst weighted-energy discrepancy
about7.3e-13. Floating tests are not certificates, step-limit proofs or path
regularity theorems. All failed draft/check logs retained. No trust/resource,
verification, Lean/Mathlib version or compiler settings changed. The newly
used Mathlib continuous-composition theorem is a pinned existing dependency.

Integrity:all3158 Foundation/root sources accounted for,3157 Foundation
modules and3156 root-reachable, with AxiomAudit only unrooted. Only the new
leaf/root/persisted audit changed.3 configurations,113 archive originals,
21 Yang–Mills originals, Cauchy/fractional originals,46 archived Yang–Mills
artifacts and earlier paused work/tools are byte-preserved. ResearchSources
remains uncommitted; no manuscript/PDF/README maintenance occurred.

Next central obligation: prove convergence of actual deterministic C1
stochastic step sums to this native construction, preferably reusing existing
finite Abel/Riemann/continuous-integrand machinery; then identify the correct
transfer kernel including c(t). The proposed Gamma-convolution bridge to
integrated Brownian history is still UNVERIFIED and may support a later
completed observed-past/causal-domain identification. Actual optimized MA
consistency/rates, the Gaussian-mixture score with data independence and
analytic domains, nonlinear Type-II causal closure, and conditional auxiliary/
reverse-SDE hypotheses remain open. This is classical functional analysis
applied to concrete stochastic objects, not a novelty or completion claim.
Exact audited BOTH-ref backup is recorded only after independent verification.
