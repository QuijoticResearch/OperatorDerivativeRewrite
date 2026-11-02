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
