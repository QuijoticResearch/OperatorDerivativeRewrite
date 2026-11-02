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
