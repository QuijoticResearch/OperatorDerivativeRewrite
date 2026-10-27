# Bakry–Émery/fBM manuscript audit — in progress

Bakry Objective 1 is ACTIVE. This is a partial mathematical audit, not completion
of either primary manuscript or authorization to activate Objective 2. No
sustained follow-on research focus has been selected before the required audits.
Original ResearchSources files are preserved unchanged and remain uncommitted.

## Sources and version distinctions

Primary 1: `ResearchSources/bakry/bakry_emery_part2_v3 (1).tex`, SHA256
`CA06321B1CB426DCAC9BCFE891AB89AF80EEE0BC8B108D1D9741C4059FACD3D7`.
Primary 2: `ResearchSources/bakry/bakry_emery_revised_v8 (2) (2).tex`, SHA256
`53B29C9365C037FEE4F9367C7EFDC4F1C2F30076F8085EFB4DAECFA694B9006D`.
All26 Bakry/fBM files agree with the saved inventory and have18 distinct hashes.
The43 primary theorem/proposition/lemma/corollary/conjecture statements have been
read; complete proofs are examined selectively where a concrete claim warrants it.
Their extraction and provisional version survey are retained in1550 audit evidence.
Reading statements does not certify their proofs or complete their repair.

The unnumbered `fbm/bakry_emery_part2_v3.tex` is DISTINCT from primary1.
The numbered primary adds the analytical-consequences section and explicit
high-chaos decay discussion; its added text cannot inherit validity from the
other version. Primary2 is also DISTINCT from `fbm/bakry_emery_revised_v8.tex`:
its changes clarify finite-dimensional CD versus CD(kappa,infinity), correct
the sign of the displayed cosine drift, and add a Schur-positivity limit argument.
Exact duplicate groups remain in STARDUST_BAKRY_FBM_SOURCE_INVENTORY.json.
Filenames such as final/revised do not establish mathematical precedence.

Early fBM abstracts vary between signed arguments and absolute arguments without
consistently spelling out the same-sign restriction. The newer primary2 does
state it. The related Hurst-curvature manuscript compares BASE R^-1 R^j with
ADJACENT (R^(j-1))^-1 R^j; these have different spectra, not competing formulas
for the same operator. Its IBM/pseudoprocess/RH and numerical global re-entry
claims require independent hypotheses and do not activate those campaigns.
The Yang–Mills bridge abstract is recorded for its later bounded audit; a
single-link or finite lattice bound supplies no continuum mass-gap theorem.

## Genuine verified mathematics reused

- FractionalSpectralGeometry.normalized_inner and covariance_positive provide
  the actual normalized Hurst covariance and its Hilbert realization for0<H<1.
- FractionalCovarianceMatrices.covarianceMatrix_posSemidef and
  covariancePower_posSemidef prove covariance and integer Hadamard powers are
  positive semidefinite. They do not identify a Gaussian OU generator with a
  fractional Fourier generator.
- BrownianCovariancePowers.covariance_factorization and generalized_eigenpair
  give the actual Brownian innovation factorization and comparison eigenpairs.
  Its comparisonRatio distinguishes adjacent-level ratios from base-level
  innovation values. Full determinant/asymptotic statements need their own proofs.
- GaussianOUCore.gamma_formula and gammaTwo_formula concern the actual Gaussian
  OU polynomial generator; shared Gamma terminology does not transfer them to
  the stable generator without an identification theorem.

## Repaired obstruction 1: universal subordination monotonicity

Primary1, cor:sub at line1279, says kappa(alpha gamma)<=kappa(gamma) for every
alpha in(0,1), gamma in(0,2). Its rationale combines a unique maximum at1 with
alpha gamma<gamma; that does not give monotonicity across the maximum.

`Foundation/FractionalCurvatureSubordinationObstruction.lean` uses the ORIGINAL
covarianceMatrix at H=3/4 and times1,2, not an arbitrary replacement kernel:

    R = [[1,sqrt2],[sqrt2,2sqrt2]], P = R Hadamard R = [[1,2],[2,8]],
    v = (1,-1/8), v'Rv = 1-7sqrt2/32 >0, v'Pv = 5/8,
    v'(P-R)v = (7sqrt2-12)/32 <0.

Thus a valid curvature lower bound at gamma3/2 must be strictly below1.
At H=1/2 the same two-point forms have sharp bound1: P-R=diag(0,2).
Subordination alpha2/3 moves gamma3/2 to1. The verified
universal_subordination_incompatible theorem states precisely that ANY proposed
curvature function satisfying kappa(1)=1 and the necessary witness inequality
cannot also satisfy the manuscript's universal monotonicity.

This is an unconditional contradiction between the manuscript's proposed
properties, with explicit actual covariance evidence. It is not a newly
constructed full-domain fractional generator or proof of all proposed global
curvature values. The corrected safe statement is that subordination CAN
increase this curvature comparison; general monotonicity on either side of1
requires further proof. Other flow assertions must be revisited:0 is not a
fixed point INSIDE(0,2), and a discrete orbit need not hit1 exactly.

## Repaired obstruction 2: curvature eigendirections are not decay channels

Primary2, prop:refined at line1413, uses Cauchy curvature eigenvalues2k-1 as
independent semigroup energy rates2(2k-1). This fails already on two frequencies.
`Foundation/BrownianCurvatureModeDecayObstruction.lean` proves:

    R = [[1,1],[1,2]], P = [[1,1],[1,4]],
    e=(1,0), w=(-1,1), P w = 3 R w, e'R w=0,
    v=(v0+v1)e+v1 w, E_3(v)=v1^2.

The mode w is the EXISTING Brownian differenceVector. The exact Cauchy Fourier
coefficient flow is diag(exp(-t),exp(-2t)); its semigroup law is verified.
For EVERY v, E_3(P_t v)=exp(-4t) E_3(v). In particular, v=(0,1) contradicts
the claimed exp(-6t) upper bound at EVERY positive time. Independent tests
also verify R M=P for M=[[1,-2],[0,3]], and M fails to commute with the actual
coefficient generator diag(-1,-2).

This is a precise finite-core coefficient obstruction under the manuscript's
own generalized-curvature eigenspace interpretation. No new infinite-domain
or stochastic-process realization is asserted. A valid curvature lower bound
and a valid generalized eigenvalue list do not supply these individual decay
channels. Retain the true coefficient multiplier rate; further refined estimates
need an invariant decomposition or a justified coupled evolution.

The summed, spatially integrated estimate in the same proposition is a
SEPARATE obligation and is not refuted by the component counterexample. In the
two-frequency phase-averaged coefficient model, its excess is
b^2 q (1-q)^2>=0, q=exp(-2t). A meaningful independent Lean check verifies this
polynomial positivity; full torus integral/component identification and a
general-N corrected proof remain to be constructed. Preserve this positive
repair route rather than rejecting the entire proposition from its false
individual-channel inference.

## Remaining central obligations — neither primary audit is complete

| Claim family | Exact remaining requirement |
| --- | --- |
| Operator realization, primary1 lines438–588 | Specify deterministic first-chaos adjoint versus full random-integrand Malliavin derivative, real/complex Hilbert domains and complexification. An adjoint of H->L2 is H-valued; a random derivative requires a different declared domain. |
| Gamma_k/Fourier/tensor dictionary | Prove finite Fourier recursion and tensor Gram identification in matching domains; covariance PSD alone is insufficient. Restrict adjacent comparisons to nonsingular denominator powers, normally k>=2. |
| Brownian determinant, ratios and volume | Reuse exact innovation comparison; prove the needed full basis/spectrum/determinants/asymptotics. Handle N=1 separately for strict determinant decrease and maximum off-diagonal correlation. Specify real versus complex volume dimension. |
| FiniteN high-chaos convergence | Audit denominator control, explicit constants and N dependence; finiteN asymptotics do not imply a dimension-uniform limit or convergence to a Gaussian process law. |
| Integrated energy hierarchy | Separate diagonal Fourier Sobolev energies from pointwise covariance eigenvectors. Check zero observable/nonzero denominator, k=1 singular base power and sharp decay constants. |
| Primary2 full-domain curvature | Preserve positive-frequency versus real test spaces, topology/closure gates and the explicitly conditional Z-matrix hypothesis. A numerical bound throughN200 is not a proof for allN. |
| Cauchy cosine-drift scalar shift | Audit actual generator recursion, Hermitian convention, cross-sign extension and boundary frequencies. Do not presume this identity false; special first-harmonic structure may make it valid. |
| Poincare/gradient/entropy consequences | Construct/identify invariant measure and semigroup domains; justify all approximation/closure steps. Diffusion entropy chain rules cannot be silently used for a jump generator. |
| Actual fBM/chaos implications | Match process laws, Gaussian versus non-Gaussian structure and factorial normalization; covariance/tensor identities do not alone identify stochastic generators or integration domains. |

## Preliminary primary-literature audit, accessed October26,2026

Spener–Weber–Zacher's result concerns the fractional Laplacian on R^d and
failure of CD(kappa,d) for FINITE dimension parameter d; it does not itself
settle an infinite-dimensional condition on the torus. Do not confuse that
dimension parameter with the manuscripts' Fourier cutoff N.
[The Fractional Laplacian has Infinite Dimension, arXiv1903.00521v3](https://arxiv.org/abs/1903.00521v3).

The author's public Part-I page is presently version2, revised March4,2026,
with a more qualified abstract describing Fourier subspaces and a drift shift.
Its source-byte identity with the archived February v8 file is not assumed;
publication existence is not proof of any claim.
[Bakry-Emery Curvature of the Fractional Laplacian via Fractional Brownian Covariance, arXiv2602.19192v2](https://arxiv.org/abs/2602.19192v2).

This is a preliminary source/scope audit, not a completed novelty survey or
claim of priority. No publication, upload or archive modification is authorized
or performed. Objective 1, its full audits and selected later focus remain active;
Objective 2 and every later campaign remain queued under the saved gates.

## Checkpoint1551 — finite integrated-energy repair

`Foundation/BrownianEnergyRepair.lean` supplies a positive repair of the separate
summed estimate in primary2 prop:refined (original line1413), with explicit
energies. For a finite complex vector a indexed by n=1,...,N, define the
Brownian Gram energy using the original matrix R_nm=min(n,m) and difference
characters on the normalized torus. Its actual integral is sum_n n|a_n|^2.
Define the r-th tail energy as the squared modulus of the Fourier sum over
n>=r; its actual integral is sum_{n>=r}|a_n|^2. The rank-one tail matrices sum
exactly to the original Brownian covariance, with no alternative kernel used.

`Integrated.actual_integrated_energy_repair` proves for every finite a and real t:

    average BrownianEnergy(exp(-n t) a_n)
      <= sum_{r=1}^N exp(-2(2r-1)t) average TailEnergy_r(a).

The proof uses convexity of exp and the exact innovation sum, followed by finite
sum rearrangement and actual torus integration. `Torus.tailEnergy_square`
identifies the tail functions as nonnegative squared moduli; `gramEnergy_average`
is a general complex-coefficient integral identity. `brownianMatrix_original`
identifies the old verified covariance and `tailMatrix_sum` its decomposition.
This discharges the previously open general-N coefficient and actual-integral
repair obligations. The scalar proof even holds at negative times on finite
polynomials; this is not a bounded backward semigroup on a completed domain.

This does NOT restore the false individual component decay. The manuscript's
undefined E_k must be corrected to explicit phase-dependent tail energies for
this theorem. Identification with an intrinsic covariance-orthogonal projection,
the actual generator's Gamma recursion, full operator domains and infinite-series
closure remain distinct obligations. Both primary audits remain incomplete;
Objective2 and all subsequent campaigns remain queued. No novelty is asserted.

## Checkpoint1552 — deterministic adjoint domain repair

Primary1 eq:adj defines the adjoint of the deterministic integral H->L2.
`Foundation/GaussianDeterministicAdjointDomain.lean` uses the actual existing
Gaussian first-chaos isometry and its bounded Hilbert adjoint. This H-valued
operator recovers first chaos (`deterministic_first`) and kills Wick orders
other than one (`deterministic_wick_other`). The first-chaos realization claim
therefore survives; the manuscript must explicitly complexify its real energy
space/operator before inserting complex Fourier coefficients.

For quadratic Wick observables, the existing closed Gaussian derivative has
squared norm4||h||^4 and is nonzero for h!=0. The deterministic adjoint vanishes.
`deterministic_lift_not_closed_gradient` proves its constant-field lift is not
in the closed derivative graph for that same observable. This is an operator-
domain distinction, not a failure of the verified Gaussian calculus.

`quadratic_duality_not_unique` proves that zero and the true nonzero quadratic
gradient both satisfy the manuscript-style pairing against ALL deterministic
directions. Thus its displayed expectation relation cannot uniquely define a
RANDOM gradient. Correct scope: either retain the bounded H-valued adjoint or
use the existing closed random-field derivative and full divergence domain.
`FractionalGaussianProcess.value_derivative_graph` already supplies the actual
fBM first-chaos derivative; no replacement process construction is needed.

This resolves a precise domain ambiguity and blocks an unjustified extension.
It does not refute thm:realization restricted to first-chaos inputs. Complex
energy-space identification, finite Fourier Gamma recursion, completed generator
domains and the other manuscript claim families remain open. Objective1 remains
active; no subsequent campaign or mathematical priority changes.

## Checkpoint1553 — actual finite stable Gamma and complex energies

`Foundation/FiniteStableGamma.lean` now constructs the finite Fourier multiplier
L(single(k,c))=single(k,-a(k)c), starting from a real symbol. Gamma_0 is the
conjugate-product and Gamma_(n+1) is the actual half-generator commutator from
primary1 eq:Gammak-def. `Core.gammaIter_single` and `gammaIter_finite` prove
its all-order kernel-power formula, including conjugation and signed frequency
differences, for arbitrary finite sums. `stable_gamma_synthesis` evaluates the
identity as an actual trigonometric function in the existing synthesis algebra.

For a(k)=|k_0|^gamma, `Bridge.stable_gamma_energy` identifies the recursive
expression with the existing covariance-power energy at signed times k_0,
using complex phase coefficients c_i character(k_i,x). `ComplexEnergy.energy_re`
splits this into real and imaginary coefficient forms; symmetry gives reality.
The old real Hadamard positivity theorem therefore yields
`Bridge.stable_gamma_nonnegative`: every finite synthesized Gamma order is real
and nonnegative at every point for0<gamma<2. Empty/repeated/signed-frequency
families and arbitrary complex coefficients are included. Axis modes give the
circle construction; the ambient multiplier acts only in coordinate0.

This resolves the finite Fourier recursion and complex quadratic-form/phase
identification in the earlier obligation table. The absolute-time covariance
version still needs same-sign frequencies; opposite Cauchy frequencies have
kernel0 whereas their absolute-time covariance is1. The algebraic formula alone
has no unrestricted positivity implication: H2 coefficients(2,-1) give energy-12.

No completed generator-domain theorem, constructed complex Hilbert adjoint,
positive curvature constant, invariant drift measure or infinite-series closure
is inferred. Tensor Hilbert-space realizations and Gaussian higher-chaos claims
must still have their exact domains/normalizations checked. Both primary audits
remain incomplete and Objective1 active; no queued campaign starts. No novelty
claim is made. Source manuscripts and their original hashes are unchanged.

## Checkpoint1554: finite sine-drift scalar identity established

Primary2 eq:drift-scalar/thm:global-drift finite-core identity now has exact Lean
support in Foundation/CauchySineDrift.lean. With A=-|n| and T=-sin(x0) d/dx0,
for ALL real r, finite complex Fourier f,g and x:
Gamma1_(A+rT)(f,g)=Gamma1_A(f,g),
Gamma2_(A+rT)(f,g)(x)=Gamma2_A(f,g)(x)+(r*cos(x0)/2)Gamma1_A(f,g)(x).
Use cauchy_scaled_drift_scalar_shift_synthesis; r=omega^2 is the manuscript
parameter. Actual finite algebra/product/derivative/conjugation and synthesis
are used. All signed and zero frequencies are handled, not just analytic modes.

Full6798job build, complete50587-declaration axiom audit,34unabridged publictypes,
28proofs/6definitions,6independent Lean checks,5208 exact finite computational
checks,2625source/config3/archive113 integrity passed. Exact checkpoint receipt
and guarded private backup follow. Detailed timing/evidence in report1554.
No invariant measure, entropy inequality, completed generator domain, or global
spectral theorem follows automatically. Both primary manuscript audits remain
incomplete. The computational quadratic-symbol test yields cos rather than
half-cos correction and blocks an unqualified transfer to other stable orders.
Preserve original manuscript bytes and all earlier counterexamples/repairs.

## Checkpoint1555: drifted uniform-measure Poincare claim refuted

Primary2 mu is normalized Lebesgue (204-205,336), E_L=-integralfLf (477-480),
and the unrestricted real-trigonometric Poincare assertion occurs1173/1392.
Foundation/CauchyDriftUniformObstruction.lean gives actual normalized circle
integrals for f=2+cos, omega^2=1: variance1/2, energy-1/2, meanLf1/2.
The claimed kappa1/2 estimate would say1/2<=-1. More strongly,
`no_uniform_poincare` rules out EVERY nonnegative constant multiplying this
uncentered energy on all real finite Fourier polynomials. Uniform generator
invariance also fails (`uniform_not_invariant`). This is a rigorous finite-domain
counterexample, not a numerical guess or an assumed covariance interpretation.

Checkpoint1554's actual drifted Gamma scalar identity remains VALID. The flaw
is treating uniform mu as though it supported the invariant-measure energy
argument. Mean-zero/centered-energy repairs and a genuinely constructed invariant
measure are distinct outstanding tasks; no Gibbs law or entropy result follows
without proof. The pointwise gradient estimate is not refuted by this witness.

Full6799job build,50610safe transitiveaxiom audit,17publictypes/15proofs/2defs,
5independentLean tests and24exact rational tests passed;2626sources/config3/
archive113 intact. Detailed logs/timing/receipt gates in ledger1555. Bothprimary
audits INCOMPLETE. Preserve originals, fullqueue and all previous results.

## Checkpoint1556: rigorous centered-energy repair of the drift Poincare claim

Foundation/CauchyCenteredEnergy.lean proves exact actual circle drift IBP and
finite signed-frequency free energy, then `centered_axis_poincare`:
Var_uniform(a+p) <= E_r(p)/(1-r/2),0<=r<2, where p is explicitly presented by
arbitrary distinct NONZERO integer modes and its synthesis is real. circleCenter
is actual mean subtraction; the theorem uses E_r(center(f)), not E_r(f).
All actual integration/normalization/injectivity/realness hypotheses are explicit.
This is a valid finite-core correction to primary2 lines1173/1392;1555's
uncentered counterexample remains valid. No3torus transversegap, sharpness,
completed domain, invariantmeasure, semigroup or entropy conclusion is inferred.

Full6800job build,50649safe transitiveaxiom audit, all25types/22proofs/3defs,
6independentLean checks,405exact rational checks passed;2627sources/config3/
archive113 intact. Exact receipt and guardedprivatebackup follow. Detailed
scope/evidence/timings in ledger1556. Bothprimaryaudits incomplete; Bakry1ACTIVE.


## Checkpoint1557 — actual Gaussian chaos realization of finite stable Gamma

Bakry Objective 1 remains ACTIVE; both primary manuscript audits remain incomplete.
Primary1 `bakry_emery_part2_v3 (1).tex`, definitions tensor/lift and
lem:gram/thm:realization/thm:tensor (452–598), uses a real tensor domain with
complex phase coefficients. The real Gram identity is valid; complex coefficients
require a specified complexification or a real Hilbert realization of both parts.

`Foundation/FractionalGammaChaosRealization.lean` provides the latter explicitly.
For actual Gaussian directions h_i, define W_n(h)=wick(h,n)/sqrt(n!). Its inner
product is <h_i,h_j>^n. Real finite sums lie in chaos sector n; distinct sectors
are orthogonal. Complex coefficients are represented by their real and imaginary
sums in PiLp 2, whose norm is the sum of squared component norms, not a sup norm.
Using actual FractionalGaussianProcess directions, 0<H<1, and nonnegative times
t_i matching the first integer frequency coordinate, `actual_gamma_realization`
identifies the FULL complex synthesized Gamma_n for stable order 2H with the
real squared norm of this representative. All n>=0 and finite complex coefficient
families are covered, including dependent/zero directions. No injectivity assumed.

`complexLift_one_derivative_energy` identifies order-one energy with the sum of
the actual deterministic adjoint derivative energies of the two components.
`higherLift_deterministic_derivative` proves this adjoint annihilates every other
sector. It is not the full random-field Malliavin derivative. The unit-direction
second-Wick norm is 2 before normalization and 1 after it. This factorial is
needed for the NEW Wick realization; it is not a missing factor in the original
tensor Gram identity, which does not use Wick polynomials.

No completed complex tensor-product isometry, stable/Gaussian OU generator
identification, arbitrary signed-time fBM realization, new covariance law,
optimal curvature, invariant measure, semigroup or entropy theorem is claimed.
This is direct reuse of existing Gaussian Wick, actual fBM, finite Gamma and
adjoint machinery supporting the primary manuscript audit, not early activation
of the queued Hermite-process campaign. No novelty claim is made.

Verification: full root6801 jobs39.579s; complete50684 safe-declaration transitive
axiom audit39.858s, only propext/Classical.choice/Quot.sound. All21 public types,
17 proofs and4 definitions/abbreviations reviewed unabridged; no private proof,
new option, local instance, sorry or axiom. Five independent Lean checks26.434s
cover imaginary coefficients, zero directions/order zero, quadratic adjoint
failure, duplicate-direction cancellation and cross-order orthogonality.
539 independent exact rational bivariate Gaussian moment tests through order6
include negative correlation, singular covariance and unequal variances.
2628 Foundation/root sources frozen; configuration3 and archive113 verified.
Primary hashes remain CA06321B1CB426DCAC9BCFE891AB89AF80EEE0BC8B108D1D9741C4059FACD3D7
and53B29C9365C037FEE4F9367C7EFDC4F1C2F30076F8085EFB4DAECFA694B9006D.
Evidence: `.lake/stardust-1557-{working-checkpoint,verification}.json`, complete
full-build/audit/independent logs and independent-moments.json. Local gates PASS;
exact commit receipt and guarded BOTH-private-ref synchronization follow this
entry; never infer remote closure from this pre-commit record alone.

Next: remaining primary tensor/curvature domain qualifications and spectral,
determinant/volume, completed-semigroup and invariant-measure/entropy claims.
Preserve all earlier counterexamples, source bytes and full queue. IBM remains
deferred/incomplete1547; no campaign transition or reflection session admitted.


## Checkpoint1558 — actual complex ellipsoid volume correction

Bakry Objective1 ACTIVE; both primary audits remain INCOMPLETE. Primary2
`bakry_emery_revised_v8 (2) (2).tex`, cor:volume/eq:volume-ratio, lines1441ff,
claims sqrt(det M) for Gamma coefficient ellipsoids on T_N^+. Its proof is
the real N-dimensional ellipsoid formula, whereas its Fourier coefficients are
complex. A domain qualification is essential, independently of the previously
refuted componentwise contraction claim. Preserve that earlier obstruction.

`Foundation/ComplexGammaEllipsoidVolume.lean` now proves actual Lebesgue volume
identities, not merely a determinant calculation. `matrix_preimage_volume`
reuses Mathlib's invertible-matrix measure pushforward. `realDouble_det` and
`realDouble_preimage_volume` prove that applying the same real matrix to real
and imaginary coordinates squares its real determinant and volume Jacobian.
All measurability and nonzero determinant assumptions are explicit.

For two complex modes, the actual covariance Gram matrices are
R=[[1,1],[1,2]], P=[[1,1],[1,4]], identified with existing H=1/2 covariance
and its entrywise square by `gram_first_actual`/`gram_second_actual`.
The real/imaginary Gram energy equals the squared norm after the triangular
map [[1,1],[0,r]] on each component. At r=1 and sqrt(3), respectively, the
resulting closed ellipsoids have volumes V and V/3. V is proved finite and
strictly positive by enclosing the sum-of-squares region between actual balls.
`cauchy_complex_volume_ratio` gives ratio3; `cauchy_complex_volume_not_real_formula`
proves it is NOT sqrt(3). This is a rigorous two-mode counterexample to using
the real exponent on the full complex coefficient space. The original real
ellipsoid proof remains valid on an explicitly chosen real coefficient slice;
our general measure theorem records the dimensional distinction without
asserting a new all-N spectral/ellipsoid theorem.

Interpretation is precise: fixed-point coefficient Gram ellipsoids (e.g. at
phase0), as used by the manuscript's matrix argument. If Gamma<=1 means a
simultaneous bound at EVERY torus point, the resulting intersection is a
different set and the manuscript's ellipsoid argument does not establish its
volume. Neither integrated-energy volume, semigroup contraction nor a dynamical
rate is inferred. No complex tensor completion or new novelty claim is made.

Verification: full6802-job root build43.721s; complete50718 safe transitive
axiom audit41.570s, whitelist propext/Classical.choice/Quot.sound only; all26
public types,20 proofs and6 definitions reviewed unabridged. Four independent
Lean checks24.466s cover actual Gram determinants, another scale, negative
orientation and tail cancellation.1875 exact rational four-coordinate tests
check complex Gram/tail-square energies for squared scales1,3,4. No sorry,
axiom, new resource/trust/toolchain/linter setting or local instance. One existing
style gate reports a long source line; no mathematical error is suppressed.
2629 Foundation/root hashes frozen, configuration3 and source archive113 intact.
Evidence `.lake/stardust-1558-{working-checkpoint,verification}.json`, complete
build/audit/independent logs and independent-exact.json. Local gates PASS;
exact commit receipt and guarded BOTH-private-ref verification follow. This
pre-commit record does not assert remote closure before terminal verification.

Next: remaining spectral/determinant asymptotics and completed semigroup,
invariant-measure/nonlocal entropy claims; do not repeat the resolved complex
volume mismatch. Preserve both primary manuscripts, all prior repairs and
counterexamples. No queue transition, new campaign, or reflection admitted.


## Checkpoint1559 — sharp finite Gamma decay at every energy level

Primary1 `bakry_emery_part2_v3 (1).tex`, energy-k/lem:dissipation/thm:decay/
cor:universality (1334–1490), now has a direct finite-core verification and
stronger decay bound in `Foundation/StableGammaEnergyDecay.lean`.
`circle_gamma_diagonal` derives the diagonal Fourier formula from the ACTUAL
Gamma recursion and normalized circle integral, for distinct integer frequencies
and every gamma>0. `energy` is defined by that integral, not postulated as a sum.
`energy_diagonal`/`energy_at` identify its weights |n|^(gamma*q) and exponential
factors exp(-2|n|^gamma*t). `generator_axis` identifies the original generator's
coefficient action; `coefficientsAt_zero`/`coefficientsAt_add` verify the finite
coefficient semigroup. Complex coefficients and negative modes are allowed.

`energy_dissipation` proves the actual real HasDerivAt identity
d E_q(P_t f)/dt = -2 E_(q+1)(P_t f), all q>=0 and all real t on the finite core.
`energy_decay_all_orders` proves E_q(P_t f)<=exp(-2t)E_q(f), for EVERY q>=0,
gamma>0, t>=0, with distinct NONZERO integer frequencies. `first_frequency_exact`
attains equality for the unit first mode. No N-dependent or chaos-depth waiting
threshold is required. This proves the manuscript's weaker high-order inequality
on its finite positive-frequency domain but qualifies the proposed interpretation:
the bound is already present at the lowest levels from the Fourier gap, and is
not evidence of convergence to a Gaussian process or Gaussian operator dynamics.

The zero-frequency order-zero example has energy1 for every t and demonstrates
why the nonzero-frequency hypothesis matters. Negative mode -1 with imaginary
coefficient has the same exact rate; mode2 at q3 has energy8exp(-4t), and q2
dissipation is -16exp(-4t).810 independent exact rational Fourier Gamma-recursion
checks verify diagonal and generator constant coefficients for integer orders1,2,3,
levels0..4, signed frequencies and27 coefficient patterns. These tests supplement,
not replace, the genuine analytic Lean derivative proof.

Full6803-job root build43.639s; complete50739safe transitiveaxiom audit44.955s,
whitelist only propext/Classical.choice/Quot.sound; all12publictypes/10proofs/2defs
read unabridged. Four independentLean checks28.896s passed. Their convert/ring
proof emits tactic suggestions but exits0 with no unsolved goal; no error or
linter was suppressed.2630Foundation/root source hashes, configuration3 and
archive113 verified. No original manuscript, compiler/trust/resource setting,
queue or other mathematical source changed beyond the new module/root/audit.
Evidence `.lake/stardust-1559-{working-checkpoint,verification}.json`, complete
logs and independent-exact.json. Local gates PASS; exact commit receipt and
guarded BOTH-private-ref verification follow, not assumed by this entry.

Limits: finite Fourier core only; no completed Sobolev domain or generator closure
is inferred. Algebraic positive orders beyond2 are not asserted to generate
probability semigroups. The pointwise covariance/Gamma curvature hierarchy is
distinct from its integrated diagonal gap. The manuscript's ratio sandwich also
requires nonzero input; its unrestricted zero-input wording remains to qualify.
Both primary audits remain INCOMPLETE; BakryObjective1 ACTIVE. Next investigate
substantive completed-domain, invariant-measure and nonlocal entropy obligations,
reusing the now verified finite core. Preserve every earlier obstruction/repair.
No reflection session, campaign transition or novelty claim is admitted.


## Checkpoint1560 — actual Cauchy diffusion-chain obstruction and entropy audit

BakryObjective1 remains ACTIVE; both primary audits INCOMPLETE. Primary2
`bakry_emery_revised_v8 (2) (2).tex` lines109 and1498–1501 invokes the classical
positive-curvature log-Sobolev implication. Its lines298ff acknowledge a separate
nonlocal entropy-production approach. The precise diffusion hypothesis cannot
be assumed for the manuscript's actual Cauchy generator, with or without sine drift.

`Foundation/CauchyDiffusionChainObstruction.lean` proves for f=cos(x) at x=0:
Lf=-1, L(f²)=-1, L(f³)=-3/2 and the ACTUAL Gamma(f,f)=1/2. Thus
`cauchy_diffusion_chain_failure` refutes L(f³)=3f²Lf+6fGamma(f,f).
The polynomial `cubicDefect` is L(f³)-3fL(f²)+3f²Lf. For every finite Fourier
polynomial, adding r*(-sin x d/dx), ANY real r, preserves that defect because
transport is a verified derivation. `drifted_cubic_defect`/`drifted_cubic_nonzero`
give the same -3/2 witness for all r. This uses original generator, Fourier
product, synthesis and Gamma definitions, not an unrelated finite jump model.

Direct reuse, not duplication: existing
`PoissonCoreCurvatureEntropy.positive_curvature_bounded_core_entropy_failure`
gives for every positive Poisson rate and every C>=0 a finite-support witness
with pointwise Gamma2>=Gamma/2 but Ent(f²)>C integralGamma. The independent Lean
suite instantiates rate1. This disproves an unrestricted jump-process transfer
of the classical quadratic entropy implication. It does NOT disprove a separate
torus Cauchy LSI, modified LSI or appropriate invariant-measure entropy theorem.
Those require their own assumptions and proofs. Earlier uniform-measure
noninvariance/Poincare obstruction and centered-energy repair remain intact.

Literature audit (read October26,2026): Weber–Zacher, arXiv:2007.01264v1,
https://arxiv.org/html/2007.01264v1, section1.1 equation(2), explicitly states
the diffusion chain-rule hypothesis and its nonlocal failure. The abstract and
section headings distinguish CD_Upsilon and modified log-Sobolev methods.
Only these inspected passages are relied on; no claim to have audited every
theorem/proof. Publisher DOI landing page S0022123621001439 returned403; arXiv
v1 supplied accessible primary text. Treat HTML render date separately from
arXiv submission date July2,2020. No novelty is claimed for chain-rule failure.

Full6804-job build42.431s; complete50752safe transitiveaxiom audit45.442s,
whitelist propext/Classical.choice/Quot.sound; all11types/10proofs/1definition
reviewed unabridged. Three independentLean checks33.120s include quadratic
zero-defect, third-order opposite-sign defect and existing Poisson entropy
counterexample.571 exact rational Fourier/transport checks passed. The fourth-order
cosine defect happens to vanish at zero; this point cancellation proves no
diffusion property and prevents extrapolating this witness to all orders.
2631Foundation/root hashes,configuration3,archive113 intact. No new option,
axiom,sorry,localinstance or resource/toolchain change. Full evidence under
`.lake/stardust-1560-*`; exactcommitreceipt and guarded BOTH-private-ref closure
follow. This pre-commit ledger entry does not assert completed remote backup.

Next substantive repair: precise nonlocal entropy forms, invariant measures or
closed operator domains using the existing library. Do not re-prove the generic
Poisson obstruction or falsely declare the specific Cauchy LSI refuted. Preserve
manuscript bytes, source hashes, all priorities and previous verified results.
No reflection session, queue change, campaign transition or publication.

## Checkpoint1561 — actual invariant-core probability law repair

CauchyPoissonCoreInvariant constructs the positive normalized harmonic-Poisson
angle law for |q|<1, proves true Fourier moments and identifies the existing
Cauchy generator plus sine transport. `actual_finite_core_balance` proves
integral L_r f d law(q)=0 for every finite signed-frequency complex trigonometric
polynomial when r=2q/(1-q^2), with actual integrability discharged. This replaces
uniform-measure invariance on the finite core; it does not prove closed-domain
or semigroup invariance, stationary paths or an entropy inequality. Both primary
audits remain incomplete. Next address those precise bridges, not duplicate
moment infrastructure. The wrapped-Cauchy candidate is known; see full source
and scope in PROJECT_STARDUST_REPORT checkpoint1561.

Full6805jobbuild42.958s; complete50792safe transitiveaudit52.392s;30types/27proofs/
3defs reviewed;5independentLean29.907s;357exact and85quadrature checks. Wrong
parameter produces independently verified residual -1/8.2632sources/config3/
archive113 intact. Full local gates passed; exactcommit and guarded PRIVATE
main/research verification pending closure. No campaign transition or publication.


## Checkpoint1563 — actual Poisson-law Cauchy nonsymmetry obstruction

Bakry Objective1 ACTIVE; both primary manuscript repairs remain INCOMPLETE.
After verified/private IBM1562 closure, the next operator-realization audit
checks whether1561's actual core-balance law permits direct use of the existing
self-adjoint machinery. It does not for nonzero q. This is an obstruction to that
proposed repair route, NOT an attribution of an explicit reversibility claim to
the manuscripts. Primary2's nonlocal entropy discussion (lines298ff) and its
log-Sobolev-under-drift discussion (1495ff) remain separate open obligations.
The earlier classical diffusion-chain counterexample and finite curvature
identities are preserved unchanged.

New Foundation.CauchyPoissonNonSymmetry uses the ACTUAL original Fourier
Cauchy generator plus r*(-sin(theta) d/dtheta), the actual normalized harmonic-
Poisson angle law from1561, and r=2q/(1-q^2), |q|<1. Let e_n(theta)=exp(i*n*theta).
`actual_forward_pairing` proves integral conjugate(e_1)*L_r(e_2) dlaw(q)=0.
`actual_backward_pairing` proves integral conjugate(L_r(e_1))*e_2 dlaw(q)=-2q.
`not_hermitian_core` therefore disproves Hermitian symmetry on the finite core
for EVERY q!=0 in this parameter range. At q=1/2,r=4/3 the two values are0,-1;
negative q reverses the defect. The q=0 witness vanishes, as it must. All pairings
are genuinely integrable; the independent Lean suite proves this for arbitrary
finite Fourier f,g, not only the two witnesses. Existing generator/core-balance
identities still hold, independently checked on every natural mode.

Consequently a symmetric/self-adjoint operator agreeing with this actual core
and weighted inner product cannot be used as the generator repair. This is a
necessary-core compatibility obstruction; no new closed generator, path process
or semigroup has been constructed here. It does NOT refute a nonreversible
invariant semigroup, an appropriate nonlocal entropy inequality, or the already
verified algebraic Gamma identities. No novelty claim is made.

Full6807-job build39.469s; complete50869safe transitiveaxiom audit38.171s,
whitelist propext/Classical.choice/Quot.sound. All13publictypes/11proofs/2defs
reviewed unabridged. Five independent Lean checks25.048s passed (both parameter
signs, zero control, general pairing integrability and preserved core balance).
285exact rational stationary-mode checks,19complex off-diagonal pairs and19real
cosine pairs passed. The latter independently give defect q, but the production
Lean counterexample uses complex modes; do not claim a separately formalized
real-cosine theorem. Tests supplement the actual analytic Lean proof.

All2634Foundation/root hashes,configuration3 and archive113 verified. Original
manuscript bytes and unrelated drafts preserved. Initial scratch elaboration
failures and the first adoption build failure are retained. A stylistic tactic
cleanup caused that build failure; the passing proof was restored and the FULL
build rerun. No error/check was suppressed and no resource, compiler, trust,
version or audit setting changed. One tactic-style suggestion remains visible.
Evidence `.lake/stardust-1563-*`. Local gates PASS; exact commit/receipt and
guarded BOTH-private-ref verification follow, not pre-claimed here.

NEXT: use the correct non-Hermitian setting to establish actual weighted energy
and dissipativity, a dense closed generator/domain and valid semigroup invariance,
then the appropriate nonlocal entropy repair. Reuse1561's law and finite balance
and the existing positive Gamma library; do not repeat mode algebra or infer
semigroup invariance from infinitesimal finite-core balance. No queue transition,
reflection, publication or extension of the frozen IBM excursion.

## Checkpoint1564 — actual Poisson-weighted finite-core energy repair

Bakry Objective1 remains ACTIVE; both manuscript repairs are incomplete.
IBM rematch1562 remains frozen and incomplete outside its stopping contract.
Building directly on1561's actual law and1563's nonsymmetry obstruction,
`Foundation/CauchyPoissonDissipativity.lean` proves for EVERY finite Fourier
polynomial f, |q|<1 and r=2q/(1-q^2):

    Re integral conjugate(f) L_r(f) d pi_q = - integral Gamma(f,f) d pi_q <= 0.

Here functions are synthesized on the actual circle-angle slice ![theta,0,0],
pi_q is the existing normalized positive Poisson-kernel law, and Gamma is the
verified stable-symbol first Gamma. `actual_core_balance` extends actual
infinitesimal balance to the entire finite Fourier algebra on that slice;
`weighted_gamma_pairing` gives the polarized identity;
`weighted_energy_identity` and `weighted_dissipativity` give the stated result.
All integrability is discharged using the existing actual-law library. Reuse
of `stable_gamma_nonnegative` proves positivity for arbitrary complex finite
coefficients. No injectivity of the three-dimensional algebra on the slice,
full-torus invariant law, reversibility or self-adjointness is asserted.

This is a positive repair compatible with1563's non-Hermitian obstruction.
The earlier real uniform-law witness 2+cos(theta) has repaired energy -1/2;
the unit mode has energy -1 and constants have zero energy. These identities
hold for every admissible q in independent Lean checks. Finite-core
dissipativity and infinitesimal balance alone do NOT construct a closed
generator, establish a semigroup or prove nonlocal entropy inequalities.
Both manuscripts' closed-domain/semigroup and entropy obligations remain open.

Full6808-job build40.705s, complete50884-safe-declaration transitive axiom audit
38.098s (only propext/Classical.choice/Quot.sound), all10 public types/9 proofs/
1 definition reviewed unabridged. Four independent Lean checks24.929s passed.
1539 exact rational finite-polynomial energy/positivity checks and19 exact
real-witness checks passed. The rational tests use real coefficients; the
general Lean theorem covers complex coefficients. First independent-check
elaboration failures were repaired locally, retained in the evidence, and
rerun; production mathematics did not change. No settings/checks were weakened.
All2635 Foundation/root sources, configuration3 and archive113 hashes checked.
Evidence: `.lake/stardust-1564-*`. Local gates PASS; exact commit/receipt and
guarded BOTH-private-ref synchronization follow, not pre-claimed here.

Promising next route, explicitly UNVERIFIED: on positive Fourier modes L_r
corresponds to V(z)=-z+r(1-z^2)/2. Its candidate fractional-linear flow is

    phi_lambda(z) = [q(1-lambda)+(q^2+lambda)z]
                   /[1+q^2 lambda+q(1-lambda)z],
    lambda=exp(-(1+q^2)t/(1-q^2)).

144 rational matrix-composition tests support the algebraic composition law;
they are not a Lean semigroup proof. Composing harmonic extensions with this
flow may supply actual positive Poisson transition operators and avoid an
invalid symmetric-generator repair. Denominator nonvanishing, disk mapping,
harmonic composition/uniqueness, kernel composition, invariance, strong
continuity and exact closed generator/core identification remain to be proved.
Audit the Cauchy phase-flow and holomorphic composition literature before any
novelty claim. No new process or semigroup is claimed at this checkpoint.
Original manuscripts and all campaign priorities remain unchanged.

## Checkpoint1565 — explicit Cauchy disk flow and actual Poisson moment composition

Bakry Objective1 ACTIVE; no campaign transition. This advances the genuine
nonreversible semigroup route left open by1563/1564, without claiming its
completed realization. `Foundation/CauchyPoissonFlow.lean` proves, for |q|<1,
0<=lambda<=1 and |z|<=1, the explicit holomorphic map

    phi_lambda(z)=[q(1-lambda)+(q^2+lambda)z]
                  /[1+q^2 lambda+q(1-lambda)z].

The denominator never vanishes on the closed disk. `disk_defect` decomposes
|D|^2-|N|^2 into three nonnegative terms; the first is strictly positive when
lambda<1. Thus `flow_strict_disk` proves actual strict interior mapping,
not just a numerical boundary check. `flow_composition` proves exact
phi_lambda(phi_mu(z))=phi_(lambda*mu)(z), and `flow_fixed` fixes q.
The lambda=1 map is identity. With a=(1+q^2)/(1-q^2)>0 and lambda=exp(-a*t),
`evolution_add` proves time-additive composition for nonnegative times and
`evolution_strict_disk` sends the entire closed disk inside at every t>0.

`flow_holomorphic` proves complex differentiability on the disk and continuity
on its closure, discharging the actual Mathlib Poisson-formula hypotheses.
`poisson_flow_moment` is an actual circle-average integral identity for every
interior complex pole and every natural power. `poisson_composition_moment`
identifies the composed kernel's positive moments with phi_(lambda*mu)(z)^n;
mu<1 is explicit so its Poisson pole is strictly interior. `poisson_fixed_moment`
proves the corresponding fixed-law moments q^n. No boundary-pole Poisson density
is substituted for the time-zero Dirac kernel.

`evolution_derivative_zero` proves the actual time derivative
V(z)=-z+q(1-z^2)/(1-q^2). `actual_positive_mode_derivative` proves, at EVERY
positive Fourier frequency and circle point, agreement with the existing
audited Cauchy/sine-drift generator L_r, r=2q/(1-q^2). This is pointwise
derivative identification, NOT an already-proved generator limit in a Banach
space norm. All finite-core dissipativity/nonsymmetry results remain intact.

Literature audit: Tönjes--Pikovsky, arXiv:2009.04725v1, read October27,
https://arxiv.org/html/2009.04725v1, equations8--10 describe the Cauchy-noise
Fourier hierarchy, quadratic OA dynamics and wrapped-Cauchy density. Our
quadratic vector field is a fixed sinusoidal-forcing specialization of that
known structure; the flow family is not asserted novel. Cestnik--Pikovsky,
arXiv:2207.02302v3, https://arxiv.org/abs/2207.02302v3, abstract inspected,
reports a broader reduction beyond the OA subspace; its full proof has NOT
been audited here and no claim from it is used as a formal premise.

Full6809-job build40.621s; complete50924-safe-declaration transitive axiom audit
41.963s, whitelist propext/Classical.choice/Quot.sound. All26 public types,
20 proofs and6 definitions reviewed unabridged. Seven independent Lean checks
25.143s passed: q=0 reduction, lambda=0 endpoint, explicit complex value,
actual derivative, positive-time interior, actual kernel mass and commuting
time maps. Exact Gaussian-rational tests passed2835 disk/defect,8505 composition
and567 derivative cases, including complex boundary/interior points and q
near both endpoints. They caught an incorrect hand-calculated test value;
the corrected value phi_(1/2)(i) at q=1/2 is6/17+10i/17. No production theorem
changed. Scratch failures and initial test evidence are retained.

The first independent run overlapped the audit's last two seconds because its
handle was not yet terminal-confirmed. After terminal confirmation, the complete
independent suite was rerun serially; final timing/verification checks enforce
that order. No process was interrupted or restarted on silence. No compiler,
resource, trust, version or verification setting changed; warnings remain visible.
All2636 Foundation/root sources, configuration3 and archive113 hashes checked.
Original manuscripts and unrelated drafts untouched. Evidence `.lake/stardust-1565-*`.
Local gates PASS; exact commit, receipt and guarded BOTH-private-ref backup
follow, not pre-claimed here.

NEXT: construct the actual complex-pole probability kernels (including the
time-zero Dirac case), promote moment identities to equality of measures or
bounded operators using justified Fourier density/uniqueness, prove strong
continuity and uniform generator convergence on a dense core, then identify
the closed domain and invariant semigroup. Positivity and invariant moments
alone do not supply these conclusions. Entropy and both primary manuscript
repairs remain incomplete. Reuse the existing actual Poisson law, continuous
torus Fourier approximation and closed-operator library; no new campaign.

## Checkpoint1566 — actual transition densities and circle probability laws

Bakry Objective1 remains ACTIVE; both manuscript repairs remain incomplete.
`Foundation/CauchyPoissonKernelComposition.lean` upgrades1565's moment identities
to POINTWISE density composition and invariant density. No new Fourier-density
infrastructure was needed. For |q|<1, positive s,t, |z|<=1 and |xi|=1, set
K_t(z,xi)=P(phi_t(z),xi), with P the actual Poisson kernel and phi the audited
fractional-linear time flow. `transition_composition` proves

    circleAverage_w K_s(z,w) K_t(w,xi) = K_(s+t)(z,xi).

`transition_positive` and `transition_mass` prove strict positivity and mass1
relative to normalized uniform circle integration. `density_invariance` proves
circleAverage_w P(q,w) P(phi_lambda(w),xi)=P(q,xi) for0<=lambda<1. These are
actual integral/density identities, stronger than equality of finitely many
moments. The proof constructs H(w)=(xi+phi_lambda(w))/(xi-phi_lambda(w)), proves
its holomorphy and continuity on the closed disk with nonvanishing denominator,
then applies Mathlib's existing Poisson formula and takes real parts through
an explicitly integrable circle average. All analytic hypotheses are discharged.

`poleLaw` constructs the actual complex-pole angle probability law from its
continuous positive density on (0,2pi]. Integrability and mass1 are proved;
`poleLaw_real` identifies it definitionally with1561's real-pole law.
`transitionLaw` gives positive-time angle laws and the exact time-zero Dirac
law. `circleTransitionLaw` pushes the positive-time law through circleMap and
uses Dirac(z) at time0. It is a probability for |z|<=1,t>=0; for |z|=1 it assigns
mass1 to the actual unit circle. The support proof explicitly verifies circleMap
measurability and uses the actual pushforward formula, not a nonmeasurable-map
fallback. Two local probability instances in these proofs were reviewed.

Scope limits: the family is not yet packaged as a measurable Markov kernel.
State-parameter measurability, Tonelli/Fubini promotion of the density identity
to composition of measures, and invariance of the resulting measure semigroup
remain to be proved. No Feller/strong-continuity, closed-generator/core, path
process or entropy theorem is claimed. The correct eventual state space is the
unit circle (or periodic observables), not all real-valued angle observables:
raw angle representatives have a seam, and interior disk starting points jump
to the boundary at positive time. Do not infer strong continuity on the entire
closed disk from these probability laws. This is a domain warning, not a new
formal seam counterexample theorem. At t=0 use Dirac; never substitute the
boundary-pole Poisson density into a mass1 formula whose pole must be interior.

Full6810-job build42.648s; complete50954-safe-declaration transitive axiom audit
40.829s (only propext/Classical.choice/Quot.sound). All25 public types/20 proofs/
5 definitions and both local probability instances reviewed unabridged.
Seven independent Lean checks24.447s passed, covering old-law compatibility,
Dirac endpoint, positive/negative parameters, actual circle support, uniform
pole, angle-parametrized composition, and integrable density normalization.
Independent4096-node floating-point quadrature passed180 composition,30
invariance and180 mass checks; maximum scaled error6.584e-15 against1e-8
tolerance. These are numerical checks, not proofs or novelty evidence.

All2637 Foundation/root sources, configuration3 and archive113 hashes checked.
Build/audit/independent Lean runs were serialized and terminal-confirmed.
Initial scratch elaboration failures were retained and repaired without
changing hypotheses or resource/compiler/trust/version/audit settings.
No manuscript or unrelated draft changed. Evidence `.lake/stardust-1566-*`.
Local verification gates PASS; exact commit/receipt and guarded BOTH-private-ref
synchronization follow, not pre-claimed here. No novelty claim;1565's literature
comparison remains applicable to this known Poisson/phase-flow construction.

NEXT: establish parameter measurability and actual measure/operator composition
on the circle; then strong continuity, uniform generator convergence on the
finite trigonometric core, a closed generator/domain and appropriate nonlocal
entropy repair. Reuse these actual densities/probability laws and existing
operator calculus. Preserve the nonsymmetry obstruction and weighted energy
identity. IBM's bounded rematch remains frozen; no campaign or queue change.

## Checkpoint1567 — actual Circle Markov transition semigroup and invariant law

Bakry Objective1 ACTIVE. `Foundation/CauchyPoissonMarkovKernel.lean` discharges
the measurable-kernel and measure-composition obligations left by1566. For
EVERY |q|<1 and nonnegative time t, `kernel q t : Kernel Circle Circle` is an
actual measurable Markov kernel. At0 it is the identity/Dirac kernel. At t>0
its law is the exact Circle.exp pushforward of the already constructed poleLaw
at the audited Cauchy flow phi_t(z). `kernel_matches_actual` identifies its
complex pushforward with1566's circleTransitionLaw, not a surrogate family.

`weight_measurable` proves the joint state/angle density measurability required
by Mathlib Kernel.withDensity; `angleKernel_apply` uses the actual measurable
branch. Neither a zero fallback nor an axiomatized kernel substitutes for the
density. The existing Mathlib measurable/Borel structure on Circle is reused.
`kernel_markov` proves mass1 with all hypotheses discharged for t>=0.

`kernel_composition` proves the actual Chapman--Kolmogorov equality

    kernel(q,t) composed with kernel(q,s) = kernel(q,s+t),  s,t>=0,

as an equality of measurable kernels, hence of their measures on EVERY Borel
set at EVERY Circle starting point. `mixture_set` proves the actual setwise
mixture using1566's density identity, withDensity integration, positivity,
integrability and Tonelli. The necessary real-to-lintegral conversion is
explicit. `next_density_integrable` uses the proved strictly positive Bochner
integral value to establish integrability (nonintegrable Bochner integrals
would be0); it does not assume a missing bound. All zero-time cases are proved
separately. `invariantLaw` is the actual Circle.exp pushforward of pi_q;
`invariantLaw_probability` and `kernel_invariant` prove its probability and
exact invariance under binding with this kernel for EVERY t>=0.

This is a genuine Markov transition SEMIGROUP, stronger than infinitesimal
finite-core balance or density/moment agreement. It is not yet a Feller or
strongly continuous operator semigroup with identified closed generator. No
path-space process, path regularity, completed-domain generator, entropy or
full manuscript repair is claimed. Pointwise Fourier derivatives1565 and
weighted dissipativity1564 remain available but do not discharge those later
operator-domain limits. Nonsymmetry1563 remains valid: the invariant kernel
does not restore a symmetric/self-adjoint generator on the given core.

Full6812-job root build38.891s; complete50980-safe-declaration transitive axiom
audit40.242s, whitelist propext/Classical.choice/Quot.sound. All21 public types,
18 proofs,3 definitions, two local probability instances and one local Markov
instance reviewed unabridged. Seven independent Lean checks31.206s passed:
actual Markov property/mass, negative-q composition, actual invariant measure,
zero-time Dirac, exact old-law identification and an EXCLUDED-PARAMETER control.
The latter proves angleKernel(1,1,z)=0 for every Circle z, illustrating why the
strict |q|<1 domain cannot be omitted. It is an independent verified test, not
a newly exported Foundation declaration. A test's numeric normalization was
repaired and rerun; production mathematics was unchanged. Retain scratch/test
failure evidence. Previous1566 density quadrature remains supporting evidence;
no repeated numerical run or new numerical discovery is claimed.

All2638 Foundation/root sources, configuration3 and archive113 hashes checked.
Lean verification stages serialized and terminal-confirmed. No resource,
compiler, toolchain, trust or audit setting changed; warnings remain visible.
Original manuscripts and unrelated drafts untouched. Evidence `.lake/stardust-1567-*`.
Local gates PASS; exact commit/receipt and guarded BOTH-private-ref backup
follow, not pre-claimed here. No novelty claim;1565's literature audit still
governs the known Cauchy/Poisson construction.

NEXT: prove Feller continuity on Circle and strong continuity on C(Circle),
then uniform generator convergence on the finite trigonometric core and a
closed generator/domain. Reuse actual kernel moments, compactness/uniform
continuity and the cumulative operator library. A possible route is to control
the kernel's chordal second moment using its first Fourier moment, then use
uniform continuity; this is a proposal, not a verified estimate. Preserve
the angle-seam/interior-start domain warnings and the distinct path-construction
and nonlocal entropy obligations. Both Bakry manuscript repairs remain open;
IBM's bounded rematch stays frozen and all subsequent queue priorities persist.


## Checkpoint1568 — actual continuous-observable contraction semigroup

Bakry Objective1 remains ACTIVE. The bounded IBM rematch is frozen at1562;
full IBM calculus is incomplete/deferred. No campaign transition or new goal.

`Foundation/CauchyPoissonFeller.lean` lifts the actual measurable Circle kernel
of1567 to bounded complex-linear operators on C(Circle, complex), for every
real pole |q|<1 and every t>=0. Positive-time density is jointly continuous
in the initial circle point and angle; compact parameter integration proves
spatial continuity of the actual integral. Zero time is the identity/Dirac
case handled separately. Continuous observables are genuinely integrable
against each transition probability. The resulting operators contract the
supremum norm, preserve constants, and satisfy P_(s+t)=P_s composed P_t.
Composition uses the actual kernel equality and Bochner integral composition,
not an assumed abstract semigroup or merely a Fourier-moment surrogate.

This is the spatial Feller property and a bounded-operator semigroup. It does
NOT yet establish strong continuity in time. Uniform convergence as t tends
to zero, norm-generator convergence, the closed generator/core/domain, path
construction and valid nonlocal entropy statements remain OPEN. Neither
Bakry manuscript repair is declared complete. Preserve the non-Hermitian
core obstruction1563, weighted dissipativity1564 and all strict parameter
domains. No novelty claim; the existing1565 literature audit remains relevant.

Full6813-job root build39.831s; complete51001-safe-declaration transitive axiom
audit43.656s, allowing only propext/Classical.choice/Quot.sound. All14 public
types,12 proofs,2 definitions and3 local Markov instances reviewed unabridged.
Five independent Lean checks26.456s passed: difference stability, three-step
composition with negative pole and zero endpoint, arbitrary complex constants,
exact native positive-time integral and nonconstant zero-time coordinate.
Scratch coercion/elaboration failures were repaired and logs retained. No
new numerical test or numerical discovery is claimed. All2639 Foundation/root
sources, configuration3 and archive113 hashes checked. Verification serialized,
terminal-confirmed; no toolchain, resource, trust or audit setting changed.
Warnings remain visible. ResearchSources and unrelated drafts unchanged.
Evidence: `.lake/stardust-1568-*`. Local gates PASS; exact-commit receipt and
guarded BOTH-private-ref verification follow, not pre-claimed by this entry.

NEXT: actual strong continuity on C(Circle), then the finite-core norm-generator
limit and closed-domain identification. The first Fourier moment/chordal
second-moment route and compact uniform continuity remain candidates requiring
proof. Reuse the accumulated machinery rather than assuming a time-continuity
theorem from spatial Feller continuity. All queue and private-backup gates persist.


## Checkpoint1569 — actual kernel concentration and strong continuity

Bakry Objective1 remains ACTIVE; both primary manuscript repairs remain open.
No campaign transition. IBM bounded rematch remains frozen1562/fullIBM deferred.

`Foundation/CauchyPoissonConcentration.lean` proves strong continuity of the
ACTUAL1567-1568 Circle transition operators on C(Circle, complex), for every
fixed real |q|<1 and every continuous observable f, at EVERY nonnegative time.
The topology is the supremum norm of continuous functions, not pointwise
convergence or a finite-mode surrogate. Together with1568 this supplies an
actual strongly continuous contraction semigroup preserving constants.

The proof first identifies the actual kernel's complex first moment with
phi_t(z). Its chordal second moment is exactly
  integral |w-z|^2 K_t(z,dw) = 2 - 2 Re(conj(z)*phi_t(z)).
This is bounded uniformly in z by twice the continuous-function norm of
phi_t-id. Joint continuity on nonnegative time times compact Circle implies
that displacement norm tends to zero. For EVERY continuous f and epsilon>0,
compact uniform continuity gives C>=0 with
  |f(w)-f(z)| <= epsilon + C*|w-z|^2.
Actual Bochner integration, proved integrability and the concentration bound
therefore give uniform convergence P_t f -> f. Contractivity and the semigroup
law yield ||P_s f-P_t f|| <= ||P_|s-t| f-f||, establishing continuity at all
nonnegative times. No differentiability/Lipschitz assumption on f is imposed.

Full6814-job build44.944s; complete51020-safe-declaration transitive axiom audit
44.593s with only propext/Classical.choice/Quot.sound. All15 unabridged public
types,14 proofs,1 definition and2 local Markov instances reviewed. Five independent
Lean checks30.275s passed: strict positive-time spread at q=0; arbitrary moving
starting points under the uniform limit; positive-time continuity at q=-1/2;
zero-time concentration; and vanishing increments over arbitrary nonnegative
base-time sequences. The last tests uniformity over the whole base-time axis.
The positive-spread test required explicit real-part simplification of complex
exp; its failed log/time and scratch failures remain preserved. Production
sources were unchanged during test repair. No new numerical/novelty claim.

All2640 Foundation/root sources, configuration3 and archive113 hashes checked.
Every verification stage serialized and terminal-confirmed. No resource,
toolchain, compiler, trust or audit setting changed; warnings remain visible.
ResearchSources and unrelated drafts untouched. Evidence `.lake/stardust-1569-*`.
Local gates PASS; exact commit receipt and guarded BOTH-private-ref verification
follow, not pre-claimed in this ledger entry.

NEXT: identify the actual norm generator on the finite trigonometric core,
then its closed operator/domain and appropriate nonlocal entropy statements.
The pointwise Fourier derivatives1565 are NOT yet norm-generator membership.
A reuse audit confirms HigherHeatClosedGenerator/HigherHeatGeneratorDomain
are specific to L2 Fourier multipliers; their domain equivalences do not
transfer without new hypotheses to this drifted C(Circle) operator.
ContractionTangentDissipativity.norm_resolvent_bound is a reusable generic
bound once the actual norm tangent is proved. StickyGeneratorClosure provides
a graph/submodule proof pattern, not a ready-made Cauchy generator theorem.
No path-space construction, closed-generator/core identification or entropy
theorem is claimed here. Preserve nonsymmetry1563 and weighted dissipation1564;
invariance/strong continuity do not restore reversibility. All later priorities,
no-expiration policy and full verification/private-backup requirements persist.


## Checkpoint1570 — actual norm generator on finite trigonometric observables

Bakry Objective1 remains ACTIVE. Both manuscript repairs remain incomplete;
IBM bounded rematch frozen1562/fullIBM deferred and all later priorities unchanged.

`Foundation/CauchyPoissonCoreGenerator.lean` identifies the right-time generator
of the ACTUAL Circle transition semigroup on every finite complex trigonometric
combination, in C(Circle, complex) SUPREMUM NORM. This strengthens1565's pointwise
mode derivatives to actual norm-domain membership. The proof does not import
an L2 multiplier-domain theorem into a different space.

Let c(z)=z and V_q(z)=-z+q/(1-q^2)*(1-z^2). Exact Poisson integrals give
P_t(c^n)=phi_t^n and P_t(star f)=star(P_t f). The Mobius increment is factored
as (1-decay(q,t))*Q(q,t), where Q is continuous as a C(Circle) valued function.
The scalar exponential slope and norm-continuity of Q prove the true uniform
right derivative V_q. Normed-algebra differentiation and real-linear conjugation
give A(c^n)=n*c^(n-1)*V_q and A(star(c^n))=star(A(c^n)), including n=0.
Finite sums cover EVERY N and all complex coefficient arrays a,b:Fin N->complex.
The theorem `core_tangent` proves the actual positive-time difference quotient
limit in norm; `core_presentation_independent` proves equal observable functions
have equal generator values, even across different finite presentations.

The auxiliary real-time orbit uses max(t,0) solely to make a total function.
ALL asserted time derivatives are right derivatives at0 along Ioi0; no false
two-sided differentiability of this extension is claimed. `positive_mode_matches_drift`
is an exact equality with the previously verified Cauchy/sine-drift synthesis,
with r=2q/(1-q^2), every positive Fourier mode and every angle. Dynamics require
|q|<1; the final purely algebraic equality alone does not construct outside-domain
Markov laws. Actual contractivity and the existing generic contraction-tangent
theorem yield r*||f|| <= ||r*f-Af|| for all r>0 on the finite domain.
This is a coercive estimate, NOT resolvent surjectivity or a closed-domain theorem.

Full6815-job root build43.993s; complete51061-safe-declaration
transitive axiom audit41.630s, whitelist propext/Classical.choice/Quot.sound.
All26 public types,18 proofs and8 definitions read unabridged; no new local
instances. Five independent Lean checks25.035s passed: positive cubic
and conjugate cubic both have multiplier -3 at q=0; at q=1/2 the generator
of c at z=i is 4/3-i; redundant constant coefficients produce zero generator;
and the resolvent bound excludes nonzero finite-domain eigenvectors at every
positive real eigenvalue. Test elaboration/coercion and finite-sum/function
presentation repairs are retained in failed logs. Production sources unchanged
during independent test repairs. No new numerical experiment or novelty claim.

All2641 Foundation/root sources, configuration3 and archive113 hashes checked.
Verification stages serialized and terminal-confirmed. Compiler/resource/trust/
toolchain/audit settings unchanged; warnings visible. ResearchSources and unrelated
drafts untouched. Evidence `.lake/stardust-1570-*`. Local gates PASS; exact commit,
receipt and guarded BOTH-private-ref verification follow, not pre-claimed here.

NEXT: construct/identify the closed generator domain, with rigorous core-density
and graph-closure/uniqueness arguments, then valid nonlocal entropy consequences.
The name finite 'core' in this module does NOT prove graph-core density. Neither
closedness, maximality, range surjectivity nor graph-core equality is asserted.
A possible integrated-orbit characterization is P_t f-f=integral_0^t P_s g ds;
its equivalence to the norm derivative and closedness would need actual proofs.
Review cumulative closed-graph/partial-linear-map and Bochner machinery first.
Path construction and full entropy/manuscript completion remain separate open
obligations. Preserve nonreversibility1563 and weighted dissipation1564.


## Checkpoint1571 — actual closed generator and exact norm-derivative domain

Bakry Objective1 remains ACTIVE; both manuscript repairs remain incomplete.
IBM bounded rematch stays frozen1562/fullIBM deferred; no queue transition.

`Foundation/CauchyPoissonGeneratorDomain.lean` constructs the ACTUAL closed
complex-linear partial generator on C(Circle, complex), for every real |q|<1.
Its graph is EXACTLY the pairs (f,g) for which (P_t f-f)/t tends in supremum
norm to g as t tends to zero from the right. This is not merely a closed
relation containing known finite-mode pairs, nor an assumed generator.

The decisive equivalence is proved for ARBITRARY continuous f and g:
  right norm tangent g <=> for every t>=0, P_t f-f=integral_0^t P_s g ds.
Forwards: bounded linearity and the actual semigroup propagate the zero-time
tangent to a right derivative at every nonnegative base time. The existing
Banach-valued FTC for right derivatives supplies the integrated identity,
using actual strong continuity and Bochner integrability. Conversely, FTC1
and strong continuity recover the zero-time norm tangent. The total max(t,0)
extension is continuous; no two-sided derivative of P_t f at0 is asserted.

The integrated orbit map is a bounded complex-linear operator of norm at most
|t|. Each integrated identity is a bounded linear kernel condition on pairs;
their intersection is closed. Vanishing vertical pairs follow from uniqueness
of the ACTUAL tangent, allowing construction via Submodule.toLinearPMap.
`generator_closed`, `generator_graph_iff` and `domain_iff` give closedness and
the exact norm-derivative domain. `finite_core_graph` embeds all verified1570
finite trigonometric pairs. The contraction resolvent bound now holds for
EVERY pair in this full graph, and graph values are unique.

Full6816-job build39.502s; complete51104-safe-declaration transitive
axiom audit41.707s, whitelist propext/Classical.choice/Quot.sound. All23
public types,17 full proofs and6 definitions reviewed unabridged; no new local
instances. Five independent Lean checks33.276s passed: limits of graph
pairs are actual norm tangents; the constant at q=-1/2 is in the closed domain
with zero value; every finite trigonometric input satisfies the integrated
formula; no positive real eigenvectors exist in the full domain; and positive
real resolvent injectivity holds for arbitrary full-graph pairs. No claim of
surjectivity is made. Earlier scratch elaboration failures are retained; all
final independent checks passed without test repair. No numeric/novelty claim.

All2642 Foundation/root sources, configuration3 and archive113 hashes checked.
Full verification serialized and terminal-confirmed. Toolchain/compiler/resource/
trust/audit settings unchanged; warnings remain visible. ResearchSources and
unrelated drafts unchanged. Evidence `.lake/stardust-1571-*`. Local gates PASS;
exact commit, receipt and guarded BOTH-private-ref verification follow, not
pre-claimed in this entry.

NEXT: actual domain density, finite graph-core equality and resolvent range,
then valid nonlocal entropy consequences. Closedness and the precise derivative
domain are now established, but neither domain density, graph-core equality
nor resolvent surjectivity has been proved in this construction. Reuse audit:
Mathlib's AddCircle.span_fourier_closure_eq_top and AddCircle.homeomorphCircle
provide a possible density transfer; normalization and mode transport still
need proof. Ordinary density alone is not graph-core density. Path-space
construction and complete entropy/manuscript repairs remain separate obligations.
Preserve nonreversibility1563 and weighted dissipation1564. All later priorities
and full source/audit/Git/guarded-private-backup requirements remain unchanged.


## Checkpoint1572 — actual generator-domain density and unboundedness

Bakry Objective1 remains ACTIVE; bounded IBM rematch1562 remains FROZEN.
`Foundation/CauchyPoissonDomainDensity.lean` proves `domain_dense` for every
real pole |q|<1: the actual closed generator domain in C(Circle,complex) is
dense in the supremum norm. The proof transports Mathlib's period-one Fourier
span along the actual homeomorphism to Circle, identifies positive and negative
modes with coordinate powers and their conjugates, and uses the previously
proved actual norm derivatives. It does not replace actual domains by formal
polynomial candidates. Transport continuity, surjectivity and normalization are
proved explicitly. Correction to checkpoint1571's reuse note: the exact theorem
is ROOT `span_fourier_closure_eq_top`, not `AddCircle.span_fourier_closure_eq_top`;
`AddCircle.homeomorphCircle` is correctly namespaced.

At q=0, `zero_power_velocity` identifies the generator image of z^n with
-n z^n. `coordinate_power_norm` is exactly one and `zero_power_velocity_norm`
is exactly n. `zero_generator_unbounded` excludes every uniform graph bound
||g|| <= C ||f||. This prevents treating this densely defined generator as a
bounded operator on all continuous observables. No claim of novelty is made.

Full6817-job root build39.118s; complete51122-safe-declaration transitive axiom
audit41.543s with only propext/Classical.choice/Quot.sound. All15 public types,
13 proofs and2 definitions were read unabridged; no new local instances.
Five independent Lean checks passed in25.135s without repair: arbitrary
observable approximation by actual norm-tangent domain elements; impossibility
of a bounded linear operator agreeing with the full zero-pole graph; quarter-turn
normalization; negative-frequency domain membership at q=-1/2; and the exact
unit-input/frequency1000-output norm test. Scratch elaboration logs are retained.
All2643 source hashes, configuration3 and archive113 hashes verified unchanged
except the declared new module and root/audit registration. No settings changed,
errors suppressed, manuscript bytes modified or unrelated drafts adopted.
Evidence: `.lake/stardust-1572-*`. Local gates PASS; exact commit, receipt and
guarded BOTH-private-ref verification follow and are not pre-claimed here.

Ordinary domain density does NOT establish finite graph-core equality.
Resolvent surjectivity, graph-core identification, actual path-space construction,
nonlocal entropy consequences and completion of both manuscript repairs remain
open. Continue these Bakry obligations with exact theorem reuse. Preserve all
negative results, campaign priorities, verification and guarded backup gates.


## Checkpoint1573 — actual orbit-integral graph regularization

Bakry Objective1 remains ACTIVE. In `CauchyPoissonOrbitRegularization`,
`shifted_integral` proves that P_t applied to the actual Banach orbit integral
from0 toT equals the orbit integral fromt toT+t, for ALL continuous observables
and t,T>=0. Bounded linear integration commutation and the actual semigroup
law discharge the identity. No input generator-domain membership is assumed.
`integrated_graph` then proves the actual closed-generator identity
A(integral_0^T P_s f ds)=P_T f-f by the Banach fundamental theorem of calculus
at both shifted endpoints. Only the right-time derivative is asserted.

`average_graph` proves graph membership of normalized orbit averages for all
T>=0 (the Lean inverse convention gives the zero pair at T=0).
`average_tendsto` proves strong convergence to EVERY continuous f as T->0+.
For EVERY pair (f,g) in the full actual generator graph,
`graph_average_tendsto` proves joint norm-topology convergence of
(T^-1 integral_0^T P_s f ds,T^-1(P_T f-f)) to(f,g). Thus these are actual graph
regularizations, not merely approximations in the observable norm. The
construction reuses existing orbit integrals and the full generator; no new
operator/domain definitions or foundational infrastructure were introduced.
This is a standard semigroup mechanism instantiated rigorously, not a novelty
claim or an assertion of an actual path-space process.

Full6818-job root build39.174s; complete51128-safe-declaration transitive audit
37.643s, only propext/Classical.choice/Quot.sound. All5 public types and5 proofs
read unabridged; no new definitions or local instances. Five independent Lean
checks passed in30.551s without repair: arbitrary-input actual tangency,
zero-time integral endpoint, graph convergence along arbitrary positive vanishing
meshes, application of full-graph resolvent coercivity, and zero generator value
iff the endpoint semigroup fixes the original input. Earlier scratch failures
were elaboration issues and their logs remain; none is a counterexample.
All2644 source hashes, configuration3/archive113 hashes verified; only the new
module/root/audit registration changed mathematical sources. Compiler, trust,
resource and toolchain settings unchanged; style warnings visible. Manuscripts
and unrelated drafts preserved. Evidence `.lake/stardust-1573-*`. Local gates
PASS; exact commit/receipt and guarded BOTH-private-ref closure follow and are
not pre-claimed in this ledger entry.

Next: use bounded fixed-T graph regularization of a dense Fourier span to
investigate a genuine smoothed Fourier graph core, then an actual positive
Laplace resolvent. Ordinary Fourier density does not imply graph-core equality;
smoothed Fourier core would not imply the unsmoothed polynomials form a core.
Hilbert energy resolvents do not establish the Banach generator resolvent.
Finite Fourier graph-core equality, resolvent surjectivity, path-space and
nonlocal entropy/manuscript completion remain OPEN. Preserve Bakry priorities,
IBM rematch1562 frozen/incomplete status and all verification/backup gates.


## Checkpoint1574 — exact smoothed finite Fourier graph core

Bakry Objective1 remains ACTIVE. `Foundation/CauchyPoissonSmoothedCore.lean`
proves `smoothedPairs_closure`: for every real |q|<1 the full actual closed
generator graph on C(Circle,complex) is EXACTLY the product-supremum-norm closure
of pairs K_T u=(T^-1 integral_0^T P_s u ds,T^-1(P_T u-u)), where T>0 and u lies
in the finite Fourier span transported from AddCircle(period1). `fourierCore`
is that explicit mapped algebraic span; its density is proved from Mathlib
`span_fourier_closure_eq_top` and the verified period-one homeomorphism transport.
For fixed T the actual map K_T is continuous. Its values on arbitrary continuous
inputs lie in the closure of K_T applied to the finite Fourier span. The
previous full-domain graph convergence of normalized averages then reaches
EVERY actual generator graph pair. Reverse inclusion uses actual graph
closedness and previously proved orbit-integral graph membership.

`smoothedCoreGraph_closure` additionally identifies the topological closure of
the LINEAR SPAN of these pairs with the full graph. `graph_pair_approximation`
gives a positive T and a finite Fourier input controlling the pair error by
any requested epsilon>0. This is a genuine smoothed graph core; it neither
asserts that the original finite Fourier polynomials form a graph core nor
assumes they are invariant under the semigroup. This standard semigroup/density
mechanism is not claimed as a new literature result. No rate, fixed averaging
time, path-space realization or resolvent surjectivity is inferred.

Full6819-job root build42.589s; complete51147-safe-declaration transitive audit
40.664s, only propext/Classical.choice/Quot.sound. All11 public types,7 full
proofs and4 definitions reviewed unabridged; no new local instances. Five
independent Lean checks passed in36.637s on the first attempt: separate
observable/generator error bounds, sequential approximation of every full graph
pair, minimality among closed relations containing the core, negative mode7
at q=-1/2 for every positive averaging time, and impossibility of a bounded
operator agreeing even just on this core at q=0. The last check uses closedness
to extend agreement and the previously verified actual unboundedness obstruction.
Scratch elaboration failures retained; no mathematical source repair after the
successful full build. Sources2645/config3/archive113 integrity verified;
ResearchSources and unrelated drafts untouched. No compiler/trust/resource/toolchain
changes or warning suppression. Evidence `.lake/stardust-1574-*`. Local gates
PASS; exact commit/receipt and guarded BOTH-private-ref verification follow,
not pre-claimed here.

Next: actual positive real Laplace resolvent and range/surjectivity, then valid
nonlocal entropy consequences and completion of both manuscript repairs.
Reuse audit: Mathlib's Measure.ResolventTransform is a Stieltjes/Cauchy algebraic
transform, not this semigroup resolvent; Hilbert graph-projection energy
resolvents likewise do not discharge this Banach generator problem. Existing
exponential-integrability and interval-integral tools offer a route via weighted
finite-time integrals and controlled tails. Smoothed graph-core equality is now
PROVED; unsmoothed polynomial graph-core equality remains OPEN. Preserve all
campaign, source, verification, independent-test, Git and guarded backup gates.


## Checkpoint1575 — actual positive Laplace resolvent and full range

Bakry Objective1 remains ACTIVE. `Foundation/CauchyPoissonLaplaceResolvent.lean`
constructs R_r f=int_(0,infinity) exp(-r s) P_s f ds as a genuine Banach integral
in C(Circle,complex), for every real |q|<1 and r>0. The actual contraction bound
discharges integrability against exponential decay. Finite weighted orbit
integrals satisfy A F_T=r F_T+exp(-rT)P_T f-f for EVERY continuous f and T>=0.
This follows from an exact shifted integral identity and Banach FTC at both
endpoints, not from assuming input generator-domain membership. Finite integrals
converge in sup norm; their boundary terms converge to zero; the actual closed
graph therefore gives (R_r f,r R_r f-f) in the full generator graph.

`positive_resolvent_onto` establishes full range of r-A. `resolvent` is a bounded
COMPLEX-linear operator, with `resolvent_norm` <=1/r. `graph_left_inverse` uses
the previously verified full-graph coercivity to prove R_r(r f-g)=f for EVERY
actual graph pair(f,g). `graph_iff_resolvent` gives the converse as well, exactly
identifying the full original graph by this inverse equation. No arbitrary
closed extension, formal Fourier-domain replacement or Hilbert energy-resolvent
substitution is used. These are standard semigroup facts instantiated for the
actual constructed kernel, not a literature-novelty claim. They concern the
supremum-norm generator; no L2-domain transfer is silently inferred.

Full6820-job root build40.753s; complete51179-safe-declaration transitive audit
38.856s, only propext/Classical.choice/Quot.sound. All20 public types,16 full
proofs and4 definitions read unabridged; no new local instances. Five independent
Lean checks passed in25.128s: actual norm-tangent recovery; uniqueness for any
full-domain solution; the signed two-parameter identity R_r-R_s=(s-r)R_r R_s;
actual integral normalization R_r 1=r^-1 1 for ALL poles; and quantitative
complex-observable stability at q=-1/2,r=2. Initial independent run25.109s failed
only on restricted-scalar normal forms and inverse numeral normalization; fixed
test scripts and original failed logs/timing are retained. Production mathematics
was unchanged after the full build. Scratch elaboration failures also retained.
Sources2646/config3/archive113 integrity verified, with only the new source and
root/audit registration changed. Original manuscripts/unrelated drafts preserved.
No compiler/trust/resource/toolchain changes or warning suppression. Evidence
`.lake/stardust-1575-*`. Local gates PASS; exact commit/receipt and guarded BOTH
private-ref closure follow, not pre-claimed in this entry.

Resolvent surjectivity is now PROVED and should not remain on the open list.
Smoothed graph-core equality1574 is preserved; unsmoothed finite Fourier
polynomial graph-core equality remains open. Return next to the concrete
nonlocal entropy/manuscript obligations rather than duplicating generator
infrastructure. Primary2 lines1495-1501 asks for sharp log-Sobolev under drift
and asserts that positive CD curvature supplies constant2/kappa; lines298-301
cite a separate nonlocal entropy-production approach. These exact assertions
need their own hypotheses/proofs; the present resolvent does NOT establish a
jump-process diffusion chain rule, sharp entropy rate, LSI or path-space process.
Reuse verified actual invariant law1567, finite weighted dissipation1564 and
nonsymmetry1563, and audit existing entropy results before new constructions.
Both primary manuscript repairs and full Bakry Objective1 remain incomplete.
All campaign/verification/source/Git/guarded-private-backup requirements persist.


## Checkpoint1576 — actual forward entropy monotonicity and invariant minorization

Bakry Objective1 remains ACTIVE. The focused reuse audit distinguishes the
existing discrete Poisson jump-entropy/Bregman and finite-core quadratic entropy
obstructions from the present Circle kernel. They are not interchangeable.
Mathlib `InformationTheory.klDiv_comp_right_le`, however, applies directly to
our verified Markov kernel and actual invariant probability law. New
`Foundation/CauchyPoissonEntropy.lean` proves `relative_entropy_contracts` for
EVERY initial probability law, |q|<1 and t>=0, with ENNReal KL divergence so
infinite initial entropy is allowed. `entropy_time_monotone` compares every
0<=s<=t using the actual kernel composition law. `entropy_stays_finite` proves
preservation of finite initial entropy. No reversibility, positive curvature,
diffusion chain rule or smooth density assumption is used. This is direct
reuse of data processing, not a novelty claim or a sharp LSI theorem.

`density_minorization` proves an actual uniform positive lower bound on the
ratio poleWeight(evolution(q,t,z),theta)/poleWeight(q,theta), over ALL starting
z in Circle and theta in[0,2pi], for each fixed |q|<1,t>0. The continuous ratio
is strictly positive on that compact set. `poleLaw_minorization` transfers this
to the genuine angle measures; `kernel_minorization` pushes it to Circle.
`strict_kernel_minorization` supplies some0<epsilon<1 with epsilon*nu_q<=K_t(z)
for EVERY z. `forward_minorization` integrates the same bound against ANY
initial probability law. Epsilon depends on q and the chosen positive t; no
formula, uniform t->0 bound, sharp coefficient or entropy decay rate is asserted.
A residual Markov kernel/mixture entropy argument remains needed for a verified
strict contraction rate. Minorization supplies nu_q absolutely continuous with
respect to the evolved law, NOT the reverse direction and not instant entropy
finiteness for a singular initial law.

Full6825-job root build40.523s; complete51188-safe-declaration transitive audit
37.656s, only propext/Classical.choice/Quot.sound. All9 public types/9 proofs
read unabridged; no new definitions. Two existing Markov and one invariant-law
probability local instances reviewed. Five independent Lean checks passed in
24.070s: the correct null-set direction for ANY evolved probability law;
real-valued entropy comparison only under finite initial entropy; exact zero
entropy of the invariant law; monotonicity for a singular Dirac initial law at
q=-1/2; and impossibility of any common positive invariant minorization at time0.
The last uses the distinct identity transitions from1 and-1; the invariant law
would give the singleton{1} both mass0 and mass1. Thus the strict positive-time
hypothesis has a verified obstruction to removal. Initial independent26.326s
failed only on an explicit lemma argument and simplified disjunction normal
forms; test-only fixes and failed logs/timings retained. Production unchanged
after full build; scratch failures retained, no error suppression.
Sources2647/config3/archive113 integrity verified; manuscripts/unrelated drafts
untouched. Compiler/trust/resource/toolchain settings unchanged, warnings visible.
Evidence `.lake/stardust-1576-*`. Local gates PASS; exact commit/receipt and
guarded BOTH-private-ref closure follow, not pre-claimed here.

Next: use actual minorization to investigate a measurable residual Markov
splitting and a legitimate nonlocal entropy contraction, with explicit domains
and coefficient hypotheses. Audit existing mixture/chain-rule tools before new
infrastructure. Keep the difference between forward-law KL and backward
observable entropy explicit in this nonsymmetric model. Neither sharp
log-Sobolev constant2/kappa nor the manuscript's diffusion-style implication
is repaired by monotonicity alone. Generator/resolvent1575 and smoothed core1574
remain verified; path-space, unsmoothed Fourier core and full manuscript repairs
remain open. All campaign/source/verification/Git/private requirements persist.


## Checkpoint1577 — actual invariant residual Markov splitting (October27,2026)

Bakry Objective1 remains ACTIVE; IBM rematch1562 CLOSED/FROZEN, full intrinsic
IBM deferred; pseudo1293 frozen. No campaign transition or priority change.
From mathematical baseline bb05f2a345dff789cb17140bbbe4627d644c518c,
`Foundation/CauchyPoissonResidualKernel.lean` constructs the actual residual
angle density (w(evolution(q,t,z),theta)-epsilon*w(q,theta))/(1-epsilon), its
withDensity kernel, and its pushforward by Circle.exp. Joint measurability,
nonnegativity on the angle domain, integrability and exact mass1 are proved
under the explicit density minorization, |q|<1, t>0 and epsilon<1. These are
actual measures/kernels, not a formal subtraction of probability laws.

`residualKernel_split` proves K_t(z)=epsilon*nu_q+(1-epsilon)*R_t(z) for
0<=epsilon<1 and the pointwise minorization. `forward_split` extends this exact
identity to EVERY probability initial law, including singular laws.
`residualKernel_invariant` proves R_t composed with nu_q equals nu_q; finite
measure cancellation and the nonzero finite coefficient are discharged.
`strict_density_minorization` and `invariant_markov_splitting` discharge the
existence of some0<epsilon<1 for EVERY fixed |q|<1 and t>0. The residual is an
explicit invariant Markov kernel. No semigroup law for R_t, uniform t->0
coefficient, sharp coefficient, path-space process or entropy rate is asserted.
This is standard minorization/splitting mathematics specialized to the actual
verified nonsymmetric flow, not a novelty claim. No external literature claim
was needed for this direct theorem-reuse checkpoint.

Full6826-job root build29.070s; complete51216-safe-declaration transitive audit
46.208s, only propext/Classical.choice/Quot.sound. All17 public types,14 proofs
and3 definitions read unabridged. One existing angle-Markov, one invariant-law
probability and one proved finite-measure local instance reviewed. Five
independent Lean checks passed in30.196s: residual KL data processing against
nu_q; actual negative-pole Dirac-law splitting; probability preservation for
arbitrary initial laws; epsilon=1 produces the zero kernel and CANNOT be Markov;
and invariant null sets remain null for almost every residual starting state.
The initial independent28.941s failed on a missing local finite-measure instance
and Measurable versus AEMeasurable API argument; test-only repairs, source,
logs and timings retained. Scratch algebra/rewrite/typeclass repairs retained.
A precommit whitespace check caught extra EOF blank lines. After removal,
full build/audit/independent gates were repeated on the final bytes; prior
successful41.538s/39.734s/33.978s evidence retained. Public-type output identical.
Production unchanged after the final complete build; no trust/resource changes or
suppression of errors/warnings. Source2648/config3/archive113 integrity PASS.
Original manuscript hashes remain pinned to inventory1292; no ResearchSources
or unrelated draft changes. Evidence `.lake/stardust-1577-*`. Local gates PASS;
exact commit/receipt and guarded BOTH-private-ref closure follow, not preclaimed.

NEXT: prove the appropriate mixture KL convexity/contraction using existing
chain-rule/data-processing machinery where possible. Residual entropy
monotonicity is verified independently, but a factor(1-epsilon) contraction for
the full transition remains a separate obligation. Do not identify forward-law
KL with backward-observable entropy in this nonsymmetric model. Sharp LSI2/kappa,
instant finiteness from singular laws, unsmoothed Fourier core, path-space and
both primary manuscript repairs remain OPEN. Actual closed generator/resolvent
and smoothed graph core are already verified and should be reused. Preserve
all audits, manuscript bytes, exact-commit receipts and guarded private backups.


## Checkpoint1578 — actual finite-time geometric entropy contraction (October27,2026)

Bakry Objective1 ACTIVE; IBM rematch1562 and pseudo1293 remain frozen. From
verified baseline0fe60129a03582e1c36d888ed9a04a95e191c145, the residual
splitting now yields a genuine quantitative forward-law entropy estimate.
`Foundation/CauchyPoissonMixtureEntropy.lean` proves a reusable KL mixture bound
on ANY measurable space for probability measures mu,nu and nonnegative weights
a+b=1: KL(a*nu+b*mu||nu)<=b*KL(mu||nu). `mixture_rnDeriv` uses actual measure
Radon-Nikodym derivatives, including the absolutely continuous part when mu is
singular. Convexity of Mathlib's klFun at1, with klFun(1)=0, gives the pointwise
bound. The integral proof explicitly requires mu<<nu; `mixture_kl_bound_all`
then handles b=0 separately and non-AC inputs with b>0 via infinite KL. No
implicit integrability hypothesis or false 0*infinity manipulation is used.
Exact dependencies: Measure.rnDeriv_add/rnDeriv_smul_left/rnDeriv_self/
rnDeriv_lt_top, InformationTheory.convexOn_klFun/klFun_one/
klDiv_eq_lintegral_klFun_of_ac/klDiv_of_not_ac and klDiv_comp_right_le, from
pinned Mathlib. This is standard convexity/data-processing mathematics, not a
novel general information-theory claim; no new external-source claim is made.

`entropy_contraction` combines that bound with checkpoint1577's ACTUAL invariant
residual probability kernel. `exists_entropy_contraction` proves for EVERY
|q|<1 and fixed t>0 some0<c<1 works for EVERY probability initial law mu:
KL(K_t mu||nu_q)<=c*KL(mu||nu_q). `entropy_geometric` reuses actual kernel
composition to iterate at ALL n>=0; `exists_geometric_entropy_decay` discharges
the coefficient existence and yields KL(K_(n*t) mu||nu_q)<=c^n*KL(mu||nu_q).
The coefficient depends on q,t, not mu or n. Infinite initial entropy is allowed
as an extended-valued bound, but supplies no finite numerical conclusion.
This closes the previous fixed-positive-time strict contraction obligation.
It does NOT establish a sharp coefficient, uniform small-time rate, entropy
production identity, instantaneous finite entropy from singular inputs, or the
primary manuscript2's sharp log-Sobolev constant2/kappa (lines1495-1501).
Forward-law entropy is not identified with backward-observable entropy in this
nonsymmetric model. No diffusion chain rule or positive CD hypothesis is used.

Full6827-job root build42.377s; complete51224-safe-declaration transitive audit
42.564s, only propext/Classical.choice/Quot.sound. All8 public types and8 proofs
read unabridged; no new definitions. Two existing Markov and one invariant-law
probability local instances reviewed. Five independent Lean checks passed on
first run25.063s: exact reset endpoint without AC; finite real-valued geometric
estimate with ENNReal finiteness discharged; strict decrease of finite positive
entropy; negative-pole singular Dirac inputs; and the geometric bound at every
later off-grid time by actual semigroup monotonicity. Scratch failures retained:
smul normalization, add versus add_left AC API, explicit coercion equalities.
No theorem weakening or trust/resource changes, no warnings/errors suppressed.
Source2649/config3/archive113 hash integrity PASS; original manuscript hashes
still pinned to inventory1292. No ResearchSources or unrelated draft edits.
Evidence `.lake/stardust-1578-*`. Local gates PASS; exact commit/receipt and
BOTH guarded private-ref verification follow, not preclaimed in this record.

NEXT: discharge genuine entropy convergence for finite-entropy laws and examine
whether positive-time upper density bounds rigorously regularize arbitrary
initial laws. Such upper domination is a DIFFERENT direction from minorization;
prove it before using RN bounds or asserting instantaneous finiteness. Then
connect valid entropy estimates to the manuscript's nonlocal dissipation/domain
claims without assuming reversibility or a diffusion CD-to-LSI implication.
Reuse the actual closed generator/resolvent1575 and smoothed graph core1574.
Both manuscript repairs, sharpLSI, path-space and unsmoothed Fourier core remain
OPEN. Campaign queue and all verification/source/Git/private requirements intact.


## Checkpoint1579 — positive-time entropy regularization for every initial law (October27,2026)

Bakry Objective1 ACTIVE; IBM rematch1562 and pseudo1293 remain frozen. From
verified baseline e5a586ef5e512efe2e326f55f09b01c0383a9028,
`Foundation/CauchyPoissonRegularization.lean` establishes the previously missing
UPPER domination. For EVERY |q|<1,t>0, `density_majorization` bounds the actual
Poisson density ratio uniformly on Circle x[0,2pi]. Continuity, strict disk
membership and positivity of the denominator are reused from the actual flow.
Compactness supplies a finite upper bound; max(B,1) supplies a positive choice.
`kernel_majorization` transports the density bound through actual withDensity
and Circle.exp, proving K_t(z)<=C*nu_q for ALL z. `forward_majorization` gives
the SAME C for EVERY probability initial law. This is the correct direction
for evolved-law absolute continuity with respect to the invariant law; it is
proved independently of the opposite minorization established in1576.

The reusable `rnDeriv_bound` works on any measurable space with sigma-finite
reference: mu<=C*nu implies dmu/dnu<=C almost everywhere (C may be ENNReal).
It follows from setwise RN-integral bounds and ae comparison, not a hidden
probability assumption. `entropy_finite_of_domination` requires probability
measures and a finite nonnegative REAL coefficient. Domination gives actual
absolute continuity; RN values lie a.e. in[0,C]; continuity of klFun on this
compact interval bounds its lintegral. Thus `positive_time_entropy_finite`
proves KL(K_t mu||nu_q)<infinity for EVERY probability input mu and EVERY t>0.
No finite initial entropy or initial absolute continuity is assumed. The
previous instantaneous-finiteness obligation is now DISCHARGED. Theorem reuse
is standard compactness/Radon-Nikodym theory, not a novelty assertion. Exact
Mathlib dependencies include IsCompact.bddAbove_image, withDensity_mono,
Measure.setLIntegral_rnDeriv_le, ae_le_of_forall_setLIntegral_le_of_sigmaFinite,
InformationTheory.continuous_klFun and klDiv_eq_lintegral_klFun_of_ac.

Full6828-job root build44.727s; complete51230-safe-declaration transitive audit
39.483s, only propext/Classical.choice/Quot.sound. All6 public types and6 proofs
read unabridged; no definitions. One existing kernel-Markov and one invariant
probability local instance reviewed. Five independent Lean checks passed in
24.843s: BOTH null-set directions for every evolved probability; finite entropy
from a negative-pole Dirac input; positive burn-in followed by geometric decay
with a finite starting entropy for ANY law; a common upper coefficient for
ALL initial laws; and the necessary C>=1 for probability domination. Initial
independent27.481s failed only on the nonnegativity argument to the ofReal
comparison API; test-only positivity proof repaired it, logs/source retained.
Scratch1 hit default heartbeat limit on an underconstrained compact-bound
elaboration and a withDensity rewrite; explicit real types, image witness and
RHS fixed both at unchanged default resources. No theorem weakening, heartbeat
increase, error suppression or compiler/trust change. Production unchanged after
full build. Sources2650/config3/archive113 hash integrity PASS. Manuscript bytes
and unrelated drafts untouched; all original hashes remain pinned to1292.
Evidence `.lake/stardust-1579-*`. Local gates PASS; exact commit/receipt and
BOTH guarded private-ref verification follow, not preclaimed in this record.

NEXT: prove full large-time entropy convergence from the actual burn-in plus
geometric estimate, including all real times, and investigate quantitative
uniform bounds where useful. Then connect entropy with a genuine nonlocal
production/domain identity. Sharp LSI2/kappa, a uniform small-time exponential
rate, reversibility, path-space and both manuscript repairs remain OPEN. The
upper constant may diverge as t approaches0; no time0 regularization claimed.
Do not conflate forward-law entropy with backward-observable entropy for q!=0.
Actual closed generator/resolvent1575 and smoothed graph core1574 are reusable.
All campaign, verification, source-integrity and guarded PRIVATE gates persist.


## Checkpoint1580 — full real-time entropy limit and fixed-law uniqueness (October27,2026)

Bakry Objective1 ACTIVE; IBM rematch1562 and pseudo1293 frozen. From verified
baseline19b2732ef1e5ca886a761e084c7186327153825e,
`Foundation/CauchyPoissonEntropyLimit.lean` proves `entropy_tendsto_zero`:
for EVERY |q|<1 and EVERY probability initial law mu, the ACTUAL forward-law
KL(K_t mu||nu_q) tends to0 as REAL t tends to+infinity. This is an ENNReal
topological limit, not a toReal convention that discards infinite entropy.
No initial absolute continuity or finite initial entropy is assumed. Actual
positive-time regularization1579 makes the time1 law finite; the geometric
bound1578 applies thereafter. `burnin_geometric_bound` uses actual kernel
composition at s+n*t. `finite_geometric_tendsto` explicitly requires finite
ENNReal D and transports c^n*D.toReal through continuous ofReal. Monotonicity
controls EVERY real time beyond a chosen integer checkpoint; no unjustified
subsequence-to-full-limit inference or time continuity assumption is used.

`positive_time_fixed_law_unique` proves that ANY probability law fixed by ONE
actual transition K_t, t>0, equals nu_q. Fixedness first gives finite entropy
by regularization, then strict contraction forces that entropy to0; Mathlib's
klDiv_eq_zero_iff identifies the law. No common stationarity assumption for all
times, reversibility, generator domain, density hypothesis or PRP is imposed.
These are standard ergodic consequences of the verified minorization/upper
bounds, not a novelty claim or a sharp log-Sobolev theorem. Exact reused tools
include ENNReal.tendsto_atTop_zero, tendsto_order,
tendsto_pow_atTop_nhds_zero_of_lt_one, ENNReal.continuous_ofReal and
InformationTheory.klDiv_eq_zero_iff, with the actual previous kernel theorems.

Full6829-job root build40.899s; complete51235-safe-declaration transitive audit
39.023s, only propext/Classical.choice/Quot.sound. All4 public types and4 proofs
read unabridged; no definitions. One existing kernel-Markov and one invariant
probability local instance reviewed. Five independent Lean checks passed first
run24.895s: singular negative-pole Dirac entropy limit; real entropy limit by
continuity at finite0; iff characterization of positive-time fixed laws; full
stationarity implies the same invariant law; and explicit time0 failure of
uniqueness using the distinct Dirac laws at1 and-1. The latter verifies the
strict positive-time restriction rather than silently weakening it.
Scratch1 failed only to rewrite a function composition inside Tendsto; explicit
function extensionality repaired it. Scratch logs retained. Production unchanged
after full build; no heartbeat/resource/compiler/trust changes or suppression.
Sources2651/config3/archive113 integrity PASS; ResearchSources and unrelated
drafts untouched. Evidence `.lake/stardust-1580-*`. Local gates PASS; exact
commit/receipt and BOTH guarded private-ref verification follow, not preclaimed.

The previously open full large-time entropy convergence obligation is now
DISCHARGED for ALL probability inputs and real times. NEXT return to the precise
remaining Bakry manuscript/domain and nonlocal entropy-production obligations,
using the actual closed generator/resolvent1575, smoothed core1574 and the
now-complete forward entropy regularization/contraction/limit chain. Audit the
manuscript's exact entropy functional and adjoint conventions before asserting
an infinitesimal production identity. Forward-law entropy and backward-observable
entropy differ in this nonsymmetric model. Sharp LSI2/kappa, a uniform small-time
rate, full L2-domain transfer, unsmoothed Fourier core, path-space construction
and both complete manuscript repairs remain OPEN. Do not substitute generic
finite-dimensional entropy identities for this actual process/operator claim.
Campaign queue and every verification/source/Git/private requirement remain.


## Checkpoint1581 — actual full-generator-domain observable entropy production (October27,2026)

Bakry Objective1 ACTIVE; IBM rematch1562 and pseudo1293 remain frozen. From
verified baseline d8766e32df2674658553333e8503b6f4c700e7bf, selective rereading
of primary2 lines286-305 and1495-1501 confirms that entropy production is cited
as an alternative to a diffusion chain rule, while the stated CD-to-LSI route
still needs repair. Existing `CauchyDiffusionChainObstruction` gives the actual
cosine cubic defect -3/2, unchanged by sine drift. This is not a refutation of
all possible model-specific LSI inequalities. Existing weighted dissipativity
was a finite-Fourier-core statement; it did not supply a full-domain logarithmic
production identity. The new proof reuses the ACTUAL closed generator1571,
resolved domain/core/resolvent1574-75, and invariant Markov semigroup1567-68.

`Foundation/CauchyPoissonObservableEntropy.lean` now proves for EVERY graph
pair(f,g) of that closed generator on C(Circle,complex), |q|<1, with
Re f(z)>=delta>0, and EVERY t>0:
 d/dt integral klFun(Re P_t f) dnu_q
   = integral log(Re P_t f) Re(P_t g) dnu_q <=0.
Here klFun(x)=x log x+1-x. This is the declared BACKWARD-OBSERVABLE functional;
it is not identified with forward-law entropy for an arbitrary initial density.
No unit-mass hypothesis is needed for this functional. Real observables are
included; arbitrary imaginary parts are allowed only because real parts are
explicitly used. The exact statements retain this convention.

`graph_orbit_derivative` obtains the full norm HasDerivAt at t>0 from the actual
integrated graph equation and FTC, then real point evaluation gives scalar
derivatives. `orbit_real_lower` proves the same lower bound under actual kernel
averaging. The logarithm is uniformly bounded on[delta,||f||]; contraction bounds
P_t g. `observable_entropy_derivative` verifies all measurability, integrability
and dominated-differentiation hypotheses. `kernel_entropy_jensen` and
`observable_entropy_decreases` prove decrease for EVERY continuous nonnegative
real part without a generator-domain hypothesis. Actual invariant-law integration
is justified by Kernel.integral_comp through the constant invariant kernel.
Finally `observable_entropy_production_nonpos` combines semigroup increments,
Jensen and the actual derivative limit. It does not assume a diffusion chain
rule, reversibility or a pre-existing abstract entropy-production hypothesis.
This is standard Markov/convexity/domain calculus specialized rigorously to the
actual model, not a novelty assertion. Main exact Mathlib dependencies:
hasDerivAt_integral_of_dominated_loc_of_deriv_le, hasDerivAt_klFun,
convexOn_klFun.map_integral_le, Kernel.integral_comp and integral FTC.

Full6830-job root build41.109s; complete51242-safe-declaration transitive audit
40.201s, only propext/Classical.choice/Quot.sound. All7 public types/7 proofs
read unabridged; no definitions. Three existing Markov and two invariant-law
probability local instances reviewed. Five independent Lean checks passed first
run24.447s: genuine norm-tangent inputs; arbitrary full-domain production
witness; nonnegative functional and contraction without graph membership;
no finite right derivative of klFun at0; and zero production for constants.
The last two guard against unrestricted logarithmic differentiation and an
unjustified universal strict sign. Scratch failures were elaboration/API issues:
RCLike.re versus Complex.re rewrites, composed derivative evaluation, explicit
norm bounds and continuity of log. Explicit reCLM integral identity repaired
the rewrite; no added assumptions, trust/resource changes or error suppression.
Production unchanged after full build. Sources2652/config3/archive113 hashes
PASS; manuscripts/unrelated drafts untouched. Evidence `.lake/stardust-1581-*`.
Local gates PASS; exact commit/receipt and guarded BOTH-private-ref closure follow.

NEXT: identify the precise remaining adjoint/forward-density and jump-Bregman
production connections, with actual domains and signs, or consolidate repaired
manuscript statements if no stronger identification is justified. No forward
adjoint-domain identification, explicit jump-kernel Bregman representation,
sharpLSI2/kappa, uniform small-time rate, completed L2 transfer, unsmoothed
Fourier core or path-space theorem is claimed. Both manuscript repairs remain
OPEN. Earlier all-law forward KL regularization/contraction/limit and uniqueness
are PROVED and must not be rebuilt. Preserve all campaign and verification gates.

## Checkpoint1582 — actual forward law and full-domain weak Kolmogorov equation

Bakry Objective1 remains ACTIVE; bounded IBM rematch1562 remains FROZEN and
incomplete beyond its stopping contract. No campaign or manuscript bytes change.
This continues1581's forward/backward distinction using the actual Cauchy circle
kernel and full closed generator, rather than imposing reversibility refuted by
CauchyPoissonNonSymmetry. The manuscript's density-adjoint and entropy claims
cannot be inferred simply by renaming a backward observable as a forward density.

`Foundation/CauchyPoissonForwardDual.lean` constructs `lawFunctional` on complex
continuous circle observables for EVERY initial probability measure, with norm
at most1. `dualOrbit` composes a continuous functional with the actual transition
operator; it is contractive, has identity at0, satisfies the nonnegative-time
semigroup law, and is continuous when evaluated on each continuous observable.
Negative times are only the existing max(t,0) extension. No norm continuity of
the entire dual semigroup is asserted.

`actual_law_duality` identifies this action with the genuine evolved measure
mu_t = (kernel q t) compose mu, for |q|<1 and t>=0. Kernel composition/Fubini and
compact-continuous integrability discharge the actual measure pairing; this is
not an abstract action lacking a stochastic-law identification. For EVERY pair
(f,g) in the full actual closed generator graph, `weak_forward_derivative` proves
at every t>0:

    d/dt integral f dmu_t = integral g dmu_t.

`weak_forward_integrated` also proves, for EVERY t>=0:

    integral f dmu_t - integral f dmu = integral_0^t integral g dmu_u du.

All integrals here are complex Bochner integrals. No initial density, initial
finite entropy, Fourier-polynomial presentation, diffusion chain rule or
symmetry is assumed. The integrated equation follows by applying the bounded
law functional to the existing full-domain integrated orbit identity; continuous
linear interval-integral interchange is justified. The positive-time derivative
uses the actual full norm orbit derivative and local positive-time equality of
the measure pairing. Standard semigroup duality is reused, with no novelty claim.

Full root6831 jobs44.793s; complete51261-safe-declaration transitive audit41.395s,
only propext/Classical.choice/Quot.sound. All11 public types,9 proofs,2 definitions
and one existing local Markov instance reviewed unabridged. Five independent
Lean tests passed25.224s: singular point-mass derivative with actual point kernel;
arbitrary closed-domain derivative witness; invariant mean of every generator
value is zero; actual law pairing obeys dual composition; and exact probability
mass preservation including time0. The first test initially needed an explicit
measurable-kernel dirac_bind rewrite (27.439s failed elaboration retained).
Earlier scratch failures concerned unfolding max(t,0), kernel composition and
functional coercions; all repaired without changing assumptions or resources.
No errors/warnings suppressed, no production edits after the full build.
Sources2653/config3/archive113 hashes PASS; original manuscripts and unrelated
untracked drafts preserved. Evidence `.lake/stardust-1582-*`. Local gates PASS;
exact commit receipt and guarded BOTH-private-ref verification follow.

Remaining: identify a justified strong forward-adjoint/density domain and actual
jump-Bregman entropy-production representation. Weak law differentiation does
not establish either. SharpLSI2/kappa, uniform small-time decay rate, full L2
domain transfer, unsmoothed Fourier core and path-space construction remain
unproved here; BOTH manuscript repairs remain OPEN. Reuse the existing all-law
positive-time finite entropy, geometric contraction, full-time entropy limit,
unique invariant law and full-domain backward-observable production results.
Next pursue an exact adjoint-domain connection or consolidate the repaired
manuscript claims if no stronger domain identification is justified.

## Checkpoint1583 — point-mass obstruction to unrestricted strong forward calculus

Bakry Objective1 ACTIVE; bounded IBM rematch1562 FROZEN. Read-only review of the
second primary manuscript lines1081-1118 reconfirmed that its Cauchy/sine-drift
operator and curvature assertions require care about backward observables versus
forward laws. This checkpoint tests a proposed strengthening of our repair; it
does NOT attribute an unrestricted all-measure strong-continuity claim to the
manuscript. The existing real BanachUnboundedAdjoint machinery was inspected;
its dense-domain uniqueness does not itself supply an adjoint value for a law.
No duplicate adjoint infrastructure or new domain assumptions were introduced.

`Foundation/CauchyPoissonDualObstruction.lean` proves an explicit obstruction
using the existing actual Fourier moments and strict disk flow. For EVERY
|q|<1, point x on the circle, and t>0, let phi_x be evaluation/integration
against delta_x. Then:

    1 <= norm(dualOrbit q t phi_x - phi_x).

`dirac_dual_power_norm` identifies the action on the nth unit coordinate mode:
its modulus is norm(evolution q t x)^n, which tends to0 as n tends to infinity
because the positive-time pole is strictly inside the disk. Initial evaluation
has modulus1 on those same norm-one observables. The reverse triangle and
operator norm bound yield `dirac_dual_norm_gap`. No measure-representation or
unproved total-variation identification is needed: this is the actual norm on
the continuous complex dual. The lower bound1 is sufficient, not claimed sharp.
`dirac_dual_not_strong_right` proves failure of right norm convergence at0 for
EVERY admissible drift. It coexists with1582's weak observable continuity and
all-law weak differential/integrated Kolmogorov equation.

At q=0, `zero_dirac_no_adjoint_value` additionally proves there is NO bounded
complex-linear functional psi satisfying psi(f)=phi_x(g) for EVERY pair(f,g)
in the full actual generator graph. The existing coordinate powers belong to
the graph, have norm1, and their generator evaluations have modulus n. Taking
n>norm(psi) contradicts boundedness. This is the exact transposed-domain pairing
criterion, not a redefinition of a point mass as inadmissible. No claim that
all nonzero-drift Dirac adjoint domains have been characterized is made.

Full6832-job build41.959s; complete51267-safe-declaration transitive audit39.975s,
only propext/Classical.choice/Quot.sound. All5 public theorem types and complete
proofs reviewed; zero new definitions/local instances. Four independent Lean
checks passed FIRST RUN24.662s: weak continuity alongside strong failure;
no positive-time sequence can recover the initial law in dual norm; the actual
distance lies between1 and2 (no infinite-mass explanation); and unbounded
transpose values already on unit coordinate modes. Scratch coercion failures
were repaired by explicit sub_apply/Dirac evaluation and typed constant limits.
Deprecated sub_apply usage was replaced before the full build. No errors or
warnings suppressed, no trust/resource/version changes. All2654 sources, config3
and archive113 hashes match. Original manuscripts/unrelated drafts preserved.
Evidence `.lake/stardust-1583-*`; local gates PASS, then exact receipt and guarded
BOTH PRIVATE branch verification. No novelty assertion for this semigroup
obstruction, and no change to mathematical priorities.

This rules out placing EVERY probability initial law in an unrestricted strong
forward C0/adjoint calculus of this dual-norm type. It does not obstruct weak
laws, positive-time regularization, or strong calculus on a justified restricted
density/adjoint domain. NEXT investigate such concrete domains, actual
positive-time density derivatives or averaged-law/resolvent regularization by
reusing existing closed-generator and Laplace results. Do not retry universal
strong convergence at a Dirac initial law. Strong forward density-domain and
jump-Bregman production identifications, sharpLSI2/kappa, uniform small-time
rate, fullL2 domain transfer, unsmoothed Fourier core, pathspace and BOTH
manuscript repairs remain OPEN. All earlier verified positive results survive.

## Checkpoint1584 — averaged-law adjoint pairing and strong orbit regularization

Bakry Objective1 ACTIVE; all queue and frozen-campaign boundaries unchanged.
This is a constructive continuation of1583's initial-point-mass obstruction.
Reuse the actual closed generator, integralOperator, integrated graph and orbit
regularization; do not build another abstract adjoint framework.

`Foundation/CauchyPoissonDualAverage.lean` defines one bounded complex functional:

    averageDual(T,phi) = (1/T) phi compose integralOperator(T).

For T>0 this is the normalized orbit average. `average_actual_law` identifies
its value for phi=lawFunctional(mu), EVERY probability mu and continuous complex
observable f, with (1/T) integral_0^T integral f d(K_s mu) ds. These are actual
law expectations with justified interval-integral interchange. A separate
measure-valued average or Radon--Nikodym density is not constructed here.

`average_adjoint_pairing` proves, for EVERY pair(f,g) in the FULL closed
generator graph and T>=0:

    averageDual(T,phi)(g) = ((dualOrbit(T,phi)-phi)/T)(f).

The right-hand side is an explicit bounded complex functional, giving exactly
the transposed-generator pairing on the original full domain, not merely on
Fourier polynomials. The T=0 expression uses Lean's inverse-zero convention and
is zero; normalization and continuity estimates below require T>0.
`average_weak_limit` proves recovery of phi against each observable as T->0+.
It does NOT assert convergence in the norm of the dual.

`integral_commutes` and `integrated_shift_bound` reuse the actual semigroup and
shifted orbit-integral identity. Removing the common interval leaves a tail
minus a head, each controlled by t*norm(f). Thus `average_strong_bound` proves
for every t>=0, T>0 and bounded phi:

    norm(dualOrbit(t,averageDual(T,phi))-averageDual(T,phi))
      <= (2t/T) norm(phi).

`average_strong_right` gives strong right continuity of the averaged orbit.
This works even when phi is an initial point-mass functional, whose unaveraged
orbit fails norm continuity by1583. The bound degenerates as T->0+, preserving
that obstruction. No strong time derivative of the averaged orbit is asserted:
a bounded transpose value and strong orbit continuity alone are not identified
with a strong derivative here. This is standard averaging regularization applied
to the actual verified model, with no novelty assertion.

Full6833-job build46.775s; complete51281-safe-declaration transitive audit50.739s,
only propext/Classical.choice/Quot.sound. All9 public types,8 full proofs,1
definition reviewed; zero local instances added. Four independent Lean checks
passed30.109s: averaged strong continuity alongside raw Dirac failure; exact
normalization on1; an actual-law bounded transpose witness for EVERY graph pair;
and norm contraction of averageDual. First test run29.687s failed solely because
an extra ring tactic followed an already-complete field_simp proof; production
was unchanged. Scratch repairs used explicit real scalar restriction for a
complex CLM, explicit interval measure and limit basepoint. All failures retained.
The source keyword check initially matched English 'admit' in the sole module
documentation block; it now excludes that explicitly counted single non-nested
comment while scanning all code unchanged. The complete transitive Lean audit
remains unchanged. No proof/error suppression, trust, toolchain or resource change.
Sources2655/config3/archive113 integrity PASS. Original manuscripts and unrelated
drafts untouched. Evidence `.lake/stardust-1584-*`; local gates PASS; exact commit
receipt and guarded BOTH-private-ref closure follow.

NEXT prioritize concrete measure/density realization and positive-time forward
domain/entropy-production links. Do not mistake this functional regularization
for that missing density identification or repeat generic averaging foundations.
Strong forward-density domain, jump-Bregman production, sharpLSI2/kappa, uniform
small-time rate, fullL2 domain transfer, unsmoothed Fourier core, pathspace and
BOTH manuscript repairs remain OPEN. Earlier law regularization, entropy limits,
weak Kolmogorov equations, backward production and Dirac counterexamples survive.

## Checkpoint1585 — concrete continuous forward density, actual measure equality

Bakry Objective1 ACTIVE. This closes the concrete positive-time density
REALIZATION gap identified after1582-1584; it does not close the time-derivative
or strong forward-generator domain obligations. Original manuscripts and queue
remain unchanged. Reuse the actual Poisson disk flow, angular density, invariant
circle probability law and measurable transition kernel already verified.

`Foundation/CauchyPoissonForwardDensity.lean` defines circleWeight(v,w) as the
normalized Poisson kernel directly on Circle. Its angular pullback is the
existing poleWeight, with all normalization factors retained. For |q|<1,t>0:

    ratio(q,t,z,w) = circleWeight(evolution(q,t,z),w)/circleWeight(q,w),
    density(q,t,mu,w) = integral ratio(q,t,z,w) dmu(z).

The denominator is strictly positive. `ratio_continuous` proves joint spatial
continuity, and `ratio_positive` proves strict positivity. `kernel_density`
identifies invariantLaw(q).withDensity(ofReal(ratio(q,t,z,...))) with the ACTUAL
kernel(q,t,z). The proof is equality on every measurable set: pull back under
Circle.exp, unfold the genuine angular withDensity measure, and cancel the
positive invariant weight. It does not rely on equality of a selected set of
Fourier moments or an assumed density representation.

For EVERY initial probability measure mu, including singular starts,
`ratio_integrable`, `density_continuous` and `density_positive` give a concrete
continuous strictly positive real density. `forward_density` proves exactly:

    invariantLaw(q).withDensity(ofReal(density(q,t,mu,...))) = kernel(q,t) bind mu.

Tonelli swaps the actual initial-law integral with invariant-law integration;
measurability and the finite real integral/ofReal conversion are discharged.
`density_rnDeriv` identifies the chosen continuous representative with the
Radon--Nikodym derivative almost everywhere. `density_integral_pairing` proves
the complex Bochner change-of-density identity. Its arbitrary-function version
uses Lean's usual integral conventions; it does not assert integrability of an
arbitrary function. Continuous observables have the established compact-space
integrability. No measure construction or density claim is left hypothetical.

Four independent Lean checks passed FIRST RUN28.823s: normalization of the
density against1; Dirac initial data yields exactly the explicit kernel ratio;
compactness gives a positive lower and finite upper bound for each fixed
q,t,mu; and density pairing equals the previous backward-operator/lawFunctional
pairing. Bounds here are not asserted uniform as t->0. The Dirac definition
identity is algebraic for all parameters; probability-density claims retain
|q|<1 and t>0. Existing initial-time strong-dual obstructions remain intact.

Full6834-job root build46.751s; complete51301-safe-declaration transitive audit
46.558s, only propext/Classical.choice/Quot.sound. All17 public types,14 full
proofs,3 definitions and2 existing invariant-probability local instances read
unabridged. Sources2656/config3/archive113 hashes PASS; production unchanged
after fullbuild. Failed scratch logs retained: explicit indicator/preimage,
function-composition and withDensity rewrite elaboration; swapped parameter
inference reached the default heartbeat limit once. Explicitly typed inner/
outer maps, scalar functions and measure identities repaired the proof without
raising heartbeats or altering hypotheses. No errors/warnings suppressed, no
trust/toolchain/resource changes. Evidence `.lake/stardust-1585-*`. Local gates
PASS; exact-commit receipt and guarded BOTH-private-branch closure follow.
No novelty claim for the kernel/Fubini density construction.

NEXT actual positive-time regularity of this concrete density in time, with
bounds away from0, then the strong forward-adjoint domain and forward entropy
production if justified. Density realization itself is now PROVED and must not
be repeatedly rebuilt. Strong density-generator identification, jump-Bregman
production, sharpLSI2/kappa, uniform small-time rate, fullL2 domain transfer,
unsmoothed Fourier core, pathspace and BOTH manuscript repairs remain OPEN.
Backward observable entropy production is distinct at nonzero drift; preserve
nonsymmetry, all-law entropy regularization/limits, weak forward calculus,
point-mass counterexamples and averaged-functional regularization.
