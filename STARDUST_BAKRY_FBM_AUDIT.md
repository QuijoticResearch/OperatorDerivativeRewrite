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
