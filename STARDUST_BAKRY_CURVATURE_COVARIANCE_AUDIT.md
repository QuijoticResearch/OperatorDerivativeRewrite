# Bakry Objective2 — curvature/covariance audit

ACTIVE since user-authorized transition6615f16; Objective1 remains deferred and
incomplete. This audit is a partial deliverable, not completion of Objective2.

## Initial reuse and literature audit (October27, checkpoint1602)

The brief displays (psi(xi)+psi(eta)-psi(xi+eta))/2. On a complex Fourier core
this is a bilinear convention; the existing conjugate-linear first slot uses
psi(eta-xi), as defined in FiniteStableGamma.Core.kernel and proved for the
actual recursive Gamma by gammaIter_single. For psi(x)=x^2 the displayed plus
kernel at(1,1) is -1, so it cannot be treated as a positive covariance kernel.
For even psi it is the difference-kernel evaluated at(-xi,eta), a cross pairing,
not the Gram matrix obtained by changing both arguments together.

The difference-kernel/conditional-negative-type correspondence is established
mathematics. Hermine Bierme, Introduction to random fields and scale invariance,
LectureI (April4,2016), PDF pages18–20 (zero-indexed), states the stationary-
increment covariance and Schoenberg equivalence. Ramesh Gangolli, Annales IHP B
3(2),1967,121–226, ChapterI, introduces Levy–Schoenberg kernels and describes
the corresponding conditionally negative functions and Gaussian covariances.
Only these relevant sections were examined, not the whole107-page paper.
Sources:
- https://www.lebesgue.fr/sites/default/files/attach/Bierme_Lecture1.pdf
- https://www.numdam.org/item/AIHPB_1967__3_2_121_0.pdf
No novelty is claimed for the finite anchored-kernel theorem below. Full
Levy–Khintchine, Bernstein subordination, exponential-positive-definite and
infinite process realizations have NOT been verified by this checkpoint.

Exact reusable declarations:
- FiniteStableGamma.Core.kernel, gammaIter_single, gammaIter_finite: actual
  signed Fourier multiplier/Gamma algebra, requiring no probabilistic positivity.
- FiniteStableGamma.Core.stable_kernel_covariance and
  FractionalCovarianceMatrices.covarianceMatrix_posSemidef: genuine fractional
  covariance for0<H<1, with sign and parameter hypotheses explicit.
- FractionalCovarianceMatrices.hurst_two_negative_energy: preserved quartic
  covariance obstruction; the new zero-sum test agrees with it.
- FractionalFourierSemigroup.contraction,strong_continuity,generator_iff:
  nonnegative rates give a genuine L2 contraction semigroup and exact domain.
  This alone does not give Markov positivity or covariance positivity.
- FractionalCovarianceMatrices.covariancePower_posSemidef and Mathlib's
  Matrix.PosSemidef.hadamard: existing route to integer kernel powers, not a
  positive curvature constant or comparison between successive powers.

## Finite general theorem and exact limitations

Foundation.AnchoredCovariance defines finite real energy c^T d c and the
anchored kernel K_o(i,j)=(d(i,o)+d(o,j)-d(i,j))/2. Center c by subtracting its
total mass at the anchor o. `covariance_identity` proves
2*c^T K_o c = -(centered c)^T d (centered c), assuming only d(o,o)=0.
`anchored_positive_iff` gives the exact quadratic-form equivalence;
`anchored_posSemidef_iff` adds symmetry and proves the genuine matrix PSD
iff conditional negativity on ALL zero-sum coefficient vectors.
No positive-definiteness assumption is smuggled into the hypothesis.

`fourier_covariance_iff` directly uses the verified FiniteStableGamma kernel:
for any even real symbol psi with psi(0)=0 and finite frequency family including
a specified zero-frequency anchor, its Hermitian Gamma kernel is PSD iff the
sampled distance matrix psi(k_j-k_i) is conditionally negative. The anchor
membership requirement is explicit; arbitrary unanchored samples have not yet
been handled by adjoining zero in this module. This is a finite algebraic
criterion, not construction of a Levy process or proof of a curvature bound.

Independent exact tests include the quartic distance on{0,1,2} with zero-sum
weights(-1,2,-1): its energy is24>0, so conditional negativity fails. In contrast,
the existing1601 spectral semigroup allows fourth-power rates. Thus spectral
contractivity does not discharge this covariance criterion. The plus-sign
quadratic kernel fails even its one-point diagonal test. Neither obstruction
invalidates the signed pseudoprocess algebra or the verified stable regime.

Next: extend the finite criterion to arbitrary sampled sets by adjoining the
anchor, and assess which symbol constructions discharge conditional negativity
using existing Hilbert/increment representations. Then examine whether the
result adds any curvature comparison beyond Schur positivity. Preserve all six
Objective2 deliverables; literature novelty and full process/domain obligations
remain open. Do not reopen IBM or switch campaigns.

## Verification1602

Full6852-job root build43.254s; complete51695-declaration safe transitive audit
44.079s (only propext, Classical.choice, Quot.sound). All14 public types,
10 full proofs and4 definitions reviewed unabridged; no new local instances or
options. Four independent Lean checks passed29.349s. The first independent run
failed only finite-function/conjugate-transpose/square-normalization elaboration;
repaired without production changes. Scratch1–6 finite-sum factoring and matrix
coercion errors were repaired explicitly; scratch7 passed. Failed logs retained,
not mathematical counterexamples. Warnings remain visible; no settings change.
Source2673/config3/archive113 integrity matches frozen manifests; original
manuscripts are unchanged. Exact local commit/receipt follow. REMOTE SYNC QUEUED
under the weekday09–17 Eastern policy; no backup claimed until verified.
Objective2 remains ACTIVE and incomplete; Objective1 deferred/incomplete.

## Checkpoint1603 — arbitrary samples and Hilbert increments (October27)

FourierCovarianceCriterion removes1602's requirement that a sampled family
already contain frequency0. `withZero` adjoins0 using Option; `negative_restrict`
extends coefficients by0 and restricts conditional negativity. Principal
submatrix positivity transfers the anchored covariance back to the original
sample. Empty samples, repeated frequencies and signed frequencies are allowed.
`symbol_iff` states the exact equivalence on ALL finite samples for even symbols
vanishing at0, on the existing Wave=(Fin3->Z) frequency group. It is not yet a
continuum R^d symbol theorem, an exponential-positive-definite theorem or a
Levy-process construction. No sampled positivity is postulated in the forward
conditional-negative direction.

`hilbert_kernel` identifies the actual Fourier Gamma kernel with inner(vk,vl)
when psi(k)=||vk||^2 and psi(l-k)=||vl-vk||^2. `hilbert_covariance` uses the
actual Gram-matrix positivity theorem, and `hilbert_negative` derives psi0=0,
evenness and conditional negativity from those exact representation hypotheses.
This is a sufficient representation theorem; it does not construct v for an
arbitrary symbol or infer a Markov generator from an arbitrary covariance.

`stable_covariance` and `stable_negative` discharge the global criterion for
0<gamma<2 by DIRECT reuse of FractionalCovarianceMatrices and the verified
stable_kernel_covariance identity, without assuming a new process or frequency
sign restriction. The current stableSymbol depends on coordinate0, so this is
a potentially degenerate rank-one symbol on Wave, not an asserted isotropic
three-dimensional symbol. Independent tests also realize the quadratic symbol
through H=R and v(k)=k0, outside the open fractional parameter range. These are
known covariance principles under the literature audit1602; no novelty claimed.

Independent exact tests cover quadratic Hilbert realization, failure of
NegativeSymbol for fourth-power rates using the three-point zero-sum vector,
an empty covariance sample, and arbitrary two-frequency Cauchy samples.
Thus the global quantifiers do not hide an anchor/nonempty/distinctness
requirement, and the higher-order signed obstruction remains preserved.

NEXT connect this general criterion to the ACTUAL iterated Fourier Gamma
recursion using existing gammaIter_finite, complex phase-energy identities and
Hadamard powers. Determine the exact finite-core positivity/curvature statement
it yields, rather than inferring a positive curvature constant, spectral gap,
completed domain or jump LSI from covariance alone. Preserve all six Objective2
deliverables; Objective1 remains deferred/incomplete.

Verification: final full6853-job build44.183s; complete51706-declaration safe
transitive audit45.163s (only propext, Classical.choice, Quot.sound). All11
unabridged public types,8 full proofs and3 definitions reviewed; no new local
instances/options. Four independent checks passed first run27.060s. Initial
scratch failed Option.elim argument order; second passed. Initial full build
passed42.877s; source review caught a leading-space definition omitted by the
public-name extraction helper. It was added to explicit type/axiom lists,
formatting normalized and source manifest refreshed; final full build and
complete audit rerun. No theorem or requirement weakened; logs retained.
Source2674/config3/archive113 hashes exact. ResearchSources unchanged. Exact
commit/receipt follow; REMOTE SYNC QUEUED under weekday09–17 Eastern policy.
Objective2 ACTIVE/incomplete; Objective1 deferred/incomplete; laterqueue intact.

## Checkpoint1604 — actual finite-core iterated Gamma positivity (October27,2026)

Objective2 ACTIVE. Foundation/FourierGammaCovariance.lean connects the general
covariance criterion to the existing ACTUAL generator recursion, rather than
only asserting positivity of an auxiliary matrix. `gamma_energy` identifies
the synthesized nth Gamma iteration with the complex energy of the entrywise
nth power of Kpsi, with phases c_i character(k_i,x). `power_psd` uses the Schur
product theorem (including n=0/all-ones); `energy_nonnegative` reuses the existing
real/imaginary energy identities. `gamma_finite_nonnegative` handles arbitrary
finite presentations, and `gamma_nonnegative` passes through the exact support
representation to EVERY f in the existing finite Fourier algebra, all n:N and
all spatial points. `negative_symbol_gamma` applies the1603 equivalence for
even, zero-normalized conditionally negative symbols. No frequency-sign or
distinctness restriction is introduced; conjugation remains in the first slot.

Thus Gamma2>=0 is established pointwise on this finite core for such symbols.
This is a known Schur/covariance consequence, not a novelty claim or a positive
curvature constant. No completed pointwise domain, Markov semigroup, stochastic
process, LSI or spectral gap is inferred. The symbol group remains Z^3, and the
existing stable example remains coordinate0/rank-one. Objective1's different
completed-domain, drift and entropy obligations remain deferred/incomplete.
Literature context remains the exact classical covariance sources in1602;
further family/subordination and novelty audits remain required.

Four independent checks passed: quadratic Hilbert symbol for all n/f/x;
Cauchy Gamma2 for arbitrary f/x; Gamma0 positivity for arbitrary symbol;
quartic CovarianceSymbol failure via the explicit three-point zero-sum test.
The last prevents applying the theorem indiscriminately to pseudoprocess rates.
NEXT investigate the converse finite-core Gamma1 criterion and its explicit
quartic pointwise witness, then productive general Levy/subordination examples.
Retain all six Objective2 deliverables and the later queue.

Verification: full6854-job build45.8204555s; complete51712-declaration safe
transitive axiom audit46.0396493s, whitelist propext/Classical.choice/Quot.sound.
All six unabridged public types and six full proofs reviewed; no new definitions,
local instances or options. Four independent proofs passed first run27.2934204s.
Initial scratch elaboration failures involved matrix coercion/Hadamard unfolding
and a missing namespace; repaired without changing hypotheses or options, with
all logs retained. Final scratch passed before adoption. Source2675/config3/
archive113 hashes exact; ResearchSources unchanged. Exact Git commit/receipt
follow. REMOTE SYNC QUEUED under the weekday09–17 Eastern policy, not backed up.

## Checkpoint1605 — exact finite-core Gamma1 criterion and explicit quartic failure (October27,2026)

Objective2 ACTIVE. `Foundation/FourierGammaCriterion.lean` proves a converse to
checkpoint1604. For an EVEN real symbol psi on the existing Wave=Z^3, positivity
of the REAL part of actual synthesized Gamma1(f,f) at the single spatial origin
for EVERY finite Fourier polynomial f is EQUIVALENT to global positive
semidefiniteness of all finite matrices Kpsi(k_i,k_j). The converse uses real
Fourier coefficients and the exact `real_gamma_energy` identity; evenness
supplies the Hermitian matrix condition. With psi(0)=0, the1603 symbol theorem
makes this equivalent to conditional negativity of psi on ALL finite samples.
No pointwise positivity at all spatial points is assumed in the converse; the
forward result1604 does give it. Finite presentations may repeat frequencies.

`quarticWitness` has frequencies 0,1,2 in the existing coordinate0 symbol and
coefficients -1,2,-1. The ACTUAL Gamma1 synthesis for stableSymbol 4 at the
origin has real value EXACTLY -12. This sharpens the prior negative-energy
matrix obstruction to a concrete failure inside the Fourier operator calculus.
The independent scratch also calculates a cubic-rate example: frequencies1,2,
coefficients4,-1 yield Gamma1 value -8. These higher-order rates cannot meet
the covariance/pointwise Gamma positivity criterion. Signed pseudoprocess
operator identities still exist; no Markov or process conclusion follows.

The equivalence is the classical negative-type/positive-kernel principle made
exact for the existing verified Fourier operator core. The sources in checkpoint
1602 (Bierme2016 LectureI and Gangolli1967 ChapterI) remain the novelty baseline;
no new stochastic curvature, positive kappa, CD bound, spectral gap, completed
pointwise domain or sharp entropy estimate is claimed. Objective1's unfinished
manuscript, drift, domain and entropy work remains deferred/incomplete.

Five independent Lean checks passed: the iff at exact hypotheses, explicit
quartic negativity, all-iteration quadratic Hilbert example, quartic failure
of the negative-symbol property via the actual witness, and a separately
calculated cubic witness. Original manuscript hashes preserved. NEXT examine
whether the evenness assumption can itself be derived from Gamma1 positivity
when psi(0)=0; then test actual Levy/subordination symbols and the limits of
passing from finite-core Gamma inequalities to closed Markov domains. Preserve
all six Objective2 deliverables and the authoritative later queue.

Verification: final full6855-job root build42.1936043s; complete51726-declaration
safe transitive axiom audit44.4928919s with only propext/Classical.choice/
Quot.sound; all ten unabridged public types, seven full theorem proofs, three
definitions, and five independent proofs reviewed. No new local instances,
options, sorry/admit or axiom. Final source2676/config3/archive113 hashes exact.
The first full build passed but two new-file style warnings were repaired;
the full build was rerun on the final bytes. Scratch elaboration repairs used
the explicit matrix type and separated real-energy rewrite; no hypotheses
changed. Exact Git commit/receipt follow. REMOTE SYNC QUEUED under weekday
09–17 Eastern policy, never reported as remotely backed up.

## Checkpoint1606 — normalization, symmetry and the weak negative-symbol obstruction (October27,2026)

Objective2 ACTIVE. `Foundation/FourierGammaNormalization.lean` proves that the
evenness hypothesis in1605 is AUTOMATIC from universal actual Gamma1 positivity
at the spatial origin when psi(0)=0. The exact two-frequency formula for the
polynomial supported on {0,k}, with real coefficients (t,1), is
Gamma1=psi(k)+t(psi(k)-psi(-k))/2. If the odd part is nonzero, a concrete t
makes this -1. Thus `normalized_gamma_iff_covariance` gives an exact equivalence
between universal finite-core origin Gamma1 real positivity and ALL finite
Kpsi matrices positive semidefinite, with no assumed symmetry. Together with
1603, `normalized_gamma_iff_negative_even` gives the precise alternative:
conditional negativity AND evenness. Theorem statements quantify all finite
Fourier polynomials on the existing Wave=Z^3; there is no frequency-sign,
distinctness, probability-process or completed-domain assumption.

Crucial qualification: the repository predicate `NegativeSymbol` currently
contains ONLY the zero-sum quadratic inequality. Its definition does not impose
the symmetry/Hermitian clause of standard negative-type conventions. The new
`antisymmetric_energy_zero` and `odd_symbol_negative` prove EVERY odd real
symbol passes that inequality: antisymmetric distance matrices contribute
zero to all real quadratic forms. The concrete `linearSymbol(k)=k0` satisfies
`NegativeSymbol` but the actual Gamma1 of `pairPolynomial(1,-2)` at the origin
has value -1. An independent cubic odd symbol gives the same discrepancy.
Hence neither the weak predicate nor its odd examples certify a symmetric
Levy exponent, positive covariance kernel, Markov generator or curvature.
The evenness clause must be kept in `symbol_iff` and any stochastic reading.
This is a precise correction of the hypothesis bookkeeping, not a claim of
novelty in classical negative-type theory.

Five independent checks passed: odd cubic weak conditional negativity; its
directly calculated Gamma1 value -1; symmetry consequence under exact h0 and
Gamma positivity; positive normalized Cauchy/stable example; and direct
negative linear witness. No original manuscript was changed. NEXT investigate
the necessity of normalization and test whether an unnormalized odd symbol can
have nonnegative real Gamma1 through a positive constant component; then pursue
actual Levy/subordination examples and domain/curvature limits. Objective1
remains deferred/incomplete, and all six Objective2 deliverables stay open.

Verification: final full6856-job build41.5229945s; complete51744-declaration
transitive axiom audit44.2039499s, whitelist only propext/Classical.choice/
Quot.sound; all13 unabridged public types,9 full proofs,4 definitions and5
independent proofs reviewed. No local instances/options/sorry/admit/axioms.
Final source2677/config3/archive113 hashes exact. The first full build passed;
a duplicate new-file header was removed and the full build rerun on final bytes.
Scratch simplification/algebra fixes and source log evidence retained.
ResearchSources unchanged. Exact commit/receipt follow. REMOTE SYNC QUEUED
under weekday09–17 Eastern policy, never claimed remotely backed up.
