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
