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
