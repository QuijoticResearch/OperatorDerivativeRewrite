# Bakry–Émery Objective 2 — paused at checkpoint 1638

**Status:** PAUSED by the user's explicit Yang–Mills transition. This is a
research checkpoint, not completion of Objective 2 or Objective 1. The last
mathematical commit is `3e395efc1de8ce61fff04bc598ed631710728f38`,
fully audited and verified on both PRIVATE backup branches. The detailed
theorem ledger is `STARDUST_BAKRY_CURVATURE_COVARIANCE_AUDIT.md`; this note
records the return point without changing any proof.

## Strongest verified results

- `FourierCovarianceCriterion.symbol_iff` and
  `FourierGammaNormalization.normalized_gamma_iff_covariance` give the exact
  finite Fourier covariance/conditional-negative/Gamma-one criterion on
  `Wave = ℤ³`, with normalization and symmetry accounted for. The
  `FourierGammaCovariance.gamma_nonnegative` theorem proves all finite-core
  Gamma iterations nonnegative for a covariance symbol. These are classical
  negative-type and Schur-product consequences, not new curvature bounds.
- The anisotropic stable active-axis threshold is sharp. For positive axis
  weight, exponent at most two is necessary and sufficient for positivity
  of the completed physical Haar-L² heat evolution; an active exponent
  greater than two has an explicit nonnegative Fourier square whose image
  is negative on a set of positive Haar measure. See checkpoints 1616–1622
  and `PhysicalHeatPositiveCone.anisotropic_physical_positive_iff_active`.
- The physical torus law, convolution semigroup, weak continuity, Markov
  kernel, countable-step heat chain, exact grid marginals and actual
  character-increment covariance derivative are verified in checkpoints
  1625–1632. This is genuine probability and discrete-time path
  construction, not a continuous-time path-regularity theorem.
- Checkpoints 1636–1638 construct the actual Poisson mixture of heat laws,
  identify its transformed symbol `1-exp(-δ r)` and convolution law, prove
  its no-jump atom, and realize a countable-step Markov chain whose
  Fourier Gamma coefficient is the covariance of one original heat jump.
  These are classical compound-Poisson facts with an exact Lean bridge
  from process covariance to the operator calculus.

## Counterexamples and limits

- `FourierGammaCriterion`'s quartic witness has negative Gamma-one value;
  higher-order signed heat rates cannot be treated as Markov covariance
  symbols merely because their formal Fourier calculus exists.
- A normalized odd symbol may satisfy a weak negative-type condition but
  fail the actual real Gamma positivity criterion; the symmetry and
  origin-normalization hypotheses are essential (checkpoints 1606–1608).
- The quadratic heat symbol has positive individual finite-time covariance
  matrices but their Loewner difference can be negative (checkpoint 1634).
  It has nonnegative Gamma-two on the finite Fourier core yet no strictly
  positive pointwise curvature constant (checkpoint 1635).
- Finite-rate Poissonization retains an origin atom of mass at least
  `exp(-rate)`; it cannot be absolutely continuous with respect to a
  reference measure whose origin singleton is null (checkpoint 1637).

## Novel candidates and unresolved questions

The verified package may be useful as a reusable exact bridge among finite
Fourier negative-type geometry, completed physical semigroups, genuine
transition laws and process covariance. That **combination** merits a
literature audit before any novelty claim; none is made here. It supplies
no positive Bakry curvature, logarithmic Sobolev constant, or quantum
Yang–Mills mass gap.

On return, the principal open obligations are: (1) closed pointwise Gamma
and Gamma-two domains for the physical Markov generator; (2) sharp
Poincaré/entropy/LSI estimates under explicit nondegeneracy assumptions;
(3) continuous-time path realization and regularity for the heat and
compound-jump semigroups; (4) a complete comparison of Lévy, Volterra and
non-Markovian covariance geometries without inferring a generator from
covariance alone; (5) the original Objective 2 manuscript/research-note
and literature/novelty deliverables. Objective 1's separate drift,
maximal/full-L² domain, entropy and original-manuscript obligations remain
deferred under `STARDUST_BAKRY_FBM_AUDIT.md`.

`ResearchSources` is unchanged. No original manuscript, theorem or
hypothesis was altered by this pause.
