# Autonomous Banach and Lévy research run

Baseline: `5386f4e689f9e0e8d78433d3870d51b81a4030b8` (Lean 4.34.1,
Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`). All work remained on
`master`. See `BANACH_NEW_DECLARATIONS.csv` for the declaration inventory.

## Verified mathematical progress

* C2, commit `d2192890faa9f15e7aff7418380e431cae47d75d`:
  `Foundation/BanachRange.lean` proves that a genuine positive lower bound on
  `δ : H →L[ℝ] Lp ℝ p μ` gives injectivity; with complete `H`, it gives a
  closed range and continuous inverse onto that range with the sharp stated
  inverse bound. The kernel of B0's actual Hölder transpose is precisely the
  annihilator of the **norm closure** of the range. A witnessed nonzero pairing
  rules a chosen element out of that closure. These are conditional Banach
  theorems about an actual supplied bounded map; they do not construct a
  stochastic integral or a nontrivial witness.
* C1, commit `5f8e48fa7e91d2772d769d7f77e344d7496de0b2`:
  `Foundation/BanachUnboundedAdjoint.lean` constructs the partial Banach
  adjoint of a densely defined `LinearPMap` on real normed spaces. Its exact
  domain is characterized by boundedness of `x ↦ φ(Tx)` in the ambient `X`
  norm. Mathlib's `LinearMap.extendOfNorm` supplies the genuine continuous
  extension. The pairing graph is an actual closed linear subspace, and
  density ensures uniqueness.
* C1 bounded compatibility, commit
  `49a61fc68b694aa5527186cb62efe9b3f6d9a6b1`: when `T` comes from
  `S : X →L[ℝ] Y` on the whole space, the adjoint domain is all of `Y*` and
  the adjoint value is the continuous transpose `φ.comp S`.
* C1 closability, commit `8d5b1168ad3c32ec8f84256b26df99b4bb598fbf`:
  if the adjoint domain separates points of `Y`, then `T` is closable. This
  is a sufficient point-separation criterion, with no assertion that the
  adjoint domain is norm-dense in `Y*`.
* C3 fixed exponent, commit `dd8560298c5598cb46bb0014745a6a93872f1c38`:
  `Foundation/BanachLpDualityFour.lean` constructs the signed nonlinear map
  `J₄(F)=F³ : L⁴→L^(4/3)` on genuine Lp classes. Lean verifies its actual
  pairing integrability, `∫J₄(F)F=‖F‖₄⁴`, and
  `‖J₄(F)‖_(4/3)=‖F‖₄³`. For a supplied bounded
  `δ:H→L⁴`, `normalFour δ u = D(J₄(δu))` satisfies
  `normalFour δ u u=‖δu‖₄⁴`; a genuine positive lower bound for `δ`
  yields `c⁴‖u‖⁴≤normalFour δ u u`.
* C3 monotonicity, commit `caf0844ac42cd40eeb535004b997f9c056416714`:
  the same actual nonlinear normal map satisfies
  `0≤(normalFour δ u-normalFour δ v)(u-v)` for every `u,v`. Its proof uses
  integrable Hölder pairings and the pointwise signed cubic inequality.

The complete `lake build` passes with 4,025 jobs. All 1,170 declarations
listed in `Foundation/AxiomAudit.lean` were checked transitively; the union
of reported axioms is `propext`, `Classical.choice`, and `Quot.sound`. No
`sorryAx` or custom mathematical axiom appears in the new dependency chains.
The elaborated types of the principal C1 theorems were inspected with `#check
@...`; in particular, `adjoint_mem_domain_iff_exists_bound` has no hidden
completeness or reflexivity hypothesis. The only existing build warnings are
the two unused `CompleteSpace` section variables in `Foundation/Adjoint.lean`
and a tactic suggestion in `Foundation/PoissonLipschitzChain.lean`.

## Reconnaissance and scope

The pinned [LeanLevy repository](https://github.com/slink/LeanLevy/tree/7e73fd9b23ad52956ec2756a815889a783131ce4)
uses Lean 4.32.0 and an MIT license. Earlier source inspection, recorded in
`INDEPENDENT_BANACH_RECONSTRUCTION_AUDIT.md`, located
`exists_isPoissonPointFamily` in
[`PoissonPointFamily.lean`](https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/RandomMeasure/PoissonPointFamily.lean)
and deterministic compensated-integral construction in
[`PoissonCompensated.lean`](https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/RandomMeasure/PoissonCompensated.lean).
During this run the saved pinned `PoissonCompensated.lean` source was inspected
again: `compensatedPoissonIntegral` (line 699) is defined as the L² limit of
simple approximations, `eLpNorm_compensatedPoissonIntegral` (line 761) proves
isometry, `integral_compensatedPoissonIntegral` (line 817) centering, and
`compensatedPoissonIntegral_eq_sum` (line 832) agreement with explicit sums
on `L¹ ∩ L²`. These statements concern **deterministic mark functions**.
The pinned GitHub blob could not be fetched anew during this run, so the
Poisson-point-family findings remain an attributed earlier source audit,
not an independently repeated Lean compile at our pinned toolchain. The
current upstream README describes broader later developments; those are not
evidence that the pinned version contains a predictable-integrand integral.
No upstream code, dependency, or license text was added to this repository.

General C3 remains open. The verified fixed `p=4` case uses Mathlib's
`MemLp.norm_rpow_div`; arbitrary `1<p<∞` still needs signed-power and
conjugate-exponent arithmetic, representative independence, continuity and
strict monotonicity estimates, then a genuine monotone-operator existence
argument. No minimizer, onto theorem, or solution of the normal equation was
asserted.

C5–C6 require an actual marked point family and process/filtration layer.
The existing one-site Poisson operator theory supplies genuine count moments
and differences but no independently scattered mark-space random measure.
Porting selected LeanLevy results would require checking all imports against
Mathlib `d13f23b`; this is a substantial separate verified effort. No new
marked model or predictable stochastic integral was built here.

The stable-process dependency analysis is in
`BANACH_STABLE_DEPENDENCY_GRAPH.md`; the cross-model operator inventory is in
`BANACH_OPERATOR_COMPARISON.md`. All stable-process claims dependent on a
constructed process, stochastic integral, or two-sided estimate remain **OPEN,
NOT LEAN VERIFIED**.

## Next independent implementation

The next C3 task is continuity and strict monotonicity for the verified
`p=4` normal map, followed by a finite-dimensional existence theorem before
attempting an arbitrary reflexive Banach-space surjectivity result. General
`1<p<∞` should follow only after signed-power exponent arithmetic and the
zero convention are proved. For concrete stochastic progress, audit and port a minimal
`PoissonPointFamily` + deterministic compensated-sum slice from the pinned
LeanLevy source in an isolated module, preserving MIT attribution; first
compile it without changing the dependency lockfile.
