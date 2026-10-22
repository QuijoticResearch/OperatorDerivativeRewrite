# blackito.tex: selective mathematical audit, checkpoint 1294

October 21, 2026. This is a bounded manuscript/reuse audit supporting the active
intrinsic IBM campaign, not a new black-noise campaign. It neither reopens the
frozen pseudoprocess calculus nor changes the research queue.

## Source integrity and scope

Read-only source: `ResearchSources/Incoming/blackito.tex`, title “Pairwise Black
Clark–Ocone and Operator-Itô Formulae for Le Jan–Raimond Sticky Flows, and the
Sticky–Coalescing Dichotomy.” SHA256:
`D86F4033700843827ACEA2A5CF670084C7E42321FD0E27817DC99256FD940F4D`.
The file was already inventoried in `STARDUST_RESEARCH_SOURCE_INVENTORY_1292.json`;
its hash is unique there. All 113 archive paths and hashes were rechecked and
preserved. The displayed journal/date placeholders do not establish publication.

Read title, abstract, structural headings and selected statements; examined the
abstract energy construction, Green reconstruction, dynamic partition argument,
invariant-reference obstruction and numerical claims selectively in detail.
Unexamined proofs remain unverified. Source line references below refer to these
preserved bytes. No manuscript was edited or staged.

## Decisive corrections and obstructions

1. **Missing density hypothesis (lines 2907–3004, `ass:gamma-axioms`, `thm:foldB`).**
   The displayed axioms require a unital algebra and sequential form closability,
   but do not explicitly require that algebra to be dense in L2. On a two-atom
   probability space take only constant functions and Gamma identically zero.
   Symmetry, vanishing, both positivity conditions and the displayed sequential
   closability criterion all hold. The closed zero derivative has the proper
   closed domain of constants, not a dense domain. Its usual full-space adjoint
   cannot be a uniquely defined operator: representing vectors are determined
   only modulo the orthogonal complement of constants.

   Repair by explicitly assuming L2 density, or by restricting the ambient
   Hilbert space to the closure of the algebra. If the word “closable” is intended
   to include density by convention, say so in addition to the displayed
   sequential definition. Actual sector-core density still requires proof.
   `EnergySeedDensityObstruction` verifies the closed proper diagonal domain,
   its failure of density, and its closed zero graph in finite coordinates.
   The coordinate topology equals that of two-atom L2; this module does not
   formalize a new probability-space/module construction or all Gamma axioms.

2. **Finite Galerkin results cannot certify full contraction (lines 947ff and
   2495ff).** Tested generalized eigenvalues below one, even with certified
   quadrature, only control the tested subspace. For energies
   E(a,b)=a²/2+2b² and R(a,b)=a²+b², E<=R on b=0, whereas E(0,1)=2>1.
   `tested_sector_contraction` and `untested_sector_failure` verify this exact
   counterexample. A complement/tail estimate is indispensable. This refutes
   the suggested inference from a finite matrix certificate to the full P3
   inequality, not the unproved actual point-start contraction itself.

3. **The cutoff error estimate needs repair (`prop:invariant-fails`, lines
   912ff).** A cutoff equal to the identity through R and zero at 2R cannot have
   O(1) derivative-square energy in that collar: Cauchy–Schwarz and the fundamental
   theorem give integral_R^{2R} |chi_R'|² >= R. Thus the proof's O(1) collar
   dismissal is invalid. There is also a factor-two mismatch in its written
   deficit. This does not establish the opposite contraction conclusion.
   A consistent rescaling chi_R(s)=R chi(s/R) retains an O(R) collar and can
   instead support leading-order comparisons after the actual gap integrals
   and remainder estimates have been justified.

4. **The module density wording is stronger than its proof (`thm:foldA` iii).**
   The displayed proof establishes density of the finite linear span of U D F,
   not density of the set of individual simple forms. Use the span statement
   unless a separate rank-one approximation argument is supplied. No explicit
   counterexample to the stronger statement is asserted here.

## What survives, conditionally

The static theorem `thm:clarkocone` (lines 1839ff) is a sound Hilbert-space Green
identity once D is closed and densely defined, its kernel consists exactly of
constants, and a Poincare gap is available. With A=D*D and G the inverse on
centered functions, delta D G f=f. The exact-form solution is orthogonal to
ker(delta), hence the minimum-norm solution; arbitrary solutions differ by
ker(delta). The manuscript correctly says its Pi is not idempotent and that
this is not a predictable Brownian Clark–Ocone projection. This audit does not
claim a fresh Lean verification of the manuscript's whole Green theorem.

The bounded-function dynamic partition argument (`thm:dynamic`, lines 2348ff)
also has a valid conditional route. For an actual Feller Markov process and
f,f² in the required generator domains, slice Green inverses represent the
centered increments f(Z_next)-P_Delta f(Z_previous). The exact sum telescopes
with the semigroup compensator. If h=Lf belongs to C0, strong continuity on h
and h² gives, uniformly in the starting state,

    E_z |h(Z_s)-h(z)|²
      <= ||P_s(h²)-h²||_infinity + 2||h||_infinity ||P_s h-h||_infinity -> 0.

The compensator therefore converges in L2 to the time integral of Lf. The
manuscript's definition only requires joint measurability of the composite
delta u, which the explicit residual supplies; it does not falsely require a
measurable Green bundle there. However, no common completed adapted-integrand
space, convergence of u_pi in that space, or closed continuum stochastic
integral follows. The manuscript itself lists these as open. Neither the
partition representation nor the expectation heat equation is the requested
full stochastic calculus.

## Blackness, sticky laws and the actual-process boundary

Le Jan–Raimond define blackness using centered additive representations whose
increments are measurable in the corresponding noise interval. Their proved
circle theorem is [The noise of a Brownian sticky flow is black](https://arxiv.org/pdf/math/0212269).
This rules out nonzero representations of that specified kind; it does not
rule out all adapted martingales or a tagged particle's own-filtration Brownian
calculus. Random past-state dependence and auxiliary sampling matter. The
manuscript's broad opening “no martingale representation” language should be
restricted to its later precise driverless definition. Its asserted transfer
from circle to line needs a localization/density argument; it is not proved
merely by referring to a local hitting estimate.

Consistent all-n-point Feller laws, not an isolated two-point model, are the
input to a stochastic flow construction; see the primary
[Flows, coalescence and noise](https://arxiv.org/abs/math/0203221).
The manuscript correctly treats its pairwise core as a vector space rather
than an algebra, and explicitly leaves higher-sector gluing open. No verified
identification with a complete LJR black flow was found in the inspected Lean
library. Do not infer one from the existing genuine sticky pair process.

The claimed generator “on L2(dx dy)” needs a precise reference measure and
Wentzell domain when a diagonal atom is present. Deterministic diagonal spatial
measure and pathwise local time are distinct objects. Gap autonomy does not
imply independence from the center. Claimed point-start score/capacity bounds
and CKC constants remain separate analytic obligations, not verified numerical
consequences. `thm:sectorclos` assumes P1 and restates its sector closability;
it does not derive P1 from the actual sticky kernel.

## Exact reuse and IBM implications

| Existing verified source | Reuse and limitation |
| --- | --- |
| `StickyNaturalMartingales.natural_martingale`, `augmented_natural_martingale`, `square_natural_martingale` | Actual sticky process and compensated-square martingales in their stated filtrations; no black-flow identification. |
| `StickyPairBrownianCoordinates`, `StickyPairSampling.coincidence_occupation` | Genuine two-point coordinate laws and occupation clock; no all-sector noise construction. |
| `StickyTerminalLawObstruction.generator_pairings_differ`, `bounded_smooth_witness` | Even the Brownian heat generator is not symmetric under its finite-time Gaussian law. Terminal-law Green generator -D*D must not be silently identified with the physical Feller generator. |
| `MixedAtomicNonclosability.no_closable_extension` | A derivative charging the atom has an explicit shrinking-jet obstruction. This does not refute the correctly tangential/diffuse sticky energy. |
| `SymmetricFactorEnergy.quadratic_energy_contraction` | Conditional contraction under positivity, symmetry and exact isometric intertwining; these hypotheses cannot be borrowed for a nonsymmetric point-start generator. |
| `StickyInitialKernelNonuniqueness` | Initial-law disintegrations can leave off-support kernel versions undetermined; not nonuniqueness of the sticky martingale problem. |
| `IBMJointIntrinsicDerivative` | Reuse its separately proved closedness and density. For intrinsic IBM, prove the actual adjoint domain and convergence; a static inverse or finite chaos test does not supply stochastic integration. |

Useful next IBM action remains comparison of the natural intrinsic adjoint
domain with the existing source-lifted divergence domain, using the established
F1–F3 and source-resolved results. No black-noise formalization or general
Hilbert-module infrastructure is needed for the two counterexamples here.

## Status and reproducibility

The explicit density and untested-mode obstructions are Lean-verified in
`Foundation/EnergySeedDensityObstruction.lean`; the conditional Green/dynamic
arguments and cutoff correction above are mathematical audit findings, not
new fully formalized sticky-flow theorems. Actual CKC, point-start kernel
estimates, global sector consistency, line blackness transfer and a continuum
adapted integral remain open/unverified in this review.

Checkpoint evidence and independent regression code are recorded in
`STARDUST_BLACKITO_VERIFICATION.json`. All existing mathematical sources are
preserved except the root import of the new obstruction module. Full-build,
complete transitive axiom audit, public-type/source review and exact private
backup gates apply without modification.
