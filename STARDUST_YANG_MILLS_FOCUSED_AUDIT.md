# Project Stardust — focused Yang–Mills audit, first proof checkpoint

Status: ACTIVE. Bakry–Émery Objective 2 is PAUSED, not completed; see `STARDUST_BAKRY_OBJECTIVE2_PAUSE.md`. This is a selective theorem audit and a concrete obstruction to one proposed transfer estimate. It is not a construction of four-dimensional Yang–Mills theory or a proof of a physical mass gap.

## Sources and research map

`STARDUST_YANG_MILLS_SOURCE_INVENTORY.json` records SHA-256 hashes and sizes for 21 selected incoming Yang–Mills candidates. The two `entropy_ym (4)` copies are byte-identical. Hashing did not entail reading every manuscript in full. Selected titles, abstracts, theorem claims and relevant proof passages were examined; all original files remain untouched.

| Approach and source | Reusable content | Exact gap or failure |
|---|---|---|
| `block_contraction_spectral_gaps.tex`, `YM_MASS_GAP_UNCONDITIONAL.tex`, `YM_unified_v12.pdf` | On an oriented scalar 2-by-2 tile, the linearized incidence calculation `Aᵀv=0` gives a clean Schur residual curvature and a candidate boundary heat factor `q₀ = exp(-λ₁/(nₚ β c₂))`. | The reference boundary gap `λ₁` and `c₂` are fixed while β grows. The factor approaches 1, so the displayed `q₀ + ε_T + η` estimate with nonnegative errors cannot itself yield a uniform `q<1`. The actual nonlinear gauge-covariant block transfer, its `H¹` comparison to heat, and scale/volume-uniform control remain separate unproved obligations. Corridor and C² regularity are explicit hypotheses in the longer versions. |
| `ym_v75 (1).tex`, `su2_companion.tex`, `yang_mills_revised.tex` | Detailed finite-window RG architecture, candidate local estimates and explicit closure targets. | The finite RG window in `ym_v75` does not establish all-scale induction or continuum mass gap. Claimed closure in companion versions requires independent gauge fixing, background-field, large/small-field, covariance and continuum estimates. Numerical constants and LP examples are exploratory, not verified uniform theorems. |
| `entropy_ym (4).tex` (and duplicate) | Exact KL chain rule and Gaussian quartic covariance diagnostics can organize an RG remainder budget. | A scale-uniform nonlinear entropy dissipation fraction is not established. The manuscript itself notes a massless Gaussian reference and warns that early Dobrushin crossover could produce the wrong physical scale or a trivial continuum limit. |
| `dimock_nonabelian (1).tex` | Explicit roadmap of missing nonabelian d=3/4 constructive estimates. | A roadmap is not the completion of the multiscale construction. |
| `su_n_leibniz_cancellations_v6.tex` | Ordered link/color Hessian structure is useful for finding symmetry-protected terms. | Color antisymmetry alone does not cancel the full ordered mixed Hessian; existing Lean counterexamples and restricted positive results distinguish the cases. |
| `ym_ns_dictionary.tex` | Shared operator patterns and Hodge analogies. | No stochastic Navier–Stokes/Yang–Mills equivalence follows; earlier selective audit remains controlling. |

The original Bałaban/Dimock work separates propagators, gauge/background choices, small-field and large-field estimates, multiscale convergence and the ultraviolet problem. The cited Dimock scalar-field exposition and QED3 work do not supply a four-dimensional SU(2) continuum construction. See primary literature links below.

## Exact verified reuse and new theorem

The existing Lean library proves positive **single conditional block** coercivity (`PeriodicSingleBlockCoercivity`) and Schur residual lower bounds (`CoerciveSchurStability`, `SparseBlockSchurCurvature`). It also proves exact-gradient and non-exact flat zero modes of the **simultaneous global interior operator** (`PeriodicInteriorGaugeKernel`, `PeriodicInteriorHolonomy`), a physical checkerboard compliance mode (`PeriodicCheckerboardPhysical`, `PeriodicCheckerboardCompliance`), and a restricted rational-bound violation (`SparseBlockWilsonAction`). These are distinct finite lattice statements. None supplies a gauge-invariant continuum correlation estimate. Bakry results for commutative finite/torus processes likewise do not automatically extend to a nonlinear SU(2) gauge quotient.

`Foundation/YMBlockHeatContractionObstruction.lean` defines the manuscript reference factor `exp(-gap/(curvatureScale * beta))` and proves four results: strict contraction at each positive β, convergence to 1 for fixed nonzero curvature scale, impossibility of a uniform `q<1` for β≥1, and impossibility of that bound after adding arbitrary nonnegative error allowances. Independent examples test both the limiting and quantitative statements. This is a theorem about the stated **fixed-boundary heat surrogate**. A β-dependent boundary spectral gap, a different geometric scaling or a nonlinear transfer mechanism could evade its hypotheses; the theorem does not disprove Yang–Mills mass generation.

## Focused route and stopping questions

**Primary route:** seek a genuinely gauge-invariant connected Wilson-loop correlation bound through a block-boundary transfer. The topological `Aᵀv=0` / Schur calculation can guide a local candidate, but one must construct the actual gauge-covariant transfer kernel, prove descent to the physical quotient, control its gradient norm, and obtain a contraction compatible with lattice spacing, large volume and continuum nontriviality. A fixed-lattice spectral gap is insufficient. First test whether a scale-dependent quotient gap or a different reference semigroup avoids the verified `q₀→1` obstruction without assuming the desired physical gap.

**Secondary diagnostic:** use entropy chain rules and Gaussian covariance identities to track remainders and detect where a proposed RG step loses control. Do not treat entropy decrease or local coercivity as a physical mass gap. A positive result must ultimately furnish gauge-invariant correlations with a physical-distance decay rate uniform through the continuum and infinite-volume limits.

Open: actual SU(2) transfer construction; gauge-invariant descent and Osterwalder–Schrader positive observable sector; scale-uniform small/large-field estimates; continuum and thermodynamic limits; nontriviality; a physical spectral gap. No external existence or mass-gap claim has been adopted as an axiom.

## Primary literature checked

- Jaffe–Witten, [Yang–Mills existence and mass gap, official problem statement](https://www.claymath.org/wp-content/uploads/2022/02/MPPc.pdf).
- Bałaban, [Propagators and renormalization transformations for lattice gauge theories I](https://doi.org/10.1007/BF01215753).
- Dimock, [The Renormalization Group According to Bałaban I: Small fields](https://arxiv.org/abs/1108.1335), [II: Large fields](https://arxiv.org/abs/1212.5562), [III: Convergence](https://arxiv.org/abs/1304.0705).
- Dimock, [Ultraviolet stability for QED in d=3](https://arxiv.org/abs/2009.01156).

## Verification, checkpoint 1639

The full root build passed, 6889 jobs. The complete transitive axiom audit passed for 52270 declarations with only `propext`, `Classical.choice`, and `Quot.sound`; it printed all five new public types without abbreviation. All four theorem proofs and the definition were reviewed in full. Four independent Lean examples passed, including a concrete curvature scale and positive error allowance. Source integrity passed for all 2709 Foundation/root Lean files, all three configuration files, the 113-file archive baseline, and all 21 selected incoming Yang–Mills candidates. Exact commit and PRIVATE backup status belong in the ledger below; do not infer a mass gap from this checkpoint. Keep the focused campaign active after closure.
