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

## Follow-on audit: necessary error scale and the Lipschitz step

The fixed-parameter bound is sharper than mere failure of uniformity. The additional Lean theorems in `YMBlockHeatContractionObstruction` prove

\[
1-e^{-\lambda/(c\beta)}\leq \frac{\lambda}{c\beta},\qquad
e^{-\lambda/(c\beta)}+E(\beta)<1\Longrightarrow
E(\beta)<\frac{\lambda}{c\beta}.
\]

Thus the **sum** of the manuscript's nonnegative `ε_T` and `η` must fit an inverse-β budget at each weak-coupling step. Merely showing that the errors vanish is insufficient. In `block_contraction_spectral_gaps.tex`, equations `q₀` and `contraction` and the discussion under “Verification of hypotheses” do not provide this rate. If its interior curvature `κ_int` is comparable to β and `η=C_DV/√κ_int`, then this mechanism requires `C_DV` on the order of at most β⁻¹ᐟ² (with a sufficiently small coefficient), unless `ε_T` consumes the budget first. This is a **necessary condition for that bound**, not a universal Yang–Mills obstruction.

There is also a distinct gap from the manuscript's `H¹` contraction to its “One-step influence contraction” and positive `κ=-log(C₀q)`. A smooth strictly positive density with bounded log derivatives does not, by itself, turn an `L²` gradient estimate into a contracting supremum Lipschitz estimate. Here is an explicit independent mathematical counterexample to that inference. On `[0,1]`, with Lebesgue reference measure, let

\[
K(x,y)=1+\tfrac12 x^{24}(2y-1),\qquad
(Tf)(x)=\int_0^1 K(x,y)f(y)\,dy.
\]

`K` is a Markov transition density, smooth and between `1/2` and `3/2`. Its `x` and `y` log derivatives are bounded by `24` and `2`, respectively. Integration by parts gives

\[
(Tf)'(x)=12x^{23}\int_0^1 f'(y)y(1-y)\,dy,
\quad \int_0^1 y^2(1-y)^2dy=\tfrac1{30}.
\]

Consequently `||(Tf)'||₂² ≤ (24/235)||f'||₂²`, a strict `H¹` contraction for every smooth `f`. But for `f(y)=y`, `(Tf)'(x)=2x^{23}`, so `Lip(Tf)=2>1=Lip(f)`. Every constant `C₀` in `Lip(Tf)≤C₀q Lip(f)` for this operator therefore has `C₀q≥2`; the manuscript's claimed positive `-log(C₀q)` does not follow. The interval model refutes the **general implication used in the proof**; it does not assert that the particular SU(2) block kernel has this behavior. A direct gauge-compatible Lipschitz/influence estimate remains required. The rational identities and inequalities were independently checked in `.lake/stardust-ym-1640-kernel-check.py`.

The manuscript's `H¹` perturbation assumption already bounds the complete derivative of `T-T₀`; its proof then says to add a covariance correction as a further term. That extra allowance is harmless but does not independently establish the assumed perturbation estimate. The definition of `T` still describes an “updated boundary variable” without a constructed transition law, so neither assumption is discharged by the Schur calculation alone.

### Verification, checkpoint 1640

The incremental target and full root build both passed (1946 and 6889 jobs). The complete transitive axiom audit passed for 52273 declarations with only the three standard allowed axioms. All eight public declarations in this module (one definition, seven theorems), including the three new unabridged types and full proofs, were reviewed. Three new independent Lean examples passed. The smooth-kernel counterexample's normalization, positivity, exact `H¹` constant, Lipschitz factor and log-derivative bounds were checked by rational arithmetic; it is documented as an external mathematical counterexample, not a Lean-formalized SU(2) theorem. All 2709 Foundation/root Lean sources, three configurations, 113 baseline manuscripts and 21 selected Yang–Mills sources passed integrity checks. No original source was changed. The exact Git approval and both PRIVATE remote-ref checks are required at closure.

## Physical-distance scaling test

The source `block_contraction_spectral_gaps.tex` bounds correlations by `C₂||F||∞||G||∞ exp(-m dist_ℒ)` in **block-lattice distance** (its clustering theorem), while its transfer matrix is written `exp(-aH)` and its continuum theorem calls the resulting rate `m_phys` without an explicit conversion. At fixed positive physical separation `r`, the number of blocks grows on the order of `r/(La)` as `a→0`. If the block factor `q<1` and the amplitude for the chosen **unrenormalized bounded observables** are uniform, the bound tends to zero at that separation. The physical rate associated with a single step of length `La` is `-log(q)/(La)`; a lattice-step rate cannot simply be relabelled a fixed physical rate.

`Foundation/YMContinuumCorrelationScaling.lean` formalizes the exact sequence-level consequences. A bound `|S_n|≤Cq^n`, with `0≤q<1` and fixed `C`, forces `S_n→0`, so no nonzero limit at a fixed separated pair survives under those hypotheses. If `S_n>0` is the raw cross covariance and another raw variance `V_n≥v>0`, then the unit-cross-covariance normalization `V_n/S_n` has no finite uniform upper bound. Two independent Lean examples test both statements. These results do **not** assert that a Yang–Mills continuum limit is trivial: `C`, the observable sup norms, the block geometry, or the normalization may depend on `a`; each dependence must be carried through the estimate.

The longer `YM_MASS_GAP_UNCONDITIONAL.tex` defines `Z(a)^{-2}` as a positive separated-support covariance, so that its normalized two-point function equals one by construction. That algebraic normalization is valid when the raw covariance is positive. The missing test is whether its later uniform `L²`/higher-moment and distributional tightness claims remain compatible with the size of `Z(a)` and the raw variance under the proposed uniform block decay. In particular, a nonvanishing raw variance would force normalized variance escape by the Lean theorem. The source's separate nontriviality, OS and continuum hypotheses remain unverified; no contradiction is claimed without their exact amplitude/variance estimates.

### Verification, checkpoint 1641

The targeted build passed 1682 jobs; the full root build passed 6890 jobs. The complete transitive axiom audit passed 52276 declarations with only the standard three allowed axioms. All three new public theorem types and complete proofs were reviewed. Two independent Lean examples passed, including the concrete `q=1/2` variance-escape case. Source integrity passed for all 2710 Foundation/root Lean files (exactly four expected differences from the 1638 baseline), three configurations, all 113 baseline manuscripts and 21 selected Yang–Mills candidates. No original manuscript was altered. Commit, exact approval and verified PRIVATE `main`/research backup are required for closure.

### Exact checkpoint receipts and private backup

- Checkpoint 1639: commit `45604da352f9e4cff93e4a41d8b241cb95b8aa3a`; exact audit receipt accepted; both PRIVATE `main` and `codex/stardust-pseudoprocess-calculus` verified at that commit at `2026-10-27T23:44:43Z`.
- Checkpoint 1640: commit `b64805c15e35de483aa83d90bd7110f254934701`; exact audit receipt accepted; both PRIVATE refs verified at that commit at `2026-10-27T23:51:20Z`.
- Checkpoint 1641: commit `9ea31633ff2662bac54a4425f0e9618bcb80bf5a`; exact audit receipt accepted; both PRIVATE refs verified at that commit at `2026-10-28T00:00:15Z`.

The subsequent receipt-record edit changes documentation only. The focused Yang–Mills campaign remains active; Bakry Objective 2 remains paused.

## Existing verified transfer and cutoff results: direct reuse audit

A selective recheck of `YM_MASS_GAP_UNCONDITIONAL.tex` found that its literal strict-small-field interpretation says `X'=x` in the definition of the block transfer (near `Tdef`). For a probability conditional interior law, `Foundation/BoundarySmoothingObstruction.lean` already proves `retainedKernel_eq`: integrating a boundary-only `f(x)` leaves `f` unchanged. Its `fixed_error_floor` and `no_strict_error_budget` prove that an identity action on any test with nonzero derivative cannot be uniformly approximated by a strict smoother within an additive error budget below one. This is a direct theorem-level obstruction to the **literal retained-coordinate interpretation**. A genuine updated boundary variable or transition kernel must be constructed; reweighting the marginal alone does not produce heat smoothing. The result does not rule out a different, nontrivial block transfer.

The same manuscript defines the conditional density with the sharp indicator `1_{||(x,y)||≤δ}`, yet its covariance-derivative lemma differentiates as though the interior integration domain were fixed. `Foundation/MovingBoundaryCovarianceCounterexample.lean` already verifies an exact ball-cutoff example with zero potential: the conditional mean of `y²` is `(1-x²)/3`, with derivative `-2x/3`, although the covariance-only formula predicts zero. `Foundation/CoerciveMovingBoundary.lean` strengthens this: `uniformly_convex_counterexample` shows the defect persists for a positive uniformly convex quadratic potential and zero mixed Hessian. Thus interior convexity or a Brascamp–Lieb inequality does not remove the boundary flux. `Foundation/GaussianBoundaryFluxBound.strict_subcorridor_bound` supplies a genuine repair estimate `|flux|≤2 exp(-3cρ²/4)` only on a strict subcorridor with positive radius margin `ρ`; the estimate degenerates if no margin is retained. These exact existing declarations were re-elaborated with their full types in `.lake/stardust-ym-reuse-type-review.log`; no duplicate Lean infrastructure was added.

In the longer manuscript's “Covariance error bound for boundary observables,” `f=f(x)` is constant under `ν_x`, so `Cov_{ν_x}(f,DV)=0`. The displayed proof instead equates that covariance with the **random centered product** `f(DV-E[DV])` before averaging. The latter can be nonzero as a random variable, while its expectation is zero. Consequently the stated upper bound is trivial for the literal boundary-only `f`; it does not supply strict transfer smoothing. If `f(X')` genuinely depends on the interior, its `y` derivative and the boundary flux require their own estimates. This distinction was also noted in the earlier verified PDF audit recorded in `PROJECT_STARDUST_REPORT.md`; the present focused crosswalk makes it an explicit gate for the mass-gap route.

**Next substantive question:** specify a gauge-covariant `X'(x,y)` or conditional transition on the physical quotient, then derive a fixed-support or correctly flux-adjusted derivative identity and a contraction in the same norm used for influence propagation. Any smooth cutoff must carry its score derivative; any sharp cutoff must carry its moving-boundary term. Compare its full error, including flux, to the inverse-β budget already proved.

The existing library has a concrete finite-word SU(2) conditional law, so this question can be sharpened without constructing another abstract kernel. `SU2BoundaryWordKernel.kernel_markov` and `SU2BoundaryJointLaw.factorization` give an actual normalized link conditional and joint measure. `SU2ConditionalHeatBath.update_markov`, `joint_invariant`, `update_idempotent` and `boundary_preserved` verify a genuine one-link heat-bath update. It resamples the **interior link while preserving the entire boundary configuration**. Thus it is a valid probability kernel but cannot itself be the missing boundary-mixing `T` in the manuscript; repeated application of that same update is idempotent. A composition that changes which links are retained would need a specified schedule, gauge compatibility and a new quantitative correlation estimate. This is exact theorem reuse, not a new SU(2) construction.

`SU2BoundedObservableGradient.observable_conjugate`, `observable_bound` and `no_supnorm_gradient_bound` provide a separately verified SU(2) class-function witness: gauge-invariant boundedness does not control the gradient seminorm. This reinforces the need to prove the influence estimate in its actual Lipschitz norm instead of transporting an `H¹` estimate by bounded-observable rhetoric. It does not show that every Wilson-loop observable has the same derivative behavior.

## Actual SU(2) entropy and large-field stress tests

`SU2BoundaryConditionedEntropy.perturbed_stationary`, `entropy_positive` and `no_strict_contraction` apply to the **actual finite-word SU(2) joint law** and its one-link heat-bath update. A nontrivial boundary event produces a distinct stationary probability law with positive finite KL divergence from the reference joint law. Consequently no global strict KL contraction factor `q<1` holds for that update over all probability inputs, at any β. This is stronger than a binary boundary example because the reference is the actual continuously distributed interaction law. It does not refute the exact KL chain rule in `entropy_ym (4).tex`, which describes marginalizing full blocks relative to a Gaussian shadow, nor a dissipation estimate restricted to a rigorously characterized RG trajectory. It does rule out substituting this one-link heat bath for the manuscript's unproved all-scale `D/W≥0.527` mechanism.

`SU2StapleExtremes.cancelling_law` gives an explicit pair of SU(2) staples whose conditional link law equals Haar for **every** β, while `identity_concentration` gives aligned staples with concentration `β·card(s)`. Thus weak-coupling large-β concentration is not uniform over arbitrary boundary configurations. The cancelling pair lies outside a small identity corridor, so it does not contradict a proved **corridor-restricted** convexity statement. It makes the missing large-field probability/control gate concrete: a local corridor Hessian cannot be promoted to a global conditional contraction without handling such boundary data.

## Minimal boundary-changing transfer checkpoint

`Foundation/SU2OneWordTransfer.lean` reuses the verified finite-staple conditional kernel with a singleton word to construct an actual Markov transition from an SU(2) state to a newly sampled SU(2) state. The state and output spaces now coincide, so successive transitions are mathematically defined. The transition is not the one-link interior heat bath above: its output replaces the input word. At β=0 every input maps exactly to Haar law, and every probability input law becomes Haar after one step. The independent witness `haar_zero_transfer_changes_identity` proves the transition is genuinely state-changing by an open set of positive Haar mass that excludes the identity. At aligned identity input the exact staple concentration is β, retaining the original weak-coupling scale.

This is a finite one-word probability construction, not a gauge-invariant 2-by-2 block transfer, a physical quotient construction or a continuum estimate. Exact zero-coupling refresh does not establish contraction uniformly as β grows; indeed the aligned concentration scale suggests that weak-coupling influence requires its own estimate. The next test is the transition's quantitative influence in a gauge-compatible observable norm and whether a composed block version can retain a contraction after carrying cutoff flux and large-field errors. No mass-gap inference follows from the present kernel.

### Verification, checkpoint 1642

Four independent Lean examples passed. The full root build passed 6891 jobs, and the complete transitive axiom audit covered 52287 declarations with only `propext`, `Classical.choice` and `Quot.sound`. The ten new public declarations (two definitions and eight theorems), their unabridged types and complete source proofs were reviewed. Source integrity passed for all 2711 Foundation/root Lean files, the three configurations, 113 baseline manuscripts and 21 selected Yang–Mills candidates. Exact commit, audit receipt and both PRIVATE backup refs were required for closure and passed as recorded below.

Closure: commit `cf797b6b1175a1398004e847846e4aafae1f6af2` received the exact-commit audit approval. Both PRIVATE `main` and `codex/stardust-pseudoprocess-calculus` refs were independently verified at that same commit at `2026-10-28T00:25:17Z`. This receipt update changes documentation only; the audited Lean/configuration input hashes are unchanged. The focused Yang–Mills campaign remains active and Bakry Objective 2 remains paused.

## Actual one-word response at weak coupling

The same transfer has a sharper exact identification at identity input. `SU2OneWordTransfer.identity_exponent` reduces its one-word staple exponent to `β·halfTrace(B)`. `transition_identity_law` then identifies the **actual transition probability law** with the previously verified Haar half-trace exponential tilt. Combining the established Haar moments `SU2TiltEnergyResponse.moment_values` with the bounded tilt derivative theorem gives `identity_mean_hasDerivAt_zero`: the outgoing half-trace mean has coupling derivative exactly `1/4` at β=0. `positive_identity_mean_near_zero` yields an outgoing positive mean at some β in every interval `(0,ε)`. Three independent Lean examples recheck the law, derivative and positivity statement.

This is a genuine finite-dimensional stochastic response and an exact reuse of the operator/tilt calculus. It does **not** control the derivative with respect to the input boundary, give a Lipschitz or entropy contraction, or survive the continuum limit by itself. The physical route in `block_contraction_spectral_gaps.tex` still needs a gauge-compatible block kernel and a scale-uniform influence estimate in the norm actually used for clustering. The response theorem is a calibration test for any proposed approximation of that kernel, not a mass-gap estimate.

### Verification, checkpoint 1643

The targeted module build and three independent Lean examples passed. The full root build passed 6891 jobs. The complete transitive axiom audit covered 52293 declarations with only the three standard allowed axioms. The four new theorem types and complete proofs were reviewed, together with the retained ten declarations in the changed module. Source/config/archive integrity passed for all 2711 Foundation/root Lean files, three configurations, 113 baseline manuscripts and 21 selected Yang–Mills candidates. Exact commit approval and both PRIVATE remote-ref checks are required for closure.

These five old declaration types were re-elaborated in `.lake/stardust-ym-reuse-type-review.log` along with the earlier crosswalk. No new Lean module was needed. The primary avenue remains a boundary-changing, gauge-compatible block transition with a proved norm/influence estimate and scale-uniform large-field control. The entropy and staple examples narrow which shortcut constructions can serve it.

## Central-input influence of the actual one-word transfer

`Foundation/SU2OneWordBoundaryInfluence.lean` tests the finite-word SU(2) Markov transition against the two central boundary inputs, `I` and `-I`. For `-I`, the exact staple exponent is `-β·halfTrace(B)` and the outgoing law is the normalized Haar half-trace tilt at parameter `-β`. Its half-trace mean has derivative `-1/4` at zero coupling; the `I` response proved in `SU2OneWordTransfer` has derivative `+1/4`. Therefore the difference of these actual outgoing means has derivative `1/2` at zero and is positive at some coupling in every interval `(0,ε)`. This proves genuine input dependence for arbitrarily small positive β, with a gauge-invariant class observable. The four new public declarations give the full exact statements and proofs.

The result calibrates a candidate boundary-changing transfer in the direction requested by `block_contraction_spectral_gaps.tex`, but it is only a one-word SU(2) probability kernel. It does not establish a contracting block transfer or a physical mass gap. The manuscript still lacks gauge-compatible 2-by-2 composition, uniform large-field control, a cutoff-flux-adjusted derivative estimate, and a continuum/volume-uniform correlation bound.

A separate, currently **unformalized** analytic stress test suggests this toy kernel cannot have a β-uniform oscillation contraction constant below one. For Haar half-trace `x(B)∈[-1,1]`, the `I` output has density proportional to `exp(β x)`. For any `0<δ<1`, the open set `{x>1-δ/2}` has positive Haar mass, and the tilted mass of `{x≤1-δ}` is bounded by the reciprocal of that mass times `exp(-βδ/2)`. Thus the `I` output mean tends to one as β tends to infinity. The `-I` output has the opposite tilt, so Haar symmetry gives a mean tending to minus one. The oscillation ratio for the class observable `x` therefore tends to one. This argument concerns only the one-word kernel and needs full Lean formalization before it is treated as a verified Stardust theorem; it is not an obstruction to every possible gauge-compatible block mechanism.

### Verification, checkpoint 1644

The targeted module build passed. Three independent Lean checks passed, including a derived theorem that the two actual transition measures are unequal for arbitrarily small positive coupling. The complete root build passed 6892 jobs; the complete transitive axiom audit covered 52297 declarations with only `propext`, `Classical.choice`, and `Quot.sound`. All four new public theorem types and complete proofs were reviewed. Source integrity covered 2712 Foundation/root Lean files, three unchanged configurations, all 113 baseline manuscript hashes and all 21 selected Yang--Mills source hashes. The unformalized large-coupling stress test above is not counted as a Lean theorem. Exact Git approval and BOTH PRIVATE ref verification remain the closure gate.

Closure for checkpoint 1644: exact Git commit `42e73c710ec646c208bcb073898efddada08b9b3` received the audited receipt. Both PRIVATE `main` and `codex/stardust-pseudoprocess-calculus` refs were verified at this same commit at `2026-10-28T00:59:16Z`. This receipt entry changes documentation only; the Lean/configuration hashes and full-build/audit evidence above are unchanged. Focused Yang--Mills remains active; Bakry Objective 2 remains paused.
