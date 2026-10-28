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

## Verified large-coupling obstruction for the one-word transfer

`Foundation/SU2OneWordLargeCoupling.lean` closes the previously unformalized stress test for the **actual one-word SU(2) kernel**, without changing its finite-dimensional scope. For every `δ>0`, the Haar upper cap `{B : 1-δ/2 < halfTrace(B)}` has positive measure. The partition is at least that mass times `exp(β(1-δ/2))` for `β≥0`, while the unnormalized mass of `{halfTrace≤1-δ}` is at most `exp(β(1-δ))`. The normalized lower-cap mass is therefore bounded by `exp(-βδ/2)` divided by the positive upper-cap mass, and tends to zero. A bounded-observable defect estimate then proves that the half-trace mean under the identity-input transition tends to `1` as `β→+∞`.

Haar translation by the central element `-I` gives exact oddness of the tilted mean. The outgoing mean from `-I` tends to `-1`, so the difference between these two outgoing half-trace means tends to `2`. `no_uniform_central_mean_contraction` states the decisive consequence: for every `q<1`, some `β≥0` makes this difference exceed `2q`. Since the input half-trace values at `I` and `-I` differ by exactly `2`, this one-word transition cannot satisfy a coupling-uniform strict oscillation contraction for that gauge-invariant class observable. The proof includes the exact positive Haar cap, partition lower bound, tail bound, convergence and symmetry identities; it does not rely on numerical extrapolation.

This is a **counterexample to using this particular one-word refresh as a uniform weak-coupling influence mechanism**. It is not a counterexample to every possible block transition, to a β-dependent physical-scale estimate, or to a continuum Yang--Mills mass gap. In particular, a physical transfer may involve simultaneous link updates, gauge quotient geometry, scale-dependent normalization and large-field control that the one-word kernel does not encode. The burden in `block_contraction_spectral_gaps.tex` remains construction of such a kernel and a scale/volume-uniform correlation estimate with all cutoff and perturbation errors included. The earlier analytic outline in this ledger is superseded as a status claim by these Lean proofs, but its finite-dimensional limitation remains.

### Verification, checkpoint 1645

The focused target built successfully. Three independent Lean examples passed, including the explicit failure of a universal `2q` bound for any `q<1`. The full root build passed 6893 jobs. The complete transitive axiom audit covered 52302 Foundation declarations and found only `propext`, `Classical.choice`, and `Quot.sound`. All five public theorem types and their complete source proofs were reviewed; private helper declarations are covered transitively through those proofs. Source/config/archive integrity passed for all 2713 Foundation/root Lean files, three unchanged configurations, 113 baseline manuscripts and 21 selected Yang--Mills candidates. No original source was edited. Exact Git commit approval and BOTH PRIVATE ref verification remain the closure gate.

Closure for checkpoint 1645: exact Git commit `f8b2e0781d817b0db48b6f4e33c6a6f5fc3767c2` received the audited receipt. Both PRIVATE `main` and `codex/stardust-pseudoprocess-calculus` refs were verified at this same commit at `2026-10-28T01:33:01Z`. This receipt entry changes documentation only; the Lean/configuration hashes and full-build/audit evidence above are unchanged. Focused Yang--Mills remains active; Bakry Objective 2 remains paused.
## Endpoint-gauge correction to the one-word witness

The phrase “gauge-invariant class observable” in checkpoints 1644–1645 was too broad for a **single open link**. Half-trace is invariant under simultaneous conjugation, but a link from one vertex to another transforms as `A ↦ g A h⁻¹` with independent endpoint gauges. `Foundation/SU2OpenLinkGaugeObstruction.lean` now defines that full endpoint invariance and proves every invariant real observable of one link is constant: the left endpoint action alone sends the identity to every group element. It computes `halfTrace(I)=1` and `halfTrace(-I)=-1`, hence half-trace is **not** endpoint-gauge invariant. The earlier response and large-coupling theorems remain valid as finite SU(2) Markov-kernel statements, but their half-trace witness cannot be presented as a physical open-link observable or a gauge-invariant mass-gap obstruction.

For comparison, a two-edge oriented closed cycle has `closedPairTrace(A,B)=halfTrace(AB)`. Under `(A,B) ↦ (gAh⁻¹,hBg⁻¹)`, the product becomes `g(AB)g⁻¹`; the verified `closedPairTrace_gauge` proves invariance, and `closedPairTrace_nonconstant` shows it retains nontrivial information. This is a minimal algebraic Wilson-loop model, not a constructed plaquette transfer or a continuum observable. It identifies the next exact requirement: any influence or spectral estimate offered as physical evidence must act on closed-loop/gauge-quotient observables and use a gauge-covariant boundary-changing kernel. One-word half-trace tests remain diagnostics only.
The obstruction extends to the **actual transfer means**: `endpointInvariant_integral` identifies the mean of any fully endpoint-invariant one-link observable under any probability law with its value at the identity, and `endpointInvariant_transfer_mean` proves that the one-word transition has the same such mean for every pair of inputs and every coupling. Thus no nonconstant physical one-link endpoint-invariant response can be extracted by changing the test function; closed loops are mathematically necessary for a nontrivial gauge-invariant test of this route.
### Verification, checkpoint 1646

The targeted module and complete 6894-job root build passed. The complete transitive axiom audit checked 52321 Foundation declarations and found only `propext`, `Classical.choice`, and `Quot.sound`; all ten new public types and their complete source proofs/definitions were reviewed. Three independent Lean examples passed: distinct closed-cycle gauge orbits, equality of actual transfer means for fully endpoint-invariant tests at central inputs, and failure of endpoint invariance for half-trace. Source/config/archive integrity passed for all 2714 Foundation/root Lean files, three unchanged configurations, 113 baseline manuscripts and 21 selected Yang–Mills candidates. No original source was edited. Exact commit approval and BOTH PRIVATE ref verification remain the closure gate.
Closure for checkpoint 1646: exact Git commit `dabbcf53b4f4c56d1baa6287aa357c7f515f65d8` received its audited receipt. Its first guarded sync attempt refused to push because the GitHub API reported the repository PUBLIC at 2026-10-28T01:48:07Z; independent `gh repo view` confirmed that visibility and admin permission. The user-required PRIVATE setting was restored before any push, and a second independent visibility check returned PRIVATE. Guarded synchronization then verified both PRIVATE `main` and `codex/stardust-pseudoprocess-calculus` refs at the exact commit at 2026-10-28T01:51:05Z; an additional post-sync visibility check remained PRIVATE. The cause of the temporary public setting is unknown. The privacy guard behaved correctly, and no checkpoint 1646 content was pushed while public. Focused Yang–Mills remains active; Bakry Objective 2 remains paused.
## Exact closed-cycle law for the one-word conditional kernel

Foundation/SU2ClosedLoopTransfer.lean applies the verified Haar staple-law pushforward to the singleton word. The quaternion polar orientation of a singleton SU(2) word is proved to be that word itself and its radius is exactly one. Therefore, for every input/staple A and every coupling β, the pushforward of the actual one-word conditional law of B by B ↦ AB is the same normalized Haar half-trace tilt at β. The observable halfTrace(AB) is exactly the nonconstant gauge-invariant two-edge closed-cycle trace from checkpoint 1646. Its conditional mean is independent of A, has derivative 1/4 at zero coupling, and tends to one as β→+∞.

This is a positive, exact finite-cycle link between the SU(2) conditional probability kernel and a genuinely endpoint-gauge-invariant observable. It also changes how the earlier one-word central-input test should be read: the central-input separation of open-link half-trace means disappears when the measured observable is the matched closed product AB; the closed-loop mean is the same for every fixed A. The local closed-cycle law alone gives no separation decay, transfer spectral gap, nontrivial four-dimensional continuum limit, or physical mass gap. A mass-gap route must couple distinct closed loops at separated physical locations through a gauge-covariant multi-link/block law and prove a uniform connected-correlation estimate.
### Verification, checkpoint 1647

The targeted module passed. Three independent Lean tests passed: exact equality of the central-input pushforward law with the identity-input law, equality of closed-cycle means for arbitrary inputs, and zero derivative of the central closed-loop mean difference. The complete root build passed 6895 jobs. The complete transitive axiom audit covered 52325 Foundation declarations and found only propext, Classical.choice, and Quot.sound. All four new public theorem types and complete source proofs, including the two private singleton identifications, were reviewed. Source/config/archive integrity passed for 2715 Foundation/root Lean files, three unchanged configurations, all 113 baseline manuscripts, and 21 selected Yang–Mills candidates. Exact Git approval and BOTH PRIVATE ref verification remain the closure gate.

Closure for checkpoint 1647: the exact mathematical commit
084d12e1f8a0a129585b0976f527527c167206de received its full-build,
axiom/type and source-integrity audit receipt. After the user designated the
GitHub repository PUBLIC and the visibility-neutral sync script was installed,
both main and codex/stardust-pseudoprocess-calculus remote refs were verified
at that exact commit at 2026-10-28T02:19:44Z. The receipt honestly reports
visibility=public. Earlier sync attempts under the superseded private-only
guard failed without pushing. This closure update changes documentation only;
all checkpoint 1647 Lean/configuration bytes and verification logs are unchanged.
Focused Yang–Mills remains active and Bakry Objective 2 remains paused.
## Exact endpoint-gauge covariance of the one-word conditional kernel

Foundation/SU2GaugeCovariantTransfer.lean proves a stronger positive identification for the actual one-word SU(2) kernel. First, the conditional law at staple A is the pushforward of the fixed half-trace Haar tilt by C ↦ A⁻¹C. Haar probability is right invariant by uniqueness of normalized Haar measure, hence conjugation invariant; the half-trace density is conjugation invariant as well. The normalized tilt therefore has an exactly conjugation-invariant law. Combining these statements gives transition_gauge_covariant: when an oriented staple changes as A ↦ gAh⁻¹ under independent endpoint gauges, the conditional output law changes by the pushforward B ↦ hBg⁻¹. This is equality of actual probability measures for every g,h,A in SU(2) and every real coupling β, with no unverified existence assumption.

Together with closedPairTrace_gauge and closedLoop_law, this establishes exact finite-cycle gauge compatibility for this conditional update. It does not construct the manuscript's updated boundary variable X' on a 2-by-2-by-2-by-2 block, a transfer on a gauge quotient of many links, a scale-uniform gradient/influence contraction, or separated Wilson-loop correlation decay. The one-cycle closed-product law is independent of its staple and so cannot by itself express propagation between distant gauge-invariant observables. The next productive test is a specified multi-link composition whose gauge action and physical observable sector are both explicit, followed by a quantitative correlation estimate with cutoff/large-field errors carried through.
### Verification, checkpoint 1648

The targeted module passed. Three independent Lean examples passed: the central-input law transforms by the predicted endpoint action, every measurable test obeys the transformed-law integral identity, and the matched closed-cycle mean is unchanged under endpoint gauges. The complete root build passed 6896 jobs. The complete transitive axiom audit checked 52336 Foundation declarations and found only propext, Classical.choice, and Quot.sound. All four new public theorem types and their complete source proofs were reviewed. Source/config/archive integrity passed for all 2716 Foundation/root Lean files, three unchanged configurations, 113 baseline manuscripts and 21 selected Yang–Mills candidates. No original manuscript was changed. Exact audited commit and verified main/research remote refs remain the closure gate; repository visibility is user-controlled under the current PUBLIC policy.

## Two-step one-word chain: exact closed-loop rectangle factorization

For the actual one-word kernel, take B from the transition at A and then D from the transition at B. The new theorem SU2TwoLoopChain.two_loop_rectangle proves that for every measurable s,t in SU(2), the nested probability of A B in s and B D in t equals mu_beta(s) mu_beta(t), where mu_beta is the normalized Haar half-trace tilt. Thus consecutive closed products in this specific directed chain have exactly factorized event probabilities, even though the open links share B. This is a rigorous finite-chain obstruction to obtaining nonzero connected correlations by merely iterating this one-word refresh. It does not describe adjacent Wilson loops in a four-dimensional Gibbs lattice with overlapping plaquettes or rule out gauge-covariant block interactions. A physically relevant route must add a specified interaction coupling the closed-loop variables and prove its scale/volume-uniform estimates. Original Yang--Mills manuscripts remain unchanged.


### Verification, checkpoint 1649

The targeted module and two concrete independent Lean tests passed, including upper/lower half-trace events at general coupling and their explicit Haar factorization at zero coupling. The complete root build passed 6897 jobs. The complete transitive axiom audit checked 52337 Foundation declarations and found only propext, Classical.choice, and Quot.sound. The single new public theorem type and complete source proof, including its two private section lemmas, were reviewed. Source/configuration/archive integrity passed for all 2717 Foundation/root Lean files, three unchanged configurations, 113 baseline manuscripts and 21 selected Yang--Mills candidates. No original manuscript changed. Exact commit approval and both remote ref checks remain the closure gate; visibility remains user-controlled under the PUBLIC policy.

## Actual two-step joint law for the one-word chain

Checkpoint 1649 established factorization of nested conditional event probabilities. `Foundation/SU2TwoLoopJointLaw.lean` upgrades this to an equality of actual probability measures. The path measure is the composition-product of the one-word law at A with the one-word Markov kernel at its sampled B. Matrix-coordinate measurability proves the map `(B,D) ↦ (AB,BD)` is measurable without an unproved product-topology instance. The pushforward is exactly `mu_beta.prod mu_beta`, where `mu_beta` is the normalized Haar half-trace tilt, for every A and real beta. In particular all measurable functions of the two consecutive closed products are independent whenever their integrals are defined.

This is a decisive obstruction to obtaining nonzero connected correlations by simply iterating this specific one-word refresh. It is a three-edge, two-vertex finite toy chain, not the interacting four-dimensional lattice measure in `block_contraction_spectral_gaps.tex`; overlapping plaquettes in that measure can couple closed products. A mass-gap route still requires a specified gauge-covariant interaction or block transfer with uniform physical-scale connected-correlation control, including cutoff and large-field errors. This result supplies no continuum construction or positive physical gap. The original manuscripts remain untouched.

### Verification, checkpoint 1650

The targeted module and three independent Lean examples passed: the actual path probability measure, explicit Haar product law at zero coupling, and an upper/lower half-trace event factorization at arbitrary coupling. The complete root build passed 6898 jobs. The complete transitive axiom audit checked 52340 Foundation declarations and found only propext, Classical.choice, and Quot.sound. Both new public theorem types and their complete source proofs, including finite matrix-coordinate measurability and the private section argument, were reviewed. Source/configuration/archive integrity passed for all 2718 Foundation/root Lean files, three unchanged configurations, 113 baseline manuscripts and 21 selected Yang--Mills originals. No original manuscript was changed. Exact commit approval and both remote ref checks remain the closure gate; repository visibility remains controlled by the user.

## Gauge-invariant two-loop interaction response

`Foundation/SU2CoupledLoopResponse.lean` tests what additional mathematics is needed after the exact independence result. On the pair of closed SU(2) holonomies `(C,D)`, take the actual Haar product baseline `mu = law.prod law` and the bounded interaction `X(C,D)=halfTrace(C) halfTrace(D)`. The normalized Gibbs law `coupledLaw(r)` has density proportional to `exp(r X)`. It is an actual probability measure and is invariant under independent conjugations of the two holonomies. At `r=0` it equals the closed-product pushforward of the actual two-step one-word chain for every input A. This is a newly specified finite interaction, not an identification with the manuscript's four-dimensional Gibbs action.

The connected covariance of the two half-traces under `coupledLaw(r)` has derivative exactly `1/16` at `r=0`, using the verified SU(2) Haar mean zero and second moment `1/4` for each factor. Consequently, for every epsilon>0, some `0<r<epsilon` gives strictly positive connected covariance. This is a concrete positive control showing that a genuine gauge-invariant interaction can transmit correlation where the bare refresh cannot. It does not give decay at separation, a transfer spectral gap, a continuum/infinite-volume construction, or a physical mass gap. The parameter r is an added two-loop coupling, not the original Yang--Mills beta. A serious block route must still construct its actual interaction and carry scale, cutoff and large-field errors uniformly. No original manuscript bytes changed.

### Verification, checkpoint 1651

The targeted module and three independent Lean examples passed: exact identification of the zero-interaction law with the actual two-step chain, full gauge invariance at a nonzero coupling, and existence of positive covariance expressed directly as integrals under the coupled law. The complete root build passed 6899 jobs. The complete transitive axiom audit checked 52364 Foundation declarations and found only propext, Classical.choice, and Quot.sound. All 17 new public definition, instance, and theorem types and their complete source proofs were reviewed; private moment and measurability lemmas are included transitively. Source/configuration/archive integrity passed for all 2719 Foundation/root Lean files, three unchanged configurations, 113 baseline manuscripts and 21 selected Yang--Mills originals. No original manuscript was modified. Exact audited commit and both verified backup refs remain the closure gate.

## Reflection-positive time shift obstruction — checkpoint 1652

In `ResearchSources/Incoming/YM_MASS_GAP_UNCONDITIONAL.tex` (SHA-256 `6F1C671629640F1AA88E6A2B2A74CF4174E0B9202C1810E3F1702492255DAC23`), lines 1173–1188 claim the OS reflected norm of every positive-time translated vector equals its unshifted norm. This is the decisive incorrect step in the proposed semigroup-contraction proof; line 1198 repeats it in the continuity argument. Reflection and translation do not commute in that way: reflection reverses time, so the reflected two-point separation increases by `2t`.

`Foundation/YMReflectionPositiveShift.lean` gives an axiom-audited counterexample at the one-particle kernel level. For the stationary covariance `C(u)=exp(-|u|)`, the positive-time reflected kernel is `C(s+t)=exp(-s)exp(-t)` for `s,t≥0`; every finite real Gram quadratic form is a square and hence nonnegative. Yet for every `t>0`, its shifted diagonal is `C(2t)=exp(-2t)<C(0)=1`. Thus positive reflected-norm preservation is false even for this elementary reflection-positive kernel. The actual contraction conclusion is compatible with this example, but it requires a different proof using reflection positivity, a well-defined quotient, and the correct shifted kernel; OS1–OS2 alone do not supply the claimed norm identity or positive Hilbert structure. The theorem's full OS hypotheses, strong continuity and self-adjoint generator are not formalized by this finite-kernel test. In particular, this does not construct a Yang–Mills continuum measure or establish a physical mass gap. The original manuscript bytes remain unchanged.

### Verification, checkpoint 1652

The targeted Lean module and two independent examples passed. The complete root build passed 6900 jobs. The complete transitive audit checked 52372 Foundation declarations and found only `propext`, `Classical.choice`, and `Quot.sound`; all five new public definition/theorem types and complete source proofs were reviewed. Source integrity passed for 2720 Foundation/root Lean files, three unchanged configurations, 113 baseline manuscripts and 21 selected Yang–Mills originals. The cited `YM_MASS_GAP_UNCONDITIONAL.tex` hash was read directly and its bytes were not changed. This finite-kernel result refutes the manuscript's isometry step only; it does not claim a complete OS reconstruction or physical mass gap.

## Positive SU(2) channel does not force connected covariance — checkpoint 1653

`ResearchSources/Incoming/YM_MASS_GAP_UNCONDITIONAL.tex` (SHA-256 `6F1C671629640F1AA88E6A2B2A74CF4174E0B9202C1810E3F1702492255DAC23`) asserts in its covariance proof at lines 1545–1553 that a positive retained character channel survives subtraction of the product of means. Lines 1683–1692 similarly use a mixing *upper* bound and positive local channel coefficients to infer a cross-block covariance *lower* bound. Neither implication follows from those stated ingredients: the connected part needs an independently proved inter-block interaction or positive spectral overlap.

`Foundation/SU2PositiveChannelObstruction.lean` supplies an actual compact-group path-law test, reusing the verified one-word SU(2) kernel. For every initial holonomy A and every ε>0, there is a positive β<ε for which the closed-loop half-trace marginal mean is strictly positive. Nevertheless, the *actual joint law* of the two consecutive closed products is the product of their tilted Haar marginals, and their connected half-trace covariance is exactly zero at that same β. All three actual integrals (joint moment and both marginals) are in the Lean theorem; the identity is not merely a symbolic covariance definition. Positive local character response can therefore coexist with no transmission across loops.

This counterexample refutes the manuscript's general inference, not its specific four-dimensional interacting Gibbs measure, whose plaquettes may have nonzero connected correlations. A corrected nontriviality proof must identify a gauge-invariant cross-block observable, prove a positive (or otherwise nonvanishing) covariance lower bound with its subtraction term controlled, and propagate that bound uniformly through the chosen normalization and continuum/volume limits. Exponential clustering alone is an upper bound and cannot supply that lower bound. The original manuscript is unchanged.

### Verification, checkpoint 1653

The targeted module build passed 4114 jobs and the complete root build passed 6901 jobs. The complete transitive axiom audit checked 52382 Foundation declarations and found only `propext`, `Classical.choice`, and `Quot.sound`. All eight new public definitions/theorem types and complete source proofs were reviewed. Two independent Lean examples passed: the actual identity-initialized path law has a positive marginal channel at some arbitrarily small positive β and zero connected covariance, and the covariance vanishes for every initial SU(2) holonomy at a fixed nonzero coupling. Source integrity passed for 2721 Foundation/root Lean files, three pinned configurations, 113 baseline manuscripts and 21 selected Yang–Mills originals; the cited manuscript SHA-256 is unchanged. This is a finite exact counterexample to the asserted inference, not a four-dimensional continuum theorem.

## OS clustering quantifier and reflection placement — checkpoint 1654

In `ResearchSources/Incoming/YM_MASS_GAP_UNCONDITIONAL.tex` (SHA-256 `6F1C671629640F1AA88E6A2B2A74CF4174E0B9202C1810E3F1702492255DAC23`), the OS mass-gap section lines 1311–1315 assumes a single finite `C` bounds connected correlations for *any* gauge-invariant local observables `A,B`, without a norm or observable-dependent prefactor. Scalar multiples of an admissible observable remain admissible. `Foundation/YMOSClusterObstruction.lean` formalizes this scaling defect under the actual gauge-invariant coupled SU(2) law from checkpoint 1651: at arbitrarily small positive loop coupling its connected covariance is positive, and no finite `C exp(-m t)` can bound all scalar multiples of one observable, for any fixed real `m,t`. This does not assign physical separation to the toy model; it proves the algebraic quantifier obstruction at any fixed separation with nonzero covariance. The manuscript itself uses the correctly homogeneous `C ||A||∞ ||B||∞ exp(-m dist)` form later at lines 1925–1930. A repair of the OS statement must use such a norm factor or allow a finite prefactor depending on each fixed test vector, while keeping a common decay exponent.

The same OS proof, lines 1325–1334, identifies the reconstructed matrix element of a positive-time-supported observable `A` with the *unreflected* covariance `<A τ_t A>-<A>²`. The OS inner product instead contains time reflection: the appropriate two-point expression is `<(θ A) τ_t A>-<A>²` (with the author's placement/conjugation convention). The new Lean theorem tests the distinction in the positive kernel `C(u)=exp(-|u|)`: for an observable at positive time `s`, the reflected pair at separation `2s+t` has `C(2s+t)<C(t)` for every `t≥0`, while the latter is the ordinary translated pair. Thus the displayed identity is false even in this elementary reflection-positive one-particle sector. This is separate from checkpoint 1652's false translated-norm isometry. Neither kernel theorem asserts a full stochastic-field OS construction.

A corrected spectral argument requires a valid reflected-positive Hilbert quotient and semigroup, a bound on its reflected matrix elements for a dense family of mean-zero local vectors with a common exponent and legitimate vector-dependent constants, and a justified cyclicity/density passage. The positivity of spectral measures then supports the standard gap inference; these prerequisites are not established by the manuscript's two displayed formulas. No original manuscript was changed and no four-dimensional physical mass gap is claimed.

### Verification, checkpoint 1654

The targeted module and three independent Lean examples passed. The complete root build passed 6902 jobs. The complete transitive axiom audit checked 52388 Foundation declarations and found only `propext`, `Classical.choice`, and `Quot.sound`. All five new public definition/theorem types and their complete proofs were reviewed; transitive dependencies are included in the audit. Source integrity passed for 2722 Foundation/root Lean files, three pinned configurations, 113 baseline manuscripts and 21 selected Yang–Mills originals. The cited manuscript SHA-256 remained `6F1C671629640F1AA88E6A2B2A74CF4174E0B9202C1810E3F1702492255DAC23`. The manuscript was not edited. The result isolates two invalid displayed OS steps and leaves the corrected continuum reconstruction and physical gap open.

## Correct positive bridge: Laplace decay excludes subgap spectral mass — checkpoint 1655

The manuscript `ResearchSources/Incoming/YM_MASS_GAP_UNCONDITIONAL.tex` (SHA-256 `6F1C671629640F1AA88E6A2B2A74CF4174E0B9202C1810E3F1702492255DAC23`) uses the standard spectral-measure implication at lines 1012–1018 and 1330–1334. Unlike its incorrect OS formulas audited at checkpoints 1652 and 1654, this measure-theoretic implication is valid when its hypotheses are stated precisely. `Foundation/YMSpectralLaplaceBridge.lean` now proves the general positive-measure version, independently of the SU(2) toy model. Let `μ` be any finite positive Borel measure on ℝ. If for every integer `n≥0` the Laplace integrand `x↦exp(-n x)` is integrable and its integral is at most `C exp(-m n)` with one finite real `C`, then `μ((−∞,m))=0`. In particular, a positive spectral measure of a nonnegative Hamiltonian satisfying that bound cannot carry mass in `[0,m)`. The proof first lower-bounds the Laplace integral by `exp(-n b) μ((−∞,b))` for every `b<m`, cancels the positive factor, takes the geometric limit, and exhausts `(-∞,m)` by countably many such intervals.

For the Yang–Mills route, this theorem requires a *genuine positive spectral measure* from a correctly constructed reflection-positive semigroup and a bound on each relevant reflected matrix element. The prefactor may depend on the fixed observable/vector; the decay exponent `m` must be common, and an appropriately dense generating sector is needed to pass from vector spectral measures to the full Hamiltonian spectrum. These process/continuum and density hypotheses are not provided by the theorem and remain open in the manuscript. The result does not establish a Yang–Mills mass gap by itself. The original manuscript remains unchanged.

### Verification, checkpoint 1655

The targeted spectral module passed 3369 jobs with a deliberately smaller Mathlib import set; the complete root build passed 6903 jobs. The complete transitive axiom audit checked 52391 Foundation declarations and found only `propext`, `Classical.choice`, and `Quot.sound`. All three new public theorem types and their complete proofs were reviewed, including the finite-measure, integrability, common-exponent and all-integer-time hypotheses. An independent Dirac-atom Lean test rejected an exponential bound that would falsely place mass below the gap. Source integrity passed for 2723 Foundation/root Lean files, three pinned configurations, 113 baseline manuscripts and 21 selected Yang–Mills originals. The cited manuscript hash was rechecked directly and remained unchanged. This is a general spectral-measure theorem, not proof that the requisite Yang–Mills spectral measures or bounds exist.

## Weak SU(2) loop coupling and two-point normalization — checkpoint 1656

`ResearchSources/Incoming/YM_MASS_GAP_UNCONDITIONAL.tex` (SHA-256 `6F1C671629640F1AA88E6A2B2A74CF4174E0B9202C1810E3F1702492255DAC23`) defines a renormalization factor from a positive separated-support covariance at lines 1560–1569 and argues for uniform centered `L²` control at lines 1704–1717. That conclusion requires a quantitative comparison of local variance with the chosen cross covariance; positivity of the latter alone does not provide it.

`Foundation/SU2WeakCouplingNormalization.lean` constructs an explicit sequence `r_n>0` of couplings for the verified gauge-invariant two-loop Gibbs laws, with `r_n<1/(n+1)` and positive connected half-trace covariance for every `n`. Thus `r_n→0` and the cross covariance tends to zero. The module identifies its `localVar(r)` with the *actual centered variance* of one loop under `coupledLaw(r)`, proves `localVar(0)=1/4`, and derives `localVar(r_n)→1/4` from the verified bounded-tilt derivative theorem. It follows that `localVar(r_n)/corr(r_n)` has no uniform finite upper bound. This is exactly the variance of a one-loop observable after unit cross-covariance normalization, up to the elementary square-root scaling convention. The selection of `r_n` is classical and noncanonical; its stated bounds and limiting properties are proved.

This is a rigorous finite interacting compact-group model exhibiting a genuine normalization obstruction. It does **not** show that the four-dimensional Yang–Mills plaquette variance stays nonzero or that its selected covariance vanishes at a particular rate. A manuscript repair must prove the actual scale-dependent variance/cross-covariance ratio is uniformly bounded for its chosen smeared gauge-invariant fields, together with the necessary higher-moment/tightness estimates. The original manuscript is untouched.

### Verification, checkpoint 1656

The targeted SU(2) normalization module passed 4114 jobs; the complete root build passed 6904 jobs. The complete transitive axiom audit checked 52403 Foundation declarations and found only `propext`, `Classical.choice`, and `Quot.sound`. All 12 new public definitions/theorem types, the private existence lemma and all complete proofs were reviewed. Two independent Lean examples passed, including a concrete positive fifth coupling and a witness with normalized variance ratio greater than 100. Source integrity passed for 2724 Foundation/root Lean files, three pinned configurations, 113 baseline manuscripts and 21 selected Yang–Mills originals. The cited manuscript hash was rechecked directly and remains unchanged. This finite-model scale test does not infer any four-dimensional continuum mass gap.

## Gauge-covariant interacting closed-loop transfer — checkpoint 1657

The focused transfer question in `ResearchSources/Incoming/block_contraction_spectral_gaps.tex` (SHA-256 `0C40FA6B92B830C0E2309BD6471D55CB0EB9BFB94296B9267AD23A5280FA4C60`, strict block-contraction theorem around lines 318–384) and `ResearchSources/Incoming/YM_MASS_GAP_UNCONDITIONAL.tex` (SHA-256 `6F1C671629640F1AA88E6A2B2A74CF4174E0B9202C1810E3F1702492255DAC23`, uniform-scale assumptions around lines 866 and 1033–1042) is whether a *specified actual transfer* can have both gauge compatibility and scale-uniform correlation control.

`Foundation/SU2InteractingLoopKernel.lean` constructs an actual Markov kernel on closed SU(2) holonomies: from state `C`, sample `D` with normalized Haar density proportional to `exp(r halfTrace(C) halfTrace(D))`. The exponent is jointly measurable and bounded, every section is a probability measure, and the transition is covariant under independent conjugations of input and output holonomies. Each transition has the explicit uniform-in-state Doeblin minorization `K_r(C,·) ≥ exp(-2|r|) Haar(·)`. This is a genuine positive finite-parameter control, obtained from the exact normalized density rather than an assumed transfer inequality.

The kernel is not an independent refresh: its conditional half-trace means at `C=1` and `C=-1` differ for arbitrarily small positive `r`, by direct reuse of the verified one-word response results. At large `r`, the same two conditional means approach `+1` and `-1`; the formal theorem shows that for every `q<1`, some `r≥0` violates the corresponding `2q` mean-separation contraction bound. Thus this concrete gauge-covariant transfer admits a Doeblin constant at each finite `r` but **no contraction factor uniform across all large couplings** in that central observable test. The explicit minorization coefficient itself decays as `r` grows, but the stronger no-uniform-contraction statement comes from actual conditional means, not merely from weakness of the bound.

This is a one-closed-loop Markov model, not the proposed four-dimensional tile/plaquette RG operator. Its two-step joint law is not identified with the separately constructed symmetric `coupledLaw(r)`, since the transition has a state-dependent normalization. No invariant law, multistep correlation decay, physical-distance estimate, continuum or infinite-volume limit, or quantum mass gap is claimed here. A successful Yang–Mills route must construct the *actual* gauge-covariant block transfer and prove a mechanism that retains a uniform physical-scale estimate despite any weakening of its finite-step minorization or mean contraction along the scaling trajectory. Original manuscripts remain unchanged.

### Verification, checkpoint 1657

The targeted interacting-loop module passed 4115 jobs; the complete root build passed 6905 jobs. The complete transitive axiom audit checked 52421 Foundation declarations and found only `propext`, `Classical.choice`, and `Quot.sound`. All 16 new public definition/theorem types and complete source proofs were reviewed, including the exact kernel section, probability, independent-conjugation covariance, Haar measure minorization and large-coupling counterexample. Four independent Lean examples passed: Markov property, conjugation covariance, exact Haar lower bound at zero coupling, and violation of a proposed `q=1/2` uniform mean contraction. Source integrity passed for 2725 Foundation/root Lean files, three pinned configurations, 113 baseline manuscripts and 21 selected Yang–Mills originals. The block-contraction source hash `0C40FA6B92B830C0E2309BD6471D55CB0EB9BFB94296B9267AD23A5280FA4C60` was rechecked directly. Both original manuscripts remain unchanged. A four-dimensional continuum mass gap is not claimed.

## Stationary interacting SU(2) loop law — checkpoint 1658

`Foundation/SU2LoopEquilibrium.lean` closes the exact finite-model connection between the gauge-covariant Markov kernel of checkpoint 1657 and the symmetric coupled Gibbs law of checkpoint 1651. For each finite real coupling r, let Z_r(C) be the transition's Haar partition function and let Z_r^tot be the product-Haar partition function for the interaction r halfTrace(C) halfTrace(D). The initial law pi_r has Haar density Z_r(C)/Z_r^tot. Lean proves its positivity/measurability, the pointwise detailed-balance density identity, and the exact measure identity pi_r compProd K_r = coupledLaw(r). It then proves pi_r is a probability measure, the coupled edge law is exchangeable, and K_r comp pi_r = pi_r. Thus this is an actual stationary, reversible one-step compact-group stochastic law, with a gauge-invariant interaction and nonzero connected half-trace covariance at arbitrarily small positive coupling.

This sharpens the previous checkpoint's caution: starting the kernel from Haar generally does not give `coupledLaw(r)` because the transition normalization depends on the starting state, but starting from the proved partition-weighted pi_r does give it exactly. The equilibrium construction is not a Yang--Mills Gibbs measure, a four-dimensional block transfer, a continuum limit or a physical mass gap. The verified Doeblin bound applies for each finite r; a uniform rate along a scale-dependent coupling trajectory, multistep spatial correlation estimate and scale/volume-uniform construction remain open. The original block-contraction manuscript `ResearchSources/Incoming/block_contraction_spectral_gaps.tex` retains SHA-256 `0C40FA6B92B830C0E2309BD6471D55CB0EB9BFB94296B9267AD23A5280FA4C60`; no source manuscript was changed.

### Verification, checkpoint 1658

The promoted equilibrium module passed its targeted 4117-job build, and the complete root build passed 6906 jobs. The complete transitive audit checked 52446 Foundation declarations; the only dependencies were `propext`, `Classical.choice`, and `Quot.sound`. All 11 new public definition/theorem types and their complete proof bodies were reviewed, including the measure-level `compProd` equality and exact stationarity statement. Three independent Lean examples passed: the equilibrium initial law is Haar at r=0, its stationary edge law is Haar product at r=0, and some arbitrarily small positive r has positive connected half-trace covariance under the actual stationary edge law. Source integrity passed for all 2726 Foundation/root Lean files, all three pinned configurations, 113 baseline manuscript files and 21 selected Yang--Mills originals. Both cited incoming manuscripts retain their prior SHA-256 hashes. No `sorry`, new axiom, original-manuscript change or physical mass-gap assertion was introduced.

## Explicit stationary-reference reset bound — checkpoint 1659

`Foundation/SU2StationaryMinorization.lean` extends the actual stationary closed-loop Markov model of checkpoint 1658. For each real r it proves the global two-loop partition function is at least exp(-|r|), the equilibrium Haar density is at most exp(2|r|), and every transition density dominates exp(-4|r|) times that equilibrium density. The resulting measure-level theorem is `exp(-4|r|) pi_r <= K_r(C,·)` for every closed-loop state C. Unlike checkpoint 1657's Haar minorization, this reset reference is the *verified invariant law* pi_r. The coefficient equals one at r=0, is positive at every finite r, and degenerates as |r| grows. The proof reuses the exact product Gibbs normalization and the actual Markov kernel; it does not postulate a four-dimensional gauge measure.

This is the precise bridge needed to reuse the previously verified residual-kernel/relative-entropy reasoning from the Cauchy Poisson library. That reasoning has not yet been transferred: a positive residual SU(2) kernel, its invariant-law split, and a strict multistep entropy or correlation inequality remain open here. Even a fixed-r rate would not be a physical mass gap without a scale- and volume-uniform relation to the four-dimensional continuum theory. The large-coupling mean-response obstruction of checkpoint 1657 rules out blindly promoting this finite-r estimate to a universal contraction factor. The motivating block-contraction manuscript `ResearchSources/Incoming/block_contraction_spectral_gaps.tex` remains read-only with SHA-256 `0C40FA6B92B830C0E2309BD6471D55CB0EB9BFB94296B9267AD23A5280FA4C60`.

### Verification, checkpoint 1659

The targeted module build passed 4118 jobs and the complete root build passed 6907 jobs. The complete transitive axiom audit checked 52452 Foundation declarations and found only `propext`, `Classical.choice`, and `Quot.sound`. All four new public theorem types and complete source proofs, including both private measurability/boundedness lemmas, were reviewed. Three independent Lean examples passed for the zero-coupling and unit-coupling measure bounds and the coefficient's positive-at-finite-r, at-most-one range. Source integrity passed for 2727 Foundation/root Lean files, all three pinned configurations, 113 baseline manuscripts and 21 selected Yang--Mills originals. No source manuscript was changed, and no mass-gap or entropy-decay conclusion is claimed.

## Residual SU(2) loop dynamics and geometric entropy — checkpoint 1660

`Foundation/SU2ResidualEntropy.lean` turns checkpoint1659's invariant-reference minorization into an actual stochastic decomposition. For every finite real coupling r, set epsilon_r=exp(-4|r|)/2, so 0<epsilon_r<1. The residual density is `(K_r(C,D)-epsilon_r*pi_r(D))/(1-epsilon_r)` relative to Haar. Lean verifies joint measurability, pointwise nonnegativity, integrability, unit mass for every C, and hence an actual Markov residual kernel R_r. It proves the exact statewise and forward-law splits `K_r(C,.)=epsilon_r*pi_r+(1-epsilon_r)*R_r(C,.)` and `K_r rho=epsilon_r*pi_r+(1-epsilon_r)*R_r rho`. The residual kernel itself preserves pi_r. This is a genuine positive stochastic construction, not formal subtraction of signed measures.

The proof then reuses the separately verified generic KL mixture bound from `Foundation/CauchyPoissonMixtureEntropy.lean` and KL data processing. For every initial probability law rho, the actual SU(2) transition satisfies `KL(K_r rho || pi_r) <= (1-epsilon_r) KL(rho || pi_r)`. The recursively defined n-step law is proved to be a probability measure and satisfies `KL(K_r^n rho || pi_r) <= (1-epsilon_r)^n KL(rho || pi_r)`. Because 0<epsilon_r<1, this is strict geometric entropy control whenever the initial KL is finite; for infinite initial KL the displayed inequality is valid but can be vacuous. No finite-entropy theorem for every point mass, Pinsker-based correlation estimate, or physical-distance clustering theorem is claimed. The rate deteriorates as |r| grows, and no scale/volume-uniform four-dimensional Yang--Mills estimate follows. The block-contraction manuscript `ResearchSources/Incoming/block_contraction_spectral_gaps.tex` remains read-only at SHA-256 `0C40FA6B92B830C0E2309BD6471D55CB0EB9BFB94296B9267AD23A5280FA4C60`.

### Verification, checkpoint 1660

The targeted module build passed 4241 jobs and the complete root build passed 6908 jobs. The complete transitive axiom audit checked 52492 Foundation declarations and admitted only `propext`, `Classical.choice`, and `Quot.sound`. All 22 public definition/theorem types and 18 full theorem proofs were reviewed, including the residual kernel's normalization, invariant split and iteration hypotheses. Three independent Lean checks passed: residual density is exactly one at zero coupling, the residual section at unit coupling is an actual probability measure, and the explicit two-step KL bound elaborates for any initial probability law. Source integrity passed for 2728 Foundation/root Lean files, three pinned configurations, 113 baseline manuscripts and 21 selected Yang--Mills originals; no original manuscript was modified. No `sorry`, new axiom, continuum construction or physical mass-gap claim was introduced.

## Positive-time entropy regularization for the stationary SU(2) loop transfer — checkpoint 1661

`Foundation/SU2PointEntropy.lean` closes the infinite-initial-entropy loophole in checkpoint 1660 for this **actual fixed-coupling Markov kernel**. For each finite real coupling r, the global partition is at most exp(|r|), the local partition at least exp(-|r|), and the stationary Haar density at least exp(-2|r|). The transition Haar density is at most exp(2|r|), hence the point transition satisfies `K_r(C,·) ≤ exp(4|r|) pi_r` for every state C. Integrating the uniform bound gives the same domination for `K_r rho` for **every** initial probability law rho, even if its initial relative entropy is infinite. Reuse of the verified generic domination-to-finite-KL theorem proves `KL(K_r rho || pi_r) < ∞` and, in particular, finite KL after one step from every point mass.

The exact iterate-shift identity and checkpoint 1660's proved residual-kernel contraction then yield `KL(K_r^(n+1) rho || pi_r) ≤ (1-epsilon_r)^n KL(K_r rho || pi_r)`, where `epsilon_r=exp(-4|r|)/2`. Lean proves every positive-time entropy is finite and that these entropies converge to zero in `ENNReal` for every starting probability law. This is a genuine nonvacuous convergence statement for the specified one-loop transfer; no finite-KL assumption on rho is needed. The use of the Cauchy Poisson domination lemma is theorem reuse, not a new general entropy principle or claim of novelty.

The estimate is at fixed r and counts Markov steps, not physical Euclidean separation. Its constants deteriorate as |r| grows. It supplies no uniform continuum/infinite-volume limit, no four-dimensional gauge-invariant field construction, no spectral measure of a continuum Hamiltonian, and no positive physical Yang–Mills mass gap. The original `ResearchSources/Incoming/block_contraction_spectral_gaps.tex` remains read-only at SHA-256 `0C40FA6B92B830C0E2309BD6471D55CB0EB9BFB94296B9267AD23A5280FA4C60`.

### Verification, checkpoint 1661

The targeted module build passed and the complete root build passed 6909 jobs. The complete transitive axiom audit checked 52508 Foundation declarations and found only `propext`, `Classical.choice`, and `Quot.sound`. All 16 new public theorem types and their complete proofs were reviewed. Three independent Lean examples passed at nonzero couplings, including a concrete point transition, a three-step point law and convergence for arbitrary initial probability laws. Source integrity passed for 2729 Foundation/root Lean files, three pinned configurations, 113 baseline manuscripts and 21 selected Yang–Mills originals. No source manuscript was changed; no `sorry`, `admit`, new axiom or mass-gap claim was introduced.

## Heat-reference block factor cannot be coupling-uniform — checkpoint 1662

The strict-block-contraction section of `ResearchSources/Incoming/block_contraction_spectral_gaps.tex` (SHA-256 `0C40FA6B92B830C0E2309BD6471D55CB0EB9BFB94296B9267AD23A5280FA4C60`, lines 318–385) defines the reference heat time `t_eff=(n_p beta c_2)^(-1)` and factor `q_0=exp(-lambda_1 t_eff)` at lines 329–337. It then writes `q=q_0+epsilon_T+eta` at lines 367–380, with nonnegative error terms. `Foundation/YMBlockRateDegeneration.lean` tests this exact quantitative route: for positive `A=n_p c_2` and `ell=lambda_1`, `q_0(beta)=exp(-ell/(A beta))` lies below one at each positive finite beta but tends to **one** as beta tends to infinity. Lean proves there is no constant `q<1` above all these reference factors; the conclusion remains true after adding **any nonnegative** beta-dependent perturbation terms. An independent test exhibits positive beta at which the concrete factor with `A=6`, `ell=5` exceeds `9/10`, and verifies the obstruction even with a positive explicit perturbation.

Thus the displayed heat-reference/triangle-inequality route does not supply a contraction factor uniformly bounded below one over arbitrarily large beta. The manuscript's pointwise `q(beta)<1` assertion can still hold if the errors are small enough at each beta. The theorem does **not** say the actual block transfer has no other uniform estimate, nor that a physical mass gap is impossible. A four-dimensional argument must establish the needed uniform physical-distance scale after tracking beta, block size, lattice spacing, operator normalization and error terms; a fixed-beta strict factor alone is insufficient. The original manuscript remains unchanged.

### Verification, checkpoint 1662

The targeted module build passed 1946 jobs and the complete root build passed 6910 jobs. The transitive axiom audit checked 52521 Foundation declarations, with only `propext`, `Classical.choice` and `Quot.sound`. The definition, all five public theorem types and complete proofs were reviewed. Three independent Lean examples passed, covering finite-coupling strictness, a concrete proposed `q=0.9` failure and an explicit positive error term. Source integrity passed for 2730 Foundation/root Lean files, three pinned configurations, 113 baseline manuscripts and 21 selected Yang–Mills originals. No original manuscript was modified, and no new axiom, placeholder or four-dimensional mass-gap claim was introduced.

## Exact macro-step scaling of the heat-reference factor — checkpoint 1663

Checkpoint 1662 shows that the manuscript's individual heat-reference factor `q_0(beta)=exp(-ell/(A beta))` tends to one as `beta→∞`, so its displayed formula cannot furnish a beta-uniform **one-step** factor below one. The complementary physical-scale question is the number of steps. `Foundation/YMBlockRateDegeneration.lean` now proves, exactly, that for every positive integer `n` and nonzero `A`, `q_0(n)^n=exp(-ell/A)` and `q_0(n)^(n k)=exp(-k ell/A)`. For `A,ell>0`, the latter decays to zero as integer macro-distance `k→∞`, **uniformly under any choice of positive integer micro-scale n(k)**. Thus degeneration of the individual reference factor is compatible with a nondegenerate rescaled heat-semigroup decay when the step count grows proportionally to beta. This is a corrected interpretation of the reference formula, not a result about the manuscript's actual block transfer.

The necessary next connection is absent: the manuscript does not prove that its physical separation corresponds to `n k` transfer iterations when `beta=n`, nor that its perturbation errors preserve the macro-step estimate, nor that the actual transfer is represented by the reference heat semigroup with scale/volume-uniform control. A different beta-to-lattice-spacing relation would change the conclusion. The exact theorem therefore neither proves nor disproves a four-dimensional Yang–Mills mass gap. The motivating `ResearchSources/Incoming/block_contraction_spectral_gaps.tex` remains read-only with SHA-256 `0C40FA6B92B830C0E2309BD6471D55CB0EB9BFB94296B9267AD23A5280FA4C60`.

### Verification, checkpoint 1663

The targeted module build passed 1946 jobs and the full root build passed 6910 jobs. The complete transitive axiom audit checked 52532 Foundation declarations and admitted only `propext`, `Classical.choice` and `Quot.sound`. All three new public theorem types and full proofs were reviewed. Independent Lean checks passed for six micro-steps at coupling two and a micro-scale varying as `k+1`. Source integrity passed for 2730 Foundation/root Lean files, three pinned configurations, 113 baseline manuscripts and 21 selected Yang–Mills originals. No source manuscript was modified and no new axiom or placeholder was introduced.

## Necessary perturbation budget for the proposed block contraction — checkpoint 1664

The manuscript `ResearchSources/Incoming/block_contraction_spectral_gaps.tex` (SHA-256 `0C40FA6B92B830C0E2309BD6471D55CB0EB9BFB94296B9267AD23A5280FA4C60`, lines 329–385) sets `q_0(beta)=exp(-ell/(A beta))` with `A=n_p c_2>0`, `ell=lambda_1>0`, and proposes `q=q_0+epsilon_T+eta`, where `eta=C_DV/sqrt(kappa_int)`. The previously verified limit `q_0→1` leaves a shrinking perturbation budget. `Foundation/YMBlockErrorBudget.lean` now proves the pointwise tangent estimate `1-q_0(beta) ≤ ell/(A beta)` and its exact necessary consequence: whenever `beta>0` and `q_0(beta)+e_1+e_2<1`, one must have `beta(e_1+e_2)<ell/A`. No positivity of the two error terms is needed for this implication. The exact allowed deficit remains `1-q_0`; the inverse-beta expression is a necessary upper budget, not a sufficient condition for strictness.

The same module formalizes the two-channel lower-envelope transfer and proves a concrete scale obstruction: for every `A>0`, real `ell`, and fixed `c>0`, the factor `q_0(beta)+c/sqrt(beta)` is at least one for **all sufficiently large** positive `beta`. An independent Lean test confirms failure already at `A=6`, `ell=5`, `beta=100`, `c=1`. Applied to the manuscript, this rules out its displayed strict-factor formula **if** its combined nonnegative perturbation has a fixed positive lower envelope `c/sqrt(beta)`. The manuscript's stated `kappa_int ≳ beta` and formula for `eta` do not by themselves establish that lower envelope, nor do they prove the stronger `O(1/beta)` upper control required to fit the necessary budget. The behavior of `C_DV`, `kappa_int`, and `epsilon_T` along the proposed scaling trajectory is an explicit unresolved obligation.

This is a theorem about the manuscript's numerical contraction formula, not the actual four-dimensional block transfer or its physical-distance scaling. The exact macro-step reference identity from checkpoint 1663 remains compatible with physical decay if the transfer and error accumulation are separately controlled. No continuum Yang–Mills mass gap is inferred. The original manuscript was not changed.

### Verification, checkpoint 1664

The targeted module build passed 1947 jobs and the complete root build passed 6911 jobs. The complete transitive axiom audit checked 52543 Foundation declarations and found only `propext`, `Classical.choice` and `Quot.sound`. All four new public theorem types and full proofs were reviewed. Three independent Lean checks passed for the explicit `beta=100` failure, eventual obstruction with arbitrary fixed `c>0`, and a split two-channel square-root envelope. Source integrity passed for 2731 Foundation/root Lean files, three pinned configurations, 113 baseline manuscripts and 21 selected Yang–Mills originals. No manuscript change, new axiom, placeholder or mass-gap assertion was introduced.

## Actual stationary SU(2) loop event mixing — checkpoint 1665

`Foundation/SU2EventMixing.lean` turns the positive residual kernel of checkpoints 1659–1660 into an exact **multistep law decomposition** for the actual gauge-covariant closed-loop Markov transfer. For each fixed real coupling `r`, let `epsilon_r=exp(-4|r|)/2`, `c_r=1-epsilon_r`, and let `R_r^n rho` be the genuine residual-kernel iterate from any initial probability law `rho`. Lean proves every residual iterate is a probability measure and constructs a stationary weight `a_n` with `a_n+c_r^n=1`. The exact measure identity is `K_r^n rho = a_n pi_r + c_r^n R_r^n rho`. No signed subtraction or assumed probability law enters the decomposition.

For every set `B` (hence every measurable event), the verified identity yields the two-sided quantitative bounds `K_r^n rho(B) ≤ pi_r(B)+c_r^n` and `pi_r(B) ≤ K_r^n rho(B)+c_r^n`. Lean also proves `K_r^n rho(B)→pi_r(B)` in `ENNReal` for every initial probability law and every `B`; the convergence uses `0<c_r<1` and the probability mass bounds on the residual iterate. Point starts and singular initial laws are included. This is a genuine setwise mixing theorem for the specified stationary finite-coupling stochastic model and complements checkpoint 1661's KL convergence without invoking an unproved Pinsker inequality.

The manuscript `ResearchSources/Incoming/block_contraction_spectral_gaps.tex` (SHA-256 `0C40FA6B92B830C0E2309BD6471D55CB0EB9BFB94296B9267AD23A5280FA4C60`, lines 320–346) leaves the boundary update variable `X'` in its proposed `Tf(x)=E_{nu_x}[f(X')]` unspecified. Its interior conditional law and Schur bound alone therefore do not identify the transfer kernel, the claimed heat reference, or the required `H^1` perturbation estimate. The present theorem applies to the **explicitly constructed SU(2) loop kernel**, not to that undetermined four-dimensional block operator. Its rate `c_r` deteriorates at strong coupling, and the index `n` counts loop Markov steps rather than physical separation. No scale/volume-uniform continuum clustering or Yang–Mills mass gap follows. Original manuscripts remain unchanged.

### Verification, checkpoint 1665

The targeted module build passed 4244 jobs and the complete root build passed 6912 jobs. The complete transitive axiom audit checked 52571 Foundation declarations and found only `propext`, `Classical.choice`, and `Quot.sound`. All four new public definitions, eight public theorem types, and complete proof bodies were reviewed, including exact measure equality, probability instances and ENNReal convergence hypotheses. Three independent Lean examples passed: three-step mixing from a Dirac state at positive coupling, four-step reverse bound at negative coupling, and setwise convergence from arbitrary initial probability laws. Source integrity passed for 2732 Foundation/root Lean files, three pinned configurations, 113 baseline manuscripts and 21 selected Yang–Mills originals. The cited source hash was rechecked directly. No source manuscript, new axiom, placeholder or physical mass-gap claim was introduced.

## Stationary SU(2) two-time event correlations — checkpoint 1666

`Foundation/SU2LagEventCorrelation.lean` constructs the genuine n-step Markov kernel of the explicit gauge-covariant closed-loop transfer and its stationary two-time joint law `J_{r,n}=pi_r ⊗ K_r^n`. Lean proves the kernel is Markov, identifies each point-started law with the previously verified iterate, proves stationarity, and proves **both** marginals of `J_{r,n}` equal `pi_r`. For measurable events A and B, the joint rectangle probability obeys the quantitative two-sided estimates `J_{r,n}(A×B) ≤ pi_r(A)pi_r(B)+pi_r(A)c_r^n` and `pi_r(A)pi_r(B) ≤ J_{r,n}(A×B)+pi_r(A)c_r^n`, where `c_r=1-exp(-4|r|)/2<1`. It follows in `ENNReal` that `J_{r,n}(A×B)→pi_r(A)pi_r(B)` for every fixed real coupling r. This is an actual stationary **two-time event correlation** theorem for the explicitly defined SU(2) chain, beyond the preceding one-time convergence theorem; it does not require a signed probability substitute.

This result does not establish four-dimensional physical-distance clustering. The lag n counts applications of the constructed loop kernel, and no proved identification makes it a spatial block separation in the continuum Yang–Mills theory. The strong-coupling rate approaches one. The proposed block transfer in `ResearchSources/Incoming/block_contraction_spectral_gaps.tex` (SHA-256 `0C40FA6B92B830C0E2309BD6471D55CB0EB9BFB94296B9267AD23A5280FA4C60`, lines 320–346) still leaves its boundary update X' unspecified; neither its continuum law nor scale/volume-uniform error control follows from this theorem. Next meaningful obligations are an explicit gauge-invariant physical transfer, its distance correspondence, and bounds uniform along the continuum and infinite-volume limits. No mass-gap conclusion is made.

### Verification, checkpoint 1666

Targeted build: 4245 jobs, success. Full root build: 6913 jobs, success. Complete transitive axiom audit: 52589 Foundation declarations, only `propext`, `Classical.choice`, `Quot.sound`. Both new public definitions, all eight new public theorem types and full proof bodies were reviewed. Four independent Lean checks passed for positive/negative/zero couplings, event bounds, limiting independence and the second stationary marginal. Source integrity passed for 2733 Foundation/root Lean files, three pinned configurations, 113 baseline manuscripts and 21 Yang–Mills originals; the cited source hash was independently rechecked. No source manuscript was modified, and the new module contains no sorry, admit or axiom declaration.

## Strong-coupling saturation of actual stationary SU(2) covariance — checkpoint 1667

`Foundation/SU2StrongCouplingCovariance.lean` identifies the one-step stationary joint law from checkpoint 1666 **exactly** with the previously verified two-loop Gibbs law: `J_{r,1}=coupledLaw(r)`. Its connected half-trace covariance therefore equals the earlier Gibbs response `corr(r)`, has derivative `1/16` at zero, and is positive at arbitrarily small positive coupling. This is a theorem about the actual stationary Markov transfer, not a merely formal Gibbs analogy.

The new strong-coupling argument proves more. For the gauge-invariant interaction `X(C,D)=halfTrace(C) halfTrace(D)`, product Haar measure gives positive mass to every open cap `X>1-delta/2` near `(1,1)`. Lean proves a partition lower bound and an exponential tail bound for `X≤1-delta` under the actual tilted coupled law. An expectation-defect estimate then proves `E_{coupledLaw(r)}[X]→1` as `r→+∞`. Simultaneous multiplication of both loops by the central element `-1` preserves product Haar measure and X but reverses each individual half-trace. The two individual stationary means are therefore exactly zero at every coupling. Consequently the **connected stationary one-step covariance tends to one**. In particular, for every real `q<1`, some nonnegative coupling r has stationary lag-one covariance greater than q. This proves that deterioration of a coupling-uniform covariance contraction for this explicit chain is intrinsic to its Gibbs law, not solely an artifact of the prior Doeblin minorization coefficient. It is stronger than the earlier point-started mean-separation obstruction because it concerns the actual stationary joint law.

This does not prove any absence or presence of a four-dimensional physical Yang–Mills mass gap. The chain is a finite compact-group surrogate, its one-step index has no proved identification with Euclidean distance or physical time, and no uniform continuum/infinite-volume construction or spectral representation is established here. The proposed block transfer in `ResearchSources/Incoming/block_contraction_spectral_gaps.tex` (SHA-256 `0C40FA6B92B830C0E2309BD6471D55CB0EB9BFB94296B9267AD23A5280FA4C60`, especially lines 320–385) still lacks an explicit boundary update and scale-uniform perturbation control. Any transfer of this obstruction or a positive contraction estimate to that setting requires independent hypotheses. The source manuscript remains unchanged.

### Verification, checkpoint 1667

Targeted build passed 4246 jobs; complete root build passed 6914 jobs. The complete transitive axiom audit checked 52602 Foundation declarations and admitted only `propext`, `Classical.choice` and `Quot.sound`. The public definition, all eleven public theorem types and complete source proofs, including the private concentration and center-symmetry lemmas, were reviewed. Five independent Lean tests passed for the exact stationary law, the weak-coupling derivative, strong-coupling limit, explicit `q=9/10` obstruction and zero individual mean. Source integrity passed for 2734 Foundation/root Lean files, three pinned configurations, 113 baseline manuscripts and 21 Yang–Mills originals; the cited manuscript hash was rechecked. No manuscript edit, new axiom, placeholder, continuum construction or mass-gap claim was introduced.

## Stationary spectral obstruction, coupling iteration, and the physical-transfer bottleneck — checkpoint 1668

The completed covariance audit now supports a genuine variational statement for the **actual stationary loop operator**, rather than merely a formal covariance analogy. `Foundation/SU2VariationalGap.lean` constructs the bounded operator P_r on the full real L2(pi_r) space from the two marginal pullback isometries into L2(coupledLaw(r)): P_r=L_r^* R_r, reusing `HilbertRepresentation.predictableAdjoint`. `operator_kernel_pairing` identifies every L2 pairing with integration against the previously constructed Markov kernel. Exchangeability proves `operator_selfadjoint`, and the existing orthogonal decomposition proves `operator_contraction`. The half-trace is centered, its variance tends to one, and its actual Dirichlet energy tends to zero. `no_uniform_L2_gap` therefore refutes any positive coupling-independent Poincare/spectral-gap lower bound for this operator. No assumption of an eigenfunction, spectral completeness, or continuum field was introduced.

The strongest new test is the discontinuous but measurable **sign of the closed-loop half-trace**, defined to be zero when the half-trace vanishes. `Foundation/SU2SignBottleneck.lean` proves its conjugation invariance, exact stationary centering, L2 membership, variance convergence to one, and the exact identity

    <f_r,f_r> - <P_r f_r,f_r> = (1/2) E[(sign(halfTrace C)-sign(halfTrace D))^2].

Changing sign forces X(C,D)=halfTrace(C)halfTrace(D) into X<=0. The established Gibbs cap bound gives probability at most C exp(-r/2), with C positive and independent of nonnegative r. `dirichlet_exponential_bound` and `exponential_variational_obstruction` prove that the sign test's actual Rayleigh quotient is at most C' exp(-r/2) for all sufficiently large r. This is an exponential upper obstruction to a uniform gap, substantially stronger than merely showing the half-trace quotient tends to zero. The formal result does not assert an optimal exponent, an isolated eigenvalue, or exact unit sign variance at finite r. The bottleneck/Dirichlet principle is classical; this checkpoint claims a verified application to the specified Gibbs kernel, not a novel general spectral theorem.

Independent semicircle Gauss-Chebyshev quadrature with 128, 256 and 512 nodes was used to challenge the candidate before formalization. At r=40 it gives sign Rayleigh quotient approximately 3.03422e-14 versus half-trace quotient approximately 0.0010417. These are diagnostic numbers, not interval-certified asymptotics or proof inputs. The formal proof uses only the cap estimate and exact symmetries. The script and results are retained in the checkpoint's temporary verification evidence.

### Proved iteration and conditional distance interpretation

`Foundation/SU2CouplingIteration.lean` proves c_r^n <= exp(-n epsilon_r), with epsilon_r=exp(-4|r|)/2 and c_r=1-epsilon_r. The actual stationary joint-event error is bounded in both directions by pi_r(A) exp(-t) whenever n epsilon_r>=t; n>=2t exp(4|r|) is sufficient. This recovers genuine finite-coupling event contraction over coupling-dependent iteration counts. It neither contradicts the exponential variational obstruction nor proves a sharp mixing time; the minorization bound may be very conservative.

`physical_distance_event_bound` states the precise conditional bridge: if m*a<=epsilon_r, then the same event estimate has exponent -m*n*a. A physical application requires a>0, m>0, an independently justified relation between r and lattice spacing a, and proof that this operator step actually represents that separation. None of these physical identifications is silently supplied by renaming n*a a distance. In particular, large positive surrogate r is not identified with large bare Yang-Mills coupling g; Wilson inverse-temperature conventions and the continuum trajectory require separate audit.

### Failed automatic bridge to the four-dimensional physical transfer

The original `ResearchSources/Incoming/block_contraction_spectral_gaps.tex`, SHA-256 `0C40FA6B92B830C0E2309BD6471D55CB0EB9BFB94296B9267AD23A5280FA4C60`, lines 320-385, still leaves its boundary update X' and perturbation estimates unspecified. The finite loop interaction r*halfTrace(C)*halfTrace(D) has not been identified with the four-dimensional Wilson transfer kernel.

The primary-source comparison is M. Luscher, *Construction of a selfadjoint, strictly positive transfer matrix for Euclidean lattice gauge theories*, DESY 76/54, Commun. Math. Phys. 54 (1977), 283-292: https://bib-pubdb1.desy.de/record/396349/files/7611148.pdf?version=1 . Its introduction identifies T=exp(-aH); the transfer construction and Proposition 1 use temporal coupling and spatial factors, together with gauge invariance. These facts justify investigating the physical transfer itself; they do not identify it with the present row-normalized loop chain or establish a uniform continuum mass gap. No external existence claim was imported as an axiom.

`Foundation/YMRowNormalizationObstruction.lean` supplies a concrete falsification of the automatic normalization step. For the positive symmetric matrix W=[[2,1],[1,1]], row normalization gives diagonal entries 2/3 and 1/2. If this were the positive h-transform W_ij*h_j/(lambda*h_i) of the SAME W, its two diagonal equations would force lambda=3 and lambda=2. `unequal_rows_not_doob` verifies the contradiction. An additional exact rational Python check gives trace(P)^2/det(P)=49/6 but trace(W)^2/det(W)=9, ruling out scalar-rescaling similarity in this example. The latter invariant computation is an independent exact check, not a Lean matrix theorem. This example refutes a general automatic bridge; it does not by itself prove that this particular SU2 kernel cannot have any physical realization.

A promising next route is therefore narrowly specified: identify the actual finite-volume gauge-invariant transfer and its positive ground-state normalization, then compare its centered Dirichlet form to the relevant physical excitation sector. Constant-row convolution cases may admit a direct normalization, but spatial Wilson factors require their own proof. Any useful four-dimensional estimate must survive increasing volume and a justified continuum scaling, with a physical separation identified. The center-sign bottleneck must also be checked in the correct geometry and observable sector, rather than transferred from the two-loop surrogate by analogy. These remain OPEN. Neither a positive physical Yang-Mills mass gap nor its impossibility is established. Bakry remains paused and the focused Yang-Mills campaign remains active.

### Verification, checkpoint 1668

The sign-bottleneck target passed 4248 jobs; the complete root build passed 6918 jobs in 29.588 seconds. The complete transitive audit passed 52672 Foundation declarations in 37.026 seconds, admitting only propext, Classical.choice and Quot.sound. All 55 public types (40 theorems and 15 definitions/abbreviations) and complete proof bodies, including private measurable/integrable bounds, were reviewed. Eight independent Lean tests passed for selfadjointness, contraction, a 1/1000 gap obstruction, sign-energy nonnegativity, conjugation invariance, phase edge cases, two-step mixing at zero coupling, and the normalization contradiction. Independent numerical resolution checks and exact rational arithmetic also passed; numerical diagnostics are explicitly not formal evidence. The first audit run rejected an unsupported pretty-printer option; it was removed and the entire audit was rerun successfully, with no mathematical change or weakened check.

Source integrity passed for 2738 Foundation/root Lean files, with exactly the seven intended source additions/changes since approved checkpoint1667; three pinned configurations, 113 baseline manuscripts and 21 Yang-Mills originals are unchanged. No sorry, admit, new axiom, manuscript modification, toolchain change, or publication/novelty assertion was introduced. Exact source manifest, full-build log, complete audit/type log, independent Lean tests, and numerical diagnostics are retained under C:/Users/ramir/AppData/Local/Temp/stardust-ym-1668-*. The exact Git approval and remote synchronization receipt are recorded separately by the guarded backup procedure; this pre-commit ledger entry does not assert remote success before verification.

## Wilson temporal sign crossing and endpoint gauge obstruction — checkpoint 1669

The next test of checkpoint1668's exponential sign bottleneck found a decisive failure of its automatic transfer to the Wilson temporal interaction. `Foundation/SU2WilsonSignCrossing.lean` constructs actual unit quaternions q+=(a,b,0,0) and q-=(-a,b,0,0), a^2+b^2=1, through the existing faithful SU(2) homomorphism. Their half-traces are a and -a, but the half-trace of C D^{-1} is 1-2a^2. Consequently the temporal Wilson action A(C,D)=1-halfTrace(C D^{-1}) is exactly 2a^2. This distinguishes the group-relative Wilson interaction from the surrogate product halfTrace(C)*halfTrace(D).

`arbitrarily_small_crossing` proves that for every epsilon>0 there are genuine SU(2) states with strictly opposite trace signs and 0<=A<epsilon. `relative_trace_can_exceed` gives relative half-trace greater than any prescribed q<1. `no_positive_crossing_barrier` refutes a positive pointwise lower action barrier on that sign-crossing set. `crossing_weight_near_max` proves that for every fixed beta>=0 and eta>0, such a crossing can have exp(-beta*A)>exp(-eta). Therefore the pointwise exponential penalty used for the product-interaction surrogate cannot simply be assigned to Wilson sign crossings. These theorems do NOT imply a lower bound on their probability under a ground-state or Gibbs measure.

The endpoint gauge audit strengthens the limitation. `action_endpointGauge` proves A(g C h^{-1},g D h^{-1})=A(C,D) for arbitrary common endpoint transformations. `openLink_sign_cut_not_gauge_invariant` constructs a pair with opposite bare-link trace signs whose common left gauge transform makes BOTH signs positive while preserving A. Thus conjugation invariance of a half-trace does not make the trace of a bare link gauge invariant under its two independent endpoints. The earlier loop-state sign theorem remains correct for closed holonomies, which transform by conjugation; it does not define a physical observable on arbitrary open lattice links.

`flatSlice_plaquette` also checks the local spatial algebra for homogeneous commuting assignments (C,1,1): every spatial commutator plaquette is identity. `flatSlice_temporal_sum` identifies the sum of the three temporal actions between (C,1,1) and (D,1,1) with A(C,D). These are actual group identities. They are not a constructed four-dimensional probability measure, a proof about a chosen noncontractible loop at general lattice size, or a claim that global holonomy modes coincide with local physical excitations. On a multi-site lattice the individual link traces in this description are gauge dependent. Closed-loop or gauge-quotient observables and boundary conditions must be specified before using it spectrally.

### Manuscript and primary-source comparison

`ResearchSources/Incoming/block_contraction_spectral_gaps.tex` remains byte-identical, SHA-256 `0C40FA6B92B830C0E2309BD6471D55CB0EB9BFB94296B9267AD23A5280FA4C60`. Its lines160-161 explicitly restrict coordinates to a small-field corridor; lines610-619 use exponential coordinates near identity. The crossing family here approaches half-trace zero and need not belong to that chart. It refutes an UNQUALIFIED global sign-barrier extension, not a correctly restricted local estimate. Conversely a sufficiently small neighborhood of identity contains no opposite half-trace signs, so this sign test cannot itself establish a nontrivial bottleneck inside that neighborhood. The manuscript still needs its large-field/patching and continuum-uniform obligations; those are not discharged by the present counterexample.

Luscher's *Construction of a selfadjoint, strictly positive transfer matrix for Euclidean lattice gauge theories*, DESY76/54, printed p8, equations(20)-(21), separates spatial plaquette weights from a temporal factor depending on relative link matrices. This supports testing the relative interaction rather than replacing it by a product of traces. Source: https://bib-pubdb1.desy.de/record/396349/files/7611148.pdf?version=1 . No positivity or existence assertion from that source is adopted as a Lean axiom. The quaternion construction and gauge counterexample are exact algebraic applications, with no novelty claim.

### Consequences and next mathematical bottleneck

PROVED: the surrogate's stationary spectral obstruction persists as checkpoint1668 states, but its particular pointwise sign-penalty mechanism does not automatically extend to the Wilson temporal factor. FAILED: using opposite bare-link trace signs as an endpoint-gauge-invariant physical bottleneck, or claiming a uniform positive temporal action cost solely from those signs. OPEN: whether a suitable CLOSED-LOOP sign sector has small conductance under the correctly normalized physical transfer. Spatial factors and the ground-state measure may suppress the near-zero-action crossing configurations; pointwise examples alone neither prove nor refute that measure-level claim.

The strongest next constructive comparison is the actual central Wilson convolution factor and its action on a gauge-invariant closed-loop observable, followed by an explicit audit of the spatial multiplier and physical scale. Existing candidates for reuse are `SU2ClosedLoopTransfer.closedLoop_law`, the quaternion multiplication identities, Haar/gauge invariance, the verified tilted half-trace moments, and the stationary Hilbert-space transfer construction. A character/closed-word eigenmode may provide a physically better reference rate than the exponentially small surrogate minorization, but no such new eigenmode or uniform perturbation estimate is claimed in this checkpoint. Ground-state normalization, gauge projection, volume dependence and continuum scaling remain separate obligations. No mass-gap conclusion or campaign transition is made.

### Verification, checkpoint 1669

The final target passed 4249 jobs. The final complete root build passed 6919 jobs in 25.204 seconds; the complete transitive axiom audit passed 52712 declarations in 38.486 seconds, admitting only propext, Classical.choice and Quot.sound. All 18 public types (13 theorems and five definitions) and full proofs were reviewed. Eight independent Lean checks passed: a rational negative-product/positive-relative-trace counterexample, action below 1/1000000, near-maximal weight at beta=1000000, spatial flatness, exact temporal sum, conjugation invariance, full endpoint gauge invariance and the gauge-dependent sign cut. Four exact rational Python quaternion checks also passed; no numerical approximation enters the proof.

Source integrity passed for 2739 Foundation/root Lean files, with exactly the three intended source changes/additions since approved1668; three configurations, 113 baseline manuscripts and 21 Yang-Mills originals remain unchanged. No new axiom, sorry, admit, changed toolchain or original manuscript modification was introduced. Final source manifest, full-build/axiom/type logs, independent Lean tests and exact-rational evidence are retained under C:/Users/ramir/AppData/Local/Temp/stardust-ym-1669-*. Git approval and remote verification are separate exact-commit receipts; this pre-commit record does not prematurely assert remote backup success. The focused Yang-Mills campaign remains active.

## Exact Wilson convolution and a gauge-invariant closed-loop mode — checkpoint 1670

Following the sign and endpoint-gauge obstructions, `Foundation/SU2WilsonConvolution.lean` now gives a constructive reference calculation for the actual central Wilson increment law nu_beta(dV)=Z_beta^{-1} exp(beta*halfTrace(V)) dHaar(V). The measure is reused from the existing verified exponential tilt and is a genuine probability law for every real beta. Its inversion invariance is proved, including the required noncommutative Haar argument: right translation and inverse-image measures are identified by probability-Haar uniqueness. No abelian-group inversion assumption is imposed on SU(2).

The exact quaternion identity

    halfTrace(CD) + halfTrace(CD^{-1}) = 2 halfTrace(C) halfTrace(D)

and inversion symmetry prove `halfTrace_eigen`: integration of halfTrace(CV) against nu_beta equals c(beta)*halfTrace(C), where c(beta)=E_nu_beta[halfTrace(V)]. `step_actual_kernel` identifies this convolution step with the already constructed SU2 one-word kernel at inverse boundary C^{-1}; it is not a postulated operator or a change to the earlier product-interaction kernel. The one-word exponent and cyclic/inverse trace identities give the relative-link Wilson factor. The kernel identification is stated for measurable test functions; the trace calculations separately prove integrability.

`wordAverage` is an explicit nested integral over a fresh independent Wilson increment at each oriented edge occurrence. `wordAverage_exact` proves, for every finite list of oriented SU2 edge states and every prefix C,

    wordAverage(beta, edges, C) = c(beta)^(length edges) * halfTrace(C * product(edges)).

`wordAverage_layer_integrable` proves integrability of every integration layer, so no formula depends on the default value of a nonintegrable Bochner integral. The finite-word construction does NOT identify noise at repeated occurrences of the same physical edge. Its immediate lattice application is to distinct independently updated oriented edges, with reversed physical edges represented in the appropriate orientation; words with shared edge variables require another proof.

For a four-edge cycle, `loop4_gauge` proves invariance under independent gauge transformations at all four vertices, with the endpoints telescoping to conjugation of the closed holonomy. `loop4_average` then gives the exact averaging factor c(beta)^4. This is a gauge-invariant loop observable, unlike the bare-link sign cut refuted in checkpoint1669. `coefficient_zero` verifies the complete zero-coupling reset of a nonempty independent word. Reusing the proved large-positive-tilt limit yields c(beta)->1 and `fixed_word_factor_tendsto_one`; `no_uniform_fixed_word_factor` refutes a coupling-independent q<1 bound on this fixed-length averaging factor. These are exact pointwise averaging identities, not a newly established full physical-transfer spectral theorem.

### Independent challenges and source comparison

An exact Fraction-arithmetic test averaged a noncommuting four-edge quaternion loop over all1296 combinations of six inversion-symmetric unit-quaternion increments. Its nonzero base loop half-trace is113/625, and its average is9153/390625, exactly (3/5)^4 times the base value. This finite symmetric law is NOT the continuous Wilson law; it independently checks the noncommutative multiplication and four-edge factorization mechanism. Separate128/256/512-node semicircle quadratures at beta=-4,0,1,4,20,100 agree on c(beta) to the tested tolerance. They are numerical diagnostics, not certified asymptotics or inputs to the Lean proof.

This calculation is a formalized application of classical compact-group convolution/fundamental-representation structure, not a novelty claim. Luscher's DESY76/54 transfer construction, printed p8 equations(20)-(21) and p9 equations(22)-(23), separates the temporal relative-link convolution from spatial plaquette factors and analyzes group characters. Source: https://bib-pubdb1.desy.de/record/396349/files/7611148.pdf?version=1 . The present elementary quaternion proof reuses Stardust's actual probability law and avoids a broad representation-theory library. It establishes no continuum existence claim from the paper.

The archived `ResearchSources/Incoming/block_contraction_spectral_gaps.tex` remains unchanged (SHA-256 `0C40FA6B92B830C0E2309BD6471D55CB0EB9BFB94296B9267AD23A5280FA4C60`). Its undefined boundary update and assumed operator perturbation estimates are not resolved merely by identifying this well-defined temporal reference. No manuscript instruction has been used as an agent instruction or mathematical assumption.

### Exact remaining physical bottleneck

PROVED: a genuine normalized Wilson convolution, an exact finite independent-word averaging formula, full four-vertex gauge invariance of the loop trace, and degeneration of its fixed-length factor as beta grows. NOT PROVED: a sharp beta-dependent rate, physical-distance scaling, a Hilbert-space spectral decomposition of the full lattice transfer, or a scale/volume-uniform physical mass gap. The full physical transfer contains spatial Wilson multiplication factors and ground-state normalization; it need not preserve this elementary loop mode. Small-field perturbation and large-field control must be quantified for THAT transfer. A promising next step is to test how spatial multiplication mixes this concrete loop mode with other gauge-invariant sectors and whether the resulting comparison has constants uniform in volume and along a justified continuum trajectory. No inference from the temporal factor alone settles the mass gap. Focused Yang-Mills remains active; all paused campaigns retain their status.

### Verification, checkpoint 1670

The targeted build passed4111 jobs; the complete root build passed6920 jobs in25.136 seconds. The complete transitive axiom audit passed52749 declarations in38.938 seconds, allowing only propext, Classical.choice and Quot.sound. All21 public types (16 theorems and five definitions), both private helper proofs and complete source bodies were reviewed. Seven independent Lean checks passed for the exact existing kernel, inverse-observable mean, zero-coupling four-edge reset, large-beta identity-loop limit, q=99/100 factor obstruction, arbitrary-layer integrability and four-vertex gauge invariance. The1296-term exact rational noncommuting test and multiresolution Wilson coefficient diagnostics passed independently.

Source integrity passed for2740 Foundation/root Lean files, with exactly the three intended changes/additions since approved1669. Three pinned configurations,113 baseline manuscripts and21 Yang-Mills originals are unchanged. No axiom, sorry, admit, toolchain change, ResearchSources modification or shared-edge independence assumption was introduced. Exact source manifest, full-build/axiom/type logs and independent evidence are retained under C:/Users/ramir/AppData/Local/Temp/stardust-ym-1670-*. The exact Git approval and guarded remote verification are recorded separately; this pre-commit ledger entry does not claim backup success before synchronization. Focused Yang-Mills remains active.

## Checkpoint 1671 — spatial weighting, moving vacuum, and an exact reset countertest

The focused Yang–Mills campaign remains ACTIVE. `Foundation/YMResetGroundState.lean` tests a concrete weakness in transferring checkpoint1670's temporal loop mode to a spatially weighted transfer. For any probability measure mu and measurable real X with |X|<=1, set h_t=exp(tX/2), Z_t=integral exp(tX), and T_t f=h_t integral(h_t f). The new bounded L2 operator is an actual rank-one operator, with its integral kernel identified almost everywhere (`operator_integral`). `ground_eigen`, `operator_norm` and `orthogonal_annihilated` establish T_t h_t=Z_t h_t, norm T_t=Z_t, and annihilation of the h_t-orthogonal subspace. `normalized_orthogonal_gap` proves the exact dimensionless gap-one quadratic-form identity there.

`ground_transform` identifies T_t(h_t f)/(Z_t h_t) with integration against the existing exponential-tilted probability measure. For bounded measurable observables this is a genuine one-step reset. The displayed Lean integral identity also uses totalized Bochner integrals for arbitrary functions; it does not assert arbitrary functions are integrable. No unitary L2 intertwiner between the two measures is claimed. Correct ground-state normalization and naive row normalization must not be interchanged.

For actual SU2 Haar measure, `wilson_zero_reset` and `transfer_is_weighted_wilson_reset` identify this operator with multiplication on both sides of the already verified Wilson convolution at ZERO kinetic coupling. With X=halfTrace, the old Haar-centered trace has overlap integral(X exp(tX/2)) with the new ground amplitude. `vacuumOverlap_derivative` proves its derivative at zero is exactly1/8. `centered_trace_moves` and `trace_mode_not_preserved_near_zero` show that arbitrarily small positive spatial parameters destroy the old trace eigenmode: its transfer is strictly positive everywhere, so cannot be a scalar multiple of the sign-changing trace. `amplitude_ratio` proves h_t(1)/h_t(-1)=exp(t), while the correctly normalized orthogonal sector still resets exactly.

PROVED: an actual bounded L2 weighted-reset operator, its ground eigenvalue/norm, exact orthogonal contraction, and failure of old trace-mode preservation. FAILED INFERENCE: mode mixing or a large spatial-amplitude ratio alone proves a spectral obstruction. This countertest invalidates that inference. CONDITIONAL BRIDGE: comparing a positive-kinetic Wilson transfer with this reference requires bounds on the moving vacuum and its orthogonal complement. OPEN: positive-kinetic quantitative estimates, multi-plaquette/shared-edge effects, volume-uniform control, physical-distance scaling and continuum limits. This is an ANISOTROPIC reference with kinetic beta=0 and independent spatial t, not an isotropic four-dimensional continuum trajectory. It proves no physical mass gap and does not refute the distinct stationary surrogate obstruction at1668. The calculation is classical rank-one/ground-state mathematics used to eliminate a misleading route, not a novelty claim or a broad auxiliary-library campaign.

Independent exact Fraction tests used two-state measures with amplitudes(2,3) and(2,100000). They checked the ground eigenvector, a nonzero orthogonal vector, idempotence of the ground-transformed kernel, and its discrepancy from naive row normalization. For(2,3), the transformed law is(2/11,9/11), versus row law(1/4,3/4). A512-node SU2 semicircle quadrature independently returned overlap(t)/t=0.1250000000260945 at t=0.0001; this is diagnostic only, not a proof input. Seven independent Lean checks passed, including the gap at t=100, the transform at t=1/2, eigenmode failure below1/1000, derivative1/8, exponential amplitude ratio, Wilson-reset identification and operator norm.

The unchanged source `ResearchSources/Incoming/block_contraction_spectral_gaps.tex` has SHA-256 `0C40FA6B92B830C0E2309BD6471D55CB0EB9BFB94296B9267AD23A5280FA4C60`; its assumed boundary-update perturbation estimates remain unresolved. The spatial/temporal factor separation in Luscher DESY76/54, printed p8 equations20–21, motivates this test (https://bib-pubdb1.desy.de/record/396349/files/7611148.pdf?version=1); no existence theorem is imported as an axiom.

Verification: targeted4112-job build and full6921-job root build passed. The complete transitive audit passed52805 declarations in41.313 seconds, allowing only propext, Classical.choice and Quot.sound. All26 unabridged public types,20 theorem proofs and6 definitions were reviewed against the intended domains. Source integrity passed2741 Foundation/root files with exactly the three intended Lean/root changes since approved1670; all3 pinned configurations,113 baseline manuscripts and21 Yang–Mills originals are unchanged. No sorry, admit, new axiom or compiler/trust change was introduced. Evidence is retained under C:/Users/ramir/AppData/Local/Temp/stardust-ym-1671-*. Exact commit approval and guarded PUBLIC two-branch synchronization are separate receipts; this pre-commit entry does not assert remote success. No campaign priorities changed.

## Checkpoint 1672 — positive-kinetic ground bridge and a sharp volume obstruction to the global comparison route

Focused Yang–Mills remains ACTIVE. The previous turn was progress: checkpoint1671 was fully audited, committed and verified on both authorized PUBLIC remote branches. The present checkpoint tests a specific route beyond the zero-kinetic reset: can positive spatial multipliers be removed from quantitative comparison without incorrectly centering at Haar measure?

### Verified positive results and exact domains

`Foundation/YMPositiveKernel.lean` proves `common_minorization`, `residual_bounds` and `oscillation_bound` for actual probability reference measures nu and measurable rows of a real kernel k with 0<m<=k(x,y)<=M. Its row density is k(x,y)/integral k(x,z)dnu(z). Every row and bounded test integrand used in the estimates is proved integrable. The normalized row dominates (m/M)nu, and for a measurable 0<=f<=1 the difference of any two row expectations is at most1-m/M. `rowLaw_probability` constructs and verifies the actual probability row measure; `rowLaw_integral` identifies its expectation with that integral formula. No joint-measurable Markov process or stationary law is asserted merely from separate row measurability.

The essential new bridge is `ground_bridge`. Let T f(x)=h(x) integral k(x,y)h(y)f(y)dmu(y), with h>0 and an actual displayed positive eigenfunction psi satisfying T psi=lam psi, lam>0. Reusing `SignedDensityProbabilitySampling.sampler` rather than introducing a new weighting framework, the reference probability is proportional to h psi dmu. The ground transform T(psi f)/(lam psi) is exactly row normalization of k AGAINST THAT REFERENCE. Thus the spatial amplitude ratio does not enter the generic minorization. `ground_affine_eigenvalue_bound` assumes h psi is measurable and integrable with positive normalization, and an actual affine eigenmode equation

    T(psi g)=eta psi g+c lam psi,  0<=g<=1,

with g attaining0 and1. It concludes |eta/lam|<=1-m/M. These are explicit hypotheses, not postulated existence axioms. The affine constant permits the usual shift/rescaling of a nonconstant bounded eigenfunction quotient. The theorem does not construct a positive vacuum, assert all L2 eigenfunctions have bounded quotients, identify the complete spectrum, or establish an infinite-volume operator. `doob_balance` proves the pointwise psi-squared detailed-balance identity for symmetric k; integration, stationary probability normalization and complete spectral realization remain distinct obligations. Algebraic identities for arbitrary functions use Lean's totalized Bochner integral; probabilistic contraction claims use the displayed bounded measurable domains.

For the actual finite-product SU2 temporal kernel

    k_beta(C,D)=exp(beta sum_i halfTrace(C_i D_i^{-1})),

`kinetic_measurable`, `kinetic_symmetric` and `kinetic_bounds` establish its measurable rows, symmetry and exp(-N|beta|)<=k_beta<=exp(N|beta|). `kinetic_oscillation_bound` and `kinetic_ground_eigenvalue_bound` therefore supply the explicit factor1-exp(-2N|beta|), independent of the positive spatial multiplier h. The latter remains conditional on its exact ground/eigenmode hypotheses. A scalar eigenmode satisfying this bound decays after j iterations by at most(1-epsilon)^j<=exp(-j epsilon), epsilon=exp(-2N|beta|); this elementary consequence is not a new theorem identifying physical time. A physical-distance conclusion still requires a justified relation between j, lattice spacing and bare coupling.

### Sharp limitation of the proposed global route

`spatial_cancellation` proves that arbitrary positive h cancels EXACTLY from the four-point cross ratio of h(C)k(C,D)h(D). `weighted_crossRatio_bound` gives the upper bound exp(4N|beta|). `center_crossRatio` exhibits the all-one/all-minus-one configurations attaining exp(4N beta), so the bound is sharp for beta>=0. `no_volume_uniform_crossRatio` proves that for any beta>0 and proposed finite bound, some N defeats it for EVERY positive spatial multiplier. No choice of such a multiplier repairs the raw whole-slice projective diameter.

This is an obstruction to this global comparison METHOD, not a spectral-gap obstruction. An explicit elementary product counterexample has one-coordinate transition [[4/5,1/5],[1/5,4/5]]. For N independent coordinates, the character indexed by S has eigenvalue(3/5)^|S|, by factoring the finite sum coordinatewise. The orthogonal character basis therefore gives gap2/5 for every N, while the corner cross ratio is16^N. This independent analytic counterexample is not claimed as a new Lean theorem here; numerical matrix checks for N=1,...,6 confirmed the predicted spectrum and ratio. It rules out inferring actual spectral slowing merely from a growing global projective diameter.

A stronger exact finite diagnostic tested gauge projection itself. On a four-edge Z2 cycle with that kinetic law, averaging all16 vertex gauge transformations gives transition entries [1+(81/625)chi(x)chi(y)]/16. All256 entries and all16 character modes were checked in exact Fraction arithmetic: the sole nonconstant eigenvalue is81/625, the gap is544/625, and the corner ratio drops from65536 before projection to124609/73984 afterward. This is a discrete Z2 gauge example, not an SU2 Haar gauge projection or a four-dimensional theorem. It demonstrates why the raw center-configuration witnesses must not be treated as physical gauge-sector witnesses.

### Independent positive-kinetic test and literature audit

A separate SU2 class-function discretization used the actual angularly averaged Wilson kernel exp(beta*x*y)*sinh(beta*sqrt(1-x^2)*sqrt(1-y^2))/(beta*sqrt(1-x^2)*sqrt(1-y^2)), with the continuous limiting value at zero and semicircle Haar weights. Fifteen(beta,t) pairs, beta=1,4,16 and t=0,1/4,2,8,32, were checked at64 and128 quadrature nodes. Ratios agreed within1e-10 and the discretized ground transform agreed with the ground-weighted row normalization. At beta=4 the second/top ratios were approximately0.658047,0.627624,0.290005,0.085043,0.012940 across those t values. These are numerical diagnostics for a weighted SU2 convolution on class functions; they neither certify its exact spectrum nor realize the full spatial-plaquette transfer of four-dimensional Yang–Mills.

The positive-operator mechanism is classical. Falk–Nussbaum, *Hidden Positivity and a New Approach to Numerical Computation of Hausdorff Dimension: Higher Order Methods*, section4, printed p11, recalls Birkhoff–Hopf contraction tanh(Delta/4), with Delta the Hilbert projective diameter; https://sites.math.rutgers.edu/~falk/papers/hdcomphp-rev.pdf . The known sharper projective factor would still deteriorate with N for this raw kernel. That theorem is literature context, not imported Lean evidence or a new axiom. No novelty is claimed for the elementary minorization, ground transform or diagonal cancellation.

The original `ResearchSources/Incoming/block_contraction_spectral_gaps.tex`, SHA-256 `0C40FA6B92B830C0E2309BD6471D55CB0EB9BFB94296B9267AD23A5280FA4C60`, was selectively re-examined at lines321–366. Its boundary update X' remains unspecified and its H1 heat-semigroup perturbation bound remains an assumption; the present positive-kernel estimates do not establish it. All original bytes remain unchanged.

### Physical bottleneck and next focused test

PROVED: actual normalized probability rows, conditional positive-kinetic ground-transform/eigenmode bounds, exact spatial cancellation, and a sharp raw-volume obstruction. CONDITIONAL: finite-volume Wilson application after constructing the correct positive ground function and identifying the gauge-projected physical transfer and its domains. FAILED: deducing a physical spectral obstruction from raw cross-ratio growth, or treating a positive multiplier's amplitude ratio as the relevant vacuum-centered contraction constant. OPEN: gauge-projected/local estimates uniform in volume, positive-kinetic vacuum realization in Lean, physical-distance scaling, and continuum/infinite-volume limits. No physical mass gap or external existence construction is assumed.

A specific next candidate is gauge-invariant tensorization: investigate whether fluctuations supported on forests vanish after gauge averaging, so kinetic contraction acts only on cycle-supported components, with a shortest-cycle rather than total-volume cost. The existing four-edge Wilson-loop identity and the exact Z2 test motivate this hypothesis, but neither proves it on SU2 lattice function spaces. First audit the available product/orthogonal machinery and test the forest-cancellation statement; do not build a broad gauge library or assume the missing local spatial comparison.

### Verification and checkpoint closure

Targeted build passed4217 jobs in25.241 seconds; the final full root build passed6922 jobs in42.305 seconds. The complete transitive axiom audit passed52875 declarations in41.194 seconds, permitting only propext, Classical.choice and Quot.sound. All32 unabridged public types,24 theorem proofs and8 definitions were reviewed. Eight independent Lean checks passed for kinetic symmetry, exact four-link center ratio at beta=3, cancellation with a nonconstant exponential loop multiplier, positive-kinetic oscillation, explicit million-level volume obstruction, actual row probability, zero-coupling reset and detailed balance. The initial independent test had a namespace ambiguity in its simp list; qualifying YMPositiveKernel.average repaired the TEST without changing mathematical sources or compiler settings.

Source integrity passed2742 Foundation/root Lean files, exactly three intended changes/additions since approved1671;3 pinned configurations,113 baseline manuscripts and21 Yang–Mills originals are unchanged. No sorry, admit, new axiom, compiler/trust change, original manuscript modification or campaign change was introduced. Source manifest, full-build/audit/public-type logs, independent Lean checks and exact/numerical evidence are retained under C:/Users/ramir/AppData/Local/Temp/stardust-ym-1672-*. Exact commit approval and guarded PUBLIC main/research remote verification are recorded separately; this pre-commit entry does not claim remote success before synchronization.

## Checkpoint 1673 — free-gauge forest cancellation, SU2 cycle domains, and two limits on kinetic-gap transfer

Focused Yang–Mills remains ACTIVE. The preceding goal turn was progress: checkpoint1672 is audited and both PUBLIC backup branches were independently verified at e7bcbbf72c7db5e6f09792930d994c7c59a7a0d3. This checkpoint tests the proposed gauge-invariant tensorization mechanism before claiming a physical spectral estimate.

### Verified forest and cycle results

`Foundation/SU2ForestCycleReduction.lean` explicitly constructs a non-Abelian gauge transformation trivializing an ordered rooted tree, for ANY group G. A finite parent certificate p:Fin(n)->Fin(n+1) satisfies val(p(i))<=val(i), with child i+1. `recursiveGauge` solves g(child)=g(parent)U(edge) by well-founded recursion, and `treeGauge_trivializes` verifies every transformed edge equals1. `forestGauge_trivializes` handles any selected subset of these edges, including disconnected forests; `forest_invariant_constant` proves every pointwise function invariant under all displayed vertex gauges is constant. There is no small-field or commutativity assumption. This is an explicit ordered-forest certificate, not a new theorem constructing an ordering for every abstract acyclic graph or identifying an arbitrary lattice marginal with such a function.

For a four-edge cycle, `cycle_reconstruct` proves for every pointwise gauge-invariant observable f (with arbitrary target type),

    f(A,B,C,D)=f(1,1,1,ABCD).

`canonical_conjugate` verifies that the resulting function of holonomy is a class function. These are actual gauge-action identities and extend checkpoint1670's trace example to all such observables. They do not turn a cycle into a tree or identify its nonconstant class functions with constants.

With the actual SU2 Haar probability, `class_sandwich_integral` and `cycle_one_edge_integrals` identify all four one-edge averages with the canonical Haar mean. `centered_cycle_one_edge_zero` shows each vanishes when that mean is zero. `class_sandwich_integrable` and `cycle_one_edge_integrable` establish the bounded-measurable domains. These conclusions are not using a nonintegrable integral's default value for the probabilistic interpretation.

The strongest analytic result is `cycle_missing_edge_pairing_zero`: for a bounded measurable centered class function F and ANY bounded measurable three-edge probe g,

    integral F(ABCD) g(A,B,C) d(Haar^4)=0.

The product law, full integrability and Fubini passage are verified. A direct matrix-coordinate proof supplies the required joint SU2 multiplication measurability; a local MeasurableMul2 instance is proved, not assumed. The final proof is within the original heartbeat limit; splitting measurable-map and integrability helpers repaired elaboration timeouts without changing compiler, trust or heartbeat settings. The theorem formally packages omission of the fourth edge; all four separate slice identities are also proved. General L2 closure and arbitrary graph conditional projections are not claimed from this bounded-cylinder result.

### A boundary condition that defeats an automatic forest argument

`boundary_fixed_path_obstruction` reuses the verified closed-pair trace to construct a NONCONSTANT two-edge path observable invariant under every INTERIOR vertex gauge:

    f(A g^{-1}, g B)=f(A,B),  f(A,B)=halfTrace(AB).

Its two endpoint gauges are fixed. Thus absence of cycles by itself does not imply cancellation for a boundary-conditioned block. The positive forest theorem assumes the full displayed vertex action; its constructed fixer happens to fix the auxiliary root, so anchoring one root is harmless. Fixing both endpoints of an open path is a different restriction and gives the explicit counterexample. Any use in the manuscript's boundary-transfer setting must specify the admissible gauges and prove that its retained/marginal observables satisfy the needed invariance.

### Independent shared-edge spectral challenge

An exact finite Z2 test used two adjacent square plaquettes sharing an edge (six vertices, seven edges). All128 characters were tested against all64 vertex gauges, and their kinetic eigenvalues were independently computed in exact Fraction arithmetic from the actual product transition with one-edge probabilities4/5 and1/5. The only gauge-invariant support masks are0,53,95,106, with sizes0,4,6,4. Nonconstant kinetic eigenvalues are a,a,b, where a=(3/5)^4=81/625 and b=(3/5)^6=729/15625. This supports the cycle-support mechanism on the tested graph, rather than a total-edge-count cost.

It also disproves a stronger, tempting assertion: an arbitrary positive gauge-invariant spatial multiplier preserves that unweighted kinetic spectral ratio. On the four plaquette-holonomy states (++,+-,-+,--), let h=(2,1,1,2). This is gauge invariant and weights the OUTER RECTANGLE loop, not the ordinary sum of elementary Wilson plaquettes. With K(s,t)=[1+a s1t1+a s2t2+b s1s2t1t2]/4 and T=diag(h)Kdiag(h), v=(1,0,0,-1) is an exact eigenvector with eta=4a=324/625. All entries are positive and the maximum row sum is R=3+b=47604/15625<4. The even sector is the explicit symmetric2x2 matrix

    [[2(1+b),1-b],[1-b,(1+b)/2]].

Its larger eigenvalue is lam+=(5(1+b)+sqrt(9(1+b)^2+16(1-b)^2))/4. The other two odd eigenvalues are4a and a; the smaller even eigenvalue is4b/lam+<a. Thus lam+ is the top eigenvalue and4a is the second. Its positive even eigenvector supplies a genuine finite ground-state transform, with stationary law proportional to its square. Consequently the normalized second eigenvalue is eta/lam+>=eta/R=675/3967>a; numerically it is0.2038328623, versus0.1296 before weighting. The exact entries, eigenvector and strict ratio lower bound were checked with rational arithmetic; the even-block formula gives the independent elementary spectral justification. This finite spectral counterexample is NOT newly Lean-formalized here and is NOT an SU2 or four-dimensional Wilson counterexample. It refutes transfer based solely on positivity and gauge invariance; the specific bare Wilson plaquette potential and any effective-loop interactions require their own estimates.

Independent noncommutative tests in the finite group S3 checked270 ordered-tree/selected-forest fields, all1296 four-cycle configurations,864 exact one-edge Haar sums, and an exact missing-edge pairing. They challenge the multiplication order and gauge conventions; they are not replacements for the SU2 Haar proofs.

### Manuscript repair and literature comparison

The selected original `ResearchSources/Incoming/dimock_nonabelian (1).tex`, SHA-256 `4D739A900C5B6E41DAC69071498E61847128B2F88781F709C0D576B9B43B889E`, was examined at lines385–418. Its axial-tree discussion places small-field/implicit-function and determinant concerns together. The verified correction is a separation of obligations: exact group-valued edge trivialization on a certified tree is global algebra and requires no small-field implicit-function theorem. This does NOT settle controlled Lie-algebra logarithms, preservation of coarse averages/boundary constraints, covariance estimates or Faddeev–Popov determinants. The manuscript's gauge potential formulation must not be silently identified with the simpler group-edge statement. Original bytes remain unchanged; this audit supplies no external Yang–Mills existence axiom.

The graph gauge action, Haar product space and invariant Hilbert-space framework are classical; Baez, *Spin Network States in Gauge Theory*, section2, records that setting and the spin-network decomposition (https://arxiv.org/html/gr-qc/9411007). Its source/target convention is opposite the written orientation used here, with the same endpoint cancellation structure. No novelty is claimed for maximal-tree gauge fixing or cycle reduction, and no Peter–Weyl or spin-network theorem has been imported into Lean as an assumption. Existing generic `ProductL2Curry` is a potential tool for the remaining product-space norm step; the periodic64-field Walsh basis concerns a different additive lattice and cannot supply the required SU2 representation automatically.

### Precise remaining bottleneck and research direction

PROVED IN LEAN: ordered-tree and selected-forest gauge trivialization/constancy, general four-cycle holonomy reconstruction, actual Haar slice cancellation and bounded three-edge pairing orthogonality, and a fixed-boundary forest counterexample. INDEPENDENT RIGOROUS FINITE COUNTEREXAMPLE: arbitrary positive gauge-invariant spatial weighting need not preserve the kinetic cycle spectral ratio. OPEN: equivariance of general retained-edge Haar marginals, closure from pointwise bounded cylinders to the correct invariant L2 space, product kinetic norm estimates on cycle-supported components, and a local spatial comparison for the ACTUAL Wilson transfer and changing vacuum. Boundary gauges, shared edges and the stationary measure must be verified explicitly.

The next focused test should exploit the literal Wilson plaquette potential and finite overlap structure, rather than assume an arbitrary gauge-invariant multiplier is benign. Challenge any proposed local comparison on shared-edge models before expanding classical gauge infrastructure. The tree/cycle results may support that test, but neither they nor the finite Z2 spectrum establishes a volume-uniform SU2 gap, a physical distance scale, continuum existence or a four-dimensional mass gap. Bakry remains paused and the campaign queue is unchanged.

### Verification and closure

Targeted build passed4218 jobs in21.601 seconds. Full root build passed6923 jobs in26.832 seconds. The complete transitive axiom audit passed52930 declarations in39.886 seconds, permitting only propext, Classical.choice and Quot.sound. All26 unabridged public types,15 theorem proofs,11 definitions/abbreviations and three private helper proofs were reviewed. Eight independent Lean checks passed: a branched non-Abelian tree, disconnected selected edges, actual loop reconstruction, centered quadratic class-function averaging, its integrability, its genuine product pairing against a nontrivial proper-edge probe, the fixed-boundary counterexample and canonical conjugation. The nonlinear test used F(W)=halfTrace(W)^2-1/4 and verified its exact Haar centering and bounds.

Source integrity passed2743 Foundation/root Lean files, with exactly three intended changes/additions since approved1672; all3 pinned configurations,113 baseline manuscripts and21 Yang–Mills originals are unchanged. No sorry, admit, new axiom, heartbeat/trust/toolchain change or ResearchSources modification was introduced. Evidence is retained under C:/Users/ramir/AppData/Local/Temp/stardust-ym-1673-*. Git approval and guarded PUBLIC main/research synchronization are recorded separately; this pre-commit ledger does not assert remote success before verification. Focused Yang–Mills remains active.

## Checkpoint 1674 — elementary-plaquette spectral deterioration and actual SU2 shared-edge projection

Focused Yang–Mills remains ACTIVE. The preceding goal turn made verified progress at checkpoint1673, 992126f3c85818c27caef3545908b2864b17e300, with both authorized PUBLIC backup branches verified. This checkpoint tests the stronger local claim left open there: can the literal insertion of one elementary Wilson plaquette be assumed to preserve the unweighted kinetic gap?

### A fully verified finite stationary counterexample with an elementary plaquette multiplier

`Foundation/WilsonPlaquetteGapCounterexample.lean` constructs an actual four-state positive Markov operator and stationary PMFs, including its positive ground state rather than assuming one. The provenance is a two-square Z2 graph sharing an edge: edges(0,1),(1,2),(3,4),(4,5),(0,3),(1,4),(2,5). The independent link-noise means are(2/3,2/3,2/3,2/3,3/4,1/2,3/4). Each is a finite positive Wilson coupling: the relative-link same/flip odds are(5,5,5,5,7,3,7), or beta_e=(log odds_e)/2. The two plaquette means are a=1/6 and the outer-rectangle mean is b=1/9. This is an anisotropic finite Z2 example, not SU2 Haar or the homogeneous four-dimensional theory.

The exact integer product-noise certificate enumerates all128 bit fields. The left and right plaquette parity masks are53 and106. The four quotient counts are119808,73728,73728,64512 with denominator331776, giving quotient probabilities(13/36,2/9,2/9,7/36). `noiseIndex_bijective` proves the8x16 enumeration covers every input exactly once, and `full_noise_quotient_certificate` identifies ALL transition entries using the relative plaquette labels. This avoids an unchecked discretization or unexplained4x4 matrix. The graph gauge-orbit interpretation and Fourier provenance were additionally challenged independently over all128 characters and64 vertex gauges.

`kinetic_centered_bound` proves the unweighted kinetic Poincare gap is at least5/6 on all centered real functions, and `kinetic_bound_sharp` supplies the1/6 eigenmode attaining equality. Now multiply on both sides by h=(2,2,1,1), a function of the FIRST elementary plaquette alone. `amplitude_wilson_form` proves EXACTLY h(s)=sqrt(2)*exp((log2)s1/2). The harmless common scalar leaves normalized spectral ratios unchanged. This is a genuine one-plaquette half weight, unlike checkpoint1673's outer-rectangle multiplier; the other spatial plaquette coupling is zero.

For T=diag(h)Kdiag(h), `ground_eigen` explicitly verifies the strictly positive ground vector psi=(5,5,2,2) with eigenvalue8/3. `step` is the actual ground transform T_ij psi_j/((8/3)psi_i). Positive entries, row sums, detailed balance, stationary weights pi=(25/58,25/58,2/29,2/29), and pi proportional to psi squared are all proved. `rowPMF` and `stationaryPMF` are actual probability mass functions; `stationary_bind` verifies stationarity as a PMF identity. No unproved Perron existence or vacuum normalization is used.

For the centered probe f=(1,-1,0,0), the verified stationary second moment is25/29 and lag pairing is125/696. `probe_rayleigh` gives their ratio5/24>1/6. Consequently `unchanged_gap_fails` refutes the original5/6 Poincare lower bound for THIS stationary operator; its gap is at most19/24<5/6. The finite chain remains strictly positive and mixing. This is strict deterioration of a proposed comparison constant, not gap closing, infinite-volume degeneracy or a physical mass-gap obstruction.

An earlier independent homogeneous-kinetic scan with r=3/5 also found deterioration with a single plaquette field and with small unequal positive fields on both plaquettes; equal fields decreased the tested ratios. Those scans are diagnostics only. The Lean theorem concerns the exact anisotropic construction just specified. Neither test licenses a claim about equal spatial couplings on the full lattice. What fails is the universal stepwise claim that inserting any positive elementary plaquette multiplier can only improve the kinetic gap.

### Actual SU2 calculation: a shared link has a nontrivial surviving channel

`Foundation/SU2SharedPlaquetteProjection.lean` returns to actual continuous SU2 Haar probability. It obtains the normalized fundamental Schur identity directly from already verified machinery: differentiate the exact Wilson convolution half-trace eigenidentity at zero tilt, use `BoundedExponentialTiltResponse.expectation_hasDerivAt_zero`, and equate the two verified derivatives. `translated_trace_covariance` proves

    integral halfTrace(CU) halfTrace(U) dHaar(U)=halfTrace(C)/4.

Haar translation then proves `sharedProduct_mean`:

    P(L,R,U)=halfTrace(LU) halfTrace(U^{-1}R),
    M(L,R)=integral P(L,R,U)dHaar(U)=halfTrace(LR)/4.

The shared edge is identified, not replaced by two independent copies. L,R represent the two exterior paths; their concatenation is the outer loop. Measurability, boundedness, integrability and zero mean of the residual P-M are verified. `sharedMean_gauge` and `sharedProduct_gauge` prove the appropriate full two-endpoint gauge identities, so this is more than a bare-link sign analogy.

For every FIXED shared U, `shared_projection_second_moments` computes the displayed iterated independent Haar exterior moments:

    integral_L integral_R P^2=1/16,
    integral_L integral_R M^2=1/64,
    integral_L integral_R (P-M)^2=3/64.

Every integral expansion used in the proof has its integrability discharged. Thus the mean and residual carry respectively one quarter and three quarters of the original squared moment under these Haar exterior variables. The theorem is an exact iterated-integral identity; it does not by itself construct the full physical L2 transfer or prove that the residual is a kinetic eigenchannel. This distinction prevents importing the Z2 coefficient into SU2, where the projection coefficient is1/4.

### A rigorous algebraic sign reduction, with the spectral bridge still open

The shared-edge decomposition suggests a precise candidate for a local SU2 perturbation audit. Let c be the fundamental Wilson increment coefficient, m its second half-trace moment, d=(4m-1)/3 and a=c^4. If the residual kinetic channel is proved to have coefficient c^6 d, the mean channel coefficient is c^6, the correct center-parity sector is isolated, and the relevant normalized eigenbranch is twice differentiable for T_t=exp(tV/2)Kexp(tV/2), with V the first plaquette half trace, the proposed second derivative of the neighboring eigenvalue ratio is

    (a/4) B(c^2,m),
    B(x,m)=(1+x)/(4(1-x))
           +3(1+xd)/(4(1-xd))-(1+x^2)/(1-x^2).

That operator perturbation formula is a CANDIDATE REDUCTION, not a proved derivative of a physical operator. The new Lean theorem `overlapBracket_positive` does rigorously settle its algebraic sign: B(x,m)>0 whenever0<x<=m<1. Indeed

    B=x[1+3d-x(3+d)]/[2(1-x^2)(1-xd)],

and the numerator bracket is bounded below by(4/3)m(1-m)>0 using x<=m. The usual variance inequality c^2<=m therefore supplies the sign condition rather than an unexplained numerical cancellation. Application to actual tilted Haar moments, the exact residual convolution action, sector isolation, operator domains and analytic perturbation hypotheses must each be proved. None has been introduced as an axiom here.

A256-node semicircle diagnostic evaluated the conditional expression at beta=1/4,1/2,1,2,4,8,16,64 and found positive signs throughout. The saved evidence labels the missing residual/spectral hypotheses explicitly. These numbers cannot substitute for the unproved operator bridge. The algebraic sign theorem and the genuine SU2 Haar moment decomposition are the proved parts; a claim of SU2 spectral deterioration would be premature.

### Manuscript and literature comparison

`ResearchSources/Incoming/block_contraction_spectral_gaps.tex`, SHA-256 `0C40FA6B92B830C0E2309BD6471D55CB0EB9BFB94296B9267AD23A5280FA4C60`, was selectively checked at lines615–651. Its asserted q=q0+epsilon_T+eta<1 and continuum trajectory still require actual norm estimates and a quantified margin. The finite counterexample does not refute a conditional perturbation theorem whose hypotheses and error bounds are genuinely established; it prevents silently setting the spatial correction to zero from Wilson form, positivity or gauge invariance. Existing `YMBlockHeatContractionObstruction` remains relevant to the insufficient rate comparison with the shrinking heat-step deficit. No manuscript byte or historical result was changed.

Luscher's DESY76/54 transfer construction separates temporal convolution and spatial multiplication (printed pp8–9, https://bib-pubdb1.desy.de/record/396349/files/7611148.pdf?version=1). The finite test respects that structure and uses explicit ground normalization. The SU2 integral is the classical normalized fundamental Schur identity, recovered through Stardust's verified derivative machinery. No novelty or external continuum existence claim is asserted; the conditional perturbative connection needs its own further mathematical and novelty audit.

### Exact bottleneck and next focused work

PROVED IN LEAN: a finite Wilson-noise quotient certificate, explicit ground-normalized stationary PMFs, failure of the unchanged kinetic gap after an elementary plaquette insertion, actual SU2 shared-edge Haar projection and residual moments, gauge invariance and a positive algebraic perturbation bracket. FAILED: universal monotonic improvement under a local elementary-plaquette insertion. OPEN: the genuine SU2 residual kinetic action and spectral-perturbation realization, homogeneous simultaneous spatial weighting, volume-uniform estimates, a physically justified distance scale, and continuum/infinite-volume limits.

The next substantive test is the quadratic one-link Wilson action on the shared residual: prove or refute the proposed coefficient d=(4m-1)/3 using the existing central-law, quaternion and moment machinery, before developing more abstract gauge infrastructure. Then test the actual operator-domain/isolation hypotheses behind the two-plaquette perturbation formula. Even a successful local deterioration theorem would require quantitative control, not imply masslessness or invalidate every possible mass-gap argument. Yang–Mills remains active; Bakry stays paused and no later campaign starts.

### Verification and closure

The targeted build passed4227 jobs in28.713 seconds. Full root build passed6925 jobs in27.823 seconds. The complete transitive axiom audit passed53073 declarations in52.938 seconds, permitting only propext, Classical.choice and Quot.sound. All69 unabridged public types,44 theorem proofs,25 definitions/abbreviations and the private integrability helper were reviewed. Twelve independent Lean checks passed across actual Haar projection/integrability/residuals/gauge transformations, the three second moments, the variance-boundary bracket case, PMF stationarity, exact Rayleigh ratio, failed gap bound, full noise provenance, literal Wilson half weight and the all-function centered kinetic bound.

Independent Fraction tests verified all128 product-noise characters, the exact ground and stationary chain, the strict Rayleigh obstruction,121 noncommuting quaternion covariance cases and512 projection-moment terms. The finite enumeration was split8x16 with a bijection proof to stay within the existing recursion limit; no native_decide, heartbeat increase or verification weakening was used.

Source integrity passed2745 Foundation/root Lean files, exactly four intended changes/additions since approved1673; all3 pinned configurations,113 baseline manuscripts and21 Yang–Mills originals remain unchanged. No sorry, admit, new axiom, trust/toolchain change or ResearchSources modification was introduced. Evidence is retained under C:/Users/ramir/AppData/Local/Temp/stardust-ym-1674-*. Exact commit approval and guarded PUBLIC main/research synchronization are separate receipts; this pre-commit entry does not claim remote success before verification.

## Checkpoint1675 — actual SU2 quadratic channel and shared-link kinetic action (October28,2026)

### Concrete bottleneck resolved

`Foundation/SU2QuadraticWilsonChannel.lean` proves the actual Wilson increment's quadratic convolution, rather than assuming the residual eigenvalue needed by checkpoint1674. Write h=halfTrace, nu_beta=SU2WilsonConvolution.increment beta, c=integral h dnu_beta, m=integral h^2 dnu_beta and d=(4m-1)/3. `bilinear_convolution` proves, for every real beta and C,D in SU2,

    integral h(CV)h(DV)dnu_beta(V)
      = d h(C)h(D)+(1-d)h(C D^{-1})/4.

The proof uses the actual central Wilson probability, its verified conjugation invariance, and an exact twelve-conjugation quaternion averaging identity. The finite average is an algebraic isotropy device, not a replacement increment distribution. All integral and finite-sum operations have their measurability and integrability discharged. This is the classical quadratic/adjoint character mechanism, not a claim of novel representation theory.

For the existing shared product P(L,R,U)=h(LU)h(U^{-1}R), mean M(L,R)=h(LR)/4 and residual Q=P-M, `sharedProduct_step` and `sharedResidual_step` prove

    step_beta P = d P+(1-d)M,     step_beta Q = d Q.

`actual_kernel_residual` and `actual_kernel_centeredSquare` explicitly identify these with integrals against the existing genuine transition kernel at C^{-1}, preserving that argument convention. The centered square h^2-1/4 is Haar-centered, conjugation invariant, belongs to Haar L2, has second moment1/16 and is a genuine pointwise kernel eigenfunction with coefficient d. These are not assertions about a spatially weighted stationary vacuum.

### Seven actual link increments, with the shared edge identified

`residualWords` and `sharedWordAverage` are recursively nested integrals against actual independent Wilson increments. Private exterior occurrences contribute c each; a SINGLE shared increment occurs in both plaquette factors and contributes d. `twoPlaquette_residual_average` proves the coefficient c^6 d on the two oriented three-edge exterior paths plus their shared edge. `outerRectangle_average` gives c^6 on the mean channel. The two coefficients are not c^8. `twoPlaquette_residual_gauge` verifies full six-vertex gauge invariance of the resulting observable. All three recursive layer-integrability statements are proved. Private occurrences are independent as defined; the theorem does not identify repeated private physical edges in an arbitrary lattice embedding.

This DISCHARGES checkpoint1674's residual kinetic coefficient premise at the actual bounded, nested-integral level. Together with its exact Haar moment weights1/4 and3/4, the local channel calculation is now rigorous. It does NOT discharge the whole proposed normalized-eigenvalue second derivative. Its product-Haar L2 operator realization, sector isolation, domain and analytic perturbation hypotheses remain open, as does the actual moment-range application in that calculation. No conditional bridge has been promoted to an axiom.

### Independent challenges and source comparison

Twelve independent Lean examples passed: actual twirl and Wilson convolution specializations, both genuine-kernel identities, centered-square Haar moments/L2, beta-zero coefficient/reset, seven-link factor, outer rectangle, full vertex gauge cancellation, recursive integrability and the empty-private-word base case. Independent rational quaternion tests passed100 exact noncommuting twirl cases. Actual Wilson radial quadrature at64 and128 nodes tested beta=-4,-1/2,0,1,4,16,64 and three noncommuting backgrounds, checking the affine product and centered-square identities within2e-12. Quadrature is diagnostic, not proof input.

A separate exact Fraction experiment enumerated512 terms for EACH of two seven-link tests, preserving one shared increment. Its deliberately compressed degree-two moment cubature has c=1/2,m=5/8,d=1/2 and yielded1213/640000 and39/25600, exactly c^6 d times1213/5000 and39/200. This cubature is NOT the actual Wilson law or a fully central SU2 law; it independently challenges the link bookkeeping only.

Luscher DESY76/54, printed pp8-9 (https://bib-pubdb1.desy.de/record/396349/files/7611148.pdf?version=1), separates spatial multiplication from the temporal convolution and uses character coefficients. The new formal calculation supplies a concrete quadratic temporal channel; it supplies no spatial spectral comparison. Original `ResearchSources/Incoming/block_contraction_spectral_gaps.tex` hash remains `0C40FA6B92B830C0E2309BD6471D55CB0EB9BFB94296B9267AD23A5280FA4C60`. Its claimed contraction margin still requires actual norm bounds after spatial insertion. All original manuscripts are untouched.

### Exact remaining mathematical bottleneck

PROVED: actual SU2 quadratic convolution, shared residual kinetic action, c^6 versus c^6 d local channels, genuine-kernel interfaces, centered-square L2 membership and full local gauge invariance. CONDITIONAL: checkpoint1674's proposed normalized stationary eigenbranch derivative. FAILED approaches remain failed: neither temporal covariance nor positivity justifies an unchanged spatially weighted gap, as the prior exact finite Wilson quotient shows. OPEN: normalized SU2 stationary transfer comparison, homogeneous four-dimensional spatial interactions, volume/scale-uniform bounds and continuum/infinite-volume limits. None of this proves a physical mass gap or a physical spectral obstruction.

Next focused work: identify the finite product-Haar operator and its normalization, then test the derivative bridge through rigorous isolation/domain estimates or a concrete variational certificate with a positive supersolution bound. Avoid a broad gauge library or assuming a general perturbation theorem without its hypotheses. Coupling-dependent iteration still needs a physically justified distance scale and bounds surviving spatial weighting. Yang-Mills remains ACTIVE; Bakry stays PAUSED and the queue is unchanged.

### Complete verification

Final full root build passed6926 jobs in47.1081462 seconds. Complete transitive axiom audit passed53165 declarations in41.5403936 seconds, allowing only propext, Classical.choice and Quot.sound. All48 unabridged public types,35 theorem proofs,13 definitions/abbreviations and six private integrability helpers were reviewed. Twelve independent Lean checks passed. No sorry, admit, new axiom, heartbeat/trust/toolchain change or weakened verification was introduced.

Source integrity passed2746 Foundation/root Lean files with exactly three mathematical source changes/additions since approved1674; all three pinned configurations,113 baseline manuscripts and21 Yang-Mills originals are unchanged. Evidence: C:/Users/ramir/AppData/Local/Temp/stardust-ym-1675-{audit.log,checks.lean,checks.log,full-build.log,independent.json,working-checkpoint.json}. Both ledgers append this result without rewriting history. Exact Git approval and guarded PUBLIC main/research synchronization are separate closure receipts; this pre-commit record does not assert remote success.

## Checkpoint1676 — finite-error Wilson vacuum certificate and its nonuniform window (October28,2026)

### Why this route was selected

Checkpoint1675 closed the actual shared-edge kinetic channel premise, but the proposed stationary eigenbranch comparison still lacked operator realization and perturbation/isolation hypotheses. Rather than assume that branch or start a general spectral library, this checkpoint tests a concrete positive-supersolution route. It gives a true exponential-weight integral bound with an explicit cubic error, and proves an obstruction to extrapolating its sufficient smallness condition. The normalized stationary spectral comparison itself remains OPEN.

### Actual measures, moment domains and nondegenerate coefficients

`Foundation/SU2WilsonGroundCertificate.lean` defines `walkLaw beta n` as the actual distribution of a product of n independent Wilson increments, recursively using product measures and measurable group multiplication. `walkLaw_probability` proves probability, including n=0 as a Dirac law. Fubini is used only after a bounded measurable integrability proof. With h=halfTrace, c=integral h dnu_beta and d=(4m-1)/3, the verified formulas are

    integral h(CV) d(walkLaw beta n)=c^n h(C),
    integral h(CV)^2 d(walkLaw beta n)=1/4+d^n(h(C)^2-1/4).

`haar_absolutelyContinuous_increment` proves reverse absolute continuity from the everywhere positive actual tilt density. The original Haar second moment1/4 then excludes m=1 at finite real beta. Actual variance expansion proves c^2<=m<1, hence |c|<1 and |d|<1. `kinetic_power_ne_one` discharges the relevant denominators for EVERY finite beta and n>0. Zero increments really are excluded from those denominator assertions. These are finite Wilson statements, with no unverified probability law or external existence axiom.

### An explicit certificate for the literal exponential weight

Put a=c^4, r=d^4 and

    A=a/(1-a), B=r(1+a)/(2(1-a)(1-r)), mu=(1+a)/(8(1-a)),
    w(t,x)=1+A t x+B t^2(x^2-1/4),
    C=(2+exp(1))(1+|A|+|B|)+|mu|(|A|+|B|).

Let K4 f(C)=integral f(CV)d(walkLaw beta 4)(V), S_t f=K4(exp(t h)f), H_t=exp(t h/2) and T_t f=H_t K4(H_t f). These are the definitions `weightedWalk` and `symmetricWalk`, not a surrogate matrix or a formal Taylor-only operator. `weightedWalk_trial_error` proves the UNIFORM POINTWISE residual

    |S_t w(t,h(C))-(1+mu t^2)w(t,h(C))| <= C |t|^3

for |t|<=1. Its expectation proof uses only the two exact moments above and an explicit bounded exponential remainder. No differentiable eigenbranch, isolation, positive vacuum existence or spectral series is assumed.

Under the explicit sufficient condition |A||t|+|B||t|^2<=1/2, w>=1/2. Thus u=H_t w is strictly positive and `symmetricWalk_four_supersolution` proves

    T_t u <= (1+mu t^2+2 C |t|^3)u.

`weightedWalk_four_domination` also proves actual L1 integrability and the corresponding one-step envelope bound for EVERY measurable f satisfying |f|<=M w, M>=0. This is an honest weighted pointwise domination/domain certificate. No completed Hilbert-space norm theorem, normalized stationary PMF, full product-lattice operator or vacuum eigenpair is thereby declared constructed. The symmetric exponential half weights are literal; a polynomial spatial potential was not substituted for Wilson form.

The probabilistic and Taylor ingredients are classical; no novelty is asserted. The useful research reduction is that this concrete upper-certificate route can proceed without analytic spectral isolation, using already verified quadratic channels and explicit finite errors. It can supply one side of a future variational comparison; it is not that entire comparison.

### A proved limitation, not an extrapolated mass-gap conclusion

`necessary_trial_window` proves that this sufficient condition forces |t|<=(1-a)/(2a) when0<a<1. Combining it with the existing actual c^4 ->1 theorem, `no_uniform_fixed_trial_window` proves that NO FIXED nonzero spatial amplitude t satisfies this sufficient condition for every sufficiently large beta. This is a theorem about this particular certificate's window. It does not say the true trial is negative outside that window, rule out a different supersolution, establish gap closing, or refute every mass-gap route. In particular neither this small-perturbation method nor checkpoint1674's conditional local derivative may be applied automatically to simultaneous homogeneous spatial weighting in four dimensions.

### Independent challenges, sources and exact remaining obligations

Fourteen independent Lean examples passed, covering genuine probability/product moments, strict finite-coupling coefficients, rational moment cancellation, nonempty positivity, the actual symmetric exponential transfer, beta-zero normalization, reverse absolute continuity, fixed-amplitude nonuniformity, the excluded n=0 case, actual L1 domination and a concrete necessary-window boundary. Initial test function-extensional simplifications were repaired in the temporary harness; final tests pass without changed theorem semantics or compiler limits.

Independent Fraction arithmetic verified240 exact moment-cancellation cases. A separate DIAGNOSTIC used64 SU2 character modes and256/512-node Haar radial quadrature for beta=0,1/2,1,4,16,64, both signs and two magnitudes of t:24 cases at EACH resolution. All tested cubic bounds and supersolution signs held; cross-resolution maximum residual difference was2.11e-15. The finite character truncation and quadrature are numerical evidence only, not proof input, a certified spectral enclosure, or a full spatial transfer construction. Diagnostics also expose the sufficient-condition failure at t=beta for the larger tested beta values; the formal fixed-t theorem is the rigorous limitation.

Original `ResearchSources/Incoming/block_contraction_spectral_gaps.tex`, SHA256 `0C40FA6B92B830C0E2309BD6471D55CB0EB9BFB94296B9267AD23A5280FA4C60`, was selectively reread at lines616-652. Its asserted q=q0+epsilon_T+eta<1 still needs actual quantified operator error margins; its conditional continuum passage is not discharged here. All manuscript bytes are preserved.

NEXT CONCRETE BOTTLENECK: combine an odd-sector Rayleigh trial using1675's genuine shared-edge c^6 and c^6 d channels with a vacuum upper certificate on the SAME actual seven-link product operator. The generic moment certificate above can be applied directly once that product law's two word moments and reversible integral domains are identified; proving equality of every nonlinear reduced kernel need not be imposed if these exact required inputs suffice. Still verify gauge invariance, center parity, ground normalization and the relevant quadratic-form domains before calling any ratio stationary spectral deterioration. Homogeneous four-dimensional overlap, volume-uniform comparison, physically justified distance and continuum/infinite-volume limits remain separate unresolved obligations. No positive physical mass gap or physical spectral obstruction has been established. Yang-Mills remains ACTIVE, Bakry stays PAUSED, and no queue change occurs.

### Final verification and source integrity

Final complete root build passed6927 jobs in27.8879347 seconds; complete transitive axiom audit passed53217 declarations in40.3549043 seconds, allowing only propext, Classical.choice and Quot.sound. All39 unabridged public types,28 theorem proofs,11 definitions and nine private helper proofs were reviewed. Fourteen independent Lean checks and the rational/numerical challenges passed. A single trailing whitespace cleanup preceded the final complete build and audit. No sorry, admit, new axiom, heartbeat/trust/toolchain change or error suppression was introduced.

Source integrity passed2747 Foundation/root Lean files, with exactly three intended mathematical source changes/additions since approved1675. All three pinned configurations,113 baseline manuscripts and21 Yang-Mills original files are unchanged. Evidence is retained under C:/Users/ramir/AppData/Local/Temp/stardust-ym-1676-*, including the final working-checkpoint manifest, full-build/audit logs, independent Lean harness and numerical JSON. Exact Git approval and guarded PUBLIC main/research synchronization are separate closure receipts; this entry does not claim a remote backup before it is verified.

## Checkpoint1677 — a common actual seven-link Markov transfer for the spectral test (October28,2026)

### Concrete identification, rather than another conditional spectral formula

`Foundation/SU2SevenLinkTransfer.lean` constructs one state space with coordinates (U,A,B,C,D,E,F), where U is the SINGLE shared edge, L=ABC and R=DEF are the two private paths. `edgeLaw` is a genuine sevenfold product measure. `noise beta` uses the actual Wilson increment on EVERY edge; `haar` uses the existing concrete SU2 Haar law. `step beta f(s)=integral f(s v)dnoise_beta(v)` updates each physical edge once. Bounded measurable Fubini, measurability, probability and the required integral domains are verified, not assumed.

`transition` is an actual Mathlib Markov kernel, built by sampling the independent product noise and applying group multiplication. `transition_markov`, `transition_eq_map` and `transition_integral` identify it exactly with the displayed step. Product-Haar right invariance and Fubini prove `step_haar_stationary` and `transition_integral_stationary` for EVERY bounded measurable probe. This is a genuine finite SU2 kinetic transition with Haar stationarity; it is not an assertion that Haar is the stationary vacuum law AFTER spatial weighting.

### Both channels and the vacuum estimate now refer to the SAME operator

Write X(s)=h(LU), Y(s)=h(U^{-1}R), M(s)=h(LR)/4 and Q(s)=XY-M, where h=halfTrace. With the existing actual c=E_nu h and d=(4E_nu h^2-1)/3, the new exact full-product identities are

    K X=c^4 X,  K Y=c^4 Y,
    K M=c^6 M,  K Q=c^6 d Q,
    K(X^2)=1/4+d^4(X^2-1/4).

`step_residual` identifies checkpoint1675's nested expression with this actual product operator, preserving one shared increment rather than silently splitting it into independent copies. `step_meanChannel`, `step_first`, `step_second` and the quadratic identities are proved for the same law. The centered-quadratic word helper serves precisely the needed first-plaquette moment identification.

`haar_path_integral` rigorously reduces the private Haar paths to independent L,R variables. It uses Haar translation and bounded Fubini, not a gauge-fixing assumption. This gives actual full-state moments

    E_haar X=0, E_haar X^2=1/4,
    E_haar (XY)^2=1/16, E_haar M^2=1/64, E_haar Q^2=3/64,
    E_haar M Q=0.

The mean and residual belong to actual Haar L2 and have strictly positive squared norms. The one-quarter/three-quarter decomposition is therefore realized on the common state space, rather than imported from a different surrogate's character normalization. `gaugeAction` explicitly uses all six vertices of the adjacent-square graph. X,Y,M,Q and the vacuum candidate are invariant under that full vertex action.

Define T_t=H_t K H_t, H_t(s)=exp(t X(s)/2), with literal exponential plaquette half weights. Applying checkpoint1676's generic moment certificate DIRECTLY to this seven-link probability law proves `spatialStep_trialVacuum_supersolution` on the SAME K. With a=c^4,r=d^4 and the previously verified A,B,mu,C,

    u(s)=exp(t X(s)/2)[1+A t X(s)+B t^2(X(s)^2-1/4)],
    T_t u <= [1+mu t^2+2 C |t|^3]u.

The exact domain is |t|<=1 and |A||t|+|B||t|^2<=1/2; strict positivity and actual inner-integral existence are proved separately. No equality of every nonlinear reduced kernel, analytic eigenbranch or vacuum existence theorem was assumed to make this identification. The necessary smallness and nonuniform-window obstruction from1676 remain in force.

### A genuine stationary kinetic obstruction, with its physical boundary explicit

`haar_first_lag` and `transition_first_lag` prove the actual stationary lag pairing E[X KX]=c^4/4. Together with E X=0 and E X^2=1/4, the lag/variance ratio is exactly c^4. The prior actual c^4 ->1 result therefore yields `no_uniform_centered_kinetic_bound`: for EVERY q<1 there is a finite beta>=0 at which this centered observable violates the proposed bound E[X KX]<=q E[X^2]. This is a precise coupling-nonuniform obstruction for the genuine finite seven-link K, not merely a row-normalization heuristic.

It does NOT establish a vanishing gap at any fixed finite beta, identify the spatially weighted stationary law, or prove a quantum four-dimensional mass-gap obstruction. Large Wilson parameter is a weak-coupling limit in the usual lattice terminology. The formal result is stated in beta, without conflating that terminology with earlier module names. The model is the unprojected local temporal kinetic piece; neither its finite patch nor its gauge-invariant probes supplies the full homogeneous lattice, Gauss-law projection, infinite-volume or continuum construction.

### Independent tests and manuscript comparison

Sixteen independent Lean checks passed: actual Markov/probability/map realization, genuine-kernel eigenmode identity, both shared channels, the common-law second moment, all four Haar quadratic values and channel orthogonality, actual L2 domains, full vertex gauge identities, bounded-probe stationarity, centered nonzero lag obstruction, same-operator vacuum upper bound and its L1 domain, beta-zero reset and nonvacuity of the residual.

Independent Fraction calculations tested two noncommuting seven-link backgrounds with the SAME Q8 moment-cubature law on every edge: probabilities9/16 at+1 and1/16 at each other signed quaternion basis element, hence c=1/2,m=5/8,d=1/2. Each private path has512 exact terms, and the shared edge has8; independence factorizes the exterior-path expectations while retaining the SAME shared increment in both plaquettes. All five channel/moment identities and the quadratic residual norm diagnostic passed exactly. This is a degree-two moment diagnostic, NOT the actual Wilson law, a fully central law or a general Haar cubature.

A separate512-node actual Wilson radial-moment calculation propagated first and second quaternion tensors through the original noncommuting edge placements. Fourteen tests, beta=-4,0,1/2,1,4,16,64 on both backgrounds, matched the expected c^4,d^4,c^6,c^6 d formulas with maximum absolute discrepancy2.23e-16. These are independent numerical diagnostics only; no quadrature enters Lean or certifies a spatial spectrum.

Original `ResearchSources/Incoming/block_contraction_spectral_gaps.tex`, SHA256 `0C40FA6B92B830C0E2309BD6471D55CB0EB9BFB94296B9267AD23A5280FA4C60`, was selectively reread at lines321-363. Its updated boundary X' and H1 comparison to the boundary heat semigroup remain separate unverified inputs. The concrete kernel constructed here has NOT been identified with that manuscript's unspecified boundary update; no operator-error margin or continuum passage is thereby certified. No manuscript byte was changed and no novelty is asserted for the classical product-measure, Haar or Markov ingredients.

### Exact next bottleneck and unresolved physical bridge

PROVED: a common actual seven-link Markov realization, Haar stationarity on bounded measurable probes, exact nonzero Haar L2 kinetic channels and orthogonality, full local gauge identities, an actual stationary kinetic lag obstruction, and a literal spatial exponential supersolution on that same operator. OPEN: reversible quadratic-form/closed-L2 realization needed for the variational comparison, center-parity control and odd trial reconstruction with finite exponential error, vacuum normalization/existence or a valid substitute, and the claimed increase of a normalized stationary eigenvalue ratio. Checkpoint1674's second-derivative formula remains CONDITIONAL.

NEXT: use these exact common-operator inputs for the bounded odd-sector Rayleigh test and a rigorous positive comparison bound, rather than adding unrelated gauge infrastructure. Coupling-dependent iteration still requires quantitative bounds on the spatially weighted operator and a physically justified distance scale. Homogeneous four-dimensional interactions, volume/scale-uniform control and continuum/infinite-volume limits remain open. Yang-Mills stays ACTIVE; Bakry stays PAUSED; every later priority is unchanged.

### Full verification and integrity

Final complete root build passed6928 jobs in43.9784092 seconds. Complete transitive axiom audit passed53303 declarations in48.4839914 seconds, allowing only propext, Classical.choice and Quot.sound. All62 unabridged public types,44 theorem proofs,16 definitions/abbreviations and two public instances were reviewed, together with seven private helper theorems and four private topology/measure instances. All16 independent Lean checks passed. The append rewrite orientation was repaired and proved finite-product instances were cached; no recursion/heartbeat increase, new axiom, trust/toolchain change, sorry, admit or error suppression was used.

Source integrity passed2748 Foundation/root Lean files with exactly three intended mathematical source changes/additions since approved1676. All three pinned configurations,113 baseline manuscripts and21 Yang-Mills originals are unchanged. Evidence remains under C:/Users/ramir/AppData/Local/Temp/stardust-ym-1677-*, including full-build/audit logs, all public types, independent Lean checks, exact/numerical diagnostics and the working-checkpoint manifest. Exact Git approval and guarded PUBLIC main/research synchronization are separate closure receipts; this pre-commit entry does not claim remote synchronization before verification.

## Checkpoint1678 — reversible forms and an exact scalar reduction of the spatial trial (October28,2026)

### Concrete bottleneck attacked

Checkpoint1677 put the kinetic channels and vacuum supersolution on one actual seven-link Markov operator, but the proposed local spectral comparison still lacked an integrated form bound and a controlled trial quotient. This checkpoint proves the bounded-core reversibility and positive form comparison, then makes an exact inverse-half-weight reduction. The resulting numerator is polynomial and its positive denominator is a SINGLE Haar radial integral. No analytic eigenbranch, stationary vacuum existence or normalized spectral gap is assumed.

### An actual reversible quadratic-form upper certificate

`Foundation/SU2SevenLinkVariational.lean` proves inversion invariance of the genuine sevenfold Wilson noise. `pairing_symmetric` proves reversibility on bounded measurable functions by actual product-measure Fubini, Haar translation and noise inversion; it is not a symmetry hypothesis. `pairing_integrable` explicitly proves the outer L1 domain. With pairing(f,g)=E_haar[f K g], integration of a nonnegative square gives

    pairing(u*r,u*r) <= pairing(u*r^2,u)

for bounded measurable u,r and u>=0, with r permitted to be signed. `supersolution_form_bound` then proves that T_t u<=q u for T_t=H_t K H_t implies

    <u*r,T_t(u*r)> <= q ||u*r||_Haar^2.

The domain is exactly the displayed bounded reweighted core. `trialVacuum_form_bound` applies this to the actual verified seven-link vacuum candidate and the SAME q=1+mu t^2+2 C |t|^3, retaining |t|<=1 and the previously proved coefficient-smallness condition. This closes the positive comparison on that core. It does not construct a full closed self-adjoint operator, silently enlarge the domain to every L2 function, or produce a vacuum eigenpair.

### Inverse half weighting removes the nonlinear kinetic numerator

Let X=first plaquette, Y=second plaquette, M=mean channel, Q=residual, H_t=exp(tX/2). `unweight` is exactly H_t^{-1}; `spatialPairing_unweight` proves

    <H_t^{-1} f,T_t H_t^{-1} g>=<f,K g>.

`Foundation/SU2SevenLinkOddTrial.lean` proves the missing actual mixed Haar moments E[YM]=E[YQ]=E[XY^2]=0, and the full three-channel Gram matrix for (Y,M,Q): diagonal(1/4,1/64,3/64). The rates are the actual c^4,c^6,c^6 d. Measurability, boundedness, integrability, Gram integration and evolution of every real linear combination are verified; no abstract vectors with assumed moments were substituted.

For any real correction parameters alpha,gamma and t, put

    g_t=Y+t(alpha M+gamma Q),  f_t=H_t^{-1}g_t.

`unweighted_odd_numerator` proves the exact numerator

    N_beta(t,alpha,gamma)=<f_t,T_t f_t>
      =c^4/4+t^2(c^6 alpha^2+3 c^6 d gamma^2)/64.

There is NO exponential remainder in this numerator. The definition names the intended odd-sector candidate; its center-parity relation to a future normalized vacuum still needs its own proof.

### A genuine positive denominator, and an exact one-variable connection

The actual norm is

    D(t,alpha,gamma)=E_haar[exp(-tX) g_t^2].

`denominator_integrable`, `unweighted_trial_norm`, `denominator_lower_bound` and `denominator_positive` prove existence and D>=exp(-|t|)/4>0 for EVERY real t,alpha,gamma. No vanishing-denominator convention is used. In particular the trial is not vacuous, and these are genuine integral/norm identities rather than a purely formal series.

The conditional right-path calculation is especially useful. With x=h(LU), y=h(U^{-1}R), m=h(LR)/4, one has Q=xy-m and

    g_t=(1+t gamma x)y+t(alpha-gamma)m.

The existing normalized Haar trace covariance gives E_R[y^2]=1/4, E_R[ym]=x/16 and E_R[m^2]=1/64. `denominator_radial` rigorously integrates out the right path and then translates the remaining left path, obtaining

    D=integral exp(-t h(V)) P(t,alpha,gamma,h(V)) dHaar(V),
    P=1/4+t(alpha+3 gamma)x/8
        +t^2[(alpha-gamma)^2+8 gamma(alpha+gamma)x^2]/64.

The exact positive representation `radialPolynomial_squares` is

    P=(1+t(alpha+3 gamma)x/4)^2/4
        +t^2(alpha-gamma)^2(1-x^2)/64.

`radialPolynomial_nonneg` uses the precise half-trace domain |x|<=1. This is a concrete connection from the seven-link spatial variational problem back to the verified one-word Haar tilt/moment machinery. It avoids a new multidimensional stochastic foundation or a Taylor expansion inside the transfer kernel. The classical ingredients and this finite trial reduction are not presented as a novelty claim.

### Independent challenges and unresolved sign

Eighteen independent Lean checks passed across full-noise inversion, bounded reversibility and square comparison, the actual supersolution form domain, exact conjugacy, all Gram entries, actual channel evolution/form, exact numerator, beta-zero normalization, global denominator positivity/nonvacuity, radial formula/squares, mixed moments and both numerator/denominator integral domains.

Independent exact arithmetic checked64 finite Q8 detailed-balance entries,12 signed square/form comparisons,128 conditional right-path degree-two moment cases and12 algebraic candidate-sign cases. The Q8 tests are finite diagnostics, NOT a replacement for actual Wilson or Haar measures. Direct three-variable Haar angular quadrature and the reduced scalar formula agreed in20 cases at EACH of128 and256 radial nodes, including both signs and non-small t. These numerical checks do not enter any Lean proof.

A further diagnostic used the 181-term Haar exponential series with70-digit built-in Decimal arithmetic at beta=1,4,16. With the proposed alpha=1/(1-c^2), gamma=1/(1-c^2 d) and small admitted t, the tested N-c^4 q D values were positive (approximately2.84e-26,1.06e-19,1.57e-18). These tiny signs have NO formal interval/tail certificate and are explicitly UNVERIFIED numerical evidence. Optional mpmath was unavailable; no dependency was installed and no precision change to Lean occurred.

The suggested scalar second coefficient is D2=(alpha^2+3 gamma^2-2 alpha-6 gamma+2)/64. At the proposed corrections the tested coefficient difference N2-c^4 D2-c^4 mu/4 equals (c^4/32) times1674's overlapBracket(c^2,m). The bracket sign already has a rigorous algebraic theorem, but the needed denominator remainder and its connection to an actual local separation are NOT declared proved by these tests.

### Manuscripts and exact next obligations

`ResearchSources/Incoming/block_contraction_spectral_gaps.tex`, SHA256 `0C40FA6B92B830C0E2309BD6471D55CB0EB9BFB94296B9267AD23A5280FA4C60`, was selectively reread at lines338-367. Its H1 operator perturbation and interior Poincare assumptions are not established by this Haar L2 form calculation. Its boundary update, corridor support and physical continuum bridge remain distinct unresolved inputs. All original bytes are unchanged.

PROVED: actual bounded-core reversibility and integrated positive comparison, exact common-operator trial numerator, actual positive norm denominator for all real parameters, exact scalar Haar reduction and its sum-of-squares factor. OPEN: a rigorous scalar error estimate establishing N>c^4 q D in a valid parameter regime; explicit admission of the chosen inverse-weighted trial to the reweighted comparison core; center parity and its relation to a vacuum; completed operator/ground normalization and stationary spectral interpretation; homogeneous four-dimensional, scale/volume-uniform, physical-distance and continuum/infinite-volume requirements. The old normalized eigenbranch derivative remains conditional. No physical mass gap or physical spectral obstruction is claimed.

NEXT: exploit the exact radial polynomial with existing bounded exponential/Taylor and Haar-moment results to prove or refute the local variational separation, rather than build more gauge infrastructure. Keep the proven shrinking-window limitation from1676; a local small-spatial-tilt result cannot be extrapolated to homogeneous large-coupling spatial weighting. Yang-Mills stays ACTIVE, Bakry PAUSED, and the queue is unchanged.

### Verification and integrity

Final full root build passed6930 jobs in27.6517875 seconds. Complete transitive axiom audit passed53369 declarations in51.0134546 seconds, allowing only propext, Classical.choice and Quot.sound. All52 unabridged public types,41 theorem proofs,11 definitions and seven private helper proofs were reviewed. Eighteen independent Lean checks and the exact/numerical diagnostics passed. No sorry, admit, new axiom, recursion/heartbeat/trust/toolchain change or error suppression was introduced.

Source integrity passed2750 Foundation/root Lean files with exactly four intended mathematical source changes/additions since approved1677. All three pinned configurations,113 baseline manuscripts and21 Yang-Mills originals are unchanged. Evidence is under C:/Users/ramir/AppData/Local/Temp/stardust-ym-1678-*, including complete logs/types, the independent Lean harness, numerical/exact JSON and working-checkpoint manifest. Exact Git approval and guarded PUBLIC main/research synchronization are separate closure receipts; this pre-commit entry does not assert remote success before verification.


## Checkpoint1679 — actual spatial variational separation with a nonempty certified interval (October28,2026)

### Discovery and exact scope

The small-spatial-tilt sign question left open at1678 is now resolved positively for the ACTUAL seven-link transfer. This is an integral/form result with a proved nonempty parameter interval, not the old conditional eigenbranch derivative. No ground state or normalized stationary spectrum is postulated. `Foundation/SU2SevenLinkSpatialSeparation.lean` reuses the actual Haar radial denominator, common-operator kinetic channels, bounded exponential remainder and positive vacuum supersolution.

Write c=coefficient(beta), m=secondMoment(beta), d=(4m-1)/3, a=c^4, mu=(1+a)/(8(1-a)), and C=eigenErrorConstant(a,d^4). The actual spatial operator remains T_t=H_t K H_t on the seven-link state, H_t=exp(t X/2). The chosen trial is f_t=H_t^(-1)[Y+t(A M+B Q)], with

    A=1/(1-c^2), B=1/(1-c^2 d).

The numerator N=<f_t,T_t f_t> was proved exactly at1678. Its actual norm D=E_haar[f_t^2] is positive for all real parameters. New `denominator_remainder` proves, for BOTH signs |t|<=1,

    |D-(1/4+t^2 D2)| <= |t|^3 E,
    D2=(A^2+3B^2-2A-6B+2)/64,
    R=(A-B)^2/64+B(A+B)/32,
    E=errorConstant(-(A+3B)/2,B(A+B)/2)/4+2|R|.

All integrability is proved for the actual Haar integrands. The mechanism is the exact radial-polynomial decomposition P=trial(-(A+3B)/2,B(A+B)/2,-t,x)/4+t^2 R. The existing weighted Taylor remainder and |exp(-tx)-1|<=2|t| then give the error before integration. No new Taylor foundation or assumed moment family is substituted.

`leadingGap_positive` identifies the actual leading difference G=N2-a D2-a mu/4 with

    G=(a/32) overlapBracket(c^2,m)>0 whenever c != 0.

The strict sign uses the previously VERIFIED actual Wilson inequalities c^2<=m<1 and |d|<1. This is no longer a numerical sign or an assumed second derivative. The boundary/reset c=0 is excluded explicitly and independent Lean checks prove G(0)=0.

### Nonempty finite-amplitude theorem and shared domain

Let J=E+mu(|D2|+E)+2C(1/4+|D2|+E), K=a J, and S=|linearCoefficient(a)|+|quadraticTrialCoefficient(a,d^4)|. The proof constructs the positive interval

    delta=min(1, min(G/(|K|+1), 1/(2(S+1)))).

For EVERY 0<t<delta, `exists_separation_interval` proves both the existing vacuum-smallness condition and N>a q D, where q=1+mu t^2+2C t^3. `trialVacuum_lower` proves the actual certificate u_t>=exp(-|t|/2)/2. `trial_admissible` constructs r=f_t/u_t, proves measurable boundedness and f_t=u_t r. Thus the lower trial and upper form comparison genuinely share the verified reweighted domain. No unproved L2-domain enlargement is used.

`trial_quotient_upper` applies the actual supersolution form theorem to that r. The resulting `exists_quotient_sandwich` gives a NONEMPTY interval on which

    a q < Rayleigh(T_t,f_t) <= q.

`normalized_trial_separation` proves the explicitly CONDITIONAL scalar bridge: for ANY positive ell<=q, Rayleigh(T_t,f_t)/ell>a under the explicit error smallness condition. It does not manufacture ell as an eigenvalue. These are literal same-operator form inequalities. They settle the finite small-tilt variational comparison; they do NOT yet prove a centered stationary spectral obstruction.

### Independent challenges and failed extrapolations

Ten independent Lean checks passed: negative D2 at A=B=1; its sharp universal lower bound -1/32; reset G=0 and failure of the nonzero-channel premise there; exact zero-tilt quotient c^4; negative-tilt remainder; actual half-trace domain; ratio-domain membership without an extra |t|<=1 premise; actual coefficient positivity; and explicit existence of positive t satisfying the two-sided quotient test.

Independent Fraction arithmetic checked18 moment-admissible parameter pairs, including m=c^2 and near-one values: coefficient identity/sign, the explicit window, vacuum smallness and strict comparison against the upper Taylor norm. These are algebra diagnostics, NOT actual Wilson realizations. Removing m>=c^2 yields a negative bracket at x=1/2,m=0; such parameters are NOT the Wilson law. This rules out casually dropping the moment hypothesis. Independent256-node Haar diagnostics checked108 signed-tilt pointwise/integral remainder cases, including |t|=1 and signed correction coefficients. Ninety-digit181-term Haar exponential series also gave positive margins for actual Wilson parameters beta=1,4,16 at half the constructed delta. Numerical intervals were NOT formally certified; none of these calculations enters the Lean proof.

### Precise research bottleneck, sources and next action

PROVED: actual finite small-tilt form separation, its rigorous cubic remainder, nonempty coupling-dependent interval, same-domain upper bound and conditional normalization implication. OPEN: construct/verify the completed spatial operator and actual positive vacuum normalization; prove the required center parity and trial orthogonality in its stationary transform; identify the resulting stationary spectral/lag obstruction. A quotient by a supersolution certificate alone is NOT the stationary transfer operator. The prior conditional eigenbranch theorem has not been promoted to unconditional spectrum.

This window is NOT uniform in beta;1676's shrinking sufficient-window obstruction remains intact. It does not admit a fixed nonzero spatial amplitude uniformly at large Wilson parameter, establish coupling-dependent contraction over a physical length, or control homogeneous four-dimensional plaquettes. The full spatial interaction, gauge/physical-sector realization, scale/volume-uniform estimates, physical-distance conversion and continuum/infinite-volume limits remain OPEN. The seven-link model must not be substituted for the actual4D lattice theory. No physical mass-gap theorem, no-gap theorem or novelty claim is made.

The retained source is `ResearchSources/Incoming/block_contraction_spectral_gaps.tex`, SHA256 `0C40FA6B92B830C0E2309BD6471D55CB0EB9BFB94296B9267AD23A5280FA4C60`. Its H1 operator-error/interior-Poincare and boundary-update/continuum hypotheses remain unverified here. No manuscript byte changed. Next focus is the actual stationary normalization/parity bridge, using the now rigorous variational input; avoid unrelated gauge-library expansion. Yang-Mills remains ACTIVE, Bakry PAUSED, and all queue priorities are unchanged.

### Verification and checkpoint closure

Full root build passed6931 jobs in41.0040393 seconds. Complete transitive axiom audit passed53402 declarations in39.2080083 seconds, permitting only propext, Classical.choice and Quot.sound. All20 unabridged public types (11 theorem proofs and9 definitions) and all5 private helper proofs were reviewed. Ten independent Lean checks passed in26.075041 seconds; independent arithmetic/numerical diagnostics passed. No sorry/admit/new axiom, error suppression, trust/toolchain or recursion/heartbeat changes were introduced.

Source-integrity verification authenticated the preceding1678 manifest against its exact-commit receipt, then checked2751 Foundation/root Lean sources: exactly the new module plus root import and AxiomAudit changed. All3 pinned configurations,113 baseline manuscripts and21 Yang-Mills originals are unchanged. Evidence is under C:/Users/ramir/AppData/Local/Temp/stardust-ym-1679-* (complete build/audit/types, independent Lean and arithmetic diagnostics, integrity script/manifest). Exact Git approval and guarded PUBLIC main/research synchronization remain separate closure receipts; this pre-commit ledger does not assert remote success before verification.


## Checkpoint1680 — actual conditional stationary ground transform and center-averaged lag obstruction (October28,2026)

### Concrete bottleneck and result

Checkpoint1679 settled the actual seven-link spatial Rayleigh separation, but a quotient divided by a vacuum upper certificate is NOT automatically a stationary spectral statement. This checkpoint identifies and verifies the required bridge for the SAME transfer. It constructs the actual measurable Markov kernel and stationary probability from explicitly supplied, uniformly positive bounded measurable eigenfunction data. It then proves that center parity can be obtained by averaging, without uniqueness or an additional Perron assumption. The remaining local existence input is now precisely isolated rather than silently treated as proved.

`Foundation/SU2SevenLinkGroundTransform.lean` defines `GroundData(beta,t)` with value lam>0, measurable psi, constants 0<lower<=psi(s), |psi(s)|<=upper for EVERY state, and the actual equation T_t psi=lam psi. No inhabitant at nonzero spatial tilt is postulated; this structure is a hypothesis contract, not an existence axiom. The uniform lower bound is essential to the displayed bounded inverse-transform domains. Continuity/compactness has NOT been slipped into the fields as an unverified theorem.

Given such data, all the following constructions and identities are Lean-verified:

    Z=E_haar[psi^2]>0,
    pi(ds)=psi(s)^2/Z haar(ds),
    rho(s,r)=H_t(s)H_t(r)psi(r)/(lam psi(s)),
    P(s,dr)=rho(s,r) transition_beta(s,dr).

Here transition_beta is the ACTUAL seven-link Wilson Markov kernel already constructed at1677, not a formal density with assumed moments. `density_measurable`, `density_integrable` and `density_integral` prove genuine measurable nonnegative unit-mass rows. `kernel_markov` proves the resulting Mathlib Kernel is Markov. `kernel_integral` identifies its integration with T_t(psi f)/(lam psi). The probability pi is constructed using the existing verified positive-density sampler; its positive finite normalizer and probability status are proved.

`stationary_pairing` gives the exact formula

    E_pi[f Pk]=<psi f,T_t(psi k)>_haar/(lam Z).

`kernel_stationary` proves stationarity against EVERY bounded measurable probe and `stationary_reversible` proves the actual reversible pairings on that domain. No reflection-positive physical Hilbert space, full closed L2 spatial operator or eigenvalue-isolation claim follows merely from these identities. No path-space process or continuum quantum field is claimed to have been constructed here.

### Center projection removes an extra hypothesis

`Foundation/SU2SevenLinkParity.lean` uses the actual state transformation multiplying only the first private right-path link D by the nontrivial SU(2) center. It is measurable and involutive, preserves product Haar and the first plaquette X, and negates Y, M, Q and the inverse-half-weighted trial f_t. The actual spatial transfer commutes with this flip by right-convolution associativity and unchanged half weights. Thus the odd sector is preserved by the literal operator, not a postulated parity decomposition.

`trial_orthogonal` proves the Haar pairing with every center-even weight is zero. Its general algebraic Bochner integral identity does not assert L1 membership; the ground-transform application separately proves actual boundedness and L2 membership.

Crucially, `GroundData.evenized` constructs psi_even=(psi+psi o flip)/2. It has the SAME eigenvalue, lower bound and upper bound, remains measurable, satisfies the actual eigenfunction equation, and is center-even by the proved involution. No uniqueness or compact positive-operator theorem is needed for this step. Consequently parity is no longer a separate existence premise of the final local reduction. This center projection is not asserted to perform the full gauge/physical-sector projection.

### Actual centered observable, variance and lag

For phi=f_t/psi, `observable_bound` and `observable_memLp` verify boundedness and the L2 domain under the ACTUAL pi, for every real correction pair A,B. For an even eigenfunction, the actual stationary mean is zero and

    E_pi[phi^2]=D/Z>0,
    E_pi[phi Pphi]=N/(lam Z),
    E_pi[phi Pphi]/E_pi[phi^2]=Rayleigh(T_t,f_t)/lam.

These are genuine probability integrals with a strictly positive denominator, not signed-functional or expectation-only replacements. `value_le_certificate` derives lam<=q from the verified positive supersolution form bound by admitting psi/ trialVacuum to its bounded reweighted core. The eigenvalue upper bound is proved, not added as a GroundData field.

`exists_stationary_obstruction_interval` takes1679's NONEMPTY interval depending only on the actual Wilson coefficients. For every 0<t<delta and EVERY supplied GroundData at that tilt, it constructs the evenized stationary law/kernel and a bounded L2 centered observable with positive variance and

    E_pi[phi Pphi]/E_pi[phi^2] > c^4.

This is a rigorous CONDITIONAL stationary lag obstruction to a proposed c^4 contraction on all centered observables. The Markov law, normalization inequality, parity, centering and domains are discharged. Existence of one uniformly positive bounded measurable eigenfunction at nonzero tilt remains an OPEN Lean obligation. The theorem does not prove a no-gap statement for the physical theory or exclude every contraction q<1.

`GroundData.kinetic` gives an actual nonvacuous instance psi=1,lam=1 at t=0 for EVERY Wilson parameter. `kinetic_kernel` recovers the original actual Wilson transition. Independent checks verify its stationary law integrates as Haar and its trial lag ratio equals c^4 exactly. This does NOT manufacture the nonzero-tilt instance required by the strict comparison.

### Independent challenges, manuscripts and remaining route

Fifteen independent Lean checks passed: actual flip involution, arbitrary signed trial parity, orthogonality against the first plaquette, nonvacuous kinetic kernel/law, density normalization, genuine probability rows, constant-observable noncentering, exact inherited eigenvalue/evenness/equation, positive variance at nonoptimized coefficients, actual first-plaquette stationarity, L2 domain and exact kinetic lag ratio. In particular, an uncentered constant observable has mean1; its large lag cannot be used as a gap obstruction.

Independent exact Fraction tests checked512 noncommuting quaternion center cases. Six numerical Q8 Wilson/path-product ground models checked the tensor-reduced eigenfunction against the full512-state matrix, center commutation/averaging, positive stochastic rows, stationary balance, reversibility, actual trial variance/lag/numerator and the quotient identity. Row normalization and ground normalization gave DIFFERENT stationary probabilities for every tested nonzero tilt, confirming why the former is an invalid substitute. These finite Q8 numerical eigenvectors are NOT continuous SU2 ground-state existence proofs, certified error intervals or Lean inputs. No novelty is claimed for classical ground transforms or center averaging.

The original `ResearchSources/Incoming/block_contraction_spectral_gaps.tex`, SHA256 `0C40FA6B92B830C0E2309BD6471D55CB0EB9BFB94296B9267AD23A5280FA4C60`, was selectively reread at lines459-484. Its reflection-positivity/physical-transfer/vacuum input is an explicit ASSUMPTION; the spectral-measure argument there does not construct those inputs. Our finite Markov construction does not discharge that physical assumption, the earlier H1/interior-Poincare hypothesis, or the continuum bridge. Original bytes remain unchanged.

NEXT LOCAL BOTTLENECK: construct GroundData(beta,t) for the continuous actual SU2 operator at nonzero spatial tilt. The candidate compact strictly-positive kernel route still needs its actual density identification, compact-operator construction and positive eigenfunction theorem with global bounds formally verified. Existing root results supply finite/reset and conditional positive-kernel machinery, not this existence theorem. Investigate this or a genuinely stronger constructive mechanism rather than adding unrelated gauge infrastructure. No existence claim is introduced as an axiom.

Still OPEN independently: the completed stationary L2 spectral interpretation; gauge/physical-sector identification; contraction under coupling-dependent iteration at a PHYSICAL distance scale; homogeneous four-dimensional interactions; volume/scale-uniform estimates; reflection positivity, continuum/infinite-volume limits. The certified small-tilt interval remains nonuniform and1676's shrinking-window limitation remains intact. No fixed nonzero spatial amplitude at large beta, physical mass gap or physical gap obstruction is established. Yang-Mills remains ACTIVE; Bakry PAUSED; every later queue priority is unchanged.

### Verification and closure evidence

Final full root build passed6933 jobs in56.8296195 seconds. Complete transitive axiom audit passed53543 declarations in38.3440946 seconds, permitting only propext, Classical.choice and Quot.sound. All63 unabridged public-type entries were reviewed:53 explicitly declared items (43 theorems,9 definitions,1 structure), plus9 structure fields and its constructor. All43 theorem proofs,9 definitions, structure and all7 private helper proofs were reviewed. Fifteen independent Lean checks passed in34.2420608 seconds; exact/numerical diagnostics passed. No sorry/admit/new axiom, trust/toolchain/recursion/heartbeat change or error suppression was introduced.

Source-integrity verification authenticated1679's manifest against its exact approval receipt, then checked2753 Foundation/root Lean files: exactly the two new modules, root imports and AxiomAudit changed. All3 pinned configurations,113 baseline manuscripts and21 Yang-Mills originals are unchanged. Evidence is under C:/Users/ramir/AppData/Local/Temp/stardust-ym-1680-* (full build/audit/unabridged types, independent Lean and numerical/exact checks, declaration list and source-integrity manifest/script). Git exact approval and guarded PUBLIC main/research remote synchronization remain separate closure receipts; this pre-commit ledger does not report a queued sync as successful.


## Checkpoint1681 — homogeneous spatial weighting breaks the transplanted trial's centering (October28,2026)

### Why this extension test precedes more eigenfunction infrastructure

Checkpoint1680 reduced the one-weight stationary comparison to an explicit uniformly positive bounded eigenfunction input. That nonzero-tilt existence construction remains OPEN; no off-the-shelf positive-kernel existence theorem was found in the inspected verified dependencies, and no external result was added as an axiom. Before building substantial general infrastructure, this checkpoint tests the user's required bridge toward actual lattice spatial weighting. The old centering depends on a private-link flip that preserves X only because Y is absent from the spatial weight. Including both neighboring spatial plaquettes gives a concrete obstruction to that automatic extension.

`Foundation/SU2HomogeneousPlaquetteObstruction.lean` defines

    V=(X+Y)/2, H_t=exp(t V), T_hom(beta,t)=H_t K_beta H_t.

The actual Boltzmann density is exp(t(X+Y)); the normalized potential V is bounded by1 and its tilt parameter is2t. Both plaquettes are weighted equally in space. The temporal Wilson parameter beta is still independent: this is NOT asserted to be the isotropic four-dimensional theory or the physical beta=t diagonal.

### Exact symmetry failure on actual states and operators

`potential_flip` proves that the old right-path center flip changes V to (X-Y)/2. At the flat state1, V=1, while V(flip1)=0. `weight_not_flip_invariant` therefore proves failure of that symmetry for EVERY nonzero signed spatial tilt. This pointwise spatial-weight obstruction does not depend on a temporal parameter.

At the actual Wilson reset beta=0, `noise_zero` and `kinetic_reset` prove that the SAME continuous SU2 seven-link noise is product Haar and K_0 is Haar averaging. These are actual measure identities, not finite-group diagnostics. `homogeneous_reset` identifies the new transfer exactly with the existing verified rank-one reset machinery. `homogeneous_not_flip_commuting` then gives an actual operator counterexample on the constant probe1: T_hom(0,t)1(flip1) != T_hom(0,t)1(1), for every t!=0. Thus one cannot merely reuse1680's commuting center projection for the new weight.

### Fully realized homogeneous reset vacuum, probability and noncentering

The existing verified reset ground transform supplies the actual ground H_t, normalizer Z=E_haar exp(t(X+Y))>0 and stationary probability

    pi_t(ds)=exp(t(X+Y))/Z haar(ds).

`ground_transform` and `ground_transform_kernel` identify the actual ground-normalized transfer with the genuine constant Markov kernel P_t(s,dr)=pi_t(dr). Probability and Markov status are proved; vacuum existence is NOT a hypothesis for this reset counterexample.

`rightMean_derivative` proves that the actual stationary mean of Y has derivative1/4 at zero, with value0 there. Hence `positive_rightMean_near_zero` supplies arbitrarily small positive spatial tilts with nonzero mean. The factor2 in the normalized-potential parameter is explicitly checked.

More decisively, take the ACTUAL old one-weight variational family

    f_t=exp(-tX/2)[Y+t(A M+B Q)].

`oldTrialOverlap_formula` proves its exact pairing with the NEW homogeneous vacuum as the sum of genuine Haar weighted integrals:

    O_AB(t)=E_haar[f_t H_t]
      = weighted(Y,Y,t/2)+t A weighted(Y,M,t/2)+t B weighted(Y,Q,t/2).

Every integral has a verified bounded measurable L1 domain. Existing actual Haar moments give O_AB(0)=0 and, for EVERY FIXED real correction pair A,B,

    O_AB'(0)=1/8.

Thus `oldTrial_not_centered_near_zero` proves positive vacuum overlap at arbitrarily small positive t. `oldObservable=f_t/H_t` is measurably bounded by exp(3|t|/2) times the original finite coefficient bound, and `oldObservable_memLp` proves its ACTUAL L2(pi_t) domain. `oldObservable_mean` proves E_pi[oldObservable]=O_AB(t)/Z. `positive_oldObservable_mean_near_zero` is therefore a genuine stationary noncentering counterexample, not a default-zero integral or a failure only at symbolic coefficients. The two old correction channels with fixed real coefficients do not remove this first-order contamination. No statement about arbitrary singular t-dependent correction coefficients is claimed.

### Apparent lag versus genuine centered correlation

`reset_lag` proves E_pi[f P_t f]=(E_pi f)^2. For the transplanted old trial, this is positive at the just-proved small tilts. Nevertheless `centered_reset_lag_zero` proves ZERO one-step lag for EVERY correctly centered integrable observable in the SAME actual stationary model. The independent Lean harness supplies the old trial's L1 domain and explicitly derives both its positive uncentered lag and zero centered lag.

This is a sharp false-positive test for transporting an uncentered Rayleigh signal into a spectral claim. It does not contradict1679/1680: their spatial weight includes X alone, and their strict comparison explicitly excludes c=0. It does not prove failure of all homogeneous-sector variational tests, failure at large temporal beta, a physical gap, or a no-gap theorem. The reset example is anisotropic when t!=0. The one-weight nonzero-temporal-coupling vacuum input and the full homogeneous/isotropic4D bridge remain separate OPEN obligations.

### Independent challenges and possible replacement route

Fourteen independent Lean checks passed: flat-state potential values, both tilt signs, actual continuous-Haar reset, actual transfer noncommutation, correctly normalized1/4 response, correction-independent1/8 overlap derivative, actual positive means in every positive tolerance, L2 and L1 domains, true probability rows, exact ground-kernel integration, zero centered old-trial lag and a positive uncentered old-trial lag.

Independent actual-Haar angular diagnostics checked36 combinations of signed t and signed A,B at EACH of96 and192 radial nodes, with the relative imaginary-axis angle integrated separately. They agreed on noncentering, the exact overlap/mean relation, positive uncentered lag and vanishing centered reset lag. Eighty-digit181-term one-word Haar series checked three shrinking tilt scales, with old mean/t tending numerically to1/8 and right mean/t to1/4. None of these quadratures/series is a certified truncation interval or a Lean input.

A candidate replacement is the plaquette-exchange antisymmetric observable Y-X, whose symmetry is compatible with equal spatial weights. An independent second-coefficient TEST for the trial Delta+t A(Y^2-X^2) gives the candidate optimized expression

    G_exchange=a^2/[8(a-r)]-a/16-a(1+a)/[8(1-a)],
    a=c^4, r=d^4, A=a/(a-r).

Twelve exact Fraction tests under0<a<1 and0<=r<=a^2 gave NEGATIVE values. Actual Wilson coefficient diagnostics at beta=1,4,16 also gave negative candidate values, approximately-0.0002105,-0.02069,-0.3078. The r<=a^2 inequality, the proposed second-coefficient reduction and its actual stationary interpretation have NOT been verified in Lean; this is a challenged candidate, not a theorem or proof that all exchange-sector reconstructions fail. Preserve it as a warning against assuming the old inflation mechanism survives a natural symmetry repair. The Haar diagnostic also suggests a stronger all-A,B exact overlap reduction to a one-word moment; only the stated weighted formula and derivative are formally established here.

### Manuscript connection, next bottleneck and campaign scope

The original `ResearchSources/Incoming/block_contraction_spectral_gaps.tex`, SHA256 `0C40FA6B92B830C0E2309BD6471D55CB0EB9BFB94296B9267AD23A5280FA4C60`, was selectively reread at lines606-638. Its Wilson-action application, plaquette-incidence, corridor convexity and reflection-positivity claims are not discharged by this seven-link calculation. Equal spatial weighting reveals a missing centering/symmetry bridge; the actual isotropic4D operator, physical-sector projection, scale/volume-uniform estimates, physical-distance conversion and continuum/infinite-volume limits remain OPEN. Original manuscript bytes are unchanged. No novelty is claimed for classical reset/tilt ingredients or general symmetry facts.

NEXT: retain the verified local one-weight comparison and its exact missing eigenfunction input, but test corrected centering and actual spatial interactions before interpreting its slowing as physical spectral evidence. A constructive eigenfunction route or compact positive-kernel route still requires actual realization and bounds; do not simply assume it. Investigate exchange/orthogonal-projection repairs against the above negative candidate tests rather than repeating the invalid center-flip transfer. Coupling-dependent iteration remains a separate question requiring a justified PHYSICAL length scale. Yang-Mills stays ACTIVE, Bakry PAUSED, and all later priorities are unchanged.

### Verification and closure evidence

Full root build passed6934 jobs in27.7348009 seconds. Complete transitive axiom audit passed53594 declarations in39.7700531 seconds, permitting only propext, Classical.choice and Quot.sound. All37 unabridged public types (29 theorem proofs and8 definitions), all8 private helper proofs and the private Haar-left-invariance instance with its local caches were reviewed. Fourteen independent Lean checks passed in26.2708593 seconds; exact/numerical diagnostics passed. No sorry/admit/new axiom, trust/toolchain/heartbeat/recursion change or error suppression was introduced.

Source integrity authenticated1680's manifest against its exact receipt and checked2754 Foundation/root Lean files: exactly the new module, root import and AxiomAudit changed. All3 pinned configurations,113 baseline manuscripts and21 Yang-Mills originals are unchanged. Evidence is under C:/Users/ramir/AppData/Local/Temp/stardust-ym-1681-* (full build/audit/unabridged types, independent Lean checks, arithmetic/Haar diagnostics, declaration list, integrity script/manifest). Exact Git approval and guarded PUBLIC main/research synchronization are separate closure receipts; this pre-commit ledger does not assert remote success before verification.


## Checkpoint1682 — all-tilt obstruction to the bare homogeneous exchange trial; Jensen normalization floor (October28,2026)

### Strongest natural centering repair tested

Checkpoint1681 showed that the old private-center projection does not survive equal weighting of both spatial plaquettes. This checkpoint tests the natural bare exchange-antisymmetric replacement Delta=Y-X against the ACTUAL homogeneous seven-link transfer. The result is a NONPERTURBATIVE limitation of that specific trial: its spatial Rayleigh quotient never exceeds c^4, and dividing by any uniformly positive bounded homogeneous eigenfunction's eigenvalue cannot restore an increase. This resolves the bare repair without assuming the earlier candidate second-coefficient formula or its unverified Wilson moment inequality. It does NOT rule out corrected exchange trials, all centered observables, a spectral obstruction or a physical mass gap.

The temporal parameter beta and common spatial tilt t remain independent in the finite model. The all-real-parameter statements include the finite equal-parameter diagonal, but this is not an identification with the entire isotropic4D lattice theory.

### Actual joint Haar law, gauge sector and homogeneous centering

`Foundation/SU2HomogeneousExchangeTrial.lean` proves `joint_haar_integral`: for every measurable F bounded on[-1,1]^2, the actual seven-link Haar integral of F(X,Y) equals the product SU2-Haar half-trace integral. The proof uses the verified private-path reduction and actual Haar translations. It does NOT assume independence under the nonzero-temporal-coupling spatial vacuum. `joint_sign_integral` and `joint_swap_integral` prove simultaneous sign reversal and exchange for that actual Haar law, with every Fubini bound displayed.

`delta_gauge` proves invariance of Delta under the full verified six-vertex local gauge action. The independent Lean harness also checks gauge invariance after the actual homogeneous inverse half weight. Actual measurability, |Delta|<=2, E_haar[Delta^2]=1/2 and

    K_beta Delta=c^4 Delta

are proved using existing common-operator channels and Haar moments, with no positive-beta restriction.

`delta_reset_centered` proves E_pi_t[Delta]=0 in the fully realized homogeneous reset law from1681. `inverse_ground_reset_centered` checks the actual observable obtained by dividing the Rayleigh trial by the reset ground too. The independent harness proves its L2 domain under that ACTUAL stationary probability, so this is not a default-zero nonintegrable integral. This repairs centering at reset, unlike the transplanted old trial. General nonzero-temporal-coupling vacuum existence and its exchange/physical-sector identification are not asserted.

### Exact numerator and ALL-TILT norm bound

Retain V=(X+Y)/2, H_t=exp(t V), T_hom=H_t K_beta H_t. The tested trial is

    f_t=H_t^(-1) Delta.

The actual form is identified with E_haar[f T_hom g]. Exact inverse-half-weight cancellation gives

    N=<f_t,T_hom f_t>=c^4/2,
    D=||f_t||_haar^2=E_haar[exp(-t(X+Y)) Delta^2].

`density_square_integrable` and `trial_memLp` prove the actual integral/L2 domains; no formal norm is substituted. `denominator_even` proves D(-t)=D(t) by the joint Haar sign identity. The pointwise elementary inequality exp(z)+exp(-z)>=2, multiplied by Delta^2 and integrated, then gives

    D(t)>=1/2>0 for EVERY real t.

`quotient_le_kinetic` therefore proves

    Rayleigh(T_hom,f_t)=N/D <= c^4

for EVERY real beta and t. There is no small-t window, Taylor truncation, analytic eigenbranch, moment-dominance assumption or assumed vacuum in this theorem. At t=0, the quotient is exactly c^4. The positive one-weight comparison at1679/1680 remains valid for its DIFFERENT weight/trial; no earlier result has been erased or strengthened by reinterpretation.

### The needed homogeneous eigenvalue floor is proved, not assumed

`Foundation/SU2HomogeneousEigenvalueFloor.lean` proves `eigenvalue_ge_one` for any explicitly supplied measurable psi with global0<l<=psi<=u, positive lam, and the ACTUAL equation T_hom psi=lam psi. It constructs no eigenfunction and introduces no existence axiom.

The proof sets q=t V+log psi. Global bounds justify every logarithmic, exponential and kinetic integral. Mathlib's existing exponential Jensen integral theorem gives, pointwise,

    K_beta q <= log(lam)+q-2t V.

Actual Haar stationarity of K_beta and E_haar[V]=0 then imply log(lam)>=0, hence lam>=1. The normalization bound is derived from the displayed operator equation; no spectral-radius, compactness or uniqueness hypothesis is concealed. This reuses the same verified Jensen infrastructure already present in the entropy developments, but it is a PRESSURE/NORMALIZATION bound, not a quantum mass-gap estimate.

`bare_normalized_no_inflation` combines this with the exact trial estimate:

    Rayleigh(T_hom,f_t)/lam <= c^4.

Thus even an existing positive bounded eigenfunction cannot turn the bare exchange trial into the old upward-ratio witness. Existence remains an open Lean input at nonzero temporal coupling. The independent harness supplies a NONVACUOUS application at beta=0 with arbitrary spatial t, using the already constructed reset ground H_t and its actual partition eigenvalue. It also derives that partition>=1 from the theorem.

### Independent challenges and scope of the failed route

Fifteen independent Lean checks passed: actual joint mixed fourth moment1/16; full finite gauge invariance; exact numerator; zero-tilt norm and quotient; all-tilt norm bound; actual Haar trial L2 domain; both homogeneous reset centering identities; exact tilt evenness; unrestricted-beta quotient bound; exclusion of lam<1 under the stated actual eigenfunction equation; full inverse-weight gauge invariance; a concrete reset ground as an eigenvalue-floor instance; and actual inverse-ground L2 membership under its stationary law.

Independent continuous-Haar angular quadrature checked seven signed tilts at EACH of96/192 nodes: norm lower bound/evenness and exchange centering. Six80-digit181-term Haar-series diagnostics agreed with the norm identity2(Z Z''-(Z')^2), without claiming formally certified truncation intervals. Fifteen finite noncommutative Q8 homogeneous-kernel cases checked kinetic Delta evolution, exact numerator, positive norm, positive top eigenfunction, eigenvalue floor, raw and normalized trial bounds and actual normalized pairing identities. These finite eigenvectors are NOT continuous-SU2 vacuum constructions or Lean proof inputs.

Two exact rational challenges show why the Jensen hypotheses matter in a broader inference. A biased two-state reset with weights19/20,1/20 and H=(1/2,2) has positive eigenvalue7/16<1, despite zero uniform-reference mean log H; that kernel is NOT stationary for the uniform reference. A stationary reset with constant H=1/2 has eigenvalue1/4<1, but its log-potential does NOT have mean zero. These do not refute the actual SU2 theorem, whose stationarity and mean-zero hypotheses are proved.

This checkpoint closes the BARE exchange-inflation attempt. The degree-two corrected candidate and its unverified coefficient reduction/Wilson r<=a^2 inequality from1681 remain OPEN; failure of the bare witness does not establish their impossibility. Do not repeat the bare route without a genuinely different mechanism. Construction of actual nonzero-temporal-coupling positive eigenfunctions, a full completed stationary spectral interpretation, corrected/exchange-sector centering and physical-sector identification remain OPEN. Coupling-dependent iteration at a PHYSICAL distance, homogeneous4D interactions, scale/volume-uniform bounds and continuum/infinite-volume limits are not supplied by these finite inequalities. In particular, an upper bound on one trial quotient is not an upper bound on the entire centered spectrum or a uniform mass gap.

### Source connection, campaign state and verification

The original `ResearchSources/Incoming/block_contraction_spectral_gaps.tex`, SHA256 `0C40FA6B92B830C0E2309BD6471D55CB0EB9BFB94296B9267AD23A5280FA4C60`, was selectively reread at lines459-484. Its spectral-measure argument requires actual centered correlations in the reflection-positive physical Hilbert space. Correcting one finite trial's centering does not provide its claimed clustering or physical transfer hypotheses. Original bytes are unchanged. Classical Haar/Jensen ingredients and this finite test are not presented as a novelty claim. Yang-Mills remains ACTIVE, Bakry PAUSED, and all later queue priorities remain unchanged.

Full root build passed6936 jobs in25.4857846 seconds. Complete transitive axiom audit passed53633 declarations in38.7034265 seconds, permitting only propext, Classical.choice and Quot.sound. All30 unabridged public types (25 theorem proofs and5 definitions) and all4 private helper proofs were reviewed. Fifteen final independent Lean checks passed in30.3433097 seconds; exact/numerical diagnostics passed. The extra final harness check resolved the actual inverse-ground L2-domain concern; mathematical sources were unchanged. No sorry/admit/new axiom, toolchain/trust/heartbeat/recursion change or error suppression was introduced.

Source integrity authenticated1681's manifest against its exact receipt and checked2756 Foundation/root Lean files: exactly the two new modules, root imports and AxiomAudit changed. All3 pinned configurations,113 baseline manuscripts and21 Yang-Mills originals are unchanged. Evidence is under C:/Users/ramir/AppData/Local/Temp/stardust-ym-1682-* (full build/audit/unabridged types, independent Lean and arithmetic/numerical checks, declaration list and integrity script/manifest). Exact Git approval and guarded PUBLIC main/research synchronization remain separate closure receipts; this pre-commit ledger does not claim a queued push succeeded.


## Checkpoint1683 — stationary slow-mode persistence and a necessary physical-distance iteration budget (October28,2026)

### Research question and exact reuse

The active question is whether coupling-dependent iteration actually overcomes the verified stationary spectral slowing, and whether a recovered contraction has a justified physical distance. The theorem-level audit found that `SU2SignBottleneck.exponential_variational_obstruction` ALREADY supplies an actual centered stationary L2 sign vector with positive variance and exponentially small one-step Dirichlet quotient. Re-proving the sign cut, trace-zero nullity, generic covariance saturation or auxiliary positivity infrastructure would not address the missing iteration question. This checkpoint reuses that vector, its exact stationary law, and `SU2VariationalGap.operator_contraction`/`operator_symmetric`/`operator_kernel_pairing` directly.

New module: `Foundation/SU2SlowModeIteration.lean`. Its P_r is the EXISTING actual stationary loop operator on L2(equilibriumLaw r), constructed from the actual edge measure and identified with the row-normalized loop kernel in pairings. `steps r n f` is repeated application of that bounded operator. No new kernel, vacuum, signed functional, probability axiom or abstract spectral replacement is introduced. The resulting normalizedLag is the stationary TRANSFER-OPERATOR pairing divided by the actual sign variance; no new theorem identifying it with the separate `stationaryLagLaw r n` integral is claimed here.

### Proved iteration obstruction

For every real r, every f in the actual stationary L2 space and EVERY natural n, including odd n:

    <P_r^n f,f> >= ||f||^2 - n <(I-P_r)f,f>.
    <P_r^n f,f> <= ||f||^2.

The proof uses reversibility and contraction, NOT a nonnegative-spectrum assumption or a spectral theorem. The one-step Dirichlet form decreases under P; even/odd iterations are controlled using symmetry and squared norms. These Hilbert-space ingredients are classical; their verified application to the existing loop bottleneck is the research content, not a novelty claim for a general operator inequality.

Combining with the existing sign theorem, there is c>0 such that for all sufficiently large r, the actual sign vector v_r is centered, ||v_r||^2>0 and SIMULTANEOUSLY FOR EVERY n:

    1 - c n exp(-r/2) <= normalizedLag(r,n) <= 1.

Consequently, any sign-covariance contraction normalizedLag(r,n)<=q requires

    (1-q) exp(r/2) <= c n.

The stronger norm target ||P_r^n v_r||<=q||v_r|| pays the same necessary budget. Positivity of the variance and the actual one-step energy estimate are explicit hypotheses in these pointwise theorems and are supplied eventually by the reused sign theorem. Neither normalization nor actual process/operator identification is an implicit extra axiom.

For ANY clock n(r) satisfying n(r)exp(-r/2)->0, `slow_clock_persistence` proves normalizedLag(r,n(r))->1. This is an obstruction to recovering fixed contraction by a sub-exponential-in-this-sense number of steps; merely saying that enough iterations mix at each fixed coupling does not provide a uniform distance estimate.

### Conditional physical-scale test; what remains open

For a PROPOSED spacing a(r)=exp(-kappa r), kappa<1/2, and ANY clock with eventually n(r)a(r)<=L, `bounded_physical_distance_persistence` proves normalizedLag(r,n(r))->1. `no_bounded_distance_contraction` excludes every eventual fixed q<1 along such a clock. For a physically shrinking spacing, the relevant subcase is 0<kappa<1/2. Lean also permits the mathematically valid kappa<=0 cases. The estimate uses a STRICT upper bound on kappa and gives no endpoint theorem, no sharp threshold, and no claim that this is the actual Yang--Mills coupling/spacing relation.

Compare the retained POSITIVE result `SU2CouplingIteration.sufficient_step_count`: roughly 2 t exp(4|r|) steps suffice for the verified Doeblin event bound. The necessary exp(r/2) and sufficient exp(4r) estimates leave a large gap; no optimal mixing asymptotic is asserted, and event bounds and L2 norm bounds are not silently equated. Fixed-r eventual mixing and this changing-r obstruction are compatible. Coupling-dependent iteration can restore contraction in the loop model, but its physical usefulness still requires a justified scale relation and the appropriate correlation/operator topology.

The actual4D extension remains OPEN. In particular one must construct/identify the genuine gauge-invariant stationary physical transfer and its vacuum normalization, a suitable centered observable, scale/volume-uniform estimates, and a justified coupling/lattice-spacing map. The r of this trace-product loop kernel has not been identified with the Wilson temporal coupling or a renormalized4D scale. `SU2WilsonSignCrossing.no_positive_crossing_barrier` and its open-link gauge counterexample already obstruct the naive transfer of this sign barrier to temporal Wilson links. They are preserved; no new positive barrier is assumed. Checkpoint1682's homogeneous bare-exchange limitation and nonzero-temporal-coupling ground-state existence/domain obligations also remain intact. No result here proves or disproves a4D physical mass gap.

### Independent attempts to break the argument

Twelve independent Lean checks passed: exact zero/two-step definitions; unit normalized zero-lag at positive variance; exact one-step equality; odd three-step lower bound; an upper-bound instance at negative coupling; actual sign centering; fixed iteration-count persistence; a nonzero kappa=1/4 bounded-distance instance; exclusion of q=1/2 along that clock; a norm-contraction cost; and the zero-step/positive-variance normalization obstruction.

Independent continuous SU2 Haar angular quadrature constructed the actual normalized trace-product kernel at r=0,1,4,8,16,32, using BOTH96 and192 nodes with integration split at the sign boundary. It checked row normalization, stationary law, sign centering, the lower/upper bounds at129 iteration counts per case, and clocks floor(exp(r/4)). Representative near-unit-distance normalized lags were0.8173444152 at r=8,0.9966201125 at r=16 and0.9999998787 at r=32. These are diagnostics, not interval-certified asymptotics or Lean inputs. An initial unsplit quadrature failed the requested cross-resolution tolerance because the sign observable is discontinuous; the split angular quadrature resolved that diagnostic failure without changing mathematical sources or tolerances.

An EXACT rational six-cycle counterexample tests removal of reversibility: for f=(2,1,-1,-2,-1,1), the stationary lag pairings are2,1,-1 at n=0,1,2, so the proposed n-step bound fails at n=2 despite norm contraction and stationarity. Seventeen exact checks on the reversible two-state flip (eigenvalue -1) confirm that a positive-spectrum assumption is unnecessary. Four two-state critical-clock diagnostics, with one-step deficit exp(-r/2) and n=ceil(exp(r/2)), approach lag exp(-1), not1. Thus the small-clock hypothesis cannot be discarded from a general bottleneck inference. This is not a counterexample to the unproved SU2 kappa=1/2 endpoint.

### Complete verification and campaign state

Full root build passed6937 jobs in40.6400273 seconds. Complete transitive axiom audit passed53662 declarations in39.0564997 seconds, permitting only propext, Classical.choice and Quot.sound. All17 unabridged public types (14 theorem proofs and3 definitions) and all4 private helper proofs were reviewed. Twelve final independent Lean checks passed cleanly in27.0081266 seconds; the earlier successful harness was cleaned of nonfatal tactic diagnostics, without changing mathematical sources. Exact/numerical diagnostics passed. No sorry/admit/new axiom, altered theorem hypothesis, toolchain/trust/resource/heartbeat change or suppressed check was introduced.

Integrity authenticated1682's source manifest against its exact approval receipt and checked2757 Foundation/root Lean files: exactly the new module, root import and AxiomAudit changed. All3 pinned configuration files,113 baseline manuscripts and21 Yang--Mills originals are unchanged. No ResearchSources byte was modified or staged. Evidence is under C:/Users/ramir/AppData/Local/Temp/stardust-ym-1683-* (full build, complete audit/unabridged types, final independent Lean harness, exact/numerical checks, declaration list and authenticated integrity script/manifest).

Yang--Mills remains ACTIVE, Bakry PAUSED, and the campaign queue is unchanged. The next bottleneck is a genuine homogeneous physical-sector/scale bridge or a sharp obstruction to one, rather than routine replication of the one-step loop audit. Exact Git approval and guarded PUBLIC main/research synchronization are separate closure receipts; this pre-commit ledger does not claim remote backup success.


## Checkpoint1684 — central-band two-step reset improves the loop iteration scale; explicit Wilson mismatch (October28,2026)

### Mathematical bottleneck and the tested mechanism

Checkpoint1683 proved that the actual stationary loop slow mode cannot be contracted by a clock n(r) with n(r)exp(-r/2)->0. The retained sufficient reset estimate required roughly exp(4r) original transitions. This checkpoint investigates a specific way to narrow that gap, rather than adding classical spectral auxiliary results or assuming a physical vacuum: pass through a small central trace band, where the trace-product loop's outgoing interaction becomes nearly unbiased.

New module: `Foundation/SU2ZeroTraceBridge.lean`. It reuses the actual normalized `SU2InteractingLoopKernel.loopKernel`, its partition bound and probability proof, the existing explicit quaternion/SU2 zero-trace state from `SU2WilsonSignCrossing`, actual kernel composition and bounded-integral machinery. No manuscript byte, mathematical axiom, pinned configuration or previous theorem is changed. Haar open-set positivity supplies the central band's strictly positive measure; no unproved trace-density formula is used by Lean.

### Proved actual two-step measure bound

Let h be the half trace, B_delta={C: |h(C)|<delta}, b_delta=Haar(B_delta). For EVERY delta>0, b_delta>0. At every nonnegative r:

    k_r(C,Z) >= exp(-(1+delta)r)       for Z in B_delta,
    k_r(Z,D) >= exp(-2 delta r)        for Z in B_delta.

These are bounds on the EXISTING actual normalized transition density. Integrating the intermediate state over B_delta gives the genuine MEASURE inequality

    (K_r composed K_r)(C, .) >= b_delta exp(-(1+3delta)r) Haar(.).

It holds for every starting C and every measurable event; no matrix surrogate, hypothetical two-step density, stationarity of Haar, spectral completeness or vacuum existence premise is used. `reset_rate_near_one` packages the consequence: for EVERY fixed eta>0 there is b>0 such that the two-step Haar reset coefficient is at least b exp(-(1+eta)r). The prefactor depends on eta. No eta=0 theorem or eta-uniform prefactor is claimed.

### Proved contraction for actual iterates and its proposed distance

Set rho=b_delta exp(-(1+3delta)r)/2; Lean proves0<rho<1. Halving avoids a zero residual at an endpoint. `twoAverage` integrates against the actual composed probability kernel, and `twoAverage_eq_transfer_twice` identifies it with TWO applications of the previously verified pointwise transfer for every measurable f valued in[0,1]. The recursive `iterate r n f` therefore uses2n original transitions.

The residual range estimate compares the actual composed measure with rho Haar and applies the same comparison to1-f. It never calls Haar the equilibrium law. For every such f, every C,D and every n:

    |K_r^(2n)f(C)-K_r^(2n)f(D)| <= (1-rho)^n <= exp(-n rho).

Measurability, probability normalization, all required bounded-integral domains and range bounds are proved. In particular all measurable-event indicators are admitted; smoothness or polynomiality is unnecessary. These are actual pointwise bounded-observable/oscillation estimates, not a new theorem about the complete centered L2 spectrum or the separate stationaryLagLaw representation.

`iterate_exponential_bound` gives error<=exp(-t) whenever t<=n rho. `sufficient_pair_count` proves that

    n >= (2t/b_delta) exp((1+3delta)r)

is sufficient (n COUNTS PAIRS; original transitions are2n). Thus the proved sufficient coupling exponent improves from4 to any fixed number greater than1, with an explicit positive band-mass prefactor. The necessary exp(r/2) scale from1683 remains valid; the optimal exponent and polynomial prefactors remain OPEN.

For the explicitly PROPOSED spacing a_delta(r)=exp(-(1+3delta)r), `proposed_distance_oscillation` proves

    oscillation <= exp(-(b_delta/4) * (2n a_delta(r))).

This is a precise positive scale-dependent estimate in the loop model. It does NOT justify that spacing physically. Contrast1683: its persistence theorem concerns a different proposed spacing exp(-kappa r), kappa<1/2. There is no contradiction, and neither estimate proves an actual4D coupling/spacing map or a physical mass gap.

### Rigorous failure of the unchanged Wilson extension

The central band's mechanism is tied to the trace-PRODUCT interaction r h(C)h(D). `zero_trace_row` proves that h(C)=0 makes its row EXACTLY Haar at every r. This fact is false for the actual one-word Wilson row already constructed in the library.

`wilson_relative_mean` proves for EVERY current C that the actual Wilson row `SU2OneWordTransfer.transition law beta C^{-1}` has relative-holonomy mean

    integral h(C^{-1}D) dW_beta(C,D) = c(beta),

where c(beta) is the existing actual Wilson increment coefficient, with verified c(beta)->1. Haar has relative mean0 by exact left invariance and the verified Haar moment. Therefore `zero_trace_wilson_mismatch` constructs, for all sufficiently large beta, an actual zero-trace C whose loop row is Haar while its Wilson row is NOT Haar. The independent Lean harness also verifies that the relative holonomy test is invariant under a COMMON endpoint transformation (C,D)->(g C h^{-1},g D h^{-1}). This is not an assertion about every gauge constraint of the full4D theory.

This counterexample blocks identifying the trace-product central-band reset with an unchanged Wilson mechanism. It does NOT exclude every Wilson minorization or alternative multiscale bridge. A gauge-compatible4D stationary transfer, actual ground-state/physical-sector identification, volume/scale-uniform controls and a justified physical spacing remain OPEN. Existing Wilson sign-crossing, seven-link homogeneous centering and bare-exchange obstructions remain preserved; no provisional Yang--Mills existence statement is introduced as an axiom.

### Independent challenges, complete verification and campaign state

Sixteen independent Lean checks passed: empty-band obstruction; positive concrete band mass; explicit trace-zero SU2 membership; actual zero-trace Haar row; actual two-step measure minorization; strict reset range; a concrete near-one exponent; zero-pair identity; one-pair identification with two actual transfers; constant preservation; discontinuous measurable-event oscillation; a sufficient pair count yielding exp(-1); the proposed distance formula with correct2n factor; common-endpoint gauge covariance of the relative test; the actual Wilson relative moment; and an eventual nonvacuous loop/Wilson row mismatch.

Independent Haar quadrature tested18 (r,delta) cases at BOTH96/192 nodes: r=0,1,4,8,16,32 and delta=.05,.2,.5. It checked the actual density formulas, a split-band arrival integral, two-step minorization on finite quadrature grids and a common41-point source/target grid, and four unit probes through33 pair-iteration counts. An initial refinement comparison used minima over DIFFERENT node grids; replacing the comparison points with the same41 fixed points resolved that diagnostic failure without weakening its tolerance or changing mathematical sources. These finite quadrature matrices are diagnostics, not interval-certified continuous results or Lean proof inputs. Four independent Wilson relative moments were approximately.24019,.65805,.90781,.95350 at beta=1,4,16,32; zero-trace Haar transport would instead give0. A negative-coupling test refutes dropping the displayed r>=0 hypothesis from the directional density bounds; the delta=0 test confirms that an empty band provides no positive reset.

Full root build passed6938 jobs in41.1388823 seconds. Complete transitive axiom audit passed53711 declarations in41.983071 seconds, permitting only propext, Classical.choice and Quot.sound. All28 unabridged public types (23 theorem proofs and5 definitions) and all7 private helper proofs were reviewed. Sixteen final independent Lean checks passed cleanly in26.414989 seconds. A formatting-induced parse failure in an intermediate full build was repaired; the complete final build/audit passed with unchanged verification settings. No sorry/admit/new axiom, altered old theorem, version/trust/resource/heartbeat/recursion change or suppressed check was introduced.

Integrity authenticated1683's source manifest against its exact approval receipt and checked2758 Foundation/root Lean files: exactly the new module, root import and AxiomAudit changed. All3 pinned configuration files,113 baseline manuscripts and21 Yang--Mills originals are unchanged. Evidence is under C:/Users/ramir/AppData/Local/Temp/stardust-ym-1684-* (full build, complete audit/unabridged types, independent Lean and quadrature checks, declaration list and authenticated integrity script/manifest). The Doeblin/range ingredients are classical; no literature novelty claim is asserted for them or for this finite-model application.

Yang--Mills remains ACTIVE and Bakry PAUSED; the queue is unchanged. The positive loop estimate and the Wilson mismatch narrow the useful next question to a genuine physical transfer/scale bridge or its obstruction. Merely shrinking a band or choosing a convenient spacing does not answer that question. Exact Git approval and guarded PUBLIC main/research synchronization remain separate closure receipts; this pre-commit record does not claim remote success.


## Checkpoint1685 — constructed homogeneous periodic Wilson ground state and a centered gauge-invariant covariance counterexample (October28,2026)

### Discovery question and change of mechanism

The active bottleneck is spatial weighting AFTER actual gauge projection and ground normalization. The earlier finite counterexample1675 used an anisotropic open shared-plaquette graph; the homogeneous seven-link exchange test1682 did not produce its hoped-for upward ratio. The audit also confirmed that the volume-diverging cross-ratio witness in `YMPositiveKernel` is explicitly UNPROJECTED, while verified tree reduction can remove gauge modes entirely. None of those facts establishes the actual spatially weighted physical gap. Repeating the trace-product loop analysis would not answer this question.

A new independent test used a nondegenerate spatial2-by-2 periodic Z2 lattice, with ALL temporal and spatial Wilson couplings equal. It found normalized centered spectral ratios about.04371,.44872,.94802 at link means.2,.5,.8, compared with the corresponding bare diagnostic ratios.04,.25,.64. These numerical results motivated an exact construction at beta=(log3)/2, NOT an assumed eigenfunction or a claimed SU2/4D result. Sympy was unavailable; the subsequent characteristic polynomial and adjugate were derived by exact Fraction arithmetic, then proved algebraically in Lean. Floating eigenvectors are never proof inputs.

The resulting verified modules are `FiniteWilsonTorusGround`, `FiniteWilsonTorusKernel`, `FiniteWilsonTorusNoise`, `FiniteWilsonTorusStationary` and `FiniteWilsonTorusProbe`. They serve this one finite homogeneous comparison test. They do not construct a general gauge-theory library or import provisional Yang--Mills existence as an axiom.

### Exact microscopic provenance and gauge sector

Vertices are(x,y) in{0,1}^2; the eight oriented positive-direction edges are ordered(x,y,d), d=0,1, with periodic endpoints. The four elementary plaquette bit masks are39,141,114,216, and the two winding masks are17 and10. Three independent plaquettes plus the two windings give32 labels for256 link configurations. Four local vertex flip masks are27,78,177,228; the fourth is the xor of the first three, and the global common Z2 gauge element acts trivially. These incidence/cubical interpretations were independently checked on the explicit graph; Lean's exact objects are the displayed bit masks and finite functions, not a general cubical-complex formalization.

Every temporal link has same/flip probabilities3/4,1/4. `microscopic_count_certificate`, `microscopic_total` and `index_bijective` verify every quotient count, normalization65536=4^8, and complete16-by-16 enumeration. All links use the SAME beta, with `temporal_odds` proving exp(2 beta)=3. `amplitude_wilson_form` proves the literal homogeneous spatial half weight

    h(label(u)) = exp((beta/2) * sum_of_the_four_elementary_plaquette_signs(u)).

Thus h is3,1 or1/3 depending on the plaquette orbit. There is no separately tuned spatial field or anisotropic link coupling. The fourth plaquette is retained in the score even though only three are independent labels.

`label_gauge`, `canonical_label`, `canonical_gauge` and `invariant_factorization` prove invariance, actual representatives and factorization of EVERY invariant microscopic observable through the labels. `gauge_projected_kernel` verifies ALL1024 entries of the kinetic matrix against the sum of the eight effective target-gauge microscopic relative-link weights. This is an explicit gauge-projected periodic model, not an unexplained32-by-32 matrix or an open-link probe called physical. The kinetic matrix is strictly positive, symmetric and stochastic; its uniform stationary PMF and stationarity as a bind identity are proved.

### A positive eigenstate is constructed, not postulated

The actual transfer is T_ij=h_i K_ij h_j. Its exact aggregation on four plaquette orbit classes has multiplicities1,4,2,1 (each also has four winding labels). An integer polynomial is

    P(x)=589824 x^4-1388800 x^3+284192 x^2-5425 x+9.

Lean proves P(2)<0 and P(9/4)>0 and uses the intermediate value theorem to choose a root lambda in[2,9/4]. No root oracle or analytic spectral-branch assumption is used. A scaled adjugate column is proved strictly positive throughout x>=2; its four polynomial eigen-equations are verified before substituting the root. `orbit_sum` verifies the aggregation for EVERY function on the four orbits and EVERY32-state row, lifting that vector to a strictly positive eigenfunction of the full transfer.

The32-state ground transform is exactly

    P_ij = T_ij psi_j/(lambda psi_i),     pi_i=psi_i^2/sum_j psi_j^2.

Its positive entries, row sums, detailed balance, normalized stationary PMF and stationarity as a PMF bind identity are proved. The four-orbit positive chain is also constructed with the correct multiplicity-weighted stationary law. Classical positive-matrix ideas underlie the construction; no novelty is claimed for Perron theory, finite gauge quotients or this method of proving a root exists. Unlike the still-conditional nonzero-coupling continuous SU2 ground contract, this FINITE positive eigenstate has no missing existence input.

### Proved observable-wise deterioration; precise spectral limitation

The probe is+1 at labels0,16, -1 at8,24 and0 elsewhere. It is a winding character restricted to the completely flat plaquette sector. `probe_gauge` proves invariance under every effective vertex gauge. It is NONLOCAL on the periodic spatial lattice; it must not be substituted for a local contractible observable in an infinite-volume mass-gap argument.

Both means vanish EXACTLY, in the kinetic uniform law and the constructed spatially weighted stationary law. The second moment in the latter is strictly positive. Lean proves

    R_bare = 25/256,
    R_stationary = (225/256)/lambda > 1/4.

The independent Lean harness strengthens the lower bound to R_stationary>=25/64 and checks R_stationary<1/2. `homogeneous_probe_increases` therefore refutes the proposed UNIVERSAL OBSERVABLE-WISE improvement under homogeneous Wilson spatial multiplication, with actual centering and vacuum normalization. No row-normalized spatial surrogate is used.

This checkpoint DOES NOT YET declare a Lean-verified comparison of the COMPLETE centered spectra. An independent EXACT rational Walsh certificate verifies all32 kinetic eigen-relations, the complete orthogonal character basis, and maximal nonconstant kinetic eigenvalue1/4. That finite certificate supplies an independent mathematical route to a global kinetic gap comparison; the corresponding ALL-CENTERED-FUNCTION Lean inequality remains OPEN. The same computation gives centered fourth trace68551681/4294967296 < (3/8)^4, a possible alternative finite proof route. Neither independent certificate is represented as an already proved Lean declaration. Complete that obligation before declaring the homogeneous full spectral-gap counterexample formally closed.

Likewise, the flat-sector probe is NOT an eigenvector. The independent Lean harness proves its average at label2 is positive although the probe itself vanishes there. Its ratio is a genuine variational witness, not a spectral eigenvalue. Floating diagnostics give lambda approximately2.1304660537, this probe's ratio.4125417762 and full centered ratio.4487202863; only the exact formulas and bounds above are Lean theorems.

### Relation to the active Yang--Mills route and manuscript

The source `ResearchSources/Incoming/block_contraction_spectral_gaps.tex`, SHA2560C40FA6B92B830C0E2309BD6471D55CB0EB9BFB94296B9267AD23A5280FA4C60, was selectively reread at the block-to-influence and reflection-positive spectral bridge. The older L2-to-Lipschitz and physical-distance issues are already recorded; no duplicate proof was started. The new finite test addresses a proposed spatial-comparison route, not every conditional assertion in that manuscript.

The new positive construction and counterexample show that gauge projection and equal coefficients do not automatically make EVERY centered observable decay faster after spatial weighting. A valid route may still exploit continuous SU2 structure, local contractible sectors, explicit overlap geometry, or scale-uniform comparison with the ACTUAL changing vacuum. Those require proofs. This model is finite Z2 gauge theory with TWO spatial dimensions plus transfer time. It is not SU2 Haar theory, a spatial3D/physical4D lattice, an infinite-volume limit, a continuum construction, gap closing or a Millennium mass-gap result. No relationship to such results is assumed.

### Independent checks and complete checkpoint verification

Twenty independent Lean checks passed: nonvacuous positive32-state eigenpair; two exact root endpoint signs; constant invariant factorization; fourth-vertex mask; canonical labels; actual projected kernel; two microscopic counts; temporal odds; literal homogeneous spatial weight; both stationary PMF bind identities; exact means and positive variance; upper/lower ratio bounds; strict observable-wise increase; gauge invariance; positive off-support probe average; and the probe's zero at that same state. Initial harness failures were repaired by specifying a constant function and its positive-denominator expression; mathematical sources were unchanged.

Independent exact Fraction checks verified32 character eigen-relations and all basis orthogonality entries; all256 link fields under all16 vertex gauges, including orbit completeness; all1024 projected kinetic entries; the four-orbit characteristic polynomial/adjugate; and the positive-eigenstate/stationary diagnostics. An initial scratch script had a syntax error and was corrected before the final checks. Numerical scans over several couplings remain diagnostics, not a formal theorem about a parameter family. No novelty claim is asserted without a separate literature audit.

Full root build passed6943 jobs in69.9916288 seconds. Complete transitive axiom audit passed53927 declarations in41.8506919 seconds, permitting only propext, Classical.choice and Quot.sound. All112 unabridged public types (63 theorem proofs,46 definitions and3 abbreviations), all103 private helper proofs and the2 private definitions were reviewed. The many internal row/count certificates are exact finite kernel checks, split to preserve default resources after a combined check hit the existing200000-heartbeat limit; no limit was raised, no native-decide axiom was introduced, and no check was suppressed. Twenty final independent Lean checks passed cleanly in28.3851244 seconds. The final full build supersedes intermediate elaboration failures; no sorry/admit/new axiom, old-theorem/configuration/toolchain/trust/resource/heartbeat/recursion change was introduced.

Integrity authenticated1684's source manifest against its exact approval receipt and checked2763 Foundation/root Lean files: exactly the five new modules, root import and AxiomAudit changed. All3 pinned configurations,113 baseline manuscripts and21 Yang--Mills originals are unchanged. Evidence is under C:/Users/ramir/AppData/Local/Temp/stardust-ym-1685-* (complete build/axiom/unabridged type audit, independent Lean checks, exact/noise/gauge/spectral diagnostics, declaration list, authenticated source manifest). Original ResearchSources bytes remain unstaged and untouched.

Yang--Mills remains ACTIVE; Bakry remains PAUSED and the queue is unchanged. The finite homogeneous full-spectrum closure and the continuous SU2/local/4D bridges are retained as separate open obligations. Exact Git approval and guarded PUBLIC main/research synchronization remain separate closure receipts; this pre-commit ledger does not claim remote success.


## Checkpoint 1686 — complete kinetic gap and homogeneous stationary deterioration

The all-centered spectral comparison left OPEN at1685 is now DISCHARGED for the actual finite homogeneous Z2 torus model. `Foundation/FiniteWilsonTorusCharacters.lean` constructs all32 real Walsh characters, proves exact integer and real orthogonality and kinetic synthesis, and bounds EVERY nonconstant kinetic eigenvalue by1/4. `Foundation/FiniteWilsonTorusGap.lean` proves Parseval and quadratic synthesis for ALL real functions on the32-state gauge quotient, then the sharp centered kinetic Poincare inequality with gap3/4. A winding character attains equality; no omitted winding sector or centering assumption is hidden.

For the actual homogeneous spatially weighted stationary transfer operator constructed at1685 (positive vacuum, normalized stationary PMF and exact detailed balance), the same module proves:

- `homogeneous_gap_counterexample` and `unchanged_gap_fails`: the universal centered3/4 Poincare lower bound fails, with exactly zero stationary mean and strictly positive variance.
- `stationary_gap_upper`: the actual centered probe has Dirichlet form at most(39/64) times its variance, so the variational gap is at most39/64, strictly below the sharp bare3/4.
- `comparison_error_necessary`: any all-centered lower bound `(3/4-epsilon)*variance <= Dirichlet` in this fixed model requires epsilon>=9/64. This is a normalized finite L2 correction budget, not a four-dimensional gradient error estimate.

The witness is gauge invariant but winding/nonlocal and is NOT an eigenvector. These statements prove strict finite-model deterioration, not gap closing. The model has two spatial dimensions plus transfer time and gauge group Z2. It supplies neither an SU2 ground-state existence theorem, a spatial3D/physical4D transfer construction, a local contractible-sector estimate, a volume/scale-uniform bound, nor a continuum mass-gap proof or refutation. The continuous SU2, actual4D and physical-distance bridges remain OPEN. Classical finite Fourier methods are reused; no novelty claim is made without a literature audit.

A further local-sector lead was independently tested rather than asserted as a theorem. The sum of the four elementary plaquette signs has centered stationary Rayleigh ratio approximately.08900072, above its bare1/16 value. An exact Fraction polynomial reduction, using the existing degree4 vacuum polynomial, reduces the candidate inequality16*centeredLag>centeredVariance to a positively scaled cubic remainder with positive Bernstein coefficients on[2,9/4]. The saved certificate is `stardust-ym-1686-plaquette-score-reduction.json`; its coefficients and positive scaling are recorded there. The actual plaquette moment/centering/sector identification and corresponding Lean inequality remain OPEN. This is a promising test of whether deterioration persists beyond the winding witness, not a proved local4D obstruction.

### Verification and integrity

The final complete root build passed6945 jobs in41.84718 seconds; the complete transitive axiom audit passed53956 declarations in45.3851144 seconds, permitting only propext, Classical.choice and Quot.sound. All23 unabridged public types (18 theorem proofs,5 definitions),65 private helper proofs and1 private definition were reviewed. Exact row certificates were split under the unchanged default200000-heartbeat limit; no native-decide axiom, sorry/admit, compiler/trust/resource/toolchain change or suppressed check was introduced.

Sixteen final independent Lean examples passed with exit0 in26.0483775 seconds. They check complete Parseval, sharpness and exclusion of larger kinetic gaps, failure without centering, actual weighted centering/positive variance, failure even of a7/10 lower bound, the necessary9/64 correction, and full gauge-invariant quotient reuse. An intermediate harness simplification left a numerical goal; replacing it with norm_num repaired only the test. The original final process handle was missing after continuation and no Lean worker remained; the final harness was rerun cleanly rather than claiming an unavailable exit status.

Independent exact Fraction tests checked100 centered rational functions (seed1686), synthesis, Parseval, the sharp winding witness, omitted-sector and uncentered counterexamples, and the39/64 stationary upper bound. These external computations are not Lean inputs. Source integrity authenticates1685's manifest against its exact approval receipt and checks2765 Foundation/root files: exactly these two new modules, root import and AxiomAudit changed. All3 pinned configurations,113 baseline manuscripts and21 Yang--Mills originals (20 distinct hashes) are unchanged. ResearchSources remains untouched and unstaged. Evidence is under C:/Users/ramir/AppData/Local/Temp/stardust-ym-1686-*.

Yang--Mills remains ACTIVE, Bakry PAUSED, and the research queue is unchanged. Exact Git approval and guarded two-branch PUBLIC synchronization are separate closure receipts; this pre-commit entry does not claim remote success. The next focused question is the precise plaquette-sector comparison and whether any usable mechanism survives continuous SU2 and scale/volume limits, without expanding a broad gauge library.
