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


## Checkpoint 1687 — actual centered elementary-plaquette sum slows

The plaquette-sector lead explicitly left OPEN at1686 is now Lean verified in `Foundation/FiniteWilsonPlaquetteSlowing.lean`. The observable is prescribed microscopically: the sum of the four elementary plaquette signs on the same2x2 periodic spatial Z2 torus, not a selected eigenvector or winding variable. `score_microscopic` identifies it with the preserved original link-field plaquette expression for EVERY one of the256 fields; `score_gauge` proves vertex-gauge invariance. It is a sum over this entire small torus, not a single plaquette or a volume-uniform local-sector theorem.

In the bare kinetic stationary law the sum S has mean0, second moment4, lag1/4 and exact kinetic eigenvalue1/16. In the ACTUAL spatially weighted stationary law constructed at1685, put G=S-mean(S). `centered_mean`, `centered_score_variance_pos` and `centered_score_slowing` prove

    mean(G)=0,  variance(G)>0,  lag(G)>(1/16)*variance(G).

`plaquette_covariance_increases` therefore proves that the normalized centered lag strictly increases from its bare1/16 value. This closes the proposed escape that1686's deterioration was demonstrated only with a winding observable. It does NOT establish deterioration for every local observable or establish that this sum controls the global spectral gap. In particular it is not a new bound exceeding the1/4 maximal nonconstant bare eigenvalue, and does not strengthen1686's global39/64 gap upper bound merely by being plaquette-derived.

### Exact proof and domains

The centering identities are proved for EVERY real function on the actual32-state stationary law, using exact transition row sums and stationarity:

    secondMoment(centered f)=secondMoment(f)-mean(f)^2,
    lagPairing(centered f)=lagPairing(f)-mean(f)^2.

There is no row-normalized surrogate or assumed vacuum existence. Reuse the positive constructed eigenvalue lambda, four-orbit ground vector v and Z=sum_b multiplicity(b)*v(b)^2. Put C=(3177/2048)*v0^2-2*(225/2048)*v0*v3+(353/18432)*v3^2. Exact finite sums and the existing orbit-block theorem identify the actual mean as4*(v0^2-v3^2)/Z, second moment as16*(v0^2+v3^2)/Z, and lag as16*C/(lambda*Z). All denominators are proved strictly positive.

The sign needed after centering is

    E=256*Z*C-16*lambda*Z*(v0^2+v3^2)-240*lambda*(v0^2-v3^2)^2 > 0.

An exact polynomial identity reduces E to P(lambda)*Q(lambda)+(73153125/65536)*R(lambda), where P is the already verified degree4 vacuum polynomial, Q is explicitly checked by ring, and

    R(x)=-3243610334169528005827+1953654217580403423644027*x
         -101506400370404313095928928*x^2+452893609599424244451318528*x^3.

Lean proves R(x)>0 for ALL x>=2 from x^2>=4 and x^3>=2*x^2. Thus P(lambda)=0 and the existing lambda>=2 suffice. No numerical root selection, new axiom or parameter-family assumption enters. Strict variance follows from positive stationary weights and the two distinct score values4 and-4. The bare eigenrelation is independently certified by exact integer row sums under the unchanged default resource settings.

### Attempts to overgeneralize and remaining mass-gap obstacles

Independent microscopic and matrix tests reproduce mean(S) approximately2.7855373958, centered variance3.5339414460 and centered lag ratio.08900072079, versus bare.0625. The SAME diagnostic test for ONE elementary plaquette gives ratio.05492253728 BELOW bare.0625. Only the sum's strict increase is Lean proved here; the single-plaquette decrease is a numerical diagnostic. The sum's behavior involves cross-plaquette covariance and cannot be promoted to a claim that every individual plaquette slows. No general local-correlation monotonicity is inferred in either direction.

This is fixed homogeneous Z2 coupling beta=log(3)/2, with two spatial dimensions plus transfer time. It proves neither strong-coupling asymptotics, continuous SU2 slowing, spatial3D/physical4D behavior, scale/volume-uniform bounds, positive or vanishing physical mass, nor a continuum existence result. These exact limitations remain material: the torus plaquette product constraint and sum over the whole small torus may matter. The focused next bottleneck is an ACTUAL continuous-SU2/4D stationary bridge or a precise obstruction to one, rather than additional finite-model declaration accumulation. Existing SU2 loop iteration and zero-trace obstructions remain intact. No novelty is asserted without an appropriate literature audit.

### Complete verification

Final full root build passed6946 jobs in44.0239846 seconds. Complete transitive axiom audit passed53983 declarations in39.2534241 seconds, allowing only propext, Classical.choice and Quot.sound. All14 unabridged public types (12 theorem proofs,2 definitions),13 private helper proofs and7 private definitions were reviewed in full. Fifteen independent Lean checks passed cleanly in28.1305337 seconds, covering bare eigen-moments, actual centering/positive variance/positive lag, failure of a15/16 inequality for this observable, strict normalized comparison, microscopic nonvacuity, vertex-gauge invariance and generic centering identities. Intermediate finite-sum elaboration failures were repaired without changing any mathematical hypothesis or raising resource limits.

Independent exact tests checked all256 microscopic plaquette identifications, all32 kinetic eigenrows and33 rational evaluations of the polynomial-division certificate; numerical actual-PMF row/stationarity checks and the contrary single-plaquette diagnostic guard against overgeneralization. External computations are not Lean inputs. Integrity authenticates1686's manifest against its exact approval receipt and checks2766 Foundation/root files: exactly the new source, root import and AxiomAudit changed. All3 configurations,113 baseline originals and21 Yang--Mills originals (20 distinct hashes) are unchanged. A filename substitution mistake in the temporary integrity helper was repaired before its successful final run; no baseline was weakened. Evidence is under C:/Users/ramir/AppData/Local/Temp/stardust-ym-1687-*.

ResearchSources remains read-only and uncommitted. Yang--Mills stays ACTIVE and Bakry PAUSED; no campaign or queue change. Exact Git approval and guarded PUBLIC two-branch synchronization are separate closure receipts, not claimed by this pre-commit ledger.


## Checkpoint 1688 — construct positive finite-product SU2 Wilson eigenfunctions

The focused route moved from finite Z2 tests to a specific continuous-SU2 bottleneck: the existing `SU2SevenLinkGroundTransform.GroundData` contract assumes a uniformly positive bounded measurable eigenfunction. No inhabitant was silently introduced. `Foundation/YMPositivePower.lean` now constructs such eigenfunctions for actual integral kernels, and `Foundation/YMFiniteWilsonVacuum.lean` instantiates the construction against actual finite-product SU2 Haar measure. This is a classical positive-operator construction formalized to serve the missing stationary bridge, not a claimed new existence or mass-gap theorem for four-dimensional quantum Yang--Mills.

### Constructive theorem and convergence

`YMPositivePower.positive_eigenfunction_exists` assumes a probability reference measure on a nonempty measurable space and a jointly measurable real kernel satisfying EVERYWHERE0<m<=k(x,y)<=M. It proves existence of measurable psi and lambda with

    m<=lambda<=M,  m/M<=psi(x)<=M/m,  integral k(x,y)*psi(y) dmu(y)=lambda*psi(x).

Neither an eigenfunction, compactness theorem, external continuum construction nor an eigenvalue equation is an input. Let f0=1, f(n+1)=T f(n) and q(n)=f(n+1)/f(n). Exact positivity, integrability and measurability are verified. `ratio_bridge` identifies q(n+1) as the normalized k-average of q(n) in the genuine probability law proportional to f(n)dmu. That reference law CHANGES with n; it is not asserted to be a stationary vacuum law.

Reusing `YMPositiveKernel.residual_bounds` and `SignedDensityProbabilitySampling`, explicit nested intervals enclose every q(n,x) and have EXACT width `(M-m)*(1-m/M)^n`. Successive normalized powers g(n,x)=f(n,x)/f(n,x0) satisfy the uniform-in-x bound

    |g(n+1,x)-g(n,x)| <= ((M/m)*(M-m)/m)*(1-m/M)^n.

The scalar ratios and each normalized power sequence are Cauchy. The chosen POINTWISE normalized-power limit is measurable and stays between m/M and M/m. Dominated convergence under the bound M*(M/m) proves its actual integral eigen-equation. The source proves a uniform geometric increment estimate and pointwise limit construction; no separate function-space uniform-convergence theorem, uniqueness theorem or top-spectrum characterization is claimed. The degenerate m=M case is included and independently tested. Symmetry and full support of the reference law are unnecessary for THIS existence theorem; psi-squared stationarity for a ground transform requires its separate symmetry/reversibility hypotheses.

### Actual continuous SU2 instantiation and remaining bridge

`YMFiniteWilsonVacuum.haar n` is the actual product of the existing SU2 probability Haar law on n links. For bounded positive measurable spatial amplitude l<=h<=u with l>0, `ground_exists` proves a positive bounded measurable eigenfunction of the actual RAW sandwich

    h(C)*integral exp(beta*sum_i halfTrace(C_i*D_i^-1))*h(D)*psi(D) dHaar(D).

The kernel bounds used are m=l^2*exp(-n*|beta|), M=u^2*exp(n*|beta|), and the psi bounds are explicitly m/M and M/m. Joint measurability and all denominators are proved. `sevenAmplitude t C=exp((t/2)*halfTrace(C1*C2*C3*C0))` is the concrete first-plaquette half-weight in seven indexed physical-link coordinates; `seven_raw_ground_exists` constructs an eigenfunction for EVERY real beta and t, including nonzero tilt, with no supplied eigenfunction.

Precisely OPEN: the measure-preserving indexed/tuple coordinate identification and Wilson partition normalization needed to transport this RAW product-Haar theorem into the existing normalized seven-link `GroundData`; gauge-sector/invariance identification for the constructed eigenfunction; any needed top-spectrum assertion; actual spatial3D/physical4D transfer realization, volume-uniform estimates, physically justified spacing and continuum/infinite-volume limits. The source's seven-link first-plaquette tilt is the local comparison model, not a complete homogeneous four-dimensional action. Existing conditional seven-link stationary obstruction theorems remain conditional UNTIL the exact bridge is supplied. Do not equate raw and row-normalized operators or declare those hypotheses discharged yet.

The crude contraction fraction m/M=(l/u)^2*exp(-2*n*|beta|) deteriorates with link count/coupling, consistent with the already verified no-volume-uniform cross-ratio obstruction. This method constructs finite-volume objects but alone supplies no positive physical mass gap, gap closing, strong-coupling asymptotic conclusion or continuum existence. The next concrete task is that normalization/coordinate transport, then reuse of the actual stationary/parity/covariance declarations; no broad gauge library is started.

### Independent tests and full verification

Final full root build passed6948 jobs in27.33364 seconds. Complete transitive axiom audit passed54043 declarations in43.5193691 seconds, allowing only propext, Classical.choice and Quot.sound. All29 unabridged public types (20 theorem proofs,8 definitions and1 instance),17 private helper proofs and1 private topology instance were reviewed in full. No sorry/admit/new axiom, native-decide trust input, heartbeat/resource/recursion/compiler/toolchain/configuration change or suppressed error was introduced.

Nine final independent Lean checks passed in38.0423843 seconds: constant-kernel powers/ratios/normalized powers, zero-width enclosure and constructive limit, actual Haar probability for zero/seven links, the zero-link amplitude2 RAW eigenvalue4 (rather than1), concrete nonzero seven-link parameters, and a nonsymmetric kernel with a reference law supported on one point. Initial harness failures were repaired by explicit measure unfolding, function-equality parentheses and numeric simplification; mathematical sources were unchanged after the final complete build/audit.

Independent Fraction tests verified30 iterations for each of three kernels: a constant kernel, a nonsymmetric2x2 kernel and the earlier four-orbit Wilson block. They check exact nested enclosure widths, ratio bounds, positivity and normalized increment estimates, including m=M. A seeded48-point SU2 quadrature checks the raw exponential/half-weight formulas and a finite matrix ground transform only as diagnostics, not as a Haar-law proof. Its initial anchor normalization amplified an absolute eigen-residual to2.56e-10; inspecting relative residual8.61e-16 identified scaling. Keeping the eigensolver's unit-norm vector retained the original absolute threshold AND added a relative check; the final residuals were1.83e-13 absolute and8.82e-16 relative. No Lean theorem or exact test was weakened. A symmetric2x2 countercheck confirms naive row normalization and the actual positive-eigenfunction ground transform have different stationary laws.

Integrity authenticates1687's manifest against its exact approval receipt and checks2768 Foundation/root sources: exactly the two new modules, root import and AxiomAudit changed. All3 pinned configurations,113 baseline manuscripts and21 Yang--Mills originals (20 distinct hashes) are unchanged. Evidence is under C:/Users/ramir/AppData/Local/Temp/stardust-ym-1688-* (full build, complete transitive/type audit, independent Lean/exact/numerical tests, declaration counts and authenticated source manifest). ResearchSources remains untouched and uncommitted.

Yang--Mills remains ACTIVE; Bakry stays PAUSED and the queue is unchanged. Exact Git approval and guarded PUBLIC main/research verification are separate closure receipts, not claimed by this pre-commit ledger. This checkpoint completes the stated positive-kernel/raw-SU2 existence result, not the remaining normalized stationary bridge or the Yang--Mills campaign.


## Checkpoint 1689 — exact normalized seven-link SU2 stationary realization

The missing normalized `SU2SevenLinkGroundTransform.GroundData` existence obligation from1688 is DISCHARGED for the existing seven-link operator, for EVERY real beta and spatial tilt t. `Foundation/SU2SevenLinkVacuum.lean` constructs its inhabitant using1688's positive-kernel limit theorem. It then directly reuses the earlier covariance theorem with the constructed actual stationary law. No supplied eigenfunction, external existence construction, new axiom or numerical quadrature is an input.

### Exact normalization rather than coordinate substitution

The generic positive-kernel theorem applies directly on the EXISTING seven-link tuple state. Consequently no indexed/tuple coordinate conversion is needed to close THIS contract; the separate1688 indexed/raw theorem remains valid without being silently identified with this operator.

`noise_withDensity` proves the original product of seven normalized Wilson increment measures is EXACTLY the existing tuple Haar law with density rho_beta. This density is the product of the seven scalar densities exp(beta*halfTrace(v_i))/Z(beta), so all SEVEN partition factors are retained. The proof reuses the scalar exponential-tilt measure, product-with-density theorem, existing noise inversion at beta0 and Haar translation invariance. `step_density` proves the actual normalized temporal transfer equals

    step_beta f(s)=integral rho_beta(s^-1*r)*f(r) dHaar(r).

`kernelDensity_apply` proves equality of the kernel integral with the original `spatialStep beta t`, including both spatial half-weights H_t(s)=exp(t*first(s)/2). This is an equality for the actual old operator, not a new row-normalized approximation. The positive bounds used are

    m=exp(-|t|)*(exp(-|beta|)/Z(beta))^7,
    M=exp( |t|)*(exp( |beta|)/Z(beta))^7.

The source writes the spatial exponential as its squared half-weight; the displayed form is algebraically equivalent. Z(beta)>0 and every factor are proved positive. Joint measurability, actual measure equality and integral change of variables are verified. Applying `YMPositivePower.positive_eigenfunction_exists` now gives the exact `GroundData` fields: positive eigenvalue, measurable uniformly positive bounded function, and the EXISTING normalized eigen-equation. `groundData_nonempty` proves inhabitance and `data` chooses from that proof. Nothing is postulated as a typeclass inhabitant or existence axiom.

### Realized covariance obstruction and exact remaining scope

`realized_stationary_obstruction_interval` reuses `SU2SevenLinkGroundTransform.exists_stationary_obstruction_interval` with `data beta t`, then its verified evenization. For coefficient c(beta)!=0 there exists delta>0, delta<=1 such that EVERY0<t<delta yields the constructed actual stationary probability and Markov kernel, with a displayed bounded observable f satisfying

    stationary_mean(f)=0,  stationary_variance(f)>0,
    stationary_lag(f)/stationary_variance(f)>c(beta)^4.

The function is exactly the previous unweighted odd-polynomial trial divided by the constructed even positive eigenfunction. Actual stationarity, reversibility, integrability and native variance are inherited by direct theorem reuse. This removes the previous missing-eigenfunction assumption from that comparison. The parameter hypothesis c(beta)!=0 and the SMALL INDEPENDENT SPATIAL TILT remain explicit. It does not imply that t=beta lies in the interval, nor that every local observable slows.

The baseline c(beta)^4 is the earlier specific bare comparison/channel coefficient, NOT a newly proved complete bare spectral-gap value. This checkpoint proves neither a global-gap comparison nor gap closing. The model has seven actual continuous SU2 link variables and two adjacent plaquette geometry, with this operator tilting the FIRST plaquette; it is not a complete equal-coupling four-dimensional action. Gauge-sector/invariance identification of the chosen eigenfunction and observable remains a separate obligation, as do relevant top-spectrum statements, homogeneous full-action comparison, spatial3D/physical4D transfer construction, volume-uniform bounds, physically justified spacing and continuum/infinite-volume limits. No Millennium conclusion or novelty claim is asserted. The new result is a rigorous realization of the existing local operator/covariance analysis, not completion of the Yang--Mills campaign.

### Full verification and independent attempts to falsify normalization

The final full root build passed6949 jobs in43.0837355 seconds. Complete transitive axiom audit passed54055 declarations in40.7115968 seconds, allowing only propext, Classical.choice and Quot.sound. All11 unabridged public types (8 theorem proofs,3 definitions),9 private helper proofs,3 private definitions and4 private instances were reviewed in full. The scalar-density measurability proof was registered with fun_prop so product-density composition could reuse it; no mathematical hypothesis or trust setting was changed. Intermediate namespace, product measurability, positivity and record elaboration failures were repaired before the final full build. All proofs use the retained default resource limits; no sorry/admit/new axiom, native-decide trust input, compiler/toolchain/configuration/resource change or suppressed error was introduced.

Thirteen independent Lean checks passed on the FIRST final harness run in25.6554402 seconds: inhabitance and positive eigenvalue at arbitrary parameters; actual constructed Markov kernel and stationary probability; positive normalizer and square integrability; unit mass of the seven-link normalized temporal kernel at zero spatial tilt; density integral1; the exact existing normalized eigen-equation; actual evenization; stationarity and reversible pairings for ALL bounded measurable probes; and a genuinely positive tilt chosen at delta/2 with zero mean and positive variance. These tests instantiate the previously conditional APIs with the newly constructed data.

Independent diagnostics use seed1689 and256 sampled seven-link quaternion fields. They check pointwise Haar substitution algebra, all seven partition factors and kernel bounds for nine(beta,t) pairs including positive/negative/zero parameters. One-dimensional quadrature is only a normalization diagnostic, not the Haar proof. Omitting Z(beta)^7 changes the factor by approximately25.76305 at beta=-2 and4.17898 at beta=1.3, illustrating why raw/normalized identification matters. A separate beta0 spatial-row diagnostic gives row-mass ratio9 for opposite plaquette configurations at tilt2*log(3); multiplying by the spatial half-weight is not row normalization. None of these sampled computations is a Lean input or evidence of a4D theorem.

Integrity authenticates1688's manifest against its exact approval receipt and checks2769 Foundation/root sources: exactly the new module, root import and AxiomAudit changed. All3 pinned configurations,113 baseline manuscripts and21 Yang--Mills originals (20 distinct hashes) remain unchanged. Evidence is under C:/Users/ramir/AppData/Local/Temp/stardust-ym-1689-* (full build, complete transitive/type audit, independent Lean and quaternion/normalization diagnostics, declaration list and authenticated source manifest). ResearchSources remains unmodified and uncommitted.

Yang--Mills remains ACTIVE; Bakry PAUSED and all other priorities unchanged. The next focused question is whether the realized local mechanism has a valid gauge-invariant/homogeneous/volume-uniform extension, rather than equating this finite local covariance comparison with a physical mass gap. Exact Git approval and guarded PUBLIC main/research synchronization are separate closure receipts; this pre-commit entry does not claim remote success.


## Checkpoint 1690 — gauge-invariant stationary obstruction and nonuniform coupling limit

The outstanding LOCAL gauge-sector issue from1689 is now DISCHARGED. `SU2SevenLinkVacuum.function_gauge` proves EVERY uniformly positive bounded eigenfunction satisfying the exact normalized seven-link `GroundData` contract is invariant under the existing six-vertex SU2 gauge action, at every state. This includes the constructed `data` and its verified evenization. Gauge invariance is a theorem, not a selection criterion silently imposed on an arbitrary eigenfunction.

### Reusable mathematical mechanism

`Foundation/YMBoundedHarmonic.lean` proves two bounded-harmonic theorems using the existing positive-kernel reset inequality. On a probability reference law with jointly measurable0<m<=k<=M, a bounded measurable harmonic function is constant; if its reference mean is0 it vanishes. The proof propagates the bound B*(1-m/M)^n and takes its proved limit. No extremum attainment, full support, symmetry or unproved Perron theorem is assumed. This is classical positive-kernel/ergodic mathematics verified here for the concrete gauge problem, without a novelty assertion.

The existing `YMPositivePower.average_reset_range` proof was made PUBLIC for exact reuse; its statement and complete proof body are otherwise byte-identical after newline normalization. No second reset proof was manufactured. The seven-link source reuses its original normalized density, Haar law and gauge action. It factors the latter as fixed left/right tuple multiplication, proves Haar integral invariance and conjugation invariance of the seven-factor noise density, and proves exact simultaneous kernel covariance and operator commutation:

    K(g*s,g*r)=K(s,r),
    T(f composed with g)(s)=T(f)(g*s).

For a positive eigenfunction psi, its gauge transform chi has the SAME eigenvalue. The bounded ratio chi/psi is harmonic for the verified ground-bridge average with reference law proportional to psi*dHaar. Bounded-harmonic constancy makes chi=c*psi; Haar normalization and the proved positive integral force c=1. This directly connects the reset/operator calculus to actual gauge invariance, without assuming an eigenbranch, uniqueness or gauge averaging in advance.

`observable_gauge`, `stationary_integral_gauge` and `kernel_integral_gauge` then prove the actual trial observable is invariant, the constructed stationary probability has invariant expectations, and its actual Markov kernel is gauge covariant. Independent Lean checks show both native Markov evolution and the original spatial operator preserve invariant observables. `gauge_invariant_stationary_obstruction_interval` strengthens1689's realized covariance theorem with explicit invariance under EVERY one of the six-vertex SU2 gauge transformations.

### Genuine parameter-uniform obstruction

The strongest new conclusion is `no_uniform_stationary_contraction`. Combining the gauge-invariant realized comparison with the EXISTING `SU2WilsonConvolution.fixed_word_factor_tendsto_one 4`, Lean proves:

    for EVERY q<1 and EVERY cutoff R,
    there exist beta>R and0<t<=1 with an ACTUAL gauge-invariant observable f,
    mean(f)=0, variance(f)>0 and stationary_lag(f)/variance(f)>q.

The state law and kernel are the constructed native stationary objects from1689. This is a genuine variational obstruction to a single subunit one-step covariance factor over that local parameter family, not merely an increasing surrogate ratio or a conditional vacuum calculation. The positive t is chosen within its beta-dependent small-tilt interval. No quantitative lower bound for that interval is supplied, and t may depend on beta.

Exact limits remain important: this does NOT establish the same obstruction at equal spatial/temporal coupling t=beta, for the complete homogeneous spatial action, or at a fixed t independent of beta. The comparison baseline c(beta)^4 remains a specific bare channel coefficient, not an asserted full bare spectral norm. No claim is made that a particular finite-parameter operator has zero gap, that coupling-dependent iteration cannot restore contraction, or that lattice steps represent a physically justified distance. Quantitative iteration rates, homogeneous-action behavior, volume-uniform estimates, actual spatial3D/physical4D realization and continuum/infinite-volume limits remain OPEN. Finite local gauge-invariant observables do not by themselves construct the four-dimensional Gauss-law Hilbert space or establish/refute a positive physical mass gap.

Simultaneous covariance must also be distinguished from independent gauge invariance in EACH kernel argument. A direct corner calculation (not a new Lean declaration) at s=r=all identities, changing only the second argument by g0=-I and the other five vertices1, flips THREE of the seven temporal link signs. The trace sum changes7 to1 while spatial plaquette traces stay unchanged, giving one-sided kernel ratio exp(-6*beta). The independent beta=.9 diagnostic returns.00451658094. Thus this kernel commutes with the gauge action and preserves its invariant sector; it is not silently identified with an independently gauge-averaged integral kernel.

### Final complete verification and independent checks

The final full root build passed6950 jobs in40.6687689 seconds. The complete transitive axiom audit passed54086 declarations in40.7907145 seconds, allowing only propext, Classical.choice and Quot.sound. All13 unabridged public theorem types/proofs (including the existing reset proof newly exposed for reuse), both new private helper proofs and both new private definitions were reviewed. Earlier build/audit evidence before adding the substantive nonuniform-coupling corollary is superseded by these FINAL passes. No sorry/admit/new axiom, native-decide trust input, compiler/toolchain/configuration/resource/heartbeat/recursion change or suppressed check was introduced.

Twelve final independent Lean checks passed in25.2889484 seconds. They cover pointwise harmonic uniqueness even at a reference-null state, gauge invariance for arbitrary GroundData and negative parameter examples, arbitrary trial coefficients and evenized data, Haar/stationary expectation invariance, kernel covariance, preservation of the invariant sector by BOTH actual Markov and spatial evolution, a genuinely positive native gauge-invariant covariance witness, and rejection of a universal q<1 covariance bound using an arbitrarily large parameter cutoff. The initial harness had an unnecessary dsimp after finite case splitting; removing it repaired only the test. Mathematical sources were unchanged during those harness repairs.

Independent seed1690 quaternion checks test256 full continuous gauge transformations at three parameter pairs, first/second/mean/residual channels and the actual normalized kernel covariance. A64-point CENTER-gauge-closed quadrature (two32-point orbits) tests positive finite-matrix eigenfunction/Markov symmetry only as a diagnostic, not as a full Haar or full-continuous-gauge proof. An exact Fraction identity-transition counterexample has a nonconstant zero-mean harmonic vector when strict positivity is dropped, guarding the theorem's essential lower-bound hypothesis. Coefficient quadrature at beta1,10,100,1000 gives fourth powers approximately.00332849,.53236364,.94148136,.99401498; the actual asymptotic input is the verified Lean limit, not these numerical values. No external calculation is a Lean input.

Integrity authenticates1689's manifest against its exact approval receipt and checks2770 Foundation/root files. Exactly the new harmonic module, reset-helper visibility, appended seven-link gauge results/import and AxiomAudit changed; the root source is unchanged. An additional exact Git/source comparison proves EVERY previous seven-link declaration body is preserved and the positive-power source differs ONLY by publishing the reset helper. All3 pinned configurations,113 baseline manuscripts and21 Yang--Mills originals (20 distinct hashes) remain unchanged. Evidence is under C:/Users/ramir/AppData/Local/Temp/stardust-ym-1690-* (final full build, complete transitive/unabridged type audit, independent Lean/exact/quaternion checks, declaration list and authenticated source manifest).

ResearchSources remains read-only and uncommitted. Yang--Mills remains ACTIVE; Bakry PAUSED and the queue unchanged. The next focused mathematical bottleneck is quantitative coupling-dependent iteration and the homogeneous-action/physical-scale bridge, using these actual gauge-invariant stationary objects. Exact Git approval and guarded PUBLIC two-branch synchronization are separate closure receipts; this pre-commit entry does not claim remote success.


## Checkpoint 1691 — actual stationary L2 transfer and all-counts gauge-sector persistence

The quantitative iteration bottleneck is now addressed on the constructed seven-link stationary system, rather than by identifying it with the earlier single-loop Hilbert space. `Foundation/SU2SevenLinkL2Transfer.lean` constructs the actual edge probability law pi(ds)P(s,dr), proves its swap symmetry and BOTH stationary marginals, and reuses the existing `HilbertRepresentation.predictableAdjoint` on the left/right measure-preserving L2 embeddings. The resulting bounded operator is a selfadjoint contraction on L2(pi). Its pairing equals the actual kernel integral for ALL L2 classes. `operator_toLp` proves exact equality with native Markov integration on bounded measurable probes; `steps_toLp` proves the equality for EVERY iterate, and `steps_pairing` identifies every covariance with the actual iterated kernel integral. Measurability and finite L2 domains are proved, not assumed from a formal transfer expression. `nativeSteps_gauge` proves that actual evolution preserves gauge-invariant observables.

`Foundation/SelfAdjointContractionIteration.lean` generalizes the already verified `SU2SlowModeIteration` argument without modifying it. For a real selfadjoint contraction T, V=<f,f> and D=V-<Tf,f>, it proves for EVERY integer n>=0:

    V-n*D <= <T^n f,f> <= V.

Odd n are included, and nonnegative spectrum is NOT assumed. The proof uses decreasing Dirichlet dissipation, a squared-norm loss bound, and separate even/odd iteration identities. It needs no spectral theorem or extra spectral-positivity axiom. This is reusable classical Hilbert/Markov mathematics, not a claim of a new abstract theorem.

`SU2SevenLinkIteration.realized_iteration_interval` applies that estimate to the actual constructed evenized vacuum and the existing trial observable. For each beta with c(beta)!=0 there is delta(beta)>0, delta<=1, and for EVERY0<t<delta, a bounded measurable gauge-invariant native f with mean0 and variance V>0. Simultaneously for ALL counts n, `native_iteration_interval` proves

    1-n*(1-c(beta)^4) <= [integral f(s) P^n f(s) pi(ds)]/V <=1.

This is an actual signed covariance expression of a genuine probability/Markov system (the observable can have either sign), not a replacement finite matrix or an uninstantiated operator hypothesis. `no_uniform_fixed_steps` proves that for EVERY fixed n, EVERY q<1 and EVERY large-coupling cutoff R, there are beta>R and0<t<=1 for which that normalized native covariance exceeds q. Thus replacing one step by any fixed block size cannot supply a coupling-uniform subunit covariance factor over this local family. This includes n=0 without an artificial positivity-of-count hypothesis.

### Scope, obstruction and physical-scale question

The interval is beta-dependent and spatial t is independently small: no equal-coupling t=beta or fixed-positive-t conclusion is established. c(beta)^4 is still a particular bare channel coefficient, not an asserted full bare operator norm. For counts with n*(1-c(beta)^4) small, the proved bound forces persistence. A necessary scale for reducing this trial's normalized covariance below q<1 is n*(1-c(beta)^4)>=1-q. This algebraic consequence supplies a step-count obstruction, NOT a sufficiency theorem, sharp mixing time or physical lattice spacing. No joint measurable choice of tilt/vacuum over beta, uniform rate for delta(beta), or homogeneous-action comparison is claimed here.

Coupling-dependent iteration MAY recover contraction; a rigorous exact two-state reversible counterexample confirms this possibility despite convergence of every fixed-step covariance to1. With eigenvalue1-eps, all-counts persistence holds, while n=1/eps gives covariance below1/2 for eps=2^(-j), j=2,...,14. Therefore extrapolating the fixed-count obstruction to ALL distance scales is a failed inference. Proving an upper contraction estimate for the actual seven-link operator, relating its constants to physical distance, and transferring any estimates to the full spatial3D/physical4D lattice with volume/continuum control remain OPEN. This checkpoint establishes/refutes no four-dimensional physical mass gap. The existing actual gauge-invariance result is reused throughout; independent gauge averaging in each kernel argument is still not silently assumed.

### Verification and integrity

The complete root build passed6954 jobs in26.099457 seconds. The complete transitive audit passed54153 declarations in40.2897285 seconds, accepting only propext, Classical.choice and Quot.sound. All45 unabridged new public types were reviewed:33 theorem proofs,9 definitions and3 abbreviations; also5 private helper proofs and6 private instances. Every prior mathematical source, including the single-loop iteration proof, remains byte-identical. No sorry/admit/new axiom, compiler/trust/toolchain/resource/heartbeat change or suppressed check was introduced.

Nine independent Lean examples test negative-spectrum odd/even sign, native constants and zero steps, exact every-iterate L2/native agreement, native gauge preservation, the actual two-step square identity, the all-counts lower bound and failure of any fixed-step uniform factor. The first constant-preservation harness needed function extensionality before simplifying the integral; that test-only elaboration repair changed no mathematical source. The final independent Lean checks passed in26.5964921 seconds. Exact Fraction tests check205 reversible two-state lag inequalities (including negative spectrum) and13 growing-distance examples. A stationary deterministic six-cycle with uniform law gives V=1/2, lag1=1/4, lag2=-1/4, violating the claimed n=2 lower bound0 when reversibility is omitted. External values are diagnostics/counterchecks, never Lean proof inputs.

Integrity authenticates1690's source manifest against the exact approval for3a3b80c91ad60b9f6fc15cddcda57d1b3987a388. It covers2773 Foundation/root files; exactly the three new modules, root import and AxiomAudit differ. All3 pinned configurations,113 baseline manuscripts and21 Yang--Mills originals (20 distinct hashes) remain unchanged. ResearchSources remains unmodified/uncommitted; unrelated untracked drafts are preserved. Evidence: C:/Users/ramir/AppData/Local/Temp/stardust-ym-1691-* (full build, complete audit/types, independent Lean/exact tests, declaration inventory and authenticated source manifest).

Yang--Mills remains ACTIVE; Bakry PAUSED and all queued priorities unchanged. The next substantive question is whether quantitative positive-kernel bounds yield a useful coupling-dependent upper contraction estimate on this actual gauge sector, and what additional homogeneous/volume/physical-scale hypotheses are indispensable. Exact-commit approval and guarded two-branch PUBLIC synchronization are closure receipts; this pre-commit entry does not claim remote success.


## Checkpoint 1692 — actual coupling-dependent covariance decay and the volume bottleneck

The sufficient-count question left open in1691 now has a rigorous finite-system answer. `Foundation/SU2SevenLinkMixing.lean` proves actual native mixing for EVERY bounded measurable centered observable of EVERY exact seven-link GroundData, for ALL real beta,t. These data are genuinely instantiated by1689's `data beta t` and its evenization, so the result is not merely an uninhabited operator contract. No small-t assumption is needed for this UPPER bound;1691's LOWER obstruction retains its own small-t restriction.

### Exact mechanism and new native estimates

The proof reuses `YMPositivePower.average_reset_range` and `YMPositiveKernel.ground_bridge`. The row-normalization reference nu is proportional to psi*dHaar; the ACTUAL invariant law pi is proportional to psi^2*dHaar. `bridgeReference`, its probability proof and `transfer_bridge` construct and identify the former without equating these laws. `nativeSteps_mean` proves centering under pi at EVERY actual iterate from the existing bounded-probe stationarity theorem.

`Foundation/YMPositiveMixing.lean` proves a single reusable range-contraction lemma: for an actual average recursion with jointly measurable0<m<=k<=M, initial bound B, and zero mean at every iterate under a possibly DIFFERENT probability pi, the pointwise bound is2*B*(1-m/M)^n. Its proof transports enclosing intervals through the verified reset-range estimate, contracts their width, proves integrability and uses the pi mean to locate0 inside each interval. No invariant-reference assumption, extremum attainment, spectral positivity, residual-kernel library or extra stochastic construction is needed. This is classical positive-kernel mixing mathematics verified for the concrete research bottleneck; no novelty claim is made.

Four existing vacuum helpers (`lower`, `upper`, `lower_pos`, `kernelDensity_bounds`) were exposed publicly for reuse. All four bodies/statements are unchanged apart from visibility. `reset_ratio` proves exact cancellation of ALL seven Wilson partition factors:

    alpha(beta,t)=lower/upper=exp(-2*abs(t)-14*abs(beta)),  0<alpha<=1.

For an actual bounded measurable f with |f|<=B and integral f dpi=0, `nativeSteps_centered_bound`, `native_covariance_bound` and `native_covariance_tendsto_zero` prove

    |P^n f(s)| <=2*B*(1-alpha)^n   for EVERY starting state s,
    |integral f(s)*P^n f(s) pi(ds)| <=2*B^2*(1-alpha)^n,
    actual stationary covariance tends to0 as n tends to infinity.

`native_covariance_macro_bound` and `sufficient_step_count` establish the explicit sufficient count

    n >= r*exp(2*abs(t)+14*abs(beta))
    implies |actual covariance at n| <=2*B^2*exp(-r).

For positive variance V, divide by V; the normalized prefactor is2*B^2/V and is NOT silently bounded uniformly in coupling or volume. No uniform all-L2 operator-norm spectral-gap estimate is claimed from this bounded-probe estimate. The result is compatible with1691's no-uniform-FIXED-count theorem: the order of the coupling and step-count limits matters. Coupling-dependent iteration really does restore decay for the constructed local process, but a physically useful/sharp count is not supplied by this coarse upper bound.

### Why this is not yet a physical-distance or four-dimensional result

A direct reuse audit of `YMFiniteWilsonVacuum.ground_exists` gives lower and upper kernel constants m=l^2*exp(-N*abs(beta)) and M=u^2*exp(N*abs(beta)). Their ratio is algebraically (l/u)^2*exp(-2*N*abs(beta)). For fixed positive |beta| and fixed0<l<=u this tends to0 as the link count N grows; a spatial Wilson half-weight generally adds further volume dependence to l/u. This is a rigorous obstruction to obtaining a NONZERO volume-uniform reset certificate by this global min/max argument. It is NOT a proof that the actual gap vanishes. This audit is a mathematical consequence of the displayed verified constants, not a newly claimed Lean formalization of a physical4D limit.

Likewise, choosing arbitrary lattice spacing a and physical rate m_phys with m_phys*a<=alpha would merely be a CONDITIONAL conversion of exp(-n*alpha) to exp(-m_phys*n*a). No physically justified relation a(beta), renormalization trajectory, homogeneous-action comparison, Gauss-law Hilbert-space identification or infinite-volume/continuum theorem has been established here. Setting t=beta is allowed in the local UPPER theorem, but that one-spatial-plaquette seven-link system is not the complete homogeneous spatial3D/physical4D transfer. The earlier lower theorem cannot be extended to t=beta by this observation.

The concrete next mass-gap-related bottleneck is local/block or gauge-projected control that avoids the global factor exp(-2*N*abs(beta)), together with justified homogeneous-action and physical-scale hypotheses. Repeating finite-dimensional positivity/eigenfunction existence or optimizing the coarse sufficient count cannot discharge it. Preserve both the genuine local slowing obstruction and this genuine finite-coupling decay result; neither establishes/refutes the Millennium mass gap.

### Verification, independent tests and source integrity

The full root build passed6956 jobs in27.1583499 seconds. The complete transitive axiom audit passed54175 declarations in42.027468 seconds, accepting only propext, Classical.choice and Quot.sound. All18 unabridged public types and full proof/definition bodies were reviewed, including the four previously private helpers; the two new private integrability/positive-mass proofs were reviewed. The generic recursion's mean-zero hypotheses are discharged by actual native stationarity in the instantiated theorem. No sorry/admit/new axiom, trust/compiler/toolchain/resource/heartbeat change, error suppression or skipped gate was introduced.

Nine independent Lean examples cover the exact reset ratio, reset1 at zero parameters, sign symmetry, zero-coupling one-step collapse of every bounded centered native probe, actual covariance convergence for arbitrary constructed evenized observables, sufficient-count native bounds, native mean preservation, the actual kernel/average bridge and the deliberately different reference/invariant laws. The zero-coupling test initially tried to prove an absolute-value inequality after norm_num had already reduced it to equality; the repair is test-only. The final independent Lean checks passed in24.747178 seconds.

Exact Fraction checks verify51 iterates of a genuinely unequal-reference example: mu=(1/2,1/2), k=[[2,1],[1,1]], P=[[2/3,1/3],[1/2,1/2]], pi=(3/5,2/5), f=(2,-3). The pi mean is0 while the mu mean is-1/2; f is a1/6 eigenmode and satisfies the proved range/covariance bounds. The mu-centered vector(1,-1) instead converges to its NONZERO pi mean1/5, directly refuting replacement of invariant-law centering by reference-law centering. Dropping strict positivity allows the identity chain to retain a centered nonzero vector. Rate diagnostics at t=.2 give sufficient r=1 counts7,1794075 and approximately3.75e30 for beta=.1,1,5: evidence of poor quantitative utility, never Lean inputs or a physical prediction.

Integrity authenticates1691's source manifest against exact approval e54d77525788f76ba2fc8609a66b8a9ee2539c37 and covers2775 Foundation/root files. Exactly two new modules, four helper visibilities in the vacuum source, root import and AxiomAudit differ; every previous proof body is identical. All3 pinned configurations,113 baseline manuscripts and21 Yang--Mills originals (20 distinct hashes) remain unchanged. Evidence: C:/Users/ramir/AppData/Local/Temp/stardust-ym-1692-* (complete build, transitive/unabridged type audit, independent Lean/exact-law tests, declaration inventory and authenticated source manifest). ResearchSources remains read-only/uncommitted; unrelated drafts are preserved.

Yang--Mills remains ACTIVE; Bakry PAUSED and the queue unchanged. Exact-commit approval and guarded PUBLIC two-branch synchronization are separate closure gates; this pre-commit report does not claim remote success.


## Checkpoint 1693 — actual gauge averaging preserves every physical slow covariance mode

A focused test of the gauge-sector escape route is now verified in `Foundation/SU2SevenLinkGaugeAverage.lean`. The aim is not a general gauge library: the actual constructed1690/1691 slow mode was already gauge invariant, so one must test whether an actual gauge average changes its dynamics before crediting projection with a new contraction mechanism.

### Concrete probability objects and exact theorem

`Gauge` is the existing six-vertex group Fin6->SU2. `gaugeHaar` is its actual product Haar probability. For ANY probability nu on that group, `randomizer nu` is an actual Markov kernel formed by mapping Kernel.id times Kernel.const(nu) under the jointly measurable physical seven-link gauge action. `randomizer_apply` identifies each transition measure exactly as nu pushed forward by g |-> g*s, and `randomizer_integral` gives its actual integral. This includes Dirac laws and the full continuous six-vertex Haar law; no finite-center surrogate is substituted for SU2.

`averagedKernel nu d` first randomizes the input gauge representative and then applies the original constructed native Markov kernel. Both Markov probability and stationarity under the ORIGINAL pi=d.stationary are proved. Stationarity holds for every bounded measurable test, not just invariant ones. The proof uses actual bounded Fubini, gauge invariance of pi and the existing native stationarity theorem; it assumes no new vacuum, quotient law or physical reconstruction.

For EVERY bounded measurable gauge-invariant f, `invariant_integral` proves that the averaged kernel acts exactly as the original kernel. `invariant_steps` proves exact pointwise equality of EVERY time iterate, not just a quadratic-form estimate or one-step equality:

    averagedSteps(n,f)(s)=nativeSteps(n,f)(s),  for all n,s.

It reuses1691's proof that native evolution preserves invariant observables. Consequently every stationary lag pairing of these f is unchanged. `no_uniform_averaged_steps` transfers the actual1691 obstruction: for ANY probability nu, EVERY fixed count n, EVERY q<1 and EVERY large-beta cutoff R, there exist beta>R and0<t<=1 with a constructed bounded invariant f of mean0, variance>0 and AVERAGED-chain normalized covariance greater than q. In particular this holds after FULL six-vertex SU2 Haar averaging. Thus discarding gauge-variant components cannot erase this already gauge-invariant local slow mode.

This is classical group-averaging mathematics applied to actual verified objects and the particular native obstruction; no claim of a new general Reynolds projection theorem is made. No idempotence or reversibility is asserted for an arbitrary, possibly asymmetric nu. The present construction does not identify a quotient/OS Hilbert space or establish a continuum field theory.

### Exact scope of the failed inference

The tested inference is that gauge averaging ALONE removes the coupling-nonuniform fixed-step covariance obstruction. That inference fails. This does NOT prove that gauge averaging cannot improve a crude density/minorization certificate, that a volume-uniform estimate at FIXED beta is impossible, or that a different block transformation cannot help. The theorem preserves the earlier positive, beta-dependent small spatial tilt and does not extend its lower obstruction to equal coupling t=beta, full homogeneous spatial action or actual4D volume/continuum limits.1692's coupling-dependent native decay remains valid on the same invariant observables because their entire dynamics agree.

An exact finite diagnostic sharply separates these issues: a two-state physical chain with eigenvalue1-2*eps times a frozen three-state gauge coordinate has raw zero transition entries. Full gauge averaging makes every entry strictly positive and kills gauge-variant modes, while preserving EVERY iterate of the physical mode and its eigenvalue arbitrarily close to1. It is therefore wrong to equate improved strict positivity after averaging with disappearance of a physical slow mode. This diagnostic is not the SU2 Haar proof; that is the Lean theorem above.

The selected manuscript passage is `ResearchSources/Incoming/block_contraction_spectral_gaps.tex`, SHA256 0C40FA6B92B830C0E2309BD6471D55CB0EB9BFB94296B9267AD23A5280FA4C60. Its unscreenable-mode corollary uses the LINEAR Schur projector P_A=A(A^T A)^(-1)A^T and P_A*v=0; its4D application invokes spanning-tree gauge fixing, linearized plaquettes, corridor coercivity and a fixed group-Laplacian gap. That Schur projection is NOT the group average constructed here. The present result neither refutes the valid linear Schur identity nor repairs the manuscript's nonlinear, norm-comparison, corridor, scaling or continuum obligations. Shared words such as projection are not a transfer theorem.

The physical bottleneck remains a quantitatively different local/block mechanism with its actual norm, boundary flux/cutoff terms and scale/volume dependence controlled. Ordinary gauge averaging preserves the physical test sector and supplies no new dynamics there. Better bounds after averaging are permitted but must be proved; physical distance cannot be obtained by naming a step count.

### Full verification and independent checks

The complete root build passed6957 jobs in26.5673307 seconds. The complete transitive axiom audit passed54199 declarations in42.2820547 seconds, allowing only propext, Classical.choice and Quot.sound. All15 unabridged public types were reviewed:9 theorem proofs,4 definitions,1 abbreviation and1 probability instance; the joint-action measurability proof and6 private instances were reviewed in full. The initial measurable-action elaboration hit the default200000-heartbeat limit; explicit product-map composition repaired the proof without raising limits or changing semantics. No sorry/admit/new axiom, trust/compiler/configuration/resource change or suppressed check was introduced.

Seven independent Lean examples check full-Haar Markov realization, identity-gauge Dirac randomization, invariant observables fixed by the randomizer, actual all-iterate agreement for constructed observables, full bounded-test stationarity, unchanged native stationary covariances and rejection of a universal fixed-step q<1 bound. The Dirac test needed measurable map_dirac evaluation, local Borel topology instances and explicit joint-action composition; these harness-only elaboration repairs changed no source theorem and retained default limits. The final independent Lean checks passed in26.2153128 seconds. Exact Fraction diagnostics verify78 product-chain iterates for eps=1/4,1/32,1/1024, stationary probability, genuine improvement of strict positivity, preservation of the physical mode and erasure of a noninvariant gauge mode. No external values are Lean inputs.

Integrity authenticates1692's manifest against exact approval6b6b4977908260dd2cb9ba872a8a7166246377c0 and covers2776 Foundation/root files. Exactly the new module, root import and AxiomAudit differ; all earlier mathematical sources are byte-identical. All3 pinned configurations,113 baseline manuscripts and21 Yang--Mills originals (20 distinct hashes) remain unchanged. Evidence: C:/Users/ramir/AppData/Local/Temp/stardust-ym-1693-* (full build, complete transitive/unabridged type audit, independent Lean/exact checks, declaration list and authenticated manifest). ResearchSources and unrelated untracked drafts are preserved.

Yang--Mills remains ACTIVE; Bakry PAUSED, all other priorities unchanged. Exact-commit approval and guarded PUBLIC two-branch synchronization remain separate closure gates; this pre-commit record does not claim remote success.


## Checkpoint 1694 — genuine joint-link cubic obstruction and a valid Schur repair

The focused block audit has found a concrete missing premise in the manuscript's evenness shortcut. `Foundation/SU2JointPlaquetteCubic.lean` constructs actual unit-quaternion exponential links, maps them through the existing faithful SU2 representation, and inserts them into the EXISTING seven-link plaquette state. All original manuscripts remain unchanged. This is an exact local Wilson-action calculation, not a finite-group surrogate or a claim about the continuum measure.

### Actual noncommuting links and joint derivatives

For the three imaginary quaternion axes I,J,K, `axisRaw_exp` proves that the link curves are NormedSpace.exp(t*axis), for EVERY real t, including negative and zero parameters. Unit norm and actual SU2 membership are proved. The tested first plaquette is exp(xI)*exp(yJ)*exp(zK), with the fourth oriented factor the identity. `configuration` is the original physical seven-link state with these three path factors; the second plaquette is unchanged. `action_gauge` proves the action value is invariant under EVERY existing six-vertex gauge transformation.

Writing A=1-halfTrace(plaquette), `action_formula` proves

    A(x,y,z)=1-cos(x)cos(y)cos(z)+sin(x)sin(y)sin(z).

Consequently `mixed_hessian` gives D_y D_x A(0,0,z)=sin(z), and `mixed_third_at_identity` gives D_z D_y D_x A(0,0,0)=1. `odd_part` proves the exact identity A(t,t,t)-A(-t,-t,-t)=2*sin(t)^3; `not_even_in_any_neighborhood` supplies a nonzero witness inside EVERY positive angle neighborhood. Single-axis evenness A(x,0,0)=1-cos(x) remains true and is independently checked. Reversing all coordinate signs WITHOUT reversing word order is not inversion of the whole noncommuting plaquette; the cubic does not contradict trace invariance under full orientation reversal.

The quadratic core Q=(x^2+y^2+z^2)/2 has zero x,y mixed entry. `mixed_remainder_hessian` proves D_y D_x(A-Q)(0,0,z)=sin(z) exactly. `mixed_hessian_linear_bound` supplies the valid global slice bound |sin(z)|<=|z|. `no_quadratic_mixed_hessian_bound` refutes a local O(z^2) bound using the existing verified `SU2OrderedLinkHessian.no_local_quadratic_bound`, rather than duplicating its small-angle argument. The nonzero cubic is a classical nonabelian/BCH mechanism; no publication-level novelty is claimed.

### The additive O(1) allowance does not automatically repair the budget

The selected source is `ResearchSources/Incoming/block_contraction_spectral_gaps.tex`, SHA256 0C40FA6B92B830C0E2309BD6471D55CB0EB9BFB94296B9267AD23A5280FA4C60. Its4D application says Wilson evenness/no cubic implies K_xx,K_xy=O(beta*delta^2)+O(1). The proved counterexample targets the inference from single-holonomy evenness to JOINT LINK-coordinate evenness. A=1-halfTrace is exactly the Wilson normalization multiplying beta in that source, so the scaled mixed remainder on this slice is beta*sin(z).

`no_uniform_quadratic_plus_constant` proves that NO constants C,C0>=0 and fixed positive neighborhood can bound beta*|mixed remainder| by C*beta*z^2+C0 simultaneously for all beta>=1 and all positive sufficiently small z. This tests the FULL additive-constant claim, not merely an omitted-C0 version.

More sharply, `budget_requires_inverse_coupling_window` proves: if0<beta,0<=z<=1,0<=C,4*C*z<=1 and that bound holds, then beta*z<=4*C0. Along this slice, retaining the proposed quadratic-plus-constant budget therefore forces an O(1/beta) window. `thermal_window_counterexample` gives violations at ARBITRARILY LARGE s (with an explicit requested cutoff), taking beta=s^2,z=1/s. Here beta*z^2=1 while the scaled mixed Hessian is s^2*|sin(1/s)|. For every fixed nonnegative C,C0 it exceeds C+C0 beyond some arbitrarily large witness. The name thermal_window denotes this inverse-square-root scale only; no stochastic typical-fluctuation law, corridor probability or lattice equilibrium asymptotic is assumed or proved.

### Positive repair: linear mixed terms can still give quadratic Schur loss

It would be an incorrect inference to discard the entire Schur route because K_xy is linear in angle. `diagonal_hessian` and `action_symmetric_xy` identify BOTH actual x,y diagonal entries at(0,0,z) as cos(z); the off-diagonal entry is sin(z). Eliminating y at positive cos(z) gives the actual scalar slice Schur complement

    S(z)=cos(z)-sin(z)^2/cos(z).

`schurSlice_lower` proves S(z)>=1-(5/2)*z^2 whenever cos(z)>=1/2. This is consistent with the existing `CoerciveSchurStability` machinery: a CORRECT O(beta*delta) mixed block contributes O(beta*delta^2) after squaring and dividing by O(beta) interior coercivity. The new exact slice calculation shows why a failed mixed-Hessian shortcut does not by itself refute a robust boundary-curvature theorem. It does not prove every boundary diagonal block has a quadratic remainder or that all link directions enjoy this slice bound.

Scope is crucial. Evenness in the LOGARITHM OF ONE PLAQUETTE is true; that logarithm depends nonlinearly on the individual link logarithms. A carefully specified spanning-tree/background coordinate change may redistribute or remove some cubic terms, but then its derivative, metric, Haar/Jacobian and boundary effects must be audited. The present formal counterexample is in genuine product-link exponential coordinates. It does NOT automatically identify three permitted independent non-tree coordinates in the manuscript's full4D gauge-fixed block, nor prove that a spatial plaquette sum lacks cancellations. Those are exact remaining obligations, not implicitly discharged by sharing the word Wilson.

The next productive test is whether the actual prescribed gauge-fixed/block geometry confines the cubic terms to mixed blocks with quadratic Schur losses, or leaves linear boundary-block errors that exceed the contraction budget. Need actual norm/cutoff/flux control and a physical scale/volume bridge. No mass gap, failure of all coordinate repairs, or impossibility of Yang--Mills construction is claimed.

### Complete verification and independent checks

The FINAL full root build passed6959 jobs in46.8657597 seconds. The FINAL complete transitive axiom audit passed54246 declarations in50.6311967 seconds, allowing only propext, Classical.choice and Quot.sound. Earlier passes before adding the substantive positive Schur repair are superseded. All27 unabridged public types and complete bodies were reviewed:19 theorem proofs and8 definitions. No old proof/source body changed; no sorry/admit/new axiom, trust/compiler/toolchain/heartbeat/resource change or suppressed verification was introduced. Existing imported resource settings remain unmodified.

Twelve independent Lean examples cover genuine signed-time exponential identity, valid single-axis parity, exact joint odd difference1/4 at pi/6, mixed remainder1/2 at pi/6, joint third derivative1, witnesses inside angle1/1000, contradiction to a zero-additive-constant budget, thermal witnesses beyond s=100, full gauge invariance, actual Schur lower bound, Schur value1 at identity and identification of the other diagonal Hessian. The initial thermal test needed explicit normalization of1+2 to3; the harness repair changes no source theorem. The final independent Lean checks passed in28.215062 seconds.

Exact Fraction tests check36 noncommuting rational unit-quaternion products and reversal of their cubic sign,25 rational sine-lower certificates for arbitrarily large thermal witnesses, and91 positive Schur-repair cases. The rational quaternion parameters are stereographic circle coordinates used only as an independent product check, not a replacement for the verified exponential identity. Diagnostic scaled mixed Hessians at s=2,10,100,1000 are approximately1.9177,9.98334,99.99833,999.99983. No diagnostic values are Lean inputs.

Integrity authenticates1693's manifest against exact approval14eb3f1a44f4c81eb4d9931e9ee6fd1f78a47329 and covers2777 Foundation/root files. Exactly the new joint-plaquette module, root import and AxiomAudit differ. All earlier mathematical sources,3 pinned configurations,113 baseline manuscripts and21 Yang--Mills originals (20 distinct hashes) remain unchanged. Evidence: C:/Users/ramir/AppData/Local/Temp/stardust-ym-1694-* (FINAL full build, complete transitive/unabridged type audit, independent Lean/exact diagnostics, declaration inventory and authenticated manifest). ResearchSources stays unmodified/uncommitted; unrelated untracked drafts are preserved.

Yang--Mills remains ACTIVE; Bakry PAUSED and all other queue priorities unchanged. Exact-commit approval and guarded PUBLIC two-branch synchronization remain separate closure requirements; this pre-commit record does not claim remote success.


## Checkpoint 1695 — cubic survives actual four-dimensional tree fixing and the full retained action

The principal geometric limitation of1694 is partially discharged by a concrete FOUR-DIMENSIONAL finite-cell calculation. The work reuses the exact `OneSidedBlockIncidence` and `OneSidedCapComplex` geometry already in the library, rather than introducing another cube or a broad gauge-theory infrastructure. The original manuscripts and all previous mathematical sources remain unchanged.

### Actual incidence and a genuine spanning tree

`Foundation/FourCubeChordIncidence.lean` uses the existing vertices Fin4->Fin2,32 retained oriented edges and24 internal square faces. It proves each face has four distinct valid edges and each retained edge belongs to three internal faces. `three_chords` gives the exact counting theorem: for ANY subset T of15 retained edges, some face contains at least3 complementary edges. Removing15 edges leaves17; their face incidences total51, exceeding24*2=48. The theorem assumes only T's inclusion/cardinality, not an unproved tree or a numerical rank certificate. It does not by itself construct a nonlinear witness for every possible tree.

The explicit axialTree retains an edge in direction i when all later base coordinates vanish. Its15-edge count, unique incoming edge at each nonroot vertex, parent relation and four-step parent-to-origin certificate are kernel checked. `Foundation/FourCubeAxialTree.lean` constructs the actual SimpleGraph on these16 vertices, proves connectedness and15 graph edges, proves `graph.IsTree` by the established finite-tree criterion, and proves exact equivalence between graph adjacency and the retained axialTree edge list. Thus the tree-gauge statement is not inferred from cardinality alone.

### Genuine non-tree SU2 field and all24 internal plaquettes

`Foundation/FourCubeWilsonCubic.lean` assigns the actual1694 exponential axes to three non-tree links of the face at base(0,0,0,1), directions0,1. Specifically edgeA carries exp(xI), edgeB carries exp(yJ), and edgeC carries exp(zK)^(-1), compensating the face's inverse orientation. All other retained links are identity. `field_tree_certificate` combines the actual graph-theoretic tree proof with identity on EVERY tree edge for EVERY real x,y,z. No gauge zero-mode elimination or supplied vacuum is assumed.

`faceAction` is the genuine oriented Wilson expression1-halfTrace(U0*U1*U2^(-1)*U3^(-1)). `innerAction` sums ALL24 existing internal faces. Exact face classification proves the multiplicities(1,2,2,2,17): one selected three-link face, two other faces for each selected edge, and17 identity faces. With A the1694 three-link action and c_x=1-cos(x), etc., `innerAction_formula` proves

    S_inner(x,y,z)=A(x,y,z)+2*(c_x+c_y+c_z).

The cubic is therefore not an artifact of discarding neighboring plaquettes. `inner_odd_part` gives S_inner(t,t,t)-S_inner(-t,-t,-t)=2*sin(t)^3. `inner_mixed_hessian` gives D_y D_x S_inner(0,0,z)=sin(z), `inner_mixed_third` gives third derivative1 at the identity, and `inner_thermal_counterexample` transfers1694's arbitrarily large beta=s^2,z=1/s violations of a fixed quadratic-plus-constant mixed-entry budget. The extra single-axis terms have zero x,y mixed derivative.

`gaugeField` uses actual16-vertex SU2 transformations at each edge's source/target. `faceAction_gauge` and `innerAction_gauge` prove invariance under EVERY such transformation, by exact reuse of `SU2WilsonConvolution.loop4_gauge` and the existing cube corner identity. This is an actual nonabelian Wilson field, not Z2 center data or a gauge-variant trace proxy.

### Boundary-frozen72-term model and precise variable roles

The existing one-sided geometry also contains48 upper/ribbon faces. When all exterior ribbon links are fixed to identity, their Wilson products reduce to the single retained-link factors. `upperAction` formalizes that literal collapsed expression. Exact small fiber counts prove multiplicities(1,2,2,43), hence

    S_upper=c_x+2*c_y+2*c_z,
    S_boundary-fixed=A+3*c_x+4*c_y+4*c_z.

`boundary_fixed_odd_part` proves the SAME2*sin(t)^3 odd part after adding ALL48 frozen-boundary ribbon contributions. The count is48, not a replacement or omission of the companion's boundary geometry. `boundaryFixedAction` is precisely the collapsed expression; this source does not introduce or claim verification of a complete112-link variable-boundary nonabelian calculus. The boundary-frozen expression is not asserted invariant under arbitrary transformations that would also change the frozen exterior links.

The variable split must not be lost: x,y,z in this witness vary RETAINED INTERIOR links. The surviving mixed term therefore lies in an interior-interior Hessian block in the companion's notation. It does NOT automatically refute a claim restricted to boundary-boundary or boundary-interior entries K_xx,K_xy. A separate actual ribbon calculation varying the cap/crossing/boundary links is still needed to test those entries. Nor does this computation identify every alternative tree/background/holonomy-coordinate chart. The existence of one genuine tree-fixed counterexample disproves a blanket assertion that tree fixing makes all joint link dependence even; it is not a proof that no carefully specified coordinate repair exists.

### Source comparison and next mathematical bottleneck

Selective source checks: `ResearchSources/Incoming/block_contraction_spectral_gaps.tex`, SHA256 0C40FA6B92B830C0E2309BD6471D55CB0EB9BFB94296B9267AD23A5280FA4C60, at its Wilson application still invokes evenness/no cubic to infer K_xx,K_xy=O(beta*delta^2)+O(1). `ResearchSources/Incoming/su2_companion.tex`, SHA256 06D3B4183167B43129D715B76D6040E3EE5E4D2E8A58F580318B5311C3011839, explicitly defines16 vertices,32 interior links,80 boundary links and72 touching plaquettes. It also EXPLICITLY RETAINS a cubic vertex and claims its FIRST centered-Gaussian integral vanishes by parity. These are different mathematical assertions. The present pointwise cubic does NOT refute centered-Gaussian odd-polynomial cancellation, establish or refute the claimed O(g^4) cluster remainder, or justify removing cutoffs/conditioning/renormalization errors. No novelty is claimed for the underlying classical BCH mechanism or finite-tree counting.

The1694 positive Schur repair remains valid and important: a linear mixed term can produce a quadratic Schur loss after elimination. The remaining bottleneck is to locate actual cubic terms in the prescribed boundary/interior blocks, prove the corrected norms and cutoff/flux estimates, and then test their inverse-coupling contraction budget and physical-scale/volume behavior. This finite4D cell establishes no continuum or infinite-volume measure, transfer-operator gap, physical mass gap or failure of Yang--Mills existence. Do not extrapolate the local cubic or finite positivity to any such conclusion.

### Complete verification and independent checks

The full root build passed6997 jobs in30.8204539 seconds. The complete transitive axiom audit passed54325 declarations in41.9643245 seconds, accepting only propext, Classical.choice and Quot.sound. All51 unabridged public types were reviewed:29 theorem proofs,21 definitions and1 decidable instance; all8 private helper proofs were reviewed. Exact finite certificates use ordinary kernel-checked decide, not native_decide or unverified external combinatorics. Several initial oversized finite evaluations reached default recursion limits; small case splits, fiber counts and the Nat-specific scalar-action identity repaired them without increasing recursion/heartbeat limits. No sorry/admit/new axiom, trust/compiler/toolchain/resource change or suppressed gate was introduced.

Eleven independent Lean checks passed in27.3699722 seconds, covering graph-theoretic treehood, exact tree cardinality, the generic three-chord consequence, nonvacuous tree-fixed field, full24/72-term formulas, exact odd difference1/4 at pi/6 with frozen ribbons, full internal mixed third derivative1, thermal witnesses beyond s=100, arbitrary vertex-gauge invariance and exact graph/edge-list identification. No source repair was needed for this final independent harness.

Exact Fraction/quaternion tests independently check27 signed parameter triples, all retained field values on the tree, all24 internal products, all48 ribbon contributions and648 noncommuting face-gauge identities. They independently certify connectivity of all16 vertices, incidence totals51 versus capacity48 and the actual multiplicities(2,2,2) and(1,2,2). These checks are diagnostics, not Lean inputs or a substitute for the full-cell proof.

Integrity authenticates1694's manifest against exact approvalf432ae8fecec0dfca97fc4d191a6d6d91a9e98cb and covers2780 Foundation/root files. Exactly the three new focused modules, root import and AxiomAudit differ; all older mathematical sources,3 pinned configurations,113 baseline manuscripts and21 Yang--Mills originals (20 distinct hashes) are unchanged. Evidence: C:/Users/ramir/AppData/Local/Temp/stardust-ym-1695-* (full build, complete transitive/unabridged type audit, independent Lean/exact checks, declaration inventory and authenticated source manifest). ResearchSources remains unmodified/uncommitted and unrelated untracked drafts are preserved.

Yang--Mills remains ACTIVE; Bakry PAUSED and all other priorities unchanged. Exact-commit approval and guarded PUBLIC two-branch synchronization remain separate closure gates; this pre-commit entry does not claim remote success.

## Checkpoint1696 — actual boundary-variable cubic obstruction in the full72-face cell

The previous checkpoint's interior/interior witness did not test the manuscript's boundary blocks. `Foundation/FourCubeBoundaryCubic.lean` now uses the EXISTING `OneSidedCapComplex.FullEdge=Interior+(Cap+Upper)` and its72 faces, rather than a new surrogate. Choose the ribbon `(edgeA,3)`, put exp(zK) on its retained interior edge, exp(xI) on its HIGH cap boundary link, and exp(-yJ) on its upper boundary link; all other links are1. The two boundary directions are different sum constructors from the retained interior direction. `boundary_cap_value`, `boundary_upper_value` and `interior_value` identify them exactly. `tree_fixed` proves EVERY retained axial-tree link remains1 for ALL real parameters. These are the actual quaternion-to-SU(2) exponential axes proved previously, not a finite approximation.

### Exact result and the failed inference

`fullAction` sums the24 original interior Wilson terms and ALL48 actual ribbon words, with orientation interior*highCap*upperInverse*lowCapInverse. The selected ribbon has cyclic trace K(z)I(x)J(y). `ribbonClass_count` proves that the48 ribbons consist of one triple term, two additional single-x terms and45 zero terms; the24 interior terms supply three single-z terms. `fullAction_formula` proves, for every real x,y,z:

    fullAction(links x y z) = A(x,y,z)+2(1-cos x)+3(1-cos z),
    A(x,y,z)=1-cos x*cos y*cos z+sin x*sin y*sin z.

`boundary_mixed_hessian` proves D_y D_x fullAction(0,0,z)=sin z with BOTH differentiated variables boundary links. `boundary_interior_mixed_hessian` proves D_z D_x fullAction(0,y,0)=sin y with an actual boundary/interior pair. `mixed_third_at_identity` is1 and `full_odd_part` is2 sin(t)^3. The quadratic Taylor core on this slice is (3x^2+y^2+4z^2)/2, whose cross entries vanish, so subtracting that core does not remove either mixed term.

`no_uniform_boundary_quadratic_plus_constant` refutes a coupling-uniform scalar bound beta*|D_yD_x fullAction(0,0,z)| <= C*beta*z^2+C0 on ANY fixed positive neighborhood with nonnegative constants. `boundary_thermal_counterexample` supplies witnesses at arbitrarily large s, beta=s^2 and z=1/s, where the proposed quadratic budget C+C0 stays fixed. This closes the1695 variable-split gap for the ambient product link coordinates of the one-sided cell. It does not assert a theorem for every alternative coordinate chart, constrained boundary submanifold, quotient metric or tree prescription. A formal operator-norm comparison in any such different domain remains a separate obligation.

Selective source recheck: `ResearchSources/Incoming/block_contraction_spectral_gaps.tex`, SHA256 0C40FA6B92B830C0E2309BD6471D55CB0EB9BFB94296B9267AD23A5280FA4C60, Wilson application around lines614–636, invokes single-holonomy evenness/no cubic to infer K_xx,K_xy=O(beta*delta^2)+O(1). That inference fails for the genuine boundary-link calculation above. Its separate32-interior/80-boundary block interpretation is explicit in `su2_companion.tex`, SHA256 06D3B4183167B43129D715B76D6040E3EE5E4D2E8A58F580318B5311C3011839, around lines572–587. Original bytes are preserved.

### Positive routes and exact remaining obstacles

The companion's different claim that a cubic vertex has zero FIRST centered-Gaussian integral by parity is NOT refuted by a pointwise cubic. Integrated cancellations, conditioning, cutoffs, measure Jacobians and cluster-remainder bounds require their own domain and error proofs. Nor does this disprove contraction: a corrected O(beta*delta) entry is STILL o(beta) as delta tends to0. The1694 Schur estimate also explicitly shows that linear mixed entries can yield quadratic loss after elimination. Those possibilities must be tested, not discarded because the stronger pointwise shortcut failed. No novelty is claimed for classical SU(2)/BCH identities.

Next substantive bottleneck: replace the false pointwise quadratic premise by valid linear estimates and determine whether the actual stationary transfer-operator/corridor/flux budget survives with a coupling-dependent physical distance scale and scale/volume-uniform constants. Finite-cell algebra supplies neither the required stationary spectral estimate nor a continuum/infinite-volume construction or a positive physical Yang--Mills mass gap. Do not infer any of these from the current counterexample, finite-cell curvature, or an unverified external existence claim. Full48-vertex gauge invariance was tested independently on exact quaternion instances here; a new universal full-cap gauge-invariance theorem is NOT claimed in this checkpoint (the existing internal gauge and loop identities remain verified).

### Verification, type/proof review and integrity

Full root build:6998 jobs,27.8100655 seconds initially and11.2178644 seconds on the final unchanged root. Complete canonical transitive audit:54368 safe Foundation declarations,42.8220109 seconds initially and40.8664006 seconds on the final source set, accepting ONLY propext, Classical.choice and Quot.sound. All26 public types were printed unabridged and reviewed:23 new declarations (8 definitions,15 theorems), plus three previously private unchanged helpers `axis_trace`, `trace_one`, `triple_action`; all7 private helper proofs were reviewed. The old helper statements and bodies are byte-identical after ONLY private-to-public spelling and removal of one surplus EOF blank line. No theorem assumption or result was weakened.

Eleven independent Lean checks passed in27.5113692 seconds: the two distinct boundary constructors, interior value, tree fixing, full72-term formula, both mixed entries equal1/2 at pi/6, mixed third derivative1, odd difference1/4, a thermal witness beyond s=100 and the quantified uniform-bound obstruction. An initial harness needed only explicit normalization of1+1=2; no mathematical source changed. Independent Fraction/quaternion tests cover27 signed rational parameter triples, all112 links, all72 face words, exact ribbon counts(1,2,45), and gauge trace preservation under transformations at ALL48 vertices (1944 face checks). These tests diagnose the construction and do not supply Lean axioms or replace the real-parameter proofs.

Authenticated1695's manifest against its exact-commit approval4e48d335b5f76f0bacef0fe0f5273796759c1310. Integrity covers2781 Foundation/root files: only the new focused module, the three old helper visibilities/EOF style, root import and axiom ledger differ. All other mathematical sources, all3 pinned configurations,113 baseline manuscripts and21 Yang--Mills originals (20 distinct hashes) remain unchanged. The concrete face set is marked irreducible LOCALLY during elaboration to avoid eagerly unfolding its finite enumeration; explicit finite proofs still unfold it when needed. This changes neither the definition nor kernel checking; no heartbeat/recursion/trust/toolchain configuration change, sorry, admit, new axiom, native_decide or suppressed gate is introduced. Evidence is under C:/Users/ramir/AppData/Local/Temp/stardust-ym-1696-*.

The separately executed persisted `Foundation/AxiomAudit.lean` initially failed on pre-existing IBM print commands whose modules it had never imported. The original HEAD already contains those commands without the root import. Added `import OperatorDerivativeRewrite` after checking that no Foundation module or root imports AxiomAudit; no audit print was removed and no mathematical declaration was introduced. The entire ledger then elaborated successfully in49.5575252 seconds. Full root build and canonical audit were repeated after this import repair; the final counts/types are unchanged. This is a ledger-dependency repair, not a new axiom or a substitute for the canonical audit.

Yang--Mills remains ACTIVE; Bakry stays PAUSED, all other queue priorities unchanged. ResearchSources is unmodified/uncommitted. Exact-commit approval and audited PUBLIC two-branch synchronization are required next; this pre-commit ledger does not claim remote success.

## Checkpoint1697 — genuine32-link Haar integration restores parity on the cubic witness family

`Foundation/FourCubeHaarParity.lean` constructs the ACTUAL finite-cell conditional partition for the existing one-sided112-edge/72-face Wilson model. `InteriorState=Interior→SU2` has32 links, `interiorHaar` is their genuine finite product of the already verified SU2 Haar probability measure, and `boundaryField x y s` assigns EVERY interior coordinate s freely. Only the chosen cap boundary link exp(xI) and upper boundary link exp(-yJ) vary; all other boundary links are1. This integrates ALL32 interior links, not the1696 axial slice or an abstract Gaussian approximation. `witness_inclusion` identifies that earlier pointwise field as an exact member of this family. No tree-quotient measure equivalence or alternative full120-face convention is assumed.

### Exact positive result

`fullAction_conjugate` proves invariance of the entire72-term action under simultaneous constant SU2 conjugation of all links. `turn_axis` proves the required conjugation identities for ACTUAL unit quaternions represented in SU2: the I conjugator fixes the I-axis and reverses J; the J conjugator reverses I and fixes J. `interiorConjugate_preserving` reuses `SU2GaugeCovariantTransfer.haar_conjugation_map` and Mathlib's `measurePreserving_pi` to prove preservation of the whole32-link Haar law. This is an exact measure change, not an unproved conditional-expectation or Gaussian parity assertion.

`fullAction_bounds` gives0≤S≤144 (72 terms each in[0,2]); all maps and Boltzmann weights are measurably constructed. For EVERY real beta,x,y, `boltzmann_integrable`, `partition_bounds` and `partition_pos` establish a finite, strictly positive partition Z with exp(-144|beta|)≤Z≤exp(144|beta|). In particular no zero/default nonintegrable Bochner integral is being used to manufacture parity. `partition_even_x` and `partition_even_y` prove exactly

    Z_beta(-x,y)=Z_beta(x,y)=Z_beta(x,-y).

The dimensionless effective action F=-log Z is therefore separately even; `freeEnergy_centered_mixed_difference` proves its centered mixed finite difference is EXACTLY zero for ALL real increments. `partition_zero_coupling` gives Z_0=1. This does NOT assert existence of boundary derivatives or silently use a derivative/integral interchange. In particular, a finite-difference identity is not presented as an already verified classical Hessian theorem.

The original pointwise cubic result remains true: at the1696 witness D_yD_x S(0,0,z)=sin z, and the simultaneous odd difference at pi/6 is1/4. An independent Lean check proves that pointwise asymmetry AND the integrated partition parity in the SAME example coexist. Thus failure of the pointwise O(beta*delta^2)+O(1) shortcut does not establish failure of integration-level cancellation.

### Actual probability-law and operator-calculus identification

`normalizedAction=-S/144` is measurably bounded by1 in absolute value; `scaled_exponent` identifies (144 beta)*normalizedAction with -beta S. `partition_tilt` identifies Z with the existing `BoundedExponentialTiltResponse.partition` on this ACTUAL32-link space. `cellLaw_probability`, `cellLaw_density` and `cellLaw_integral` then reuse the verified bounded-tilt construction to establish the genuine Gibbs probability measure

    d mu_beta,x,y = exp(-beta S(boundaryField x y s))/Z_beta(x,y) d Haar^32(s)

and its normalized integral formula. This is a concrete instantiation of existing machinery, not a new axiomatic law or a duplicate derivative library. The displayed general integral identity uses Lean's total Bochner convention; genuine bounded measurable observables are integrable under this probability measure, explicitly tested for a retained-link half-trace. No all-observable integrability or new unbounded operator domain is claimed.

### Manuscripts, mathematical scope and next bottleneck

This supplies a rigorously positive repair candidate relevant to `su2_companion.tex`'s distinction between pointwise cubic vertices and cancellation after integration. Source SHA256 remains06D3B4183167B43129D715B76D6040E3EE5E4D2E8A58F580318B5311C3011839. The separate failed single-holonomy-evenness inference in `block_contraction_spectral_gaps.tex` (SHA256 0C40FA6B92B830C0E2309BD6471D55CB0EB9BFB94296B9267AD23A5280FA4C60) is NOT restored as a pointwise statement. No original manuscript is edited or certified wholesale. Global conjugation and Haar uniqueness are classical; no novelty claim or publication is made.

The theorem is for the SPECIFIED two-boundary-axis family with all remaining boundary links1. It is not generic parity for arbitrary boundary data, a full O(g^4) cluster estimate, a proof that all cubic terms integrate away, a uniform effective-Hessian estimate, or a stationary transfer/contraction theorem. The coarse144 bound is finite-cell normalization control, not scale/volume-uniform mass-gap control. Constant-conjugation symmetry here relates DIFFERENT boundary parameters; it must not be confused with random gauge averaging at a fixed boundary, which cannot erase the previously verified gauge-invariant covariance modes.

Next substantive test: add boundary directions that cannot all be fixed while a single direction is reversed by one conjugation, and examine the actual integrated covariance/low-coupling coefficients using existing Haar moment and response results. Three orthogonal axes permit a cubic monomial invariant under simultaneous reversal of two coordinates, so the current symmetry does not forbid it. A candidate using two actual ribbons sharing one retained interior link should be independently tested before asserting any surviving integrated cubic coefficient. Boundary differentiability, differentiated cancellation, conditioning/cutoff error bounds, corrected Schur estimates, actual stationary operator norms, coupling-dependent physical distances and continuum/infinite-volume limits remain separate open obligations. No physical Yang--Mills mass gap is established or refuted.

### Complete checkpoint verification

Full root build:6999 jobs in26.7870875 seconds. Complete canonical transitive axiom audit:54439 safe Foundation declarations in41.6555026 seconds, ONLY propext, Classical.choice and Quot.sound. All44 public types were printed UNABRIDGED and reviewed (31 theorems,10 definitions,1 abbreviation,2 probability instances), with all5 private helper proofs and all definitions/instances reviewed in full. The entire persisted axiom ledger also elaborated successfully in48.0844924 seconds; no print checks were removed.

Fifteen independent Lean checks passed in29.0960013 seconds: actual interior cardinality32, Haar probability, full-action conjugation, witness inclusion, all-real-coupling integrability and strict normalization positivity, genuine Gibbs probability, expectation of1, nonconstant bounded half-trace integrability, both exact parameter parities, centered mixed free-energy difference, zero-coupling normalization, coexistence with the pointwise1/4 odd witness, and a concrete noncommuting-axis conjugation identity. Independent exact Fraction/quaternion tests use81 full-interior configurations/boundary pairs with ALL32 interior links varying, checking11664 face-trace symmetries on all72 faces and the actual112-edge field. These tests do not numerically approximate Haar integration; the measure-preservation and integral identities are Lean proofs.

Integrity authenticates1696's source manifest against exact approvalcb278d57fab78ed19084c3292d706cbedf394c3f. It covers2782 Foundation/root files: ONLY this new focused module, the root import and appended axiom print ledger change; ALL older mathematical sources,3 pinned configurations,113 baseline manuscripts and21 Yang--Mills originals (20 distinct hashes) are unchanged. Local irreducibility annotations prevent eager enumeration of the existing finite sets while elaborating dependent indices; explicit proofs retain kernel checking. No new resource/compiler/trust/toolchain configuration, sorry/admit/new axiom/native_decide, suppressed verification, manuscript modification or unrelated file staging is introduced. Evidence: C:/Users/ramir/AppData/Local/Temp/stardust-ym-1697-*.

Yang--Mills remains ACTIVE, Bakry PAUSED, all other queue priorities unchanged. Exact-commit approval and guarded PUBLIC synchronization of both authorized branches are next closure gates; this pre-commit ledger does not yet claim remote success.

## Checkpoint1698 — genuine integrated cubic survives in a three-boundary-axis family

The1697 two-axis partition parity is preserved, but it cannot be promoted to generic boundary parity. Three focused modules now prove an ACTUAL full32-interior-link Haar variance identity, a gauge-invariant boundary-loop coefficient, analytic coupling response, and non-evenness of the genuine partition at arbitrarily small positive coupling and arbitrarily small boundary angles. This addresses the proposed integration repair rather than adding an unrelated gauge library.

### Actual model, channel identification and gauge test

Use the EXISTING112-edge/72-face one-sided cap complex and1697's actual `interiorHaar` on ALL32 SU2 interior links. At v=(0,0,1,1), choose retained direction0. Its two outward ribbons have directions2 and3. On the direction2 ribbon put exp(xI) on the HIGH cap link, exp(-yJ) on the upper link, and exp(-zK) on the LOW cap link; every other boundary link is1. These are THREE actual boundary links, not retained interior coordinates. `FourCubeIntegratedCubic.fill` permits all32 interior coordinates to vary freely. `cellAction` is the complete24-internal-plus48-ribbon Wilson action, with the existing0≤S≤144 bound and full L2 domains proved.

`FourCubeHaarChannels.linkProbe_pair` identifies actual product-Haar pair integrals of halfTrace(A*s_e): distinct retained links have zero covariance, while the same link has covariance halfTrace(A*B^-1)/4. It directly reuses the verified `SU2SharedPlaquetteProjection.translated_pair_covariance`, actual coordinate marginal maps, and finite-product independence. `interiorGauge_preserving` proves invariance of the WHOLE32-link Haar law under arbitrary16-vertex interior gauge transformations. Existing internal-face gauge identities then prove that the internal action is orthogonal to every open fundamental ribbon channel (`internal_link_orthogonal` / `internal_link_covariance`). The proof uses an actual endpoint center gauge transformation, not an assumed vanishing integral. Internal bounds and all probe/sum/residual MemLp2 obligations are discharged before using Mathlib's covariance/variance identities.

Only TWO ribbons share the chosen retained link (`edge_fiber`); their boundary words are I(x)J(y)K(z) and1. `pair_trace_gauge` proves halfTrace(B_chosen*B_partner^-1) invariant under ALL48 actual vertex gauges, using the existing source/target maps. It is a closed six-boundary-link Wilson word; an independent Lean check proves the six edges are distinct. Thus the surviving coefficient is not an open-link gauge artifact. This does not assert invariance of the full32-link Haar law under a nonconstant vertex transformation with boundary data held unchanged; the internal closed action and the boundary loop have their separately proved invariances.

### Exact integrated identity and analytic response

Let L_A(s)=halfTrace(A*s_chosenEdge), and G_x,z=S_x,0,z+L_I(x)J(0)K(z). `cellAction_residual` proves S_x,y,z=G_x,z-L_I(x)J(y)K(z) pointwise for the full72-term action. The closed-action orthogonality and the two-ribbon covariance calculation give Cov(G_x,z,L_A)=-halfTrace(A)/4. Hence `variance_formula` proves the EXACT actual Haar identity

    Var(S_x,y,z)=Var(G_x,z)+1/4+halfTrace(I(x)J(y)K(z))/2.

No unknown internal variance is assumed or assigned a numerical value: G is an explicitly defined bounded function. This makes `variance_odd_y` and its concrete witness unconditional:

    Var(S_x,y,z)-Var(S_x,-y,z)=-sin(x)sin(y)sin(z),
    difference at x=y=z=pi/6 = -1/8.

`FourCubeIntegratedResponse` defines Z_beta(x,y,z) as the ACTUAL Haar integral of exp(-beta*S) and F=-log Z. Bounded exponential-tilt machinery proves exponential integrability for every real beta. `exponential_domain` identifies the integrable-exponential domain as ALL real numbers. Mathlib's `MGFAnalytic` then supplies real analyticity and the justified integral derivatives; positivity of Z is proved. `freeEnergy3_second_zero` identifies the actual second coupling derivative at0 with -Var_Haar(S), not with a formal Taylor coefficient.

Consequently `freeEnergy3_second_odd_y` gives F''_beta(0;x,y,z)-F''_beta(0;x,-y,z)=sin(x)sin(y)sin(z). `integrated_mixed_cubic` proves the exact ordered boundary derivative

    D_z D_x D_y [D_beta^2 F(0;x,y,z)] at x=y=z=0 = 1/2.

The order is explicit: coupling derivatives are evaluated first, then y, x, z. No interchange of boundary/coupling derivatives or unproved joint Taylor remainder is asserted. `exists_positive_coupling_nonparity_of_sine` proves that whenever the sine product is nonzero, EVERY positive epsilon admits0<beta<epsilon with Z_beta(x,y,z)!=Z_beta(x,-y,z). `exists_small_boundary_nonparity` strengthens this: for EVERY positive epsilon and delta, there are0<t<delta and0<beta<epsilon with Z_beta(t,t,t)!=Z_beta(t,-t,t). Its proof restricts the proved analytic functions to a nondegenerate closed interval and verifies UniqueDiffOn/C2 hypotheses before comparing derivatives at the endpoint0. It does not infer a positive-coupling counterexample from totalized derivatives without differentiability.

### Manuscript status and exact limits of the obstruction

Selective recheck of `ResearchSources/Incoming/su2_companion.tex`, SHA25606D3B4183167B43129D715B76D6040E3EE5E4D2E8A58F580318B5311C3011839, around lines133–140 confirms the actual claim: an O(g) cubic fast vertex has zero FIRST centered-Gaussian integral by parity, followed by claimed Wilson-form absorption and an O(g^4) effective remainder. The centered-Gaussian odd-integrand identity itself is NOT refuted here. Nor does this small-beta result refute a proved large-beta/small-g renormalized O(g^4) theorem; that theorem and the absorption/cutoff/closure bridges remain unverified. The relevant missing inference is that eliminating interior variables automatically removes every boundary cubic. The actual finite Haar counterexample above rules out that unqualified extension. Original manuscript bytes and earlier counterexamples remain unchanged.

1697's exact two-axis positive result remains fully valid on its DIFFERENT specified boundary family. Global conjugation flips two of three orthogonal axes, so a triple product is allowed by that symmetry; one cannot reuse separate two-axis parity outside its hypotheses. The source-independent pointwise K_xx/K_xy obstruction1696 also remains valid. No novelty is claimed for classical Haar orthogonality, shared-edge integration or cumulant identities; the contribution here is the verified full-cell identification and exact scope of the repair/counterexample.

These are finite one-sided-cell results, NOT a full physical4D transfer operator, homogeneous stationary vacuum, volume-uniform contraction bound, continuum/infinite-volume construction, confinement theorem or mass-gap conclusion. The small-positive-beta regime must not be conflated with beta→infinity. The endpoint-center change used for Haar orthogonality need not preserve a truncated small-field domain; no cutoff-domain identity is silently imported. The coarse144 action bound only establishes finite normalization/analyticity and is not a scale-uniform physical estimate.

Return the next substantive test to the LARGE-beta contraction budget: examine exact conditional Haar integration of the selected retained edge with the other31 interior links fixed, using the existing SU2 staple/radial-response calculus. Determine whether the corrected linear mixed term survives that actual conditional integration and how its coupling dependence compares to the claimed quadratic remainder. Distinguish this one-edge conditional calculation from the full32-link marginal just proved, and connect any estimate to the previously constructed stationary operator only through explicit hypotheses. Avoid additional low-coupling coefficient enumeration unless it serves that bottleneck.1692's coupling-dependent upper mixing,1691/1693's fixed-count obstruction and gauge-invariant slow modes, and every missing physical-scale/volume bridge remain preserved.

### Full verification, independent tests and integrity

The full root build passed7002 jobs in29.4740907 seconds. Complete canonical transitive axiom audit passed54565 safe Foundation declarations in48.7120609 seconds, only propext, Classical.choice and Quot.sound. ALL79 public types were printed UNABRIDGED and reviewed:59 theorem proofs and20 definitions; all9 private helper proofs were reviewed in full. The complete persisted axiom ledger elaborated successfully in59.7432478 seconds. No new source-level heartbeat/recursion/compiler/trust setting, sorry/admit/new axiom/native_decide or suppressed verification gate is introduced. Local irreducibility only avoids eager enumeration of the unchanged finite index sets; all proofs remain kernel checked.

Eighteen independent Lean checks passed in32.4840373 seconds, including actual interior gauge measure preservation, probe variance1/4, closed/open orthogonality, the exact two-ribbon fiber, selected word, ALL48-vertex boundary-loop invariance, six DISTINCT boundary edges, L2 membership, variance difference-1/8, all-real-coupling partition positivity/analyticity, actual second-derivative/variance identification, the mixed derivative1/2, second-response difference1/8, positive witnesses below beta=10^-6, both boundary angles below10^-3 AND coupling below10^-6, preserved1697 two-axis parity, and boundary-loop trace difference-1/4. No mathematical source repair was needed for that final harness.

Independent exact Fraction/quaternion diagnostics expand the full72-face action into multilinear retained-coordinate tensors for27 signed rational unit-circle triples and contract the S3 first/second moment rule. They independently verify both simultaneous-sign and middle-sign variance differences, all32 interior variables, and27 full48-vertex gauge tests of the six-link loop. The diagnostic also predicts the absolute variance formula55/2+halfTrace(IJK)/2+(3/2)cos(x)+(1/2)cos(z) and variance30 at the identity. Those ABSOLUTE values remain diagnostics, NOT new Lean theorems; the formal proof deliberately isolates the exact y-dependence needed for the obstruction instead of expanding boundary-independent constants.

Integrity authenticates1697's source manifest against exact approval519ee2e1d2533367613a9b8270163b416239fe92. It covers2785 Foundation/root files: only the THREE focused new modules, root import and axiom ledger differ. ALL older mathematical source bytes,3 pinned configurations,113 baseline manuscripts and21 Yang--Mills originals (20 distinct hashes) are unchanged. ResearchSources remains read-only/uncommitted, unrelated drafts preserved. Evidence: C:/Users/ramir/AppData/Local/Temp/stardust-ym-1698-* (full build, complete audit/types, full ledger check, independent Lean/quaternion tests, declaration inventory and authenticated manifest).

Yang--Mills remains ACTIVE, Bakry PAUSED and all other queue priorities unchanged. Exact-commit approval and guarded PUBLIC two-branch synchronization remain closure gates; this pre-commit entry does not claim remote success.


## Checkpoint1699 — cubic response survives actual one-link conditional Haar integration

Focused Yang–Mills remains ACTIVE; Bakry Objective2 remains PAUSED. Return to large positive coupling after1698's full32-link SMALL-coupling nonparity theorem. This checkpoint establishes an actual conditional stochastic integral and its boundary derivatives, rather than extrapolating the small-coupling result.

### Exact geometry, integral and domains

`FourCubeConditionalAction.conditional_action` proves the exact existing full72-face action when the selected retained edge U is free and the OTHER31 retained edges equal1, with1698's three-axis boundary data. Writing h(U)=halfTrace(U), A=I(x)J(y)K(z), and C=5+2(1-cos x)+2(1-cos z), it is S(U)=C-4h(U)-h(UA). The selected edge meets exactly FIVE faces in this one-sided cell: three internal faces and the chosen/partner ribbons. Four staples are identity and one is A. This is not the six-plaquette conditional of a standard full four-dimensional lattice. The cap partition [1,2,2,43] is proved; no independent face-count assumption is inserted. The only older proof-source change exposes `FourCubeBoundaryCubic.ribbon_caps_distinct` publicly with its original statement/body unchanged.

`FourCubeConditionalRadial` reuses the verified SU(2) quaternion polar decomposition and Haar tilt law. The five-staple radius satisfies R^2=17+8h(A), 3<=R<=5. The actual conditional partition is

    Zcond(beta;x,y,z)=exp(-beta*C(x,z))*mgf halfTrace law (beta*R(x,y,z)).

All real beta and all real boundary parameters are admitted. Boundedness supplies the complete scalar exponential-integrability domain, partition positivity, and the exact free energy Fcond=beta*C-cgf(beta*R). The radius never vanishes. The derivative of the scalar cgf is proved equal to the actual tilted-Haar mean m(t), with differentiability obtained from existing analytic-cgf machinery. No new probabilistic existence axiom, derivative/interior-integral exchange, or derivative-order interchange is assumed.

### Integrated derivatives and large-coupling conclusion

`FourCubeConditionalResponse.conditional_mixed_hessian` proves the exact ordered boundary slice

    D_x D_y Fcond(beta;0,0,z)=4*beta*m(beta*R(0,0,z))/R(0,0,z)*sin z.

`conditional_mixed_cubic` proves, for EVERY real beta,

    D_z D_x D_y Fcond(beta;0,0,0)=(4*beta/5)*m(5*beta).

Every required derivative is accompanied by differentiability/HasDerivAt proofs; totalized Lean derivatives are not being used outside their proved domains. The existing `SU2OneWordLargeCoupling.positive_mean_tendsto_one` then gives `conditional_mixed_cubic_normalized_limit`: this ordered third derivative divided by beta tends to4/5 as beta tends to positive infinity. Thus a genuine conditional Haar integration retains a cubic boundary coefficient of linear large-beta size. It does not eliminate that coefficient by an unqualified parity argument.

### Exact limitations and next bottleneck

This is ONE free edge with31 fixed values, NOT the32-link marginal. It neither proves nor refutes a full-block large-beta estimate, a renormalized centered-Gaussian O(g^4) theorem, a stationary-transfer spectral gap, homogeneous-coupling slowing, or a physical continuum mass gap.1697's two-axis parity and1698's three-axis full-marginal small-beta nonparity remain valid on their stated families. The manuscript's first centered-Gaussian odd-integrand identity remains valid. The new mechanism is compatible with all those results.

The next precise local test is whether the displayed conditional Hessian can satisfy a coupling-uniform O(beta*z^2)+O(1) budget; its explicit mean/radius factors permit a rigorous test. A bound on a third derivative alone does not settle such a Hessian inequality. A subsequent full-marginal bridge would additionally require controlling the mean Hessian and covariance terms under the remaining31-link conditional law; pointwise conditional behavior alone supplies no such control. Any standard4D extension must first account for the omitted negative-direction plaquette and the actual stationary operator. Scale/volume-uniform and continuum estimates remain open. No novelty claim is made.

### Complete verification and preserved sources

The complete root build passed7005 jobs in29.8331193 seconds. The canonical complete transitive audit passed54648 safe Foundation declarations in41.869212 seconds, accepting only propext, Classical.choice and Quot.sound. All55 public types were printed unabridged and reviewed:36 new theorem proofs,18 definitions/abbreviations and the unchanged newly exposed helper theorem; all8 private proofs were reviewed in full. The entire persisted axiom ledger elaborated in50.366736 seconds. No new resource/compiler/trust setting, sorry/admit/axiom/native_decide or weakened verification gate was introduced.

Sixteen independent Lean checks passed in29.2095333 seconds after correcting an omitted namespace in the external test harness; mathematical sources were unchanged. The checks include the actual72-face action, three internal faces, cap counts, radius identity/bounds, actual Haar polar integral, all-real partition positivity/exponential domain, cgf/mean derivative, nonzero radius, mixed boundary Hessian, ordered cubic, normalized limit and a concrete beta=1 specialization. Independent exact Fraction/quaternion diagnostics again passed243 full72-face conditional cases. Independent Simpson quadrature of SU(2) Haar angle integrals (4096 subdivisions) and eight-corner boundary finite differences (h=.002) agree with the formula for beta=1,5,20,100,500; the last normalized value is0.7995192259, consistent with the proved4/5 limit. These numerical checks are diagnostics, not substitutes for the Lean proofs.

Source integrity authenticates1698's manifest against exact audited commit98517fb8136540f4c688b0cbff7858791681d44e. It covers2788 Foundation/root sources: only the three new conditional modules, root import, axiom ledger and the single private-to-public helper change differ. The old helper's complete statement/proof is otherwise byte-identical after newline normalization. All other old mathematical files,3 pinned configurations,113 baseline manuscripts and21 Yang–Mills originals (20 distinct hashes) are unchanged. ResearchSources remains unmodified/uncommitted; unrelated drafts are preserved. Evidence: C:/Users/ramir/AppData/Local/Temp/stardust-ym-1699-* (complete builds/audits/types, independent Lean/quaternion/quadrature checks, exact declaration inventory and authenticated source manifest).

Exact-commit approval and guarded PUBLIC main/research synchronization follow this checkpoint; this pre-commit entry does not claim remote success. Repository visibility remains exclusively user-controlled. Campaign priorities remain unchanged.

Final source-byte closure: the staged whitespace gate caught one blank EOF line in the new action module. It was removed, and the complete root build, canonical audit/all55 public types, all16 independent Lean checks and complete persisted axiom ledger were rerun successfully on the final bytes; the timings above are those final runs. No theorem statement or proof was changed by that cleanup.


## Checkpoint1700 — a shrinking-corridor obstruction and the surviving linear estimate

Focused Yang–Mills remains ACTIVE; Bakry Objective2 stays PAUSED. This checkpoint resolves1699's explicit local inequality question, using the SAME actual one-link conditional integral of the existing72-face one-sided cell. The other31 retained links remain fixed1. No new stochastic/gauge foundation or unrelated campaign is introduced.

### Exact positive and negative theorems

In `FourCubeConditionalObstruction`, H(beta,z) is the ACTUAL ordered mixed boundary derivative D_x D_y Fcond(beta;0,0,z), not an action derivative or an expectation-level surrogate. All derivative existence/domain obligations were proved in1699. Its exact formula is H=4*beta*m(beta*R)/R*sin z, R=radius(0,0,z) in[3,5].

`mixedHessian_normalized_limit` proves H(beta,z)/beta -> L(z)=4*sin(z)/R for every FIXED real z as beta tends to positive infinity. `exists_slope_exceeds_quadratic` directly reuses the earlier verified SU(2) sine-versus-quadratic obstruction: in every positive boundary neighborhood, L(z)>C*z^2 somewhere for any nonnegative C. `eventually_exceeds_budget` then proves H(beta,z)>C*beta*z^2+C0 eventually at such an angle, for ANY real C0. `exists_arbitrarily_large_budget_violation` and `no_uniform_quadratic_budget` give the exact quantified failure of a coupling-uniform C*beta*z^2+C0 bound on any fixed positive neighborhood and any coupling tail.

The stronger result avoids conflating a fixed-angle limit with a shrinking corridor. `eventually_shrinking_lower` proves

    H(s^2,1/s) >= s/5 eventually as s -> positive infinity.

This uses the actual tilted-Haar mean convergence, radius>=3 (so its argument tends to infinity EVEN WITH the changing angle), radius<=5, and the established elementary sine lower bound. No uniform derivative-limit exchange is assumed. `exists_shrinking_budget_violation` shows that for ANY real C,C0, any epsilon>0 and any beta0, there exists s>0 with 1/s<epsilon and s^2>beta0 for which

    |H(s^2,1/s)| > C*s^2*(1/s)^2+C0.

Along this shrinking corridor beta*z^2=1, so the proposed quadratic budget stays constant while the actual mixed Hessian diverges. This supplies the missing explicit inequality obstruction; a large third derivative alone was not used to assert it.

Positive repair: `mean_abs_le` proves |m(t)|<=1 under the ACTUAL normalized tilted Haar probability measure, and `mixedHessian_linear_bound` proves the all-real bound |H(beta,z)|<=(4/3)*|beta|*|z|. `mixedHessian_zero` proves H(beta,0)=0, so the estimate concerns a genuine departure from the zero-boundary mixed Hessian. The order beta*|z| is therefore a valid replacement here. The lower bound along beta=s^2,z=1/s shows that its scale cannot be replaced by beta*z^2+constant uniformly.

### Manuscript comparison and limits of the obstruction

Selectively reread `ResearchSources/Incoming/block_contraction_spectral_gaps.tex`, lines605–620, SHA2560C40FA6B92B830C0E2309BD6471D55CB0EB9BFB94296B9267AD23A5280FA4C60. It infers Kxx,Kxy=O(beta*delta^2)+O(1) from evenness of the single-holonomy Wilson expansion. Earlier1696 already distinguished single-word evenness from joint link-coordinate cubic terms. The present result shows that an UNQUALIFIED extension of the quadratic mixed-Hessian budget through an actual conditional Haar integral fails, even on an inverse-square-root shrinking boundary corridor.

Scope is essential: the manuscript's exact variables include spanning-tree gauge fixing, an exponential-coordinate corridor and interior/boundary splitting. This checkpoint integrates one link over ALL SU(2), fixes31 physical coordinates, and differentiates two retained boundary directions. It is NOT the manuscript's full gauge-fixed block marginal, cutoff conditional law, or literal interior/boundary Delta_xy block. Those identifications remain separate obligations. No claimed implication between these different Hessians is silently assumed. The conditional free energy with fixed coordinates is not asserted invariant under arbitrary gauge changes of boundary data alone. The one-sided geometry still has five incident faces, not the standard six-plaquette lattice conditional.

Nor does failure of the quadratic MIXED-HESSIAN budget refute a Schur-complement mechanism. A linear bound Kxy=O(beta*delta) still gives Kxy^2/beta=O(beta*delta^2) if the required interior coercivity and other block estimates hold. Existing verified Schur machinery preserves that possibility; its actual-block hypotheses must be established rather than replaced by the false stronger estimate. The elementary weaker bound remains o(beta) when delta->0. No stationary-transfer spectral obstruction, scale/volume-uniform contraction, continuum Yang–Mills existence or physical mass gap follows from this conditional result.

The local conditional budget question is now resolved. Prefer the substantive remaining bridge next: actual full-block Hessian/covariance or Schur estimates and their relation to the actual stationary operator/physical scale, rather than further variations of this one-link counterexample. Preserve1691–1693's finite stationary results and their homogeneous-coupling/volume limitations,1694's Schur repair,1697's two-axis parity and1698's full32-link SMALL-beta nonparity. No novelty claim or campaign transition is made.

### Full verification and integrity

The complete root build passed7006 jobs in25.5751662 seconds. Canonical complete transitive axiom audit passed54684 safe Foundation declarations in40.8374911 seconds, with only propext, Classical.choice and Quot.sound. All13 public declaration types (11 theorem proofs,2 definitions) were printed UNABRIDGED and reviewed, and all complete proof/definition bodies were reviewed; there are no private helpers or new local instances in this module. The entire persisted axiom ledger elaborated successfully in49.7458906 seconds. No sorry/admit/new axiom/native_decide, source-level resource/compiler/trust change or weakened gate is introduced.

Twelve independent Lean checks passed in25.0015146 seconds: actual mixed derivative formula, fixed-angle normalized limit, arbitrary small-angle slope witness, eventual real additive budgets, arbitrarily large coupling violations, absence of a uniform bound, changing-angle lower bound, a shrinking witness below10^-3 and above beta=10^6, actual tilted-mean bound, all-real linear estimate, zero-boundary value and the literal free-energy derivative interpretation. Independent4096-subinterval SU(2) Haar-angle quadrature with four-corner boundary finite differences h=.0002 agrees with the derivative formula for s=2,4,8,16,32,64,128. At s=32, beta=1024 and z=1/32, it gives25.5903311 versus a quadratic budget15 for C=10,C0=5; beta*z^2=1. Numerical checks are diagnostics, not proof and not an explicit proved start time for the eventual inequality.

Integrity authenticates1699's source manifest against exact approved commit2298389b91b6ee9c39db9a8697da5ac66319c7fd. It covers2789 Foundation/root files: only ONE new focused module, its root import and the axiom ledger differ. ALL older mathematical sources,3 pinned configuration files,113 baseline manuscript originals and21 Yang–Mills originals (20 distinct hashes) remain unchanged. ResearchSources remains unmodified/uncommitted and unrelated drafts are preserved. Evidence: C:/Users/ramir/AppData/Local/Temp/stardust-ym-1700-* (full build/audits, complete types, independent Lean/quadrature tests, exact declaration inventory, authenticated manifest).

Exact-commit approval and guarded PUBLIC main/research backup remain the closure gates; this pre-commit entry does not assert remote success. Repository visibility remains exclusively user-controlled. Yang–Mills remains ACTIVE, Bakry PAUSED, with all other queue priorities preserved.


## Checkpoint1701 — exact full-Haar gauge pin; full-block cubic lead

Focused Yang–Mills remains ACTIVE and Bakry Objective2 remains PAUSED. After1700 resolved the one-link conditional budget, return to the actual32-link block. The principal NEW LEAN THEOREM removes its residual root gauge factor exactly. A separate full-block cubic calculation is explicitly an independently tested lead, NOT a newly verified Lean result or an integrated large-beta theorem.

### Proved actual32-link to31-link partition identity

`FourCubePinnedHaar` reuses the EXISTING `OneSidedPinnedInterior.pole` (origin,direction0), its `Free` index of31 edges, the actual72-face action, product SU(2) Haar law, and the proved interior gauge invariance/origin-star boundary identities. The raw retained-link state space is32 copies of SU(2). Pinning removes ONE SU(2) gauge factor (three real dimensions), leaving31 copies, not31 total real dimensions.

For ANY boundary assignment b:Boundary->SU2 and ANY real beta, define Z(beta,b)=the actual32-link Haar integral of exp(-beta*S(b,s)). `partition_eq_pinned` proves EXACTLY

    Z(beta,b)=integral over31 independent normalized Haar links y of exp(-beta*S(b,fillPole(1,y))).

There is no missing determinant, beta-dependent gauge volume or unproved normalization factor: the removed normalized Haar factor is1. This is a measure-preserving gauge change and Fubini, NOT conditioning on the measure-zero event that a raw Haar edge equals1. The31-link measure is genuine product Haar, NOT a Gaussian approximation or Lebesgue chart measure. Arbitrary open-link observables are not asserted unchanged under pinning.

The proof first establishes the actual action invariance for a gauge transformation supported at the origin, with every boundary link held fixed. No ribbon touches that origin. `rootLeft_preserving` proves that simultaneous left multiplication of the remaining origin-star coordinates preserves31-link product Haar. `conditional_pole_integral` shows independence of the pole value after actual integration. `split_preserving`/`split_reconstruct` use Mathlib's finite-product measurable equivalence to split off the pole, and the uniform exp(144*abs(beta)) majorant supplies integrable Fubini. Both full and pinned partitions are positive for every real beta and arbitrary b. `partition3_eq_pinned` identifies the EXACT full three-axis family already used in1698, so its existing full-marginal results transfer by equality.

This closes a real integration/coordinate bridge to the existing pinned quadratic Schur machinery. It does NOT identify the Haar measure in exponential coordinates with a flat Gaussian density, prove nonlinear coercivity, provide a volume-uniform estimate, or construct a continuum stationary transfer operator.

### Independently tested full-block cubic: a lead, not a Lean theorem

The exact rational test `stardust-ym-1701-harmonic.py` constructs the ACTUAL24 internal plus48 ribbon incidence rows, all32 retained variables and the SAME three distinct boundary-axis sources as1698. It solves the scalar normal equations L X=-D^T B exactly, detecting rank31 and the four-origin-link gauge vector. Converting its free-root choice to the EXISTING origin-direction0 pin preserves the computed cubic; no inverse of the singular32-by32 Gram is assumed. The rank/kernel/pin facts themselves were already verified in `OneSidedBlockRank` and `OneSidedPinnedInterior`; those results are reused, not advertised as new.

Evaluating the oriented quaternion Wilson cubic on the full harmonic extension gives the candidate coefficient

    31877443263/69438734552 = approximately 0.459072929089

for xyz, versus1 with every interior velocity fixed zero. A second, independently implemented exact multivariate quaternion Taylor algebra through degree3 agrees. The three color directions are orthogonal: the actual quadratic Hessian is DIAGONAL with entries526589/289542,130821/193028,11003/8774. The script's off-diagonal spatial source Gram numbers are NOT mixed-color Hessian entries and are labelled separately. The canonical pinned normal-equation coefficient table and these numerical values remain EXTERNAL COMPUTATIONAL CERTIFICATES, not Lean theorems in this checkpoint.

Independent direct nonlinear quaternion evaluation on ALL72 faces agrees as the angle shrinks. With all93 retained real coordinates allowed to relax numerically, the eight-corner local-minimum cubic estimates are0.4590435528,0.4590655854,0.4590710820 at h=.02,.01,.005, respectively; final finite-difference gradient norms are at most1.8e-10. The corresponding harmonic-path estimates converge to the same rational lead. These are LOCAL numerical minimizations, not global-minimum or measure-concentration certificates. No GPU/PyTorch dependency, package installation or workflow configuration change was needed.

The mathematics suggested is that quadratic interior elimination does not automatically annihilate the joint Wilson cubic. However, the exact normal-equation table and Taylor-coefficient identity must first be identified with the existing Lean canonical response. Then a valid analytic LOCAL minimizer/variational jet theorem is needed. Any assertion about the true full Haar free energy additionally needs global pinned-minimum control and uniform parameter-dependent Laplace estimates through the required derivatives. A scalar Laplace limit alone does not justify differentiating that limit. The new exact Haar pin supplies the correct93-real-coordinate integration domain but none of those later estimates. Preserve this promising lead without asserting full-marginal large-beta nonparity, a mass-gap obstruction, or novelty.

### Remaining focused bottleneck

Use the existing canonical Schur response, pin, positive Gram and physical boundary quotient instead of building another gauge library. Resolve the nonlinear pinned saddle/minimum and derivative-convergence hypotheses, or obtain a direct full-Gibbs Hessian/covariance estimate. Keep1700's valid linear mixed-Hessian repair and potential quadratic Schur loss; neither the conditional counterexample nor the harmonic cubic proves failure of physical contraction. The actual four-dimensional stationary operator, homogeneous-coupling/physical-distance and scale/volume/continuum bridges remain open. No campaign transition, deadline or prior theorem status changes.

### Complete verification and source integrity

The full root build passed7007 jobs in27.1897804 seconds. Canonical complete transitive axiom audit passed54722 safe Foundation declarations in50.656034 seconds, only propext, Classical.choice and Quot.sound. ALL27 public types were printed UNABRIDGED and reviewed:14 theorem proofs,9 definitions,2 abbreviations and2 probability instances. Every complete proof/definition body and the single private ribbon-origin helper was reviewed. The complete persisted axiom ledger elaborated in46.4145055 seconds. No sorry/admit/new mathematical axiom/native_decide, new resource/compiler/trust option or weakened gate is introduced. Local irreducibility avoids eager finite-set enumeration; origin geometry is directly reused from the prior origin-star theorem. The singleton product measure uses Mathlib's explicit subtype Fintype to match the proved measurable split; its probability law is proved, not assumed.

Sixteen independent Lean checks passed in25.7079223 seconds, covering the existing31-edge cardinality, both probability measures, Haar-preserving root translations, fill/gauge identification, arbitrary-boundary full-action invariance, Boltzmann majorant, pole independence, actual product-measure split and reconstruction, exact full/pinned partitions, the existing three-axis partition, positivity, ratio1 and equality of actual logarithmic free energies. Independent exact rational/quaternion tests on9 arbitrary noncommuting112-link fields verify all72 action terms, root inverse/reconstruction and that all80 boundary links remain unchanged. The separately labelled exact harmonic normal-equation/determinant test, independent multivariate Taylor algebra, and direct nonlinear local-minimum diagnostics agree as detailed above; they are NOT substitutes for missing Lean/analytic/large-beta proofs.

Integrity authenticates1700's source manifest against exact approved commitb1ff51401c00728e8a0362fcb01274914e322966. It covers2790 Foundation/root files: only ONE new focused full-Haar pin module, its root import and the axiom ledger differ. ALL old mathematical sources,3 pinned configurations,113 baseline original manuscripts and21 Yang–Mills originals (20 distinct hashes) are unchanged. ResearchSources remains unmodified/uncommitted; unrelated drafts are preserved. Evidence: C:/Users/ramir/AppData/Local/Temp/stardust-ym-1701-* (full build/audits, complete types, independent Lean and exact nonabelian tests, harmonic and multivariate/nonlinear diagnostic scripts/results, declaration inventory and authenticated manifest).

Exact-commit approval and guarded PUBLIC main/research synchronization follow this checkpoint; this pre-commit record does not assert remote success. Repository visibility remains exclusively user-controlled. Yang–Mills stays ACTIVE, Bakry PAUSED, all other campaign priorities and verification requirements unchanged.


## Checkpoint1702 — global nonlinear pinned vacuum control and actual Haar tails

Focused Yang–Mills remains ACTIVE; Bakry Objective2 remains PAUSED. This checkpoint addresses a central obligation left by1701: GLOBAL minimum control for the actual pinned action at IDENTITY boundary data. Here global means all configurations of this fixed72-face one-sided cell, NOT infinite volume or a continuum statement. No small-field cutoff, Taylor truncation or assumed inverse of an unpinned Hessian is used.

### Proved nonlinear bound and unique minimum

`FourCubePinnedCoercivity.defect U=1-halfTrace(U)` is the genuine SU(2) Wilson trace defect. A quaternion norm identity proves its rigidity: defect(U)=0 iff U=1. The proved three-factor bound defect(A*B*C)<=3*(defect(A)+defect(B)+defect(C)) follows from unit-quaternion distance, the triangle inequality and the scalar three-term square inequality. This elementary metric argument is a necessary ingredient, not a claim of novelty.

Let S(s) be the existing FULL72-face action with ALL80 boundary links equal1. `vacuum_decomposition` identifies S as the24 internal Wilson costs plus48 ribbon costs. Each retained link whose source is not the origin occurs in a ribbon; its defect is therefore at most S. For an origin link other than the pinned pole, the selected origin plaquette expresses that link as a product of its plaquette holonomy inverse and two non-origin links. Those two links have DISTINCT ribbon witnesses, so their two costs and the one plaquette cost together are at most S. Applying the three-factor metric bound gives `pinned_link_bound`:

    s(pole)=1 -> defect(s(e)) <= 3*S(s), for EVERY retained edge e.

For the actual31-link pin, `pinned_coordinate_bound` proves defect(y(e))<=3*pinnedAction(y), globally in y. `pinnedAction_zero_iff` and `pinnedAction_positive_iff` prove that the identity configuration is the UNIQUE zero-action/global-minimum state of the pinned action. Existence is explicit: its action is0, while all action values are nonnegative. The result does not classify or exclude positive-action metastable local minima. Without the pin, origin-supported nonidentity gauge transformations still have zero action; their existence is preserved rather than hidden in a coercivity hypothesis.

`global_energy_barrier` is quantitative: if ANY pinned coordinate has defect at least epsilon, then pinnedAction>=epsilon/3. Thus configurations separated from the identity in a specified coordinate have an explicit positive energy barrier. Constant3 is a proved convenient bound, NOT an asserted sharp constant. This is a nonlinear statement on the actual compact group configurations, not merely positivity of the scalar quadratic Gram.

### Genuine integrated consequence, with normalization kept explicit

`pinnedAction_measurable` and `boltzmann_integrable` establish the actual function/domain and Haar integrability for EVERY real beta. `tail_event_measurable` verifies the event. For beta>=0, `boltzmann_barrier` and `boltzmann_tail_bound` prove the ACTUAL unnormalized Haar integral estimate

    integral over {y : defect(y(e))>=epsilon} exp(-beta*pinnedAction(y)) d(pinnedHaar)
      <= exp(-beta*epsilon/3).

The measure is the genuine31-factor normalized Haar law from1701. Its exact full32-link partition identification is already proved. The tail theorem does NOT silently divide by a constant partition: the normalized bound retains the actual denominator Z(beta). The independent Lean harness explicitly checks that division step. Positivity of Z alone is not a useful uniform lower bound or a concentration rate.

### Exact remaining analytic and physical bridges

This closes1701's global pinned MINIMUM/energy-barrier obligation at identity boundary data. It does not yet prove uniform saddle isolation for perturbed boundary parameters, an analytic minimizing branch, the actual Hessian/canonical Gram identification in exponential coordinates, the diagnostic harmonic cubic coefficient, or derivative-controlled large-beta Laplace asymptotics. In particular, a positive global barrier at one boundary value is not permission to differentiate a partition limit.

A concrete next route to normalized concentration is now visible: continuity of the actual pinned action plus positive Haar mass of an open low-energy neighborhood could give Z(beta)>=c_epsilon*exp(-beta*epsilon/6), then an exponentially decaying normalized coordinate tail. Mathlib ALREADY provides the finite-product IsOpenPosMeasure instance; no new probability foundation is required. These continuity/lower-bound/normalization steps remain OPEN, not inferred merely from the new unnormalized tail theorem. Uniform boundary perturbation control and all required parameter derivatives remain additional obligations afterward.

Retain1701's exact rational full harmonic cubic31877443263/69438734552 as a separately labelled external computational lead; it is NOT promoted to a Lean theorem or an integrated asymptotic by this checkpoint. Retain1700's failed quadratic mixed-Hessian budget and surviving linear/Schur repair, and all earlier stationary-transfer results/limitations. A one-cell pinned vacuum estimate is not an actual four-dimensional stationary-transfer gap, a scale/volume-uniform contraction, quantum-field existence or a physical mass gap. No novelty claim, campaign transition or queue change is made.

### Complete verification and preserved sources

The full root build passed7008 jobs in27.0613974 seconds. Canonical complete transitive axiom audit passed54754 safe Foundation declarations in39.6684342 seconds, only propext, Classical.choice and Quot.sound. ALL25 public types (20 theorem proofs,5 definitions) were printed UNABRIDGED and reviewed, as were every complete proof/definition body and all9 private helper proofs. The complete persisted axiom ledger elaborated in46.260737 seconds. No sorry/admit/new mathematical axiom/native_decide, resource/compiler/trust option or weaker verification gate was introduced. Existing finite geometry and gauge-pin declarations were directly reused; the metric helpers serve the concrete global-action estimate.

Sixteen independent Lean checks passed in26.5887418 seconds: defect positivity/rigidity/inversion, the three-factor inequality, actual action decomposition/positivity, the global pinned link and31-coordinate bounds, uniqueness/strict positivity of the vacuum, actual measurability/all-real Boltzmann integrability, the explicit epsilon=.1 energy barrier1/30, the true tail integral, the normalized ratio with its REQUIRED partition denominator, and preserved zero-action root-gauge transformations before pinning.

Independent exact rational quaternion tests checked21 pinned112-link fields against ALL72 action terms and32 retained coordinates. They include noncommuting Cayley fields, near-vacuum low-energy mode directions, identity and large Cayley scales; all per-link defect<=3*action and zero-rigidity sample checks passed. The maximum sampled defect/action ratio was approximately.852094; no sharpness or optimum is inferred. Three separate nonidentity origin-gauge fields had exact zero unpinned action, checking the necessity of the pin. These sampled diagnostics do not replace the universal Lean theorems.

Integrity authenticates1701's source manifest against exact approved commit192293aeab54518cb7594ec4f67f15dfc0efc9c3. It covers2791 Foundation/root files: only ONE new focused global pinned-coercivity module, its root import and the axiom ledger differ. ALL older mathematical source files,3 pinned configurations,113 baseline original manuscripts and21 Yang–Mills originals (20 distinct hashes) remain unchanged. ResearchSources remains unmodified/uncommitted and unrelated drafts are preserved. Evidence: C:/Users/ramir/AppData/Local/Temp/stardust-ym-1702-* (full build/audits, complete types, independent Lean and exact quaternion tests, declaration inventory and authenticated manifest).

Exact-commit approval and guarded PUBLIC main/research synchronization are the remaining closure gates; this pre-commit record does not assert remote success. Repository visibility remains exclusively user-controlled. Yang–Mills remains ACTIVE, Bakry PAUSED, all other priorities and verification requirements unchanged.

Final-byte closure: the staged gate caught a trailing space in the new metric proof. It was removed, with no statement/proof change, and the full root build, complete canonical audit/all25 types, all16 independent Lean checks and full persisted axiom ledger were rerun successfully on the final source bytes. The timings above are those final runs.


## Checkpoint1703 — actual normalized pinned Gibbs concentration

Focused Yang–Mills remains ACTIVE; Bakry Objective2 remains PAUSED. The missing normalization step from1702 is now proved for the actual31-link pinned72-face cell at IDENTITY boundary. This is a genuine family of probability measures constructed from product Haar, not a formal expectation functional or an assumed concentrating law.

### Actual law, continuity and positive denominator control

`FourCubePinnedConcentration` uses the existing bounded exponential-tilt construction with source X(y)=-pinnedAction(y)/144 and tilt parameter144*beta. The actual action lies in[0,144], so |X|<=1 is proved. `gibbs_probability` verifies a probability measure for EVERY real beta. `tilted_partition_eq`, `normalizer_integral` and `gibbs_integral` identify its exact Boltzmann normalization and actual integrals:

    Z(beta)=integral exp(-beta*S(y)) d(pinnedHaar),
    integral f d(gibbs(beta))=integral f(y)*exp(-beta*S(y)) d(pinnedHaar)/Z(beta).

Z(beta) is exactly the pinned partition already identified with the original32-link full Haar partition in1701. No gauge-volume factor or unidentified normalizer is inserted.

`pinnedAction_continuous` is proved from the actual finite plaquette/ribbon group products and trace, reusing the original fill and action decomposition. Define lowEnergy(delta)={y:S(y)<delta} and c_delta=lowMass(delta)=pinnedHaar.real(lowEnergy(delta)). The set is open. For delta>0 it contains the verified identity vacuum; existing product-Haar positive-open-set support then proves c_delta>0. This argument uses an OPEN neighborhood, not positive measure of the single identity point.

`normalizer_lower` supplies the missing quantitative denominator estimate, for beta>=0:

    c_delta*exp(-beta*delta) <= Z(beta).

The c_delta are actual Haar probabilities, independent of beta for fixed delta, but no uniform volume dependence or explicit small-delta asymptotic is claimed.

### Proved coordinate and simultaneous configuration probabilities

For epsilon>0 and beta>=0, `gibbs_coordinate_tail_mass` identifies the actual normalized event probability, and `gibbs_coordinate_tail_bound` combines1702's global energy barrier and unnormalized Haar-tail estimate with the NEW denominator lower bound at delta=epsilon/6:

    gibbs(beta)[defect(y(e))>=epsilon]
      <= exp(-beta*epsilon/6)/c_(epsilon/6).

`gibbs_coordinate_tail_tendsto_zero` proves this probability tends to0 as beta tends to positive infinity. The input is the actual fixed-cell law; no heuristic exchange of limits or derivatives is used.

The result is simultaneous, not merely one coordinate at a time. `configurationTail(epsilon)` is the UNION of the31 coordinate events. Its measurability, finite-union estimate and the EXACT existing31-edge count give

    gibbs(beta)[exists e:defect(y(e))>=epsilon]
      <=31*exp(-beta*epsilon/6)/c_(epsilon/6).

`gibbs_configuration_tail_tendsto_zero` proves convergence to0; `gibbs_configuration_good_tendsto_one` proves the complementary probability tends to1. The independent harness verifies that this complement is exactly the event EVERY pinned link has defect<epsilon. The factor31 counts SU(2) links; the pinned manifold still has93 real dimensions. A separate general weak-convergence or stochastic-dynamics theorem is not asserted without its hypotheses.

### What this resolves and what remains open

The base-point global-minimum and NORMALIZED-tail obligations are now closed for the actual pinned finite cell. The proof does not automatically apply to boundary perturbations, an unpinned raw-link delta limit, an infinite lattice or continuum Yang–Mills. In particular, the original unpinned root gauge coordinate remains free; removing it was a gauge change, not conditioning on a measure-zero raw-link event. General gauge-invariant observable transport still needs its exact statement; partition equality alone is not silently promoted to equality of every raw-link marginal.

This is a law indexed by beta, not a constructed physical-time flow, filtration or stationary transfer operator. It does not establish a physical spectral gap or a volume-uniform contraction. Constants c_delta are fixed-cell constants and may degenerate with volume or delta. No such dependence is erased.

The next substantive bottleneck is the LOCAL fluctuation/rescaled Gaussian and boundary-parameter analysis needed to test1701's nonzero full harmonic cubic and actual full-Gibbs Hessian/covariance. Concentration at the vacuum does not justify multiplying a small covariance by beta or differentiating a partition asymptotic. The exact actual Hessian-to-canonical pinned Gram identification, uniform perturbed-boundary saddle isolation and moment/derivative-controlled Laplace limits remain OPEN. Prefer those obligations over routine additional consequences of fixed-cell concentration. Preserve the conditional obstructions and surviving linear/Schur route, all manuscript status distinctions and the unresolved actual four-dimensional stationary/physical-distance/volume/continuum bridges. No novelty claim or campaign transition is made.

### Complete verification, independent actual-law checks and source integrity

The complete root build passed7009 jobs in27.0296576 seconds. The canonical complete transitive axiom audit passed54782 safe Foundation declarations in42.0844799 seconds, only propext, Classical.choice and Quot.sound. ALL26 public types were printed UNABRIDGED and reviewed:18 theorem proofs,7 definitions and1 actual probability instance. Every complete proof/definition body and all5 private continuity/exponential-limit helpers were reviewed. The complete persisted axiom ledger elaborated in56.9810142 seconds. No sorry/admit/new mathematical axiom/native_decide, resource/compiler/trust change or weaker verification gate was introduced.

Nineteen independent Lean checks plus a zero-tilt helper passed in33.0334319 seconds. They cover actual action continuity/source bound/probability for all real beta, the exact integral-normalizer relation, lowMass(.01)>0 and the true partition lower bound, normalized coordinate-event identification and exponential bound, coordinate and simultaneous configuration limits, event measurability, exact factor31, normalizer(0)=1, gibbs(0)=the ORIGINAL product Haar measure, exact beta-zero marginal mean defect1 obtained independently from Haar evaluation/trace moments, all-beta total normalization, and the equality between the good-event complement and EVERY link having defect<epsilon. A type-inference repair in the external marginal harness supplied its explicit Free index; no mathematical source repair or repeated full build was required for that harness change. These exact independent checks do not rely on a Monte Carlo approximation or manufacture a numerical estimate of the potentially tiny positive Haar constants.

Integrity authenticates1702's source manifest against exact approved commitfbac6017e75addbd320145adcdce59e57476410e. It covers2792 Foundation/root files: only ONE new focused actual normalized-Gibbs module, its root import and the axiom ledger differ. ALL older mathematical source files,3 pinned configurations,113 baseline original manuscripts and21 Yang–Mills originals (20 distinct hashes) remain unchanged. ResearchSources remains unmodified/uncommitted; unrelated drafts are preserved. Evidence: C:/Users/ramir/AppData/Local/Temp/stardust-ym-1703-* (full build/audits, complete types, independent actual-law Lean checks, declaration inventory and authenticated source manifest).

Exact-commit approval and guarded PUBLIC main/research synchronization are the closure gates; this pre-commit record does not assert remote success. Repository visibility remains exclusively user-controlled. Yang–Mills stays ACTIVE, Bakry PAUSED, all other priorities and verification requirements unchanged.


## Checkpoint1704 — actual pinned Wilson Frechet Hessian identified with the canonical Gram form

October28 local / October29 UTC. Focused Yang–Mills remains ACTIVE; Bakry remains PAUSED. This closes the previously open base-point Hessian-identification obligation from1703, not the rescaled Gibbs or boundary-derivative Laplace obligations. No campaign transition, new existence assumption or physical mass-gap claim is made.

### Actual action, exact domains and normalization

`Foundation/SU2FourWordVariation.lean` extends the existing verified three-factor matrix exponential jets to FOUR ordered factors. `path_hasDerivAt` and `pathSlope_hasDerivAt` hold for arbitrary four complex2x2 matrices and every real curve parameter. Trace cyclicity cancels the ordered commutator contributions at the identity: `trace_second_zero` identifies the traced second jet with the trace of the SQUARE of the total generator. `action_second_zero` is the actual second derivative of the Wilson action, not a stipulated quadratic energy.

For the existing normalized su(2) generator `algebraElement`, `signed_second_zero` and `signed_slope_second_zero` give the exact face coefficient

    d²/dt² Wilson(exp(t A(u)) exp(t A(v)) exp(-t A(w)) exp(-t A(z))) at0
      = lengthSq(u+v-w-z)/4.

`signed_first_zero` verifies the actual first derivative vanishes. No commutativity of the four matrices is assumed. This identity at the identity background does not remove nonabelian cubic terms or contradict the earlier away-background mixed-response counterexamples.

`Foundation/FourCubePinnedSecondVariation.lean` constructs actual SU(2)-valued logarithmic rays using the retained exponential-membership theorem. `core_log_coe`, `core_log_inv_coe`, `face_model` and `ribbon_model` identify the true group products and inverses. `ray_model` is the full actual cell decomposition:24 internal four-link faces plus48 ribbon faces. The derivative helpers hold at every real ray parameter; the resulting second-variation formula is evaluated at0.

`incidence_identity` reuses the existing scalar curl/ribbon incidence energy, independently for each of the three colors. `pinnedChart_fill` identifies the actual31-link pinned ray with the32-link ray whose canonical pole velocity is zero. It preserves the exact pinning convention of1701; it is not conditioning Haar measure on a measure-zero event.

For EVERY pinned velocity V in Free -> Fin3 -> Real, `pinned_first_zero` proves zero actual first variation, and `pinned_second_gram` proves

    d²/dt² S_pinned(pinnedChart(V,t)) at0
      = (1/4) sum_a dot(V_a, localGram * V_a).

`pinned_second_positive` proves this is strictly positive whenever V is nonzero, reusing the previously verified pinned Gram positivity. The quarter factor is essential: the matrix tangent frame is (imagJ,imagK,imagI)/2. The unpinned incidence form still has its root gauge kernel. Nothing here asserts positivity in all unpinned directions or across all backgrounds.

### Genuine Frechet-Hessian bridge

`Foundation/FourCubePinnedHessian.lean` defines `coordinateAction V` to be the actual pinned action of the exponential coordinates, evaluated at ray parameter1. `coordinateAction_contDiff` proves ContDiff Real2 on the entire finite-dimensional coefficient space. It uses analytic matrix exponentiation, continuous linear evaluations and actual finite face products; it does not assume a chart inverse or a Haar coordinate density.

`coordinateAction_line` proves exact agreement with the actual pinned rays. `hessian_diagonal_ray` uses the iterated Frechet chain rule along a continuous linear map to identify the second Frechet derivative at coefficient0, evaluated on(V,V), with the actual one-variable second derivative. Thus `hessian_diagonal_gram` and `hessian_positive` establish the actual Frechet-Hessian quadratic form and its strict positive definiteness in every nonzero pinned direction. This is stronger than merely declaring an abstract positive Gram matrix or computing unrelated directional proxies. A separate explicit off-diagonal polarization theorem or a numerical eigenvalue lower bound is not asserted.

### Independent checks and retained obstructions

Fourteen independent Lean applications check cancellation of a repeated positive/negative face generator, actual ray derivative applications, zero first variation, C2 and differentiability, the Frechet/ray bridge, exact Gram normalization, strict positivity, zero-kernel implication, zero-direction second variation and canonical pole pinning. These passed in28.9232922 seconds.

A separate quaternion implementation tests the ACTUAL72-face group action, using the correct normalized quaternion frame (v2,v0,v1)/2. Six seeded rational pinned fields, a single link with five incident faces, a free origin link with three internal faces and the unpinned common-root gauge direction were tested: nine cases at each of three symmetric finite-difference scales. The single-link predictions are exactly5/4 and3/4; the gauge-direction prediction is0. All tested second differences agree with the quarter-incidence/Gram prediction within the stated O(h²) numerical envelope, with decreasing errors on halving h. This is a numerical diagnostic, not a proof of the limiting Gibbs law. An initially unjustified overly tight diagnostic tolerance was corrected to an explicit O(h²) envelope plus error-ratio check; no mathematical claim was weakened to make that diagnostic pass.

The concrete next bottleneck is now the actual LOCAL MEASURE and moment-controlled Laplace limit, rather than the identity-background Hessian. Still OPEN: an appropriate inverse logarithmic chart and product-Haar Jacobian/density control; rescaled Gibbs moment convergence and uniform integrability; uniform isolation of the perturbed-boundary saddle; parameter-dependent Laplace estimates strong enough for differentiated third-order responses.1703's normalized fixed-cell concentration and this positive local Hessian do not on their own justify multiplying a covariance by beta or differentiating an asymptotic partition formula. The exact external full harmonic cubic31877443263/69438734552 remains computational evidence only; its Lean coordinate conversion and actual full-Gibbs response identification are not discharged here.

The one-sided72-face cell remains distinct from a scale/volume-uniform four-dimensional lattice construction. Physical-distance transfer dynamics, continuum/infinite-volume estimates and a positive physical mass gap remain unresolved. Earlier conditional cubic obstructions and the surviving linear mixed-Hessian/coercive Schur route are preserved. This is a verified local classical calculation needed by a specific mass-gap-related manuscript audit, not a claim of new continuum Yang–Mills mathematics or a campaign devoted to auxiliary declaration counts.

### Complete verification and integrity

The complete root build passed7012 jobs in57.8064471 seconds. The canonical COMPLETE transitive axiom audit passed54868 safe Foundation declarations in39.9211541 seconds, allowing only propext, Classical.choice and Quot.sound. ALL64 public types were printed unabridged and reviewed:41 theorem proofs,21 definitions and2 abbreviations, together with all6 private proof helpers and all complete source bodies. No sorry/admit/new mathematical axiom/native_decide, toolchain change, resource increase or trust weakening was introduced. The complete persisted axiom-ledger elaboration passed in46.6482589 seconds.

Source integrity authenticates1703's manifest against approved commit2b4e33291e3a3fc2b05c2843663e01121cc9f07f and covers2795 Foundation/root files. Only the THREE new focused variation/Hessian modules, root import and axiom ledger differ. ALL older mathematical sources,3 pinned configurations,113 baseline original manuscripts and21 Yang–Mills originals (20 distinct hashes) remain unchanged. ResearchSources remains read-only/uncommitted; unrelated drafts are preserved. Evidence: C:/Users/ramir/AppData/Local/Temp/stardust-ym-1704-* (complete build/audits/types, fourteen Lean checks, independent quaternion script/results, declaration inventory, timings and authenticated source manifest).

Exact-commit approval and guarded PUBLIC main/research synchronization remain the closure gates. This pre-commit ledger records local verification and does not claim remote success. Repository visibility remains exclusively user-controlled. The mathematical campaign and every queue and verification requirement remain unchanged.


## Checkpoint1705 — exact SU(2) Haar hemisphere density from the existing Gaussian realization

October28 local / October29 UTC. Focused Yang–Mills stays ACTIVE; Bakry stays PAUSED. This checkpoint resolves an actual local-measure ingredient needed after1704's pinned Hessian calculation. It does not establish the full rescaled Gibbs limit, a differentiated Laplace theorem or a physical mass gap. No campaign or original manuscript is changed.

### Actual measure construction and exact domains

`Foundation/SU2GaussianConeCoordinates.lean` reuses `GaussianAngularSphere`, `QuaternionAngularHaar` and the faithful quaternion/SU(2) equivalence. `gaussianDirection` maps FOUR independent standard real Gaussians through Euclidean normalization and the existing quaternion representation. `gaussianDirection_law` proves its pushforward is the actual normalized SU(2) Haar probability. `lintegral_haar_gaussian` is therefore an actual law identity for every measurable nonnegative extended-real observable, not a matching-moments argument or a new Haar assumption.

The map `cone(r,y)=(r,r*y0,r*y1,r*y2)` has an explicitly verified Frechet derivative and determinant r^3. Its inverse divides the last coordinates by r. Both inverse identities require r!=0; injectivity and the self-image theorem are restricted to the POSITIVE cone r>0. `lintegral_positive_cone` applies Mathlib's verified higher-dimensional change-of-variables theorem on exactly that measurable set. The independent harness supplies a concrete collision at r=0, proving unrestricted injectivity false.

`rawGaussian_density` derives the four-dimensional product Gaussian density directly from the existing scalar Gaussian probability laws, using measurable rectangles, restricted product measures and finite-product integration. No multivariate-density assertion is assumed. `gaussianDirection_halfTrace` and `gaussianDirection_positive_iff` identify the positive-trace hemisphere when the Gaussian input is nonzero. The chosen normalization convention maps input0 to the group identity; the independent check confirms its half-trace is1. Thus the pointwise hemisphere equivalence FAILS at that input. `rawGaussian_ae_ne_zero` proves the exceptional singleton has zero actual Gaussian probability, and `lintegral_haar_hemisphere_cone` transfers the RESTRICTED actual Haar law using this precise almost-everywhere fact.

### Completed radial reduction and Haar integral identity

For a=1+|y|^2, `gaussianDensity_cone` proves the exact separated Gaussian weight. `radial_gaussian_integral`, `radial_gaussian_integrable` and `radial_gaussian_lintegral` prove, for every a>0,

    integral_(r>0) r^3 exp(-a*r^2/2) dr = 2/a^2.

The ordinary integral, integrability and nonnegative integral are all verified. The proof uses the existing Gamma integral and the r->r^2 substitution; no improper integral is assigned a formal value without its domain.

`hemisphereChart(y)` is the existing quaternion/SU(2) image of the normalized vector(1,y0,y1,y2). `chartDensity(y)=1/(2*pi^2*(1+|y|^2)^2)`. The square-root Gaussian prefactor and radial marginal constant are proved exactly in `cone_density_normalization` and `cone_radial_density`.

The main theorem `lintegral_haar_hemisphere_chart` proves, for EVERY measurable f:SU(2)->[0,infinity],

    integral_(halfTrace(U)>0) f(U) dHaar(U)
      = integral_(R^3) chartDensity(y)*f(hemisphereChart(y)) dy.

The coordinate split is a verified measure-preserving finite-product equivalence. Tonelli is applied with explicit product measures and positive-ray/whole-space restrictions. No finite-integrability requirement is silently imposed; infinite nonnegative integrals are included. The factor1/2 is retained: this is the restriction of Haar probability to ONE hemisphere, not an already conditioned probability law. The exact three-dimensional density identity, not just its four-dimensional cone reduction, is now closed in Lean.

### Literature comparison and a relevant chart-moment obstruction

This Gaussian-ratio distribution is classical. Sergio Verdu, *The Cauchy Distribution in Information Theory*, Entropy25(2023),346, Section2, item6, equation(6), records the spherical multivariate Cauchy density and its Gaussian-ratio representation; item2 records divergence of absolute moments of order>=1. Source: https://doi.org/10.3390/e25020346 ; directly inspected PDF: https://mdpi-res.com/d_attachment/entropy/entropy-25-00346/article_deploy/entropy-25-00346.pdf . No novelty is claimed for that distribution or this classical change of variables. The contribution here is independent formal identification with the actual Haar law already used by the finite-cell audit.

EXTERNAL MATHEMATICAL ARGUMENT, NOT YET A LEAN THEOREM: in these ratio coordinates, integrating out two variables gives the hemisphere marginal1/(2*pi*(1+z^2)). Its truncated absolute first moment is log(1+R^2)/(2*pi), which diverges. The ratio coordinates share a Gaussian denominator and are dependent. Compactness of SU(2) does not bound this chart, which becomes singular near halfTrace=0. On the fixed finite cell, a finite-beta Gibbs density bounded above and below by positive constants relative to product Haar cannot remove an existing nonintegrability. This warns against demanding unrestricted ratio-coordinate moment convergence at finite beta. The exact coordinate-recovery identity and transfer of this divergence to the actual full Gibbs law remain Lean obligations; the numerical checks do not substitute for them. A LOCAL cutoff or a different bounded coordinate representation can remain productive. This obstruction concerns this chart; it does not refute local Gaussian fluctuations or the earlier positive Hessian.

### Independent checks and precise next bottleneck

Thirteen independent Lean checks passed in26.5705914 seconds. They include an explicit global cone-injectivity counterexample, the negative-cone exclusion, determinant0 on the singular plane and determinant8 at a concrete positive input, the Gaussian-origin half-trace exception, chart-density normalization at0, two exact radial integrals, actual probability of the Gaussian pushforward, the actual Haar hemisphere-mass integral identity and the zero-triple radial marginal. Two numerical simplifications in the external harness required explicit rational reduction; mathematical sources and full-build inputs were unchanged.

A separate NumPy-only160-node Gauss-Legendre implementation passed21 diagnostics: five radial Gaussian reductions, hemisphere mass1/2, three positive real-coordinate caps checked against the independent semicircle antiderivative, four truncated first-moment values and eight finite-difference Jacobian determinants. The diagnostic uses interval splits and an explicit infinite-ray transform; it is not a certified quadrature/error bound or a proof of infinite moments. SciPy and mpmath were unavailable, so no packages were installed and the existing NumPy runtime was used. Evidence is C:/Users/ramir/AppData/Local/Temp/stardust-ym-1705-independent.py/.json/.log.

The new chart is a GAUSSIAN-RATIO chart.1704's Frechet Hessian was proved in EXPONENTIAL coordinates. Their transition and exact tangent normalization must be proved before combining these results. Product-chart transport for all31 retained links, cutoff domains and the local rescaled moment/dominated-convergence argument are still OPEN.1703's epsilon=1 simultaneous concentration theorem is a precise reuse candidate for proving the all-positive-trace chart domain has Gibbs probability tending to1; its exact event identification has not yet been added as a Lean theorem here. Uniform perturbed-boundary saddle isolation and derivatives through third-order Laplace asymptotics remain open, as do1701's full harmonic-cubic Lean coefficient identification and the actual scale/volume/continuum physical bridges. Concentration plus a Hessian plus a chart density is not automatically the required limit theorem.

### Complete verification and preserved sources

The full root build passed7013 jobs in44.6450857 seconds. The canonical COMPLETE transitive audit passed54943 safe Foundation declarations in43.705644 seconds, permitting only propext, Classical.choice and Quot.sound. ALL48 public types were printed unabridged and reviewed:33 complete theorem proofs,13 definitions and2 abbreviations. The two private measurability helpers and every complete proof body were reviewed. The complete persisted axiom ledger passed in47.4789936 seconds. No sorry/admit/new mathematical axiom/native_decide, resource increase, toolchain/configuration change or weaker check was introduced.

Authenticated integrity compares against1704's manifest approved at c6130c55f387bc46e77f3b09f51454c3ea41f14f. Among2796 Foundation/root files, only ONE new focused Gaussian-cone/Haar-density module, the root import and axiom ledger differ. ALL older mathematical sources,3 pinned configurations,113 baseline original manuscripts and21 Yang–Mills originals(20 distinct hashes) are unchanged. ResearchSources is unmodified/uncommitted; unrelated drafts remain intact. Full evidence: C:/Users/ramir/AppData/Local/Temp/stardust-ym-1705-*.

Exact-commit approval and guarded PUBLIC main/research synchronization are still required for closure. This pre-commit record makes no remote-success claim. Repository visibility is exclusively user-controlled; all existing research priorities and verification gates remain unchanged.


## Checkpoint1706 - actual Haar-chart inverse, two jets, and a necessary local Gaussian cutoff

October29,2026. Focused Yang-Mills remains ACTIVE. This checkpoint continues the actual fixed four-dimensional cell, not merely the seven-link loop surrogate. New sources are Foundation/SU2HemisphereChart.lean, Foundation/SU2HemisphereJets.lean and Foundation/FourCubeHemisphereCoercivity.lean. They reuse1701's normalized31-link pinning,1702's actual72-face coercivity,1703's Gibbs concentration,1704's exponential-coordinate Hessian machinery and1705's actual Haar hemisphere density. No new mathematical axiom, external existence assertion or physical mass gap is assumed.

### Exact coordinate identification and normalization

For y in R^3, let q(y)=(1,y)/sqrt(1+|y|^2) and let chart(y) be its actual SU(2) matrix. SU2HemisphereChart.coordinates uses the three recovered quaternion imaginary coordinates divided by its real coordinate. `coordinates_chart` proves coordinates(chart(y))=y for every y. `chart_coordinates` proves the converse for EVERY positive-half-trace SU(2) matrix, with that hemisphere hypothesis explicit. Outside the hemisphere the total division convention is not asserted to give a chart inverse. `chart_injective`, `chart_matrix`, `chart_halfTrace` and measurable maps are verified. `lintegral_coordinate_observable` identifies the actual restricted Haar integral of every nonnegative measurable coordinate observable with density

    rho(y) = 1/(2*pi^2*(1+|y|^2)^2).

This is the one-hemisphere restriction, not a separately normalized probability. The factor1/2 from1705 is retained; a full31-link joint change-of-variables theorem is still a separate obligation.

The tangent frame is exactly frame(y)=(2*y1,2*y2,2*y0) in the repository's existing generator basis. For B=A(frame(y)), the actual matrix curve c_y(t)=chart(t*y) satisfies c_y(0)=I, c_y'(0)=B and c_y''(0)=B^2=-|y|^2*I. `curve_two_jet` proves its value and first TWO derivatives agree with exp(t*B) at zero. Derivatives are obtained from the actual normalized quaternion formula, with all-real-t differentiability of its positive scalar square-root weight; no hypothetical chart smoothness or unverified transition is used. This is a SINGLE-LINK matrix two-jet theorem: the full action's ratio-coordinate Hessian has not yet been assembled. Higher-order jets cannot silently be identified. Numerical expansion finds cubic imaginary coefficient difference -|y|^2*y/3 between the ratio chart and the corresponding exponential chart; that cubic difference is a diagnostic, NOT a new Lean theorem.

### Actual local domination and cutoff probability

Let Y assign R^3 coordinates to all31 retained links and define

    Q(Y)=sum_e |Y_e|^2.

`quadraticMass_sum_squares` verifies this exact93-real-coordinate quadratic form, including Q(0)=0 and Q(constant(a,0,0))=31*a^2. On the explicit per-link cutoff 1+|Y_e|^2<=2, `local_defect_lower` gives |Y_e|^2/4 <= defect(chart(Y_e)). Combining the actual defect<=3*S theorem and the exact31-link count gives `local_action_lower`:

    Q(Y)/372 <= S(chartField(Y)),     372=4*3*31.

For beta>=0 and beta*t^2=1, `scaled_action_lower` and `scaled_boltzmann_domination` therefore prove

    Q(Y)/372 <= beta*S(chartField(t*Y)),
    exp(-beta*S(chartField(t*Y))) <= exp(-Q(Y)/372),

provided every scaled link satisfies 1+|t*Y_e|^2<=2. The clock relation and cutoff are actual theorem hypotheses. `gaussian_envelope_integrable` proves the right-hand envelope integrable for the actual finite-product Lebesgue measure on all93 real coordinates, from existing scalar Gaussian integrability. No normalized Gibbs fluctuation limit follows merely from this bound.

Define localStateDomain in the actual pinned SU(2) state space by positive half-trace AND chartRate(coordinates)<=2 on every link. The event is measurable. Defect<1/4 implies this condition; `outside_localStateDomain_subset` identifies its complement as a subset of the existing actual configurationTail(1/4). `gibbs_outside_cutoff_le_tail` and the earlier concentration theorem imply the outside probability tends to0 and `gibbs_cutoff_tendsto_one` proves the ACTUAL normalized finite-cell Gibbs probability of this cutoff tends to1 as beta tends to infinity. For beta>=0 the previous quantitative tail result immediately supplies outside probability <=31*exp(-beta/24)/lowMass(1/24); that numeric substitution is a consequence of existing theorems, not a separately exported simplification here. This proves precisely why the local cutoff is legitimate for bounded observables in a future fluctuation-limit proof. It alone does not control arbitrary unbounded ratio-coordinate moments.

### Decisive obstruction to the global shortcut

`no_global_affine_quadratic_bound` proves there are NO constants c>0 and C with

    c*Q(Y) <= S(chartField(Y))+C   for all Y.

The actual compact-group action satisfies S<=144, whereas the constant-coordinate field Y_e=(a,0,0) has Q=31*a^2. Given c,C, the proof constructs a=sqrt((|C|+145)/(31*c)) and derives the contradiction. Thus even an additive constant cannot repair a positive global quadratic lower bound in this unbounded chart. `no_global_positive_quadratic_bound` is the C=0 corollary. This obstruction blocks removing the cutoff from this action-coercivity argument. It does NOT refute a local Gaussian limit, weighted-density estimates of another form, contraction or a physical mass gap. The chart-coordinate absolute-moment divergence discussed in1705 still requires its own Lean proof and actual-Gibbs transfer; it is not certified by the present global-action counterexample.

### Independent checks and verification

All17 independent Lean checks passed in27.8169723 seconds. They test both inverse identities with the correct domain, the explicit frame factor/permutation, both second-jet identities, Q(0), Q(constant(100,0,0))=310000, the scaled beta=4,t=1/2 bound, actual93-dimensional integrability, cutoff probability convergence and the global affine obstruction. Concrete counterexamples independently show Q/372<=S fails for all31 coordinates(100,0,0), and the single-link lower bound fails at y=(3,0,0) when its cutoff is omitted.

Separate NumPy-only diagnostics reuse the independently enumerated actual72-face quaternion action: five rational pinned fields at three decreasing symmetric scales agree with the incidence Hessian prediction under the CORRECT factor2/permutation;25 scaled actual-action Gaussian bounds and nine explicit affine-bound counterexamples passed. The third-jet diagnostic was checked against its derived fifth-order correction rather than an unjustified tolerance. These finite differences and floating comparisons are diagnostics, not certified derivative/remainder estimates, a general parameter theorem or an actual Gibbs limit.

The full root build passed7016 jobs in31.1434044 seconds. The canonical COMPLETE transitive safe-Foundation audit passed55036 declarations in42.2994637 seconds, permitting only propext, Classical.choice and Quot.sound. ALL69 public types were printed unabridged and reviewed, and all54 complete theorem proofs,14 definitions and one abbreviation were read. The complete persisted Foundation/AxiomAudit.lean verification passed in47.9066225 seconds. No sorry/admit/new axiom/native_decide, resource increase, compiler option, version/configuration change, trust alteration or reduced audit was introduced. The local `convert!` tactic resolves equivalent matrix-norm instances without introducing compiler options.

Authenticated source integrity compares to1705's exact approval at bab688bb6140cd6316c80680095a914ea0d346db. Among2799 Foundation/root files, ONLY the three focused new modules, root imports and axiom ledger differ. ALL older mathematical files,3 pinned configurations,113 baseline original manuscripts and21 Yang-Mills originals(20 distinct hashes) are unchanged. ResearchSources remains unmodified and uncommitted; all unrelated planning drafts remain untouched. Evidence is C:/Users/ramir/AppData/Local/Temp/stardust-ym-1706-*.

The user's publication-role separation has also been saved as a controlling preamble in AGENTS.md, STARDUST_REFLECTION_POLICY.md and STARDUST_CAMPAIGN_QUEUE.md, and the EXISTING reflection heartbeat updated without changing its target, daily trigger, active status, date gate or45-minute cap. Publication/manuscript/PDF maintenance and editorial README duties belong exclusively to the separate publication agent. No publication agent or parallel campaign was created. Existing drafts/history, mathematical reflection, research ledgers, proofs and campaign priorities are preserved. This checkpoint does no publication maintenance.

### Exact next bottleneck and physical scope

Next transfer the single-link two-jet identity through the full finite Wilson action, proving its ratio-coordinate scalar quadratic limit with the exact generator normalization. Then establish the31-fold product Haar transport and rescaling Jacobian, pointwise local density limit, normalized partition-function asymptotics and a justified dominated-convergence theorem using the verified local envelope. These are still OPEN; a Hessian, a chart density and a dominating function are not by themselves a completed convergence proof. Uniform perturbed-boundary saddle isolation, third-order parameter derivatives/Laplace estimates, the full harmonic-cubic Lean coefficient, stationary transfer lower obstructions at physical coupling-distance scales and scale/volume/continuum bridges remain OPEN. The constant372 explicitly depends on this31-link cell; no uniform physical four-dimensional theorem or mass gap is claimed. The route remains a precise test of the manuscript-motivated full-block asymptotic mechanism rather than broad auxiliary gauge-library expansion. No novelty claim is made for the classical chart identities or the local Laplace strategy.

Exact-commit approval, secret scan and guarded PUBLIC main/research synchronization remain closure gates. This pre-commit ledger entry does not assert remote success. Repository visibility is exclusively user-controlled; master and every other research priority remain unchanged.


## Checkpoint1707 - actual full-cell Haar-coordinate quadratic and Boltzmann limits

October29,2026. Focused Yang-Mills remains ACTIVE. The missing full-action second-jet bridge from1706 is now proved. New sources are Foundation/FourCubeAmbientAction.lean and Foundation/FourCubeHaarQuadraticLimit.lean. These are directed at the fixed-cell Laplace/response bottleneck, not an expansion of general gauge-theory infrastructure. No manuscript or publication artifact was created, revised, compiled or reviewed. The source archive is preserved by hash checks only.

### Actual action identification, not a hypothetical smooth surrogate

FourCubeAmbientAction realizes the existing24 internal-face plus48 ribbon-face action as a finite real polynomial in32 interior2x2 complex matrices and their conjugate transposes. `core_actual`, `face_actual` and `action_actual` prove exact equality to the repository's actual SU(2) core fields, Wilson faces and identity-boundary vacuum action for EVERY actual interior state. Nothing is integrated over unrestricted nonunitary matrices. The ambient function only supplies a valid finite-dimensional derivative computation.

`adjointLinear` and `adjointCLM` explicitly make conjugate transpose a REAL continuous linear map in this finite matrix space. No false operator-norm isometry or NormedStarGroup assumption is introduced. `action_contDiff` proves C2 regularity using finite products, sums and the existing real trace CLM. For every retained31-link coordinate field Y, `ratioPath_actual` identifies the resulting path with the ACTUAL pinned action at chartField(t*Y); `expPath_actual` identifies its exponential comparison with the already verified pinnedRay. The pinned root is exactly the identity in both paths.

The ratio path and comparison path are C2 for all real t; positive1+t^2*|y|^2 justifies all square-root and reciprocal derivatives. Their values and first two matrix-field derivatives agree at0. `action_first_transfer` and `action_second_transfer` transport this agreement through the actual full action, using Mathlib's verified chain rule and `iteratedDeriv_vcomp_two`. This closes the previous distinction between1704's exponential Hessian and1705's actual Haar chart at SECOND order. No third-order transition or boundary derivative is asserted.

### Exact coefficient and the strongest pointwise conclusion

Let L be OneSidedPinnedInterior.localGram and define

    G(Y) = sum_(a=0,1,2) (Y^a)^T L Y^a,
    R_Y(t) = S(chartField(t*Y)).

The repository's generator frame is frame(y)=(2*y1,2*y2,2*y0). `frame_lift` proves compatibility with the pinned extension. `frame_quadraticForm` proves the frame contributes EXACTLY a factor4 in the Gram form, cancelling1704's factor1/4. Thus `ray_zero`, `ray_first_zero` and `ray_second_gram` prove

    R_Y(0)=0,   R_Y'(0)=0,   R_Y''(0)=G(Y).

`ray_second_positive` proves G(Y)>0 for every nonzero retained field. `ray_taylor_polynomial` identifies the actual second Taylor polynomial for every evaluation t. `ray_quadratic_remainder` proves

    R_Y(t) - (G(Y)/2)*t^2 = o(t^2) as t ->0.

For EVERY fixed Y, `ray_quadratic_limit` and `boltzmann_quadratic_limit` prove

    R_Y(t)/t^2 -> G(Y)/2,
    exp(-R_Y(t)/t^2) -> exp(-G(Y)/2),

as real t tends to0 THROUGH NONZERO VALUES. This is the actual Boltzmann weight at beta=1/t^2 and the correct covariance quadratic form, with no unproved Gaussian approximation inserted into the premises. It is pointwise in Y, not a uniform remainder or a theorem about normalized Gibbs measures.

`no_unpunctured_quadratic_limit` proves that for nonzero Y the corresponding UNPUNCTURED Lean quotient limit is FALSE: total division assigns R_Y(0)/0^2=0, whereas G(Y)/2>0. This is a topology/domain issue for the written quotient, not an obstruction to the usual mathematical punctured limit or a continuous extension assigning the limiting value at0. Future dominated-convergence arguments must retain nonzero scales or define that extension explicitly.

### Independent testing and a rejected numerical assumption

Seventeen independent Lean checks passed in25.7740946 seconds. They verify actual ambient/state action identification, the actual two coordinate paths, C2 regularity, no linear term, the full Gram coefficient, positive second variation for a concrete nonzero constant field, the exact second Taylor polynomial, the punctured limit, failure of the unpunctured limit and the real exponential limit. They independently refute retaining an erroneous extra factor1/4 in the actual coordinate Hessian.

A NumPy-only diagnostic independently evaluates the full72 faces both by quaternion multiplication and by complex matrix multiplication with conjugate-transposed inverse links. All64 one-sided quotient/matrix-action comparisons across eight rational pinned fields, both signs and four decreasing scales passed, as did12 basis-coordinate normalization tests across four links and three quaternion axes. They agree with half the independently enumerated incidence Gram energy. These are numerical diagnostics, not certified remainder rates or proofs of integration limits.

An initial diagnostic additionally demanded geometric MONOTONE error reduction at every sampled scale. Six comparisons rejected that stronger, unjustified assumption: cubic/quartic cancellations can make an intermediate coarse-scale error anomalously small. The script now preserves those comparisons as rejected-assumption evidence rather than treating Taylor convergence as monotone convergence of errors. A separate exact Lean rational-polynomial counterexample in the independent harness verifies the logical distinction. The mathematical theorem and its little-o topology were not weakened to accommodate this diagnostic; the formal proof uses the verified C2 Taylor theorem. Diagnostic evidence is C:/Users/ramir/AppData/Local/Temp/stardust-ym-1707-independent.py/.json/.log.

### Verification, integrity and exact remaining obligations

The complete root build passed7019 jobs in27.2267185 seconds. The canonical COMPLETE transitive safe-Foundation axiom audit passed55093 declarations in42.5203262 seconds, allowing only propext, Classical.choice and Quot.sound. ALL40 new public types were printed unabridged and reviewed:29 complete theorem proofs,10 definitions and one abbreviation. Both private C2 helpers and every complete proof/definition body were read. The complete persisted Foundation/AxiomAudit.lean run passed in46.1580249 seconds. No sorry/admit/new mathematical axiom/native_decide, increased resources, changed compiler/trust setting or toolchain/configuration change was introduced. All evidence uses C:/Users/ramir/AppData/Local/Temp/stardust-ym-1707-*.

Source integrity authenticates1706's manifest against its exact approval at b670ac199289994fb843ea72189ffb03b408ac16. Among2801 Foundation/root files, ONLY the two new focused modules, root imports and axiom ledger differ. ALL older mathematical sources,3 pinned configurations,113 baseline original manuscripts and21 Yang-Mills originals(20 distinct hashes) remain unchanged. ResearchSources is unmodified/uncommitted, unrelated drafts/history are preserved, and publication-role and research-priority instructions are unchanged.

The next bottleneck is now INTEGRATION rather than the pointwise Hessian bridge: prove31-fold restricted Haar transport, the93-real-dimensional scaling Jacobian, cutoff density convergence, normalization positivity/asymptotics and a justified dominated-convergence theorem for actual normalized Gibbs observables. Reuse1706's actual local Gaussian envelope and cutoff probability tending to1. Do not substitute convergence of an unnormalized pointwise integrand for convergence of actual Gibbs expectations, and do not demand unrestricted chart-coordinate moments already suspected to be nonintegrable. The scalar chart density contributes its own product/Jacobian factors and cannot be silently discarded. Uniform perturbed-boundary saddle control, third-order parameter/Laplace estimates and the exact full harmonic-cubic Lean coefficient remain OPEN, as do stationary physical transfer estimates and all scale/volume/continuum mass-gap bridges. The present theorem concerns ONE fixed actual four-dimensional cell at identity boundary; no positive physical mass gap or novelty of classical Taylor/Laplace methods is claimed.

Exact-commit approval, new-history secret scan, guarded PUBLIC main/research synchronization and independent exact remote-ref verification remain closure requirements. This pre-commit ledger entry does not assert that backup has already happened. Visibility is exclusively user-controlled. The indefinite research goal remains active.


## Checkpoint1708 - actual normalized finite-cell Gibbs limit, not only pointwise weights

October29,2026. Focused Yang-Mills remains ACTIVE. This checkpoint discharges the product-Haar/scaling/integration/normalization bottleneck left by1707 at identity boundary. It constructs an actual limiting probability measure and proves convergence of the actual pinned Gibbs expectations for EVERY globally bounded measurable real test of rescaled coordinates. The proof concerns the existing full72-face four-dimensional cell, not the earlier seven-link surrogate. It does not establish a physical mass gap or a scale/volume-uniform theorem.

New sources are Foundation/FourCubeHaarProductCoordinates.lean, Foundation/FourCubeHaarLaplaceDensity.lean, Foundation/FourCubeHaarPartitionAsymptotic.lean and Foundation/FourCubeHaarGibbsLimit.lean. Each serves the actual finite-cell limit. Existing1701 pinning,1703/1706 actual Gibbs concentration,1705 actual single-link Haar density,1706 local domination and1707 full-action quadratic limit are reused without alteration. No manuscript, PDF, publication directory or editorial README was created, revised, compiled or reviewed.

### Exact joint Haar transport and scaling

`coordinateLaw_eq_map` and `chart_map_coordinateLaw` identify BOTH directions between the actual restricted single-link Haar law and rho(y)dy, where

    rho(y)=1/(2*pi^2*(1+|y|^2)^2).

The finite measure is the ONE-HEMISPHERE restriction; no probability renormalization is inserted. `joint_restriction`, `coordinateField_map` and `chartField_map` transport the actual31-link product restriction. `productCoordinateLaw_density` identifies its full93-real-dimensional Lebesgue density

    R(Y)=product_(31 retained links e) rho(Y_e).

The proof establishes single-link integrability from the actual finite Haar pushforward, product integrability, equality on measurable rectangles and then equality of measures. It does not assume Gibbs links are independent: the product law is the UNTILTED Haar base measure. `lintegral_joint_density` and the ordinary `integral_joint_density` give the actual nonnegative and real integral identities, with measurable-test hypotheses explicit. `cutoff_preimage` and `integral_actual_cutoff` identify the existing actual SU(2) cutoff exactly.

`field_finrank` proves the dimension is93=31*3. `integral_rescale` proves the exact absolute Jacobian |t|^93 for every NONZERO real t. The absolute value covers negative scales; t=0 is excluded. The independent check refutes dropping that exclusion using a strictly positive Gaussian integral. Root gauge removal still has normalized Haar factor1 under1701; no conditioning on a measure-zero event or extra Gaussian gauge-volume factor is used.

### Dominated convergence, including its actual domain

Let G(Y)=sum_a (Y^a)^T L Y^a, where L is the verified pinned localGram.1707 proves the ACTUAL action S(chart(tY))/t^2 tends to G(Y)/2 for every fixed Y through nonzero t. Define the rescaled density

    D_t(Y)=1_(all e:1+|tY_e|^2<=2) R(tY) exp(-S(chart(tY))/t^2).

`eventually_scaledCutoff` proves the indicator tends pointwise to1. Continuity and positivity of rho, the exact product bound R(Y)<=R(0), and1706's actual action bound prove, for EVERY t!=0 and Y,

    0 <= D_t(Y) <= R(0)*exp(-|Y|^2/372).

The right-hand side is the existing integrable93-dimensional Gaussian envelope. `scaledDensity_tendsto`, `gaussianDensity_integrable` and `gaussianDensity_integral_positive` establish

    D_t(Y) -> g(Y)=R(0)*exp(-G(Y)/2),
    0 < C=integral g(Y)dY < infinity.

`scaledDensity_integral_tendsto` applies the actual filter dominated-convergence theorem. `bounded_test_integral_tendsto` applies it to EVERY globally bounded measurable f, not just continuous functions. `normalized_bounded_test_tendsto` gives the corresponding normalized cutoff-density ratio. All limits use the punctured real neighborhood of0; `scaledDensity 0` is not silently assigned the limiting density, and no unpunctured convergence is asserted. No monotone error rate or unproved uniform Taylor remainder is used.

### Actual full partition and normalized Gibbs observables

`localPartition_rescale` proves the exact identity between the ORIGINAL Haar cutoff partition and |t|^93*integral D_t. `actual_cutoff_probability` proves its ratio to the ORIGINAL normalizer is precisely the actual normalized Gibbs cutoff probability.1706 independently proves that probability tends to1; `inverse_square_tendsto` gives beta=1/t^2 ->+infinity. Therefore `actual_normalizer_asymptotic` proves

    Z(1/t^2)/|t|^93 -> C >0,

for the actual fixed-cell normalizer. The independent Lean harness also transfers this to the original UNPINNED32-link Haar partition using1701's exact `partition_eq_pinned`, without a new hypothesis.

Write X_t(U)=t^(-1)*coordinateField(U). The coordinate map is globally measurable by the repository's total-division convention; its inverse is asserted only on the verified hemisphere domain. For every measurable f:Field->R with |f(Y)|<=M and M>=0, `cutoff_numerator_rescale` identifies the actual Haar numerator and `actual_cutoff_test_tendsto` identifies its actual Gibbs-normalized limit. Outside the cutoff, `outside_test_bound` gives the uniform bound

    abs(integral_(outside cutoff) f(X_t(U)) dGibbs_(1/t^2))
      <= M*Gibbs_(1/t^2)(outside cutoff) ->0.

Thus `actual_gibbs_bounded_test_limit` applies to the FULL actual Gibbs expectation, not a conditional or hypothetical Gaussian expectation. It uses genuine integrability of the bounded tests under the actual probability measure when splitting inside/outside integrals.

`limitingDensity(Y)=g(Y)/C` is integrable, nonnegative and has integral1. `limitingLaw` is the ACTUAL withDensity measure on Field, and `limitingLaw_probability` proves it is a probability measure. The main theorem `actual_gibbs_limit_law` proves

    integral f(X_t(U)) dGibbs_(1/t^2)(U) -> integral f(Y) dlimitingLaw(Y)

for EVERY globally bounded measurable real f. Its conclusion uses an actual constructed law, not just a formal quotient functional. The independent Lean harness derives setwise convergence for EVERY measurable coordinate set, with no continuity/null-boundary assumption, and checks a cosine observable. No uniform supremum over all tests, total-variation metric theorem, new `IsGaussian` instance, closed determinant normalizer or explicit covariance= L^(-1) theorem is exported here. The target's positive quadratic-exponential density and probability normalization are the exact verified characterization.

### Independent checks, full verification and source preservation

All22 independent Lean semantic checks passed in28.2073581 seconds. They cover the exact93-dimensional exponent, product density at0, retained hemisphere-mass product formula, both actual product pushforwards, the cutoff preimage, reflection/negative-scale Jacobian, a concrete zero-scale Jacobian counterexample, cutoff partition scaling, the exceptional t=0 density, finite integrability at nonzero scales, positive limiting normalizer, actual probability mass1, normalized constants, original unpinned partition reuse, a bounded cosine, discontinuous setwise convergence and the positive-beta square-root clock identity. A harness-only function-application elaboration was repaired; mathematical sources/build inputs were unchanged.

A NumPy-only independent diagnostic used8192 Gaussian importance samples with precision from the independently enumerated actual face-incidence matrix. It evaluated the actual72-face quaternion action at beta256,1024,4096, retaining all product-density and cutoff factors. At4096 the local scaled-partition/Gaussian-constant estimate was1.0016030274 (empirical Monte Carlo standard error0.0009979918), and the weighted cosine estimate0.5186075959 compared with the classical Gaussian reference0.5186416711. A separate conditional-Haar product test gave0.7918628208 versus0.7918555746. These are floating diagnostics, not certified Monte Carlo confidence bounds, a proof of global outside contributions, or a Lean determinant/covariance identity. The numerical determinant-expression log normalizer is explicitly external to the proved abstract C. Evidence: C:/Users/ramir/AppData/Local/Temp/stardust-ym-1708-independent.py/.json/.log.

The complete root build passed7023 jobs in76.0354983 seconds. The canonical COMPLETE transitive audit passed55210 safe Foundation declarations in42.6824818 seconds, accepting only propext, Classical.choice and Quot.sound. ALL81 public types were printed unabridged and reviewed:64 complete theorem proofs,14 definitions and3 measure instances. The one private rectangle-integral helper and all complete source bodies were read. The complete persisted Foundation/AxiomAudit.lean run passed in47.8688419 seconds. No sorry/admit/new mathematical axiom/native_decide, resource increase, compiler/trust change or toolchain/configuration change was introduced.

Source integrity authenticates1707's manifest against exact approval d135fa708bb4f2ab5e198478275992d11bbd8cfd. The recursive Foundation/root count matches the complete2805-file manifest. ONLY the four focused new modules, root imports and axiom ledger differ. ALL older mathematics,3 pinned configurations,113 baseline originals and21 Yang-Mills originals(20 distinct hashes) remain unchanged. ResearchSources stays unmodified/uncommitted; all unrelated drafts/history are preserved. Evidence uses C:/Users/ramir/AppData/Local/Temp/stardust-ym-1708-*.

### What remains open and the next focused bottleneck

The actual identity-boundary finite-cell normalization and bounded-observable fluctuation limit are NOW CLOSED; do not continue reporting them as merely conditional or pointwise gaps. This does NOT close uniform perturbed-boundary saddle/control, third-order parameter response, differentiation of the asymptotic expansion, the full harmonic-cubic Lean coefficient, stationary transfer contraction/lower bounds at physical distance scales, or scale/volume/continuum existence and mass-gap requirements. An ordinary asymptotic formula cannot be differentiated without those additional estimates.

Bounded-test convergence does NOT imply convergence of unrestricted chart-coordinate moments. The earlier finite-beta Cauchy-type chart-moment obstruction still awaits its own Lean divergence/actual-Gibbs proof; it is not discharged by this theorem. A productive next route is to test parameter-uniform response and rescaled BOUNDED physical observables using the established actual Gaussian limit and outside-cutoff estimate, with every polynomial-growth/domain requirement separately justified. Prefer a concrete actual transfer/correlation estimate or counterexample over broad auxiliary expansion. No novelty is claimed for classical finite-dimensional Laplace methods. This is one fixed pinned cell at identity boundary, not a four-dimensional continuum quantum field construction. Yang-Mills remains ACTIVE and all other campaign priorities remain unchanged.

Exact-commit approval, complete new-history secret scanning, guarded PUBLIC main/research synchronization and independent exact remote-ref verification remain closure gates. This pre-commit entry does not claim remote backup is already verified. Visibility is exclusively user-controlled; the indefinite research goal remains active.

## Checkpoint1709 - actual physical-action exponential moments, sharp domain and scaled mean

October29,2026. Focused Yang-Mills remains ACTIVE. The preceding checkpoint1708 is committed at19b518b5daf7d6a956d4319c8196fd4c82554fa5; independent remote checks found BOTH authorized main/research refs exactly there and repository PUBLIC. Master and the separate publication branch were preserved. This checkpoint pursues a concrete physical-observable consequence of the actual72-face fixed-cell limit, rather than assuming convergence of unrestricted ratio-chart moments or differentiating an asymptotic expansion.

The new focused source is Foundation/FourCubePhysicalEnergy.lean. It imports the existing actual partition asymptotic directly. Let S be the ACTUAL pinned72-face action, mu_beta the ACTUAL normalized Gibbs probability, beta=1/t^2 and E_t(U)=S(U)/t^2. The existing31 retained SU(2) coordinates have93 real tangent directions. Every finite-scale physical action and its exponential are integrable: scaledEnergy_integrable and exponential_integrable prove the required domains for ALL real t and s from the existing bounded physical energySource. This says nothing about unrestricted ratio-coordinate moments.

### Exact exponential identity and sharp limiting domain

energyMGF_partition proves, on the FULL Gibbs measure without a cutoff remainder,

    M_t(s)=integral exp(s E_t(U)) dmu_(1/t^2)(U)
          = Z((1-s)/t^2)/Z(1/t^2).

The MINUS sign is essential. partition_ratio_tendsto transports the verified full partition asymptotic through the nonzero clock t/sqrt(c), for c>0; it retains the absolute93-dimensional Jacobian at negative as well as positive t. Therefore energyMGF_tendsto proves, for EVERY real s<1,

    M_t(s) -> (sqrt(1-s))^(-93),   t ->0 through NONZERO real values.

This conclusion follows from an exact actual partition ratio, not an unjustified application of bounded-test convergence to an unbounded exponential. normalizer_tendsto_zero and the exact Z(0)=1 prove energyMGF_boundary_tendsto: M_t(1)->+infinity. Nonnegative physical action gives monotonicity in s, so energyMGF_supercritical_tendsto proves divergence for EVERY s>=1. Thus the finite limiting exponential-moment domain s<1 is SHARP, although every finite-scale exponential moment exists. The total auxiliary definition limitMGF outside s<1 is NOT a valid limiting formula; in particular Lean's total sqrt/inverse makes limitMGF(1)=0 while the ACTUAL moments diverge there. The independent checks retain this explicit obstruction to extending the displayed finite formula across its domain. No new Gamma-law identification, moment-generating-function uniqueness theorem or distributional-convergence theorem is claimed here.

### Actual mean scaling without differentiating an asymptotic

energyMean_sandwich proves the two ACTUAL integral inequalities, for every a>0,

    (1-M_t(-a))/a <= integral E_t dmu_(1/t^2) <= (M_t(a)-1)/a.

The proof uses pointwise 1+x<=exp(x), proved integrability of all three functions and normalized probability mass1. limitMGF_hasDerivAt_zero and the two one-sided exponential secants establish the limiting slope93/2. actual_energyMean_tendsto first fixes a, takes the verified moment limit, and only THEN lets the secant approach0 using the order characterization of limits. There is NO interchange of a parameter derivative with an unproved asymptotic remainder.

actual_beta_mean_tendsto checks the physical beta clock t=1/sqrt(beta), eventually beta>0, and proves

    beta * integral S(U) dmu_beta(U) -> 93/2 = 46.5,   beta ->+infinity.

The dimension is93 after the already verified normalized root-gauge removal, not96. The independent Lean harness explicitly rejects assigning derivative96/2 to the limiting exponential function. The result is a physical bounded-action observable with growing beta prefactor; it does not assert finite or convergent global ratio-chart moments.

### Uniform exponential tail control for scaled physical energy

energyTail_bound proves for EVERY real t,R and a>=0,

    mu_(1/t^2)(E_t>=R) <= exp(-a R) M_t(a).

This is a full actual-Gibbs integral inequality, with measurable tail set and integrability verified; it is not a conditional-chart estimate. eventual_energyTail_bound proves that, for EACH fixed 0<=a<1, eventually in nonzero t near0, SIMULTANEOUSLY FOR ALL real R,

    mu_(1/t^2)(E_t>=R) <= exp(-a R) ((sqrt(1-a))^(-93)+1).

Taking 0<a<1 gives exponential tightness at the physical scale S~1/beta. The positive limiting mean and the sharp exponential domain do not determine any spatial transfer spectrum. In particular no stationary correlation decay, physical mass gap, continuum existence or scale/volume-uniform inequality follows merely from these one-cell thermal statements.

### Independent evidence, complete verification and integrity

ALL23 independent Lean checks passed in28.055516499996884 seconds. They test the actual93-dimensional count, normalization, the exceptional t=0 convention, reflection/negative clocks, finite-scale integrability beyond the limiting exponential domain, the exact negative-coupling partition at s=2, the c=4 rescaling factor, physical-beta mean and eventual46-to47 bounds, negative-parameter moment limit, the critical total-definition/domain obstruction and actual divergence at s=1 and2, monotonicity, full-measure tail bounds, simultaneous-in-R control and rejection of the96-dimensional slope. Broad simplification in the TEST harness initially over-expanded93rd powers and reached the unchanged recursion limit; explicit rewrites repaired the harness. A temporary launcher path-name error was also corrected. No mathematical source change or resource increase was needed for these test repairs.

An independent NumPy diagnostic used16384 samples of a Gaussian reference obtained from independently enumerated face incidence, then evaluated the ACTUAL72-face quaternion action with the full Haar product density and local cutoff. At beta16384 the weighted scaled energy mean was46.4858010049 versus the proved46.5 limit; exponential moments at s=-0.1,-0.05,0.05,0.1 agreed with the predicted values (at0.1:133.9475659198 versus134.1909758300). The local scaled-partition estimate was1.0005276324 times the Gaussian constant, empirical Monte Carlo standard error0.0003562094. These are finite-sample diagnostics of the cutoff representation, NOT certified error bounds, a monotone convergence rate, a proof of full-Gibbs outside contributions, or a substitute for the exact full-measure Lean proofs. Evidence: C:/Users/ramir/AppData/Local/Temp/stardust-ym-1709-independent.py/.json/.log.

The complete root build passed7024 jobs in42.54991329999757 seconds. The canonical COMPLETE transitive safe-Foundation audit passed55248 declarations in43.537670199992135 seconds, allowing only propext, Classical.choice and Quot.sound. ALL28 public types were printed unabridged and reviewed:23 complete theorem proofs and5 definitions. Every complete source body was read; no private proof helpers were added. The complete persisted Foundation/AxiomAudit.lean run passed in46.15555049999966 seconds. No sorry/admit/new mathematical axiom/native_decide, changed toolchain/configuration/trust/compiler setting or increased resources were introduced. Evidence prefix: C:/Users/ramir/AppData/Local/Temp/stardust-ym-1709-*.

The integrity manifest authenticates1708's exact approved receipt. Among2806 recursive Foundation/root sources, ONLY the new physical-energy module, root import and axiom ledger differ. All older mathematics,3 pinned configurations,113 baseline original manuscripts and21 Yang-Mills originals(20 distinct hashes) remain byte/hash unchanged. ResearchSources stays unmodified/uncommitted. No manuscript/PDF, manuscripts/, docs/papers/ or editorial README was created, revised, compiled or reviewed. Existing drafts/history and the separate publication role are preserved. No campaign/queue/reflection-policy change was made.

### Exact remaining focused questions

The actual finite-cell physical-action mean and exponential domain are now CLOSED, not merely inferred from bounded chart tests. The methods are classical finite-dimensional Gibbs/Laplace tools; no novelty claim is made. Second/higher physical moment convergence, variance/heat-capacity limits and an explicit Gamma-law identification are NOT automatically certified by the first-mean proof. Uniform perturbed-boundary saddle/coercivity, third-order boundary response, differentiation with respect to boundary parameters and the full harmonic-cubic Lean coefficient remain OPEN. A next substantive bridge is quadratic-stable boundary perturbation control at theta=t*a: a merely linear-in-theta action error would blow up under beta=1/t^2 and is insufficient. Any resulting response estimate must still be connected to an ACTUAL stationary transfer operator before making a spectral claim. The loop-chain slowdown results do not automatically transfer to this72-face cell, and no volume/scale/continuum mass-gap bridge is established. Preserve these distinctions and pursue the strongest concrete transfer/response route rather than broad auxiliary expansion.

Exact Git approval, new-history secret scan, guarded public two-branch synchronization and independent remote-ref verification remain closure gates; this pre-commit ledger does not claim remote backup already succeeded. Repository visibility is exclusively user-controlled. The indefinite research goal remains active.

## Checkpoint1710 - quadratic-stable actual boundary window and uniform domination

October29,2026. Focused Yang-Mills remains ACTIVE. The preceding physical-energy checkpoint269365f989364af20dbd78956677b05b61f26270 passed both guarded backup refs and independent PUBLIC visibility/ref checks. This checkpoint attacks the next specific bottleneck: boundary perturbations theta=t*a with beta*t^2=1. A merely linear angle error would generate beta*theta of order1/t and fail to give a uniform Boltzmann comparison. Existing actual SU(2) defect control instead supplies a quadratic boundary budget, coupled to the full72-face Haar partition.

New sources: Foundation/FourCubeBoundaryCoercivity.lean and Foundation/FourCubeScaledBoundaryControl.lean. Existing actual root-pinning, coercivity, chart/Haar density, partition asymptotic and physical-energy results are reused without alteration. This is one fixed112-edge/72-face cap complex with the existing31-link pin, not an infinite four-dimensional lattice or continuum field construction. No broad gauge library or publication work was undertaken.

### Arbitrary-boundary action and full partition comparisons

For arbitrary actual SU(2) boundary data b define

    B(b)=sum_(48 ribbons p) defect(word(b,p)),    defect(W)=1-halfTrace(W),
    S_b(U)=fullAction(fill(b,fillPole(1,U))),    S_0(U)=pinnedAction(U).

boundaryAction_decomposition identifies the ORIGINAL full72-face action as internal action plus the48 actual twisted ribbon defects. B is nonnegative. Reuse of the verified three-factor defect inequality gives, globally for EVERY boundary b and EVERY pinned state U,

    S_0(U)/3-B(b) <= S_b(U) <= 3*S_0(U)+3*B(b).

The upper/lower estimates are also proved before pinning, for the full32-link interior state. These are genuine action comparisons, not Taylor polynomials or hypotheses about a hypothetical minimizer. Their constants are deliberately coarse; no optimality claim is made. B is a reference-dependent boundary comparison budget in the displayed gauge/identity frame. No invariance of B under independent endpoint gauge changes, intrinsic boundary norm, or gauge-invariant mass-gap criterion is asserted.

perturbedAction_measurable and perturbed_boltzmann_integrable discharge actual measure-theoretic domains for every real beta. For beta>=0, boltzmann_upper/lower and pinnedPartition_upper/lower prove on the FULL Haar integrals

    exp(-3 beta B(b))*Z_0(3 beta) <= Z_b(beta)
      <= exp(beta B(b))*Z_0(beta/3).

The normalized root-gauge volume remains1; the independent checks transfer BOTH comparisons to the original unpinned32-link partition by the existing exact partition_eq_pinned. Nonnegative beta is an essential hypothesis of these order comparisons, not a restriction on finite-scale integrability; the harness explicitly refutes removing it in the scalar action96 example.

### Explicit actual-cell obstruction to dropping the budget

uniformChordBoundary(W) puts identity on all caps and W^(-1) on all48 boundary chords. uniformChord_word, uniformChord_cost and uniformChord_action_at_one prove EXACTLY

    word(b,p)=W,   B(b)=48 defect(W),   S_b(identity interior)=48 defect(W).

For W=axis(0,pi), the actual perturbed action is96 while S_0(identity)=0. no_boundary_free_upper proves that for EVERY real K it is FALSE that S_b(U)<=K*S_0(U) for all b,U. This is an actual pinned72-face counterexample, not only a single-word analogy. It does not refute estimates containing an additive boundary budget. The same construction at arbitrary W remains available for sharper local tests.

### Moving three-axis boundary, uniformly over amplitude balls

axis_defect_upper uses the existing actual axis trace and the elementary global sine bound to prove defect(axis(a,theta))<=theta^2/2 for ALL real theta. It makes no small-angle or sign assumption. Therefore boundaryCost_upper proves for the existing three-axis family

    B(boundaryData(x,y,z)) <=216*(x^2+y^2+z^2).

For b_t=boundaryData(t*x,t*y,t*z), scaled_boundaryCost checks the exact clock beta*t^2=1, beta>=0, and proves

    beta*B(b_t) <=216*(x^2+y^2+z^2).

Both signs of nonzero t are permitted. The independent harness proves beta*t^2=1 is impossible at t=0, and separately verifies the divergent linear-error clock (1/t^2)*t->+infinity as t->0 from the right. The quadratic correction avoids that specific failure; no claim of a full boundary expansion follows from this bound alone.

normalizedPartition_bounds and moving_partition_bounds compare the ACTUAL full partition ratio Z_(b_t)(1/t^2)/Z_0(1/t^2) with the already verified coupling ratios at3 beta and beta/3. uniform_moving_partition_bounds proves: for every fixed amplitude budget R, ONE punctured neighborhood of t=0 works SIMULTANEOUSLY FOR ALL real x,y,z with x^2+y^2+z^2<=R, and there

    exp(-648 R)*((sqrt(3))^(-93)/2) <= Z_(b_t)(1/t^2)/Z_0(1/t^2)
      <= exp(216 R)*((sqrt(1/3))^(-93)+1).

In particular the lower constant is strictly positive and both constants are independent of t and the amplitudes within the ball. The result follows from actual full-Haar partition comparisons and the verified dimension93, not from an assumed Gaussian shift formula. It establishes nondegeneration/boundedness, NOT a contraction factor less than1. The constants are far too coarse to infer a physical spectral gap.

### Uniform integrable density and exact actual-cutoff transport

Let m(Y)=sum_(31 links,3 colors)Y_ea^2 and R_Haar(Y) be the already verified product chart density. The existing cutoff is all links:1+|tY_e|^2<=2. scaled_action_lower and scaled_boltzmann_bound prove for any boundary with beta*B(b)<=A, on that cutoff,

    beta*S_b(chart(tY)) >= m(Y)/1116-A,
    exp(-beta*S_b(chart(tY))) <= exp(A)*exp(-m(Y)/1116).

The factor1116=3*372 explicitly retains the loss from the actual global action comparison. broadened_gaussian_integrable reuses the existing integrable93-dimensional Gaussian envelope by a nonzero scalar dilation; no duplicate Gaussian foundation is built. boundaryScaledDensity is the ACTUAL cutoff integrand

    D_(t,x,y,z)(Y)=1_cutoff R_Haar(tY)*exp(-S_(b_t)(chart(tY))/t^2).

It is measurable and nonnegative. For every t!=0 and every amplitude triple in x^2+y^2+z^2<=R, boundaryScaledDensity_bound proves the SAME domination

    D_(t,x,y,z)(Y) <= R_Haar(0)*exp(216 R)*exp(-m(Y)/1116).

The right side is integrable over ALL93 real coordinates and independent of t and the particular amplitudes. boundaryScaledDensity_integrable follows for every nonzero t and all amplitudes. movingLocalPartition_rescale identifies its integral with the ORIGINAL actual restricted Haar partition, with exact |t|^93 Jacobian. The absolute value retains negative scales. No integrability at t=0 is asserted: the total definition there is the constant R_Haar(0), checked independently. No global quadratic chart coercivity is claimed outside the cutoff, consistent with the preserved affine-coercivity counterexample.

### Verification, independent tests and source preservation

ALL21 independent Lean checks passed in32.89432060002582 seconds: identity-boundary budget/action/partition, both original unpinned partition comparisons, exact cost/action96, the zero reference action and no-budget counterexample, negative axis angles and negative fluctuation clock, impossible zero clock, integrable broader Gaussian, nonzero-scale density integrability and exceptional zero-scale value, actual cutoff Jacobian, uniform amplitude-ball density control and strictly positive full-partition lower bound, zero-amplitude normalization, divergent linear-error clock and the essential nonnegative-coupling hypothesis. A test-only axis-zero reduction was written via the existing defect-zero characterization rather than expanding matrices. Proof-development namespace/finite-sum/measurability elaboration issues were resolved explicitly; no resource increase or theorem weakening was used.

Independent NumPy tests evaluated the actual112-edge72-face quaternion action for4096 arbitrary normalized quaternion configurations with arbitrary boundary data and the exact root pin. Both global action inequalities passed. The actual all-chord central counterexample gave action96. Moving-boundary cutoff integration at t=0.1,0.05,0.01,-0.01 retained the product Haar density. At0.01 the estimated partition ratio was0.2325605193, empirical delta-method standard error0.0109463864; the external classical Gaussian/Schur reference was0.2459290420. This is finite-sample diagnostic evidence, not a certified Monte Carlo error bound, monotone convergence rate, formal perturbed Gaussian limit or boundary-derivative theorem. The coarse scaled-cost bound451.44 exceeded the actual tested value2.9715857298; this illustrates the lack of sharpness and is not evidence for contraction. Evidence: C:/Users/ramir/AppData/Local/Temp/stardust-ym-1710-independent.py/.json/.log.

The complete root build passed7026 jobs in30.220646300003864 seconds. The canonical COMPLETE transitive safe-Foundation audit passed55302 declarations in48.42273489999934 seconds, accepting only propext, Classical.choice and Quot.sound. ALL42 public types were printed unabridged and reviewed:34 complete theorem proofs and8 definitions. Both full source files and the one private internal-action nonnegativity helper were read in full. The COMPLETE persisted Foundation/AxiomAudit.lean run passed in65.71354409999913 seconds. No sorry/admit/new mathematical axiom/native_decide, resource increase, compiler/trust setting or toolchain/configuration change was introduced. Evidence prefix: C:/Users/ramir/AppData/Local/Temp/stardust-ym-1710-*.

Integrity authenticates1709's manifest against exact approval269365f989364af20dbd78956677b05b61f26270. Among2808 recursive Foundation/root files, ONLY the two new focused modules, root imports and axiom ledger differ. All older mathematics,3 pinned configurations,113 baseline original manuscripts and21 Yang-Mills originals(20 distinct hashes) remain unchanged. ResearchSources remains unmodified/uncommitted. No manuscripts/PDFs, publication directories or editorial README were created, revised, compiled or reviewed. Existing drafts/histories, publication role and all campaign priorities remain unchanged.

### Exact remaining boundary and transfer obligations

Quadratic-stable comparison, full-partition nondegeneration and integrable cutoff domination on bounded moving-boundary amplitude balls are NOW VERIFIED. They should no longer be listed as missing hypotheses. A pointwise perturbed joint-action Taylor limit, its explicit effective Gaussian/Schur normalizer, parameter-uniform derivative bounds through third order, full harmonic-cubic Lean coefficient and actual large-beta third boundary response remain OPEN. Uniform domination of the density alone does not justify differentiating a limit.

The next immediate integration bridge is uniform control of the ACTUAL perturbed Gibbs mass outside the existing chart cutoff. A prospective reduction to verify in Lean is a bound by exp(4A)*[Z_0(beta/3)/Z_0(3 beta)] times the existing identity-boundary outside probability at beta/3 when beta*B(b)<=A. This is a NEXT proof target, not an exported theorem here; it requires the actual normalized perturbed law and exact integral identification. Combined with a proved perturbed Taylor limit, the present envelope could then support a full normalized shifted-Gaussian theorem. Boundary derivatives would still need their own valid integrable bounds and convergence. None of the current fixed-cell results establishes stationary physical transfer contraction, a scale/volume-uniform gap, infinite-volume/continuum existence or a Yang-Mills mass gap. No novelty is claimed for the elementary compact-group/Laplace comparison method.

Exact-commit approval, new-history secret scanning, guarded PUBLIC main/research synchronization and independent post-push ref/visibility checks remain closure requirements. This pre-commit entry does not claim remote backup has already succeeded. Repository visibility belongs exclusively to the user. The indefinite research goal remains active.

## Checkpoint1711 - actual perturbed Gibbs laws, uniform concentration and bounded cutoff removal

October29,2026. Focused Yang-Mills remains ACTIVE. Checkpoint1710,4df869190e1162a7a2d5f12bb4f11644d0c67554, was independently verified on BOTH authorized main/research backup refs with repository PUBLIC. The present checkpoint discharges its explicitly recorded missing ACTUAL perturbed-law/cutoff-probability bridge. It reuses the existing positive exponential-tilt probability library, full72-face action,31-link pin, quadratic boundary comparison and reference partition/concentration theorems. No manuscript, PDF, publication directory or editorial README was created, revised, compiled or reviewed.

New focused sources: Foundation/FourCubeBoundaryGibbsComparison.lean and Foundation/FourCubeMovingBoundaryConcentration.lean. All results concern the existing finite112-edge72-face cap complex and its normalized31-link pinned Haar state. They do not construct an infinite four-dimensional lattice measure, continuum field, time evolution or stationary transfer operator.

### Actual probability laws and normalization, for arbitrary boundary data

For every real beta and actual SU(2) boundary data b, source(b,U)=-S_b(U)/144 is measurable and bounded in absolute value by1, from the proved actual action range[0,144]. law(beta,b) is an ACTUAL probability measure, instantiated from BoundedExponentialTiltResponse.tiltedMeasure; law_probability proves the probability instance without an extra assumption. tilted_partition_eq, density_formula and law_withDensity identify its density against the ORIGINAL pinned product Haar measure exactly as

    d mu_(beta,b)/dHaar(U)=exp(-beta*S_b(U))/Z_b(beta).

law_identity identifies the identity-boundary law with the previously verified pinned Gibbs measure. law_integral gives the exact actual integral formula. bounded_test_integrable proves genuine integrability of every measurable uniformly bounded observable, and bounded_setIntegral_bound proves its valid set-integral norm estimate. The unrestricted law_integral identity uses Lean's total Bochner convention; it is NOT an integrability assertion for arbitrary unbounded or nonmeasurable functions. All applications to varying observables below use explicit measurability and a finite uniform bound.

The law and density identities exist for ALL real beta. The order comparisons below require beta>=0. This checkpoint concerns the actual normalized law on the existing31-link pin. The earlier exact32-link partition equality is preserved; no new pushforward theorem for arbitrary unpinned observables or gauge-dependent cutoff events is asserted.

### Full-measure domination, retaining the partition factor

Set

    C(beta,b)=exp(4 beta B(b))*Z_0(beta/3)/Z_0(3 beta),
    B(b)=sum_(48 ribbons p) defect(word(b,p)).

The preceding ACTUAL pointwise action and full-Haar partition bounds prove density_comparison and law_le_reference, for beta>=0,

    mu_(beta,b) <= C(beta,b)*mu_(beta/3,identity).

This is a comparison of actual measures on the WHOLE pinned state space, with no chart cutoff and no observable restriction. law_real_le_reference gives the corresponding real-valued bound for EVERY set A. The conversion from ENNReal explicitly checks finiteness, so no infinity-to-real artifact is used. The normalizer ratio cannot be discarded merely because an unnormalized Boltzmann weight has a pointwise bound.

comparisonCoefficient_ge_one proves rigorously C(beta,b)>=1: evaluate the actual probability-measure comparison on the full state space. The independent Lean harness also proves that NO actual law(beta,b) can be dominated by(1/2) times the reference probability measure. This is a limitation of full positive-measure domination as a contraction argument, not an obstruction to centered correlation decay or a spectral gap by other methods. In particular these constants must not be presented as stationary transfer contraction factors.

### Uniform concentration on bounded moving-boundary amplitude balls

Write beta=1/t^2, b_t=boundaryData(t*x,t*y,t*z), and x^2+y^2+z^2<=R. The verified quadratic budget beta*B(b_t)<=216R implies the ACTUAL all-set estimate

    mu_(1/t^2,b_t)(A) <= exp(864R)*Q(t)*mu_((1/t^2)/3,identity)(A),
    Q(t)=Z_0((1/t^2)/3)/Z_0(3*(1/t^2)).

moving_law_real_bound proves it for every nonzero real t, both signs, and every set A. referenceRatio_tendsto proves Q(t) tends to the finite positive constant

    ((sqrt(1/3))^(-93))/((sqrt(3))^(-93)).

The proof uses the two already verified exact full-partition scaling limits, their strictly positive denominators and an explicit cancellation. third_clock_tendsto verifies the reference coupling(1/t^2)/3->+infinity through the punctured real neighborhood. Hence the old actual identity-boundary outside probability tends to0 at that clock.

leakageEnvelope(R,t)=exp(864R)*Q(t)*mu_((1/t^2)/3,identity)(outside cutoff) tends to0. moving_outside_bound dominates the ACTUAL perturbed outside probability by this SINGLE envelope. uniform_outside_concentration proves: for every R and epsilon>0, ONE punctured neighborhood of0 works SIMULTANEOUSLY FOR ALL x,y,z in the amplitude ball and there

    mu_(1/t^2,b_t)(outside cutoff)<epsilon.

uniform_inside_concentration proves the corresponding absolute difference from probability1 inside the cutoff. These are normalized probability statements, not unnormalized density estimates or assumed Gaussian probabilities. The existing actual cutoff is all31 links in the positive-trace hemisphere with chartRate<=2. No global affine chart coercivity is asserted, consistent with the preserved explicit obstruction.

### Cutoff removal for varying actual observables

moving_outside_tendsto_zero permits arbitrary real amplitude profiles x(t),y(t),z(t) satisfying the displayed uniform squared-amplitude budget. Neither continuity nor convergence of these parameter profiles is assumed or needed. This does not construct a stochastic process in t or assert joint path measurability; it is a uniform scalar-parameter probability theorem.

moving_outside_integral_tendsto_zero proves the actual outside integral tends to0 even when the observable f_t varies with t, provided EACH f_t is measurable on the pinned state space and |f_t(U)|<=M for ONE finite constant M, uniformly in t,U. bounded_test_integrable discharges actual integrability, and the set-integral bound is applied before squeezing to zero. The independent Lean harness tests x(t)=sin(1/t),y(t)=cos(1/t),z(t)=0 and the varying physical observable sin(1/t)*cos(S_0(U)). No nonexistent limit of the amplitudes or observable is smuggled into the argument.

Small outside mass alone gives NO bound on unrestricted ratio-coordinate moments, unbounded boundary-derivative fields or observable norms growing as t->0. Those require their own weighted estimates or uniform-integrability arguments. The theorem does not silently cover them.

### Verification, independent diagnostics and integrity

ALL20 independent Lean checks passed in28.10483419999946 seconds. They cover the actual probability instance for every real beta, identity and zero-coupling law identification, mass1, nonnegative density, full measure/all-set domination, C>=1 and C(0,b)=1, impossibility of strict half-measure domination, the exceptional Q(0)=1 convention, leakage-envelope convergence, exact uniform inside/outside quantifiers, oscillating amplitude profiles, actual integrability of the bounded physical action, measurable bounded set-integral domains, a varying physical observable and the full all-set moving-window bound. A TEST-only constant-function notation in withDensity_one was made explicit; no mathematical source change or resource increase was needed for that repair.

An independent NumPy diagnostic used4096 normalized-quaternion Haar samples for the actual pinned72-face action, with fixed arbitrary boundary data. Finite empirical Haar quadrature verified the normalized density and event comparison factors at beta0,0.02,0.1,0.4. At identity boundary the sampled density ratio at the identity point was2.595092368 at beta0.02, showing why testing an unnormalized weight bound alone does not test the normalized-density statement. A negative-coupling diagnostic produced a comparison coefficient below1, OUTSIDE the proved beta>=0 order-comparison domain. These are diagnostics in a finite empirical quadrature model, NOT certified continuous-Haar partition values, a new formal negative-beta counterexample or a simulation proof of uniform cutoff concentration. Evidence: C:/Users/ramir/AppData/Local/Temp/stardust-ym-1711-independent.py/.json/.log.

The complete root build passed7028 jobs in64.23121510000783 seconds. The canonical COMPLETE transitive safe-Foundation axiom audit passed55358 declarations in43.82404510001652 seconds, allowing only propext, Classical.choice and Quot.sound. ALL34 public types were printed unabridged and reviewed:26 complete theorem proofs,7 definitions and1 actual probability instance. Both complete source files and every proof/definition/instance body were read; no private helper was added. The COMPLETE persisted Foundation/AxiomAudit.lean run passed in49.51023949999944 seconds. No sorry/admit/new mathematical axiom/native_decide, increased resource setting or toolchain/configuration/compiler/trust change was introduced. Explicit unfolding/cancellation repaired proof elaboration while preserving every mathematical hypothesis. Evidence prefix: C:/Users/ramir/AppData/Local/Temp/stardust-ym-1711-*.

The source manifest authenticates1710 against exact approved4df869190e1162a7a2d5f12bb4f11644d0c67554. Among2810 recursive Foundation/root sources, ONLY these two focused new modules, root imports and axiom ledger differ. All older mathematics,3 pinned configurations,113 baseline original manuscripts and21 Yang-Mills originals(20 distinct hashes) remain byte/hash unchanged. ResearchSources remains unmodified/uncommitted. Existing drafts, histories, publication-role separation, reflection policy and campaign priorities are preserved.

### Exact next mathematical bottleneck

The prospective outside-probability bridge recorded at1710 is NOW CLOSED: actual perturbed probability laws, correct normalized comparison, uniform moving-window cutoff concentration and bounded-observable cutoff removal are VERIFIED. Together with1710's actual Haar cutoff transport and uniform integrable Gaussian envelope, this supplies the integration control needed for a future perturbed action limit. It does NOT supply that pointwise Taylor limit, an explicit shifted Gaussian/Schur normalizer, parameter-uniform third derivatives or the actual large-beta mixed cubic response.

Next pursue the joint boundary/interior action expansion with the ACTUAL SU(2) curves, reusing the verified matrix jets, full face incidence and Schur machinery. Any claimed third-order response must additionally prove the appropriate weighted derivative domains, integrable bounds and convergence; bounded-test cutoff removal does not settle a test with a t-dependent growing norm. The full harmonic-cubic coefficient remains an external rational diagnostic until verified in Lean and connected to actual Gibbs boundary derivatives. Stationary physical transfer estimates, scale/volume-uniform control, infinite-volume/continuum construction and a positive Yang-Mills mass gap remain OPEN. The reference-dependent boundary cost is not an intrinsic gauge-invariant spectral estimate. No novelty is claimed for classical finite-dimensional Gibbs comparison/concentration tools.

Exact-commit approval, new-history secret scan, guarded PUBLIC main/research synchronization and independent post-push remote-ref/visibility checks remain checkpoint closure gates. This pre-commit ledger does not assert remote backup already succeeded. Visibility is exclusively user-controlled. The indefinite research goal remains active.


## Checkpoint1712 - actual joint moving-boundary action and full Haar partition limit

October29,2026. Focused Yang-Mills remains ACTIVE. Previous checkpoint1711,4f25f6218509a13cb181901ae3426f044c34334a, was independently verified on BOTH authorized backup refs with repository PUBLIC. This checkpoint closes its explicitly missing pointwise perturbed Taylor limit and full-partition integration bridge. It does not exchange derivatives with a limit. The primary researcher performs no publication duties: no manuscript/PDF, manuscripts/, docs/papers/ or editorial README work. Original manuscript checks here are hashes only.

Five focused sources: SU2FourCurveJetTransfer, SU2AxisMatrixJets, FourCubeMovingBoundaryQuadratic, FourCubeMovingActionLimit and FourCubeMovingLaplaceLimit under Foundation/. They concern the actual existing finite112-edge72-face cap complex with normalized31-link pinned Haar coordinates, not a volume-uniform lattice or continuum construction.

For fixed real amplitudes a=(x,y,z), b_t=boundaryData(tx,ty,tz), and actual93-dimensional pinned Haar chart Y, movingRay is the ACTUAL full action S_(b_t)(chartField(tY)). The new four-word transfer theorem compares C2 matrix curves having matching value, first and second derivatives with the exponential model. The actual axis matrix formula proves axis0,axis1,axis2 correspond to normalized Pauli vectors (0,0,2r),(2r,0,0),(0,2r,0). Boundary inverses and signed word slots are proved explicitly. No matching THIRD jet is assumed.

For each ribbon p let v0 be the verified normalized interior chart velocity, v1 the high-cap velocity, v2 the chord velocity and v3 the low-cap velocity. Its explicit second variation is q_p=|v0+v1-v2-v3|^2/4. The actual chosen chord and low-cap velocities already carry their boundaryData inverse signs. Omitting mixed terms or changing inverse-slot signs is invalid. Define

    Q_a(Y)=Q_0(Y)+sum_(48 ribbons p)(q_p(Y,a)-q_p(Y,0)).

This is an explicit finite quadratic polynomial, not a derivative postulated to exist. Exact full-action decomposition, actual matrix jets and Taylor's theorem prove movingRay is C2, its value and first derivative vanish at0, second derivative equals Q_a, and its remainder after (Q_a/2)t^2 is o(t^2). Thus S_(b_t)(chartField(tY))/t^2 tends to Q_a(Y)/2 through the PUNCTURED real neighborhood, for both signs of t. Nonnegativity Q_a>=0 follows independently from actual full-action nonnegativity and the proved quotient limit. At a=0 the old Q_0 is recovered exactly. Lean's total quotient at t=0 cannot replace this punctured topology.

Set g_a(Y)=R_Haar(0)*exp(-Q_a(Y)/2), where R_Haar is the actual previously verified product chart density. The actual scaled cutoff density D_t tends pointwise to g_a. Its prior integrable envelope bounds g_a by R_Haar(0)*exp(216*(x^2+y^2+z^2))*exp(-mass(Y)/1116). Measurability, genuine integrability and C_a=integral g_a>0 are now proved. Filter dominated convergence gives integral D_t -> C_a. g_a is an UNNORMALIZED quadratic-exponential density; no new IsGaussian law, explicit inverse covariance, determinant or completed-square identity is asserted.

Actual normalized cutoff probability equals movingLocalPartition/Z_(b_t)(1/t^2) and tends to1 by1711's genuine perturbed Gibbs concentration. The exact Haar chart transport and this probability yield

    Z_(b_t)(1/t^2)/|t|^93 -> C_a > 0,
    Z_(b_t)(1/t^2)/Z_0(1/t^2) -> C_a/C_0,
    -log(Z_(b_t)(1/t^2)/Z_0(1/t^2)) -> -log(C_a/C_0).

These are ACTUAL full-Haar partition/free-energy limits at fixed amplitudes. The independent Lean harness transfers the partition asymptotic to the original unpinned32-link normalizer and existing partition3 using prior exact identities. No conditioning on a measure-zero pin is introduced. Strict positivity justifies logarithm continuity; it does not justify boundary differentiation. Uniform-in-amplitude convergence and a normalized bounded-observable moving-law theorem are not exported here.

Verification and independent checks:
- build: PASS, 55.889655999984825 seconds.
- audit: PASS, 39.88132129999576 seconds.
- checks: PASS, 30.462504299997818 seconds.
- axiom-ledger: PASS, 50.739238500013016 seconds.

The full root build passed7033 jobs; canonical COMPLETE transitive safe-Foundation axiom audit passed55469 declarations allowing only propext, Classical.choice and Quot.sound. ALL71 public types were printed unabridged and reviewed:56 theorem proofs,14 definitions and1 abbreviation, no instances. All five complete source bodies and both private helpers (boundary_alternative and axis_zero) were read. The persisted complete Foundation/AxiomAudit.lean run passed. No sorry/admit/new mathematical axiom/native_decide, resource increase, toolchain/configuration/compiler/trust change or audit weakening was introduced.

ALL29 independent Lean examples passed. They test axis normalization/inverses/two-jets, explicit mixed-word and inverse-slot Hessians, actual chart/ribbon identification, C2/value/first/second jets, Q_a nonnegativity and zero-amplitude reuse, invalid unpunctured quotient, integrability/positive limit, original unpinned and partition3 limits, normalized partition/free energy and the zero-amplitude partition identity. Independent NumPy full72-face quaternion calculations and separately enumerated signed incidence tested11 fixed cases at h=.02,.01,.005. A selected mixed case gives actual joint quadratic10 versus incorrectly separated8. Boundary-only symmetric finite differences tend to the explicit quadratic; its odd cubic diagnostic tends to1. These are floating diagnostics, NOT certified error bounds, a formal third-response theorem, determinant identity or mass-gap proof. Evidence prefix: C:/Users/ramir/AppData/Local/Temp/stardust-ym-1712-*.

The source-integrity manifest authenticates1711 against exact approved4f25f6218509a13cb181901ae3426f044c34334a. Among2815 recursive Foundation/root Lean files, only the five new modules, root imports and AxiomAudit differ. All older mathematics,3 pinned configurations,113 baseline originals and21 Yang-Mills originals(20 distinct hashes) remain unchanged. ResearchSources stays unmodified/uncommitted. All drafts/histories, publication separation and campaign priorities are preserved.

Exact remaining bottleneck: the actual fixed-amplitude joint Taylor and full-partition limits are NOW VERIFIED and must no longer be listed as missing hypotheses. Explicit completion of the square/Schur normalizer and identification with existing harmonic data remain open. Parameter derivatives through third order, weighted integrability and convergence for actual boundary response remain separate obligations; neither fixed-amplitude convergence nor bounded-test cutoff removal proves them. The external full harmonic-cubic rational diagnostic is still not a Lean theorem about actual Gibbs third derivatives. Stationary physical transfer contraction, a physically justified iteration distance, scale/volume-uniform estimates, infinite-volume/continuum construction and positive Yang-Mills mass gap remain OPEN. No novelty is claimed for classical finite-dimensional Taylor/Laplace tools. Continue the focused mathematical bottleneck rather than broad auxiliary-library expansion.

Exact-commit approval, new-history secret scanning, guarded PUBLIC main/research synchronization and independent post-push ref/visibility checks are closure gates. This pre-commit entry does not assert backup already succeeded. Visibility is exclusively user-controlled. The indefinite research goal remains active.


## Checkpoint1713 - actual full-Haar moving-boundary limit equals the pinned Schur form

October29,2026. Focused Yang-Mills remains ACTIVE; Bakry remains paused. Previous1712,1ad7d3335b4e94fe2ad9f1248b1e5d00f1325390, is exact-commit approved and independently verified on BOTH authorized backup refs with repository PUBLIC. This checkpoint identifies its actual quadratic-exponential partition limit using the EXISTING OneSidedSchurForm completed square. It builds one focused bridge, Foundation/FourCubeMovingSchurLimit.lean, rather than new Gaussian infrastructure. No publication duties were performed: no manuscripts/PDFs, manuscripts/, docs/papers/ or editorial README were created, revised, compiled or reviewed. Original-source checks are hashes only.

Exact actual-to-linear identification. Let Y be the actual93-dimensional retained Haar chart and a=(x,y,z) fixed real boundary amplitudes. For each normalized Pauli channel j, eta_j(c)=boundaryVector(x,y,z,c)(j). Its values retain the actual cap/chord inverse signs proved at1712. The chart frame is T(Y)=(2Y_1,2Y_2,2Y_0). scalar_joint_difference identifies the old pinned incidence energy with its actual ribbon correction; jointQuadratic_schur_input proves

    Q_a(Y)=(1/4) sum_(j=0,1,2) jointEnergy(T(Y)_j,eta_j).

The original full action divided by t^2 therefore tends to (1/8)sum jointEnergy, not (1/4)sum. This normalization is independently tested in Lean. All local matrices are the previously verified ACTUAL31-coordinate pinned incidence matrices. The proof explicitly checks zero inner boundary curl and the signed high-cap/chord/low-cap ribbon rows. No matrix is silently replaced by a surrogate.

Define the harmonic chart shift h_a by T(h_a)_j=response(eta_j), using the existing inverse pinned Gram response. In quaternion chart order h_a=(response(eta_2)/2,response(eta_0)/2,response(eta_1)/2). Define

    E(a)=(1/4)sum_j reducedEnergy(eta_j)
        =(1/4)sum_j eta_j dot (schur*eta_j).

actual_completed_square proves Q_a(Y)=E(a)+Q_0(Y-h_a), with E(a)>=0. actual_minimum_bound and actual_unique_minimizer prove h_a is the UNIQUE global minimizer of THIS quadratic limiting action, with value E(a). This is not a theorem about the exact finite-t nonlinear action's minimizer or an assumed implicit nonlinear saddle. Positivity uses the established pinned Gram theorem, retaining the original gauge pin and its exact Haar normalization.

effectiveEnergy_zero_iff_gauge proves E(a)=0 exactly when EACH eta_j lies in the existing scalar boundary-gradient range. This is the precise infinitesimal, channelwise gauge degeneracy of the limiting Schur energy. It is not a claim of full nonabelian gauge invariance for arbitrary parameterized reference-boundary costs, nor a physical spectral-gap estimate.

Full-Haar normalizer identification. The actual limiting density from1712 now satisfies

    g_a(Y)=exp(-E(a)/2)*g_0(Y-h_a),
    C_a=integral g_a=exp(-E(a)/2)*C_0.

The integral equality uses actual Lebesgue/Haar translation invariance on the full93-coordinate space and the already proved finite, strictly positive C_0. No determinant formula, numerical inverse, IsGaussian axiom, conditioning on a measure-zero pin or differentiation under an integral is assumed. Combining with1712's actual full-Haar partition theorem gives

    Z_(b_t)(1/t^2)/Z_0(1/t^2) -> exp(-E(a)/2),
    -log(Z_(b_t)(1/t^2)/Z_0(1/t^2)) -> E(a)/2,

through the PUNCTURED real neighborhood of0, both signs, for b_t=boundaryData(tx,ty,tz). The limiting ratio is positive and <=1. Its being <=1 is NOT a transfer-operator contraction statement. The independent harness also identifies the normalized limiting density as g_0(Y-h_a)/C_0, so the scalar factor cancels only after the correct C_a is retained. No new normalized actual moving-law convergence theorem is exported here.

Verification and independent testing:
- build: PASS, 25.719220900005894 seconds.
- audit: PASS, 40.47027029999299 seconds.
- checks: PASS, 27.51154740000493 seconds.
- axiom-ledger: PASS, 48.81928829997196 seconds.

The full root build passed7034 jobs. The canonical COMPLETE transitive safe-Foundation axiom audit passed55500 declarations, permitting only propext, Classical.choice and Quot.sound. ALL20 public types were printed unabridged and reviewed:16 theorem proofs,3 definitions and1 abbreviation, no instances. The entire source and all four private helpers (boundary_zero,local_upper,boundary_inner,boundary_upper) were read. The COMPLETE persisted Foundation/AxiomAudit.lean run passed. No sorry/admit/new mathematical axiom/native_decide, resource increase, toolchain/configuration/compiler/trust change or verification weakening was introduced. Local irreducibility of the existing finite geometry sets avoids unnecessary unfolding at congruence; no recursion/heartbeat limit was increased.

ALL18 independent Lean examples passed. They test the actual normal equations after frame transport; the physical factor1/8; completed square/minimum/strict uniqueness; pointwise translated and normalized densities; correct positive normalizer and upper bound; exact gauge criterion and nongauge positive E; gauge-zero limit1; free-energy limit; positive-E ratio<1 and failure of an unpunctured limit; zero-amplitude E=0/shift=0; and the absolute full partition asymptotic. The positive-E test proves the old zero-coupling value at t=0 is1 and cannot equal exp(-E/2). A TEST-only higher-order zero-function simplification was repaired by unfolding the finite dot product; mathematical sources and resources did not change for that repair.

An independent exact-rational calculation reconstructed all72 face rows and solved the actual32-link scalar normal equations, then converted to the SAME pole0 pin. All32 equations in all3 source columns were checked exactly. Nine deterministic rational amplitude/interior cases satisfy joint energy=effective minimum+centered energy exactly. A separate65536-sample Gaussian importance diagnostic gave normalizer ratio estimate0.9305933382083179 versus predicted0.9308463707661071, standard error0.0012238147019999447, effective energy0.14332206122082464. Rational calculations are independent finite-cell algebra diagnostics; floating integration is NOT a certified integral/error bound, proof of the Haar asymptotic, third derivative, mass gap or novelty. Evidence prefix: C:/Users/ramir/AppData/Local/Temp/stardust-ym-1713-*.

Source integrity authenticates1712's manifest against exact approval1ad7d3335b4e94fe2ad9f1248b1e5d00f1325390. Among2816 recursive Foundation/root Lean files, only the new focused module, root import and AxiomAudit differ. All older mathematics,3 pinned configurations,113 baseline originals and21 Yang-Mills originals(20 distinct hashes) remain unchanged. ResearchSources remains unmodified/uncommitted. Existing drafts/history, publication separation, daily reflection policy and queue are preserved.

Exact next bottleneck. The explicit leading Schur normalizer and its connection to the actual fixed-cell Haar boundary free energy are NOW VERIFIED, not missing hypotheses. No large-beta third boundary derivative follows from this leading fixed-amplitude limit. Its first correction requires actual higher action jets, the correct Gaussian averages/connected terms, and weighted remainder/tail estimates; dividing an unspecified o(1) by t is invalid. The external harmonic-cubic rational diagnostic remains unconnected to an actual Haar third-response Lean theorem. Matrix two-jet matching alone must NOT be promoted to three-jet matching. Next audit/reuse the existing actual SU(2) cubic and smooth bounded-tilt results for this specific correction, with exact domains and independent coefficient tests, rather than expanding a broad gauge library. Parameter-uniform derivative convergence, stationary physical transfer estimates, physically justified iteration scales, volume/continuum-uniform control and positive Yang-Mills mass gap remain OPEN. These leading finite-dimensional Laplace/Schur tools are classical; no novelty is asserted.

Exact-commit approval, new-history secret scanning, guarded PUBLIC main/research synchronization and independent remote-ref/visibility verification remain closure gates. This pre-commit entry does not claim a remote backup already exists. Visibility belongs exclusively to the user. The indefinite goal remains active.


## Checkpoint1714 - exact quaternion odd words and actual72-face cubic/Boltzmann corrections

October29,2026. Focused Yang-Mills remains ACTIVE, Bakry paused. Previous1713,aa4332c9b5e9dfc05cbf1e9a5daa75883e0a03d0, is exactly approved and independently verified on BOTH authorized backup refs with repository PUBLIC. Two focused sources, Foundation/SU2QuaternionOddWord.lean and Foundation/FourCubeMovingOddAction.lean, now identify the missing POINTWISE odd correction for the actual full cell. They do NOT exchange a limit and a Haar integral. No manuscript/PDF, manuscripts/, docs/papers/ or editorial README was created, revised, compiled or reviewed. ResearchSources checks are hashes only.

A distinct mathematical mechanism replaces unnecessary third-jet matching. For ANY four raw real quaternions q_i, with A(q)=1-Re(q_0 q_1 q_2 q_3), exact_odd_word proves

    A(q)-A(star q)=2 sum_(i<j<k) Re(q_l)*det(Im q_i,Im q_j,Im q_k),

where l is the omitted index. No unit norm, probability or asymptotic assumption is required for this algebraic identity. odd_quotient divides it correctly by2t^3 for t!=0. Consequently, if q_i(-t)=star(q_i(t)), Re(q_i(t))->1 and Im(q_i(t))/t->v_i through the punctured real neighborhood, then the odd action quotient tends to the sum of the four triple determinants of v. This result uses FIRST tangents and exact inverse parity; it does not equate hemisphere/exponential third matrix jets or infer third differentiability from a central quotient.

matrix_word_odd_limit applies this identity to genuine SU(2) matrix curves starting at identity, with actual HasDerivAt hypotheses and P_i(-t)=P_i(t)^(-1). Four explicit real continuous-linear coordinate maps recover quaternion real/imaginary parts from the actual matrix representation. recover_inverse and wordAction_raw prove the exact quaternion/matrix/product identification. The slope limit at0 supplies imaginary-coordinate/t convergence. No surrogate matrix or unproved analytic jet is substituted.

ACTUAL full-cell bridge. links(Y,a,t) is exactly the original112-edge field obtained from the31-link Haar chart tY, the existing root pin and b_t=boundaryData(tx,ty,tz). links_zero, links_hasDerivAt and links_parity are verified for EVERY actual edge. Interior parity follows from the actual even hemisphere weight times affine imaginary curve; boundary parity uses the actual axis/inverse definitions. Each oriented face factors into its two direct and two inverse links; the inverse derivatives are the actual matrix adjoints. fullAction_rows proves equality with the SUM OF ALL72 ACTUAL face words for arbitrary SU(2) fields. It explicitly transports all24 inner plaquettes and all48 cap ribbons, retaining their signs and geometry.

Define C(Y,a) as the sum over those72 faces of the four triple determinants of the recovered imaginary first derivatives of their actual signed factors. It is an explicit finite polynomial built from already defined chart/boundary velocities, not a derivative or coefficient assumed to exist. actual_cubic_odd_limit now proves, for EVERY fixed chart Y and fixed real amplitudes a,

    [S_(b_t)(chart(tY))-S_(b_(-t))(chart(-tY))]/(2t^3) -> C(Y,a).

The formula includes both interior and boundary cubic contributions. It is not a single selected ribbon, a three-axis toy word, a conditional one-link action or a zero-coupling variance calculation. All limits are through the punctured real neighborhood, both signs.

Combining the exact odd quotient with1712's ACTUAL quadratic action limit gives actual_boltzmann_odd_limit:

    [exp(-S(t)/t^2)-exp(-S(-t)/t^2)]/(2t)
      -> -C(Y,a)*exp(-Q_a(Y)/2).

The proof factors the exponential difference using the continuous extended derivative slope dslope(exp,0), derives the negative-time scaled action from the positive-time action and its exact odd difference, and handles t!=0 before cancellation. It does not differentiate the leading partition asymptotic. In particular the pointwise first odd Boltzmann correction is NOW VERIFIED, not a missing hypothesis.

Verification and independent checks:
- build: PASS, 10.308425399998669 seconds.
- audit: PASS, 40.58246949999011 seconds.
- checks: PASS, 27.01090799999656 seconds.
- axiom-ledger: PASS, 45.61212289999821 seconds.

The final complete root build passed7036 jobs. The canonical COMPLETE safe-Foundation transitive axiom audit passed55574 declarations, allowing only propext, Classical.choice and Quot.sound. ALL33 public types were printed unabridged and reviewed:17 complete theorem proofs,14 definitions and2 abbreviations; no instances. Both entire source files and both private helpers (chart_parity,retained_inner) were read. The COMPLETE persisted Foundation/AxiomAudit.lean run passed. No sorry/admit/new mathematical axiom/native_decide, resource increase, toolchain/configuration/compiler/trust change or weakened check was introduced. Default-instance elaboration, geometry namespaces, explicit derivative points and quotient signs were repaired without changing the mathematical claims.

An audit-setup loop initially listed only the first module's17 public declarations. Its assertion caught this BEFORE checkpoint acceptance; the incomplete type manifest was not used as a complete review. After that run terminated, the enumeration was corrected to BOTH modules/all33 public declarations, the persisted ledger was completed, and the root build plus canonical audit were rerun. The accepted timings above belong to the corrected run. The earlier26.484824799990747-second root build and40.30193580000196-second canonical audit are diagnostic passes with incomplete printed-type coverage, not the accepted complete type-review gate. No performance optimization is claimed from these cached timing differences.

ALL18 independent Lean examples passed. They test determinant orientation and inverse signs, exact non-even raw quaternion words, collinear cancellation, the ACTUAL chart/Pauli normalization imag(recover(generator(Y)))=Y, quaternion recovery of SU(2) inverses, actual112-edge initial values/first derivatives/parity, exact72-face count and action coverage, both actual odd limits, the Schur completed-square expression in the Boltzmann coefficient, nonzero coefficients and failure of an unpunctured action quotient. Two explicit two-atom determinant calculations give mean determinant1 but determinant of mean0; replacing cubic averages by a mean evaluation requires a genuine cancellation/domain theorem and is not universally valid.

Independent diagnostics checked32 rational quaternion words exactly against the full weighted triple-determinant identity. Eleven actual full72-face quaternion cases at t=.02,.01,.005 compared the odd action and Boltzmann quotients with their separately enumerated signed-incidence determinant predictions, including boundary-only, mixed interior/boundary and zero-boundary cases. The external harmonic cubic31877443263/69438734552 was reproduced as an EXACT RATIONAL FINITE-JET DIAGNOSTIC, still not a Lean-certified actual integrated Haar response. These floating quotient tests provide no certified rate, integrable domination, Gaussian average, limit exchange, large-beta third boundary derivative, volume/continuum estimate or mass-gap theorem. Evidence prefix: C:/Users/ramir/AppData/Local/Temp/stardust-ym-1714-*.

The source manifest authenticates1713 against exact approvalaa4332c9b5e9dfc05cbf1e9a5daa75883e0a03d0. Among2818 recursive Foundation/root Lean files, only the two new focused modules, root imports and AxiomAudit differ. All older mathematics,3 pinned configurations,113 baseline originals and21 Yang-Mills originals(20 distinct hashes) remain unchanged. ResearchSources stays unmodified/uncommitted. Existing drafts/history, publication role separation, daily reflection and campaign priorities are preserved.

Precise remaining integration bottleneck and strongest next route. Pointwise odd action and Boltzmann limits are now CLOSED. Full integrated first correction remains OPEN. A concrete route is to use the EXACT odd-word identity plus |sin(tr)/t|<=|r| and the actual hemisphere weight bound to dominate the cubic action quotient by an explicit degree3 coordinate/amplitude polynomial. An exponential difference bound, together with the already verified local quadratic coercivity at BOTH signs, should then give a polynomial times the existing integrable Gaussian envelope. This bound and its integrability must be PROVED, not inferred from the existing density bound. Full-cutoff removal after division by t additionally needs the actual outside exponential tail to beat the |t|^(-94) scaling; mere outside probability->0 is insufficient. These are prospective reductions, not exported theorems here.

For the limiting average,1713 supplies the actual translated centered quadratic density. Every determinant monomial uses three distinct quaternion colors; a promising reuse mechanism is separate color reflections of the centered pinned quadratic form. Once the necessary polynomial integrability and measure-preserving transformations are verified, eight-sign averaging may eliminate all centered terms and retain the harmonic evaluation. This would avoid assuming a new IsGaussian law or an unproved covariance formula. The proposed averaging theorem is OPEN and the two-atom test records why its symmetry hypotheses matter. Computing or importing the external rational harmonic coefficient still needs an actual Lean certificate tied to the proved coefficient definition.

None of these pointwise results establishes a parameter-uniform boundary third-derivative theorem, actual stationary transfer contraction, physically justified iteration distance, scale/volume-uniform estimates, infinite-volume/continuum existence or positive Yang-Mills mass gap. Classical quaternion/parity tools are reused; no novelty is claimed. Continue this specific actual integration bottleneck rather than building unrelated gauge infrastructure.

Exact-commit approval, new-history secret scan, guarded PUBLIC main/research backup and independent remote-ref/visibility checks remain closure gates. This pre-commit entry does not assert backup already succeeded. Visibility is exclusively user-controlled. The indefinite research goal remains active.


## Checkpoint1715 - rigorous weighted integration and actual full-Haar odd partition correction

October29,2026. Focused Yang-Mills remains ACTIVE; Bakry remains paused. Previous1714,02d20c378e3fb7a804b1bd4b5f62010e623fd526, is exactly approved and independently verified on BOTH authorized backup refs with repository PUBLIC. This checkpoint closes its missing integrable-domination and quantitative full-cutoff-removal obligations for the FIRST ODD PARTITION CORRECTION. It does not evaluate the resulting cubic average or interchange a boundary derivative with a large-beta limit. Three focused sources: Foundation/FourCubeOddEnvelope.lean, FourCubeOddIntegral.lean and FourCubeOddFullPartition.lean. No manuscript/PDF, manuscripts/, docs/papers/ or editorial README work was performed. Original-source checks are hashes only.

Actual scale-uniform bounds. Write a=(x,y,z), m(Y)=quadraticMass(Y), and

    H(Y,a)=1+m(Y)+|x|+|y|+|z|.

For every nonzero REAL t, every actual112-edge field component and every signed face factor, the recovered imaginary quaternion component divided by t is bounded in absolute value by H. The interior proof uses the ACTUAL hemisphere weight in[0,1]; the boundary proof uses the ACTUAL axis/inverse formulas and |sin(tr)/t|<=|r|. The root pin and every inverse sign are retained. Generic determinant and weighted four-word bounds give24H^3 per face, hence the full72-face estimate

    |[S(t)-S(-t)]/(2t^3)| <=1728H(Y,a)^3.

This action bound is GLOBAL in chart Y and needs no cutoff. H is linear in m, so H^3 has degree up to6 in the raw chart coordinates; it is a conservative polynomial envelope, not a sharp degree3 bound in Y. No physical contraction meaning is attached to1728.

The exponential mean-value inequality is applied on a common upper half-line for BOTH signed exponents. On the ACTUAL chart cutoff, the previously verified quadratic coercivity yields

    |[exp(-S(t)/t^2)-exp(-S(-t)/t^2)]/(2t)
      <=1728H^3 exp(216*(x^2+y^2+z^2)) exp(-m/1116).

actual_boltzmann_odd_bound proves this for both signs of t. The cutoff is an explicit hypothesis; no false global affine chart coercivity is introduced. A proved exponential-series inequality absorbs H^3 into the broader Gaussian exp(-m/2232), with fixed-amplitude constant6*2232^3*exp((1+|x|+|y|+|z|)/2232). wider_gaussian_integrable reuses the existing Gaussian integral by scalar rescaling; cubic_weight_integrable is genuine integrability, not a formal moment declaration. Constants depend on the amplitudes; no uniform parameter-derivative convergence is claimed.

Actual Haar-density integration. Let D_t(Y) be the exact existing moving-boundary scaled cutoff density with the original product Haar Jacobian, and let g_a(Y)=R_Haar(0)exp(-Q_a(Y)/2) from1712. Product Haar density and the cutoff are proved EVEN in t. Therefore the signed density

    O_t(Y)=[D_t(Y)-D_(-t)(Y)]/(2t)

has a single integrable Gaussian-polynomial envelope for EVERY nonzero t. The already verified pointwise odd Boltzmann limit gives

    O_t(Y) -> f_a(Y)=-C(Y,a)g_a(Y).

Explicit coordinate/linear-map composition proves measurability of the actual cubic coefficient and f_a. firstDensity_integrable proves f_a is genuinely integrable, and oddDensity_integrable proves each O_t is integrable. In particular the displayed integrals are not merely Lean's default-zero values outside an integrable domain. f_a is a SIGNED correction density, not a probability density or a new stochastic law. Pointwise positivity is not assumed. Scalar filter dominated convergence now proves integral O_t -> I(a)=integral f_a, and exact Jacobian cancellation identifies the ACTUAL cutoff partition odd quotient with denominator2t|t|^93. This checkpoint exports integrability and integral convergence; a separate L1-norm-convergence theorem is not claimed.

Quantitative removal of the full Haar cutoff. Outside localStateDomain, the existing coordinate-tail inclusion and actual pinned link estimate give S_0(U)>=1/12. The actual boundary-action comparison gives the ALL-STATE outside bound

    exp(-S_(b_t)(U)/t^2) <= exp(216*|a|_2^2)exp(-1/(36t^2)).

Integrating against the ORIGINAL normalized pinned Haar probability measure yields the same upper bound for outsidePartition(t,a). gaussian_tail_power94 proves exp(-1/(36t^2))/|t|^94 ->0 through the punctured real neighborhood, by the verified inverse-square clock and exponential domination of the47th power. Both outside partitions divided by |t|^94 vanish; their signed odd difference divided by2t|t|^93 also vanishes. Mere concentration to probability1 was NOT substituted for this stronger rate.

full_partition_split is an exact integral identity for ALL real t, with integrability established before splitting. Combining it with the proved cutoff correction yields

    [Z_(b_t)(1/t^2)-Z_(b_(-t))(1/t^2)]/(2t|t|^93) -> I(a),
    [N_(b_t)(1/t^2)-N_(b_(-t))(1/t^2)]/(2t) -> I(a)/C_0,

where N_b=Z_b/Z_0 and C_0=integral g_0>0. These are ACTUAL FULL-HAAR partition statements for the original finite112-edge72-face cap complex and31-link pin. The independent Lean harness transports the first identity to the original unpinned32-link partition via its earlier exact equality, not measure-zero conditioning. Both signs of t are included, amplitudes are fixed, and the limiting scalar I(a) remains an explicit absolutely integrable cubic Gaussian-weighted average. This is a real integration result beyond a finite Taylor coefficient or a conditional one-link surrogate.

Verification and independent evidence:
- build: PASS, 40.21305759999086 seconds.
- audit: PASS, 40.189566200017 seconds.
- checks: PASS, 25.1690998999984 seconds.
- axiom-ledger: PASS, 44.85801310001989 seconds.

The complete root build passed7039 jobs. The canonical COMPLETE safe-Foundation transitive axiom audit passed55662 declarations, allowing only propext, Classical.choice and Quot.sound. ALL47 public types were printed unabridged and reviewed:42 complete theorem proofs and5 definitions, no abbreviations/instances/private helpers. All three complete proof/definition source files were read. The COMPLETE persisted Foundation/AxiomAudit.lean run passed. No sorry/admit/new mathematical axiom/native_decide, resource increase, version/configuration/compiler/trust change, hidden mathematical assumption or weakened audit was introduced. An overly unfolded measurability attempt hit the existing default heartbeat limit; it was replaced by direct compositions of existing continuous/linear coordinates and finite maps, retaining the original limit and all domains. No resource limit was increased.

ALL26 independent Lean examples passed. They cover the real-weight hypothesis in the determinant envelope, exponential differences on a nonpositive half-line, the positive budget and actual coordinate bounds, total quotient behavior at t=0 versus the explicit nonzero domain, cutoff sign symmetry, both Gaussian/envelope integrability domains, measurable and genuinely integrable signed first density, cutoff and actual full-Haar corrections, the original unpinned partition, normalized partition, actual outside gap/weight/tail scale and exact full partition split. Conditional tests show the correction density is negative wherever C>0 and that a nonzero integral coefficient precludes an unpunctured normalized odd limit. These conditions are not an exported proof that I(a) is nonzero. The first harness run needed two TEST-only repairs (absolute-value orientation and mul_zero in a zero-denominator simplification); mathematical sources/resources were unchanged for those repairs. The original unpinned identity passed throughout.

A fixed-seed independent NumPy diagnostic evaluated all112 actual quaternion links and72 faces on4096 shifted-Gaussian importance samples arranged in512 octets of color signs. It checked the actual cubic and local Boltzmann envelopes at t=.08,.04,.02,.01. Numerical odd cutoff integrals divided by C_0 were0.019773096062241514 at.04,0.019754207071632487 at.02 and0.01974950352849341 at.01, approaching0.019747936737136904 predicted from the external exact-rational harmonic coefficient and Schur energy. Octet sample standard errors were respectively5.4779190749057966e-5,1.363383998602818e-5,3.4056444711145376e-6. All sampled points lay inside the cutoff at these scales; this is NOT a bound on true outside Haar mass. Color-sign sample averaging of the cubic agreed to floating tolerance with its harmonic evaluation. These are importance-quadrature diagnostics, not a certified integral/error rate, a Lean color-averaging theorem, a nonzero I(a) theorem, boundary derivative interchange, continuum estimate, mass gap or novelty claim. Evidence prefix: C:/Users/ramir/AppData/Local/Temp/stardust-ym-1715-*.

Source integrity authenticates1714 against exact approval02d20c378e3fb7a804b1bd4b5f62010e623fd526. Among2821 recursive Foundation/root Lean files, only these three focused modules, root imports and AxiomAudit differ. Every older mathematical source,3 pinned configurations,113 baseline originals and21 Yang-Mills originals(20 distinct hashes) remains unchanged. ResearchSources stays unmodified/uncommitted. Existing drafts/history, publication-role separation, daily reflection policy and campaign priorities are preserved.

Exact remaining bottleneck. The missing scale-uniform odd envelope, genuine signed-density integrability, actual Haar limit exchange, |t|^(-94) outside removal and normalized full-partition odd formula are NOW VERIFIED and must no longer be listed as missing hypotheses. I(a) still needs a rigorous evaluation. The strongest next route is the separate color-reflection symmetry of the EXISTING centered pinned quadratic density after1713's harmonic translation: every determinant monomial uses three distinct quaternion colors, suggesting an exact eight-sign averaging identity. Prove its actual coordinate normalization, measure-preserving changes of variables and integrable polynomial domains before replacing a cubic average by its harmonic value. The external harmonic rational31877443263/69438734552 still needs an actual Lean certificate tied to C; numerical agreement is not that proof.

The first odd partition correction along beta=1/t^2 with angles=t*a is NOT a theorem interchanging a fixed-beta third boundary derivative and the large-beta limit. A corresponding free-energy odd theorem, parameter-uniform derivative/closure estimates, fixed-beta actual third-response asymptotics and resulting thermal-bound implications remain OPEN unless separately proved. Stationary physical transfer contraction, a physically justified iteration distance, scale/volume-uniform bounds, infinite-volume/continuum existence and a positive Yang-Mills mass gap remain OPEN. This finite-cell integration checkpoint makes no completion claim and asserts no novelty for classical dominated-convergence/Laplace tools.

Exact-commit approval, new-history secret scanning, guarded PUBLIC main/research synchronization and independent post-push ref/visibility verification remain checkpoint closure gates. This pre-commit entry does not assert backup already succeeded. Visibility is controlled exclusively by the user. The indefinite research goal remains active.


## Checkpoint1716 — exact harmonic evaluation of the actual signed cubic correction and odd free energy

October29,2026. Focused Yang-Mills remains ACTIVE; no transition, completion, publication, novelty or physical mass-gap claim. This extends exact checkpoint1715 a7250190a1e8332e051a3d38e0f4b248d7592762. The primary researcher retains no manuscript/PDF or editorial duties. Original manuscripts were hash-checked only; publication directories, README and drafts were not touched.

Five focused Lean modules: FourCubeCubicCoordinates, FourCubeColorReflection, FourCubeCubicSignAverage, FourCubeCubicIntegral and FourCubeCubicFreeEnergy. The bottleneck is evaluating1715's GENUINELY integrable signed correction I(a), without assuming an unproved Gaussian covariance or treating a Taylor coefficient as an actual Haar result.

Actual coordinate normalization. The recovered imaginary quaternion of algebraElement(v) is exactly (v2/2,v0/2,v1/2); that of the existing hemisphere generator(u) is u. Inverse face slots carry minus signs from skew-Hermitian velocities. Thus1714's actual full72-face cubic C(Y,a) is exactly the determinant sum of the explicit oriented raw vectors, including the root pin and every interior/boundary slot. No coordinate factors were fitted numerically.

Exact color reflections. For s in Bool^3, reflect(s,Y) changes each quaternion color sign separately at EVERY free link. affine(s,h,Y)=h+reflect(s,Y-h) is an involutive homeomorphism preserving the actual93-dimensional product Lebesgue volume. This follows coordinatewise from measure-preserving negation and translations, not a postulated Gaussian measure. The existing centered quadratic form is a SUM of three identical-color Gram energies, so EACH separate color reflection preserves it and its density. After1713's proved harmonic translation h_a, each affine reflection about h_a preserves the actual limiting density g_a(Y). A general wrong center is not assumed to preserve this density.

Finite algebra. Every determinant monomial uses each of the three colors once. For arbitrary mean vectors and fluctuations, summing over the eight independent color signs cancels every nonconstant sign term. The exact identity

    sum_s C(affine(s,h,Y),a) = 8 C(h,a)

holds for ANY center h and every Y. This is finite polynomial algebra; it assumes neither a probability law nor stochastic independence. Let

    H3(a)=harmonicCubic(a)=C(h_a,a),
    E(a)=effectiveEnergy(a),  C0=integral g_0>0.

For the actual density f_a(Y)=-C(Y,a)g_a(Y), separate-color invariance yields sum_s f_a(affine(s,h_a,Y))=-8 H3(a)g_a(Y). Each transformed f_a is genuinely integrable by the measure-preserving map and1715's proved integrability. The eight-term sum/integral interchange and exact integral invariance therefore give

    I(a)=integral f_a = -H3(a) integral g_a
        = [-H3(a) exp(-E(a)/2)] C0.

This discharges the signed cubic-average evaluation left open at1715. No formal nonintegrable Bochner default value is used. The proof needs separate color reflections, not merely simultaneous centered sign symmetry: the independent Lean harness gives a two-atom fluctuation example with vectors (+/-e0,+/-e1,e2), simultaneous signs correlated, whose mean determinant is1 while the determinant of the means is0. The independent eight-sign sum is0 as required. Thus generic centered-law substitution is false.

ACTUAL full-Haar consequences. With b_t=movingBoundary(t,a), beta=1/t^2, original finite-cell partition Z and normalized N_b=Z_b/Z_0, through both sides of the punctured REAL neighborhood0:

    [Z_(b_t)(1/t^2)-Z_(b_-t)(1/t^2)]/(2t |t|^93)
        -> [-H3(a) exp(-E(a)/2)] C0,
    [N_(b_t)(1/t^2)-N_(b_-t)(1/t^2)]/(2t)
        -> -H3(a) exp(-E(a)/2).

The independent Lean harness transports the first formula from the pinned31-link partition to the ORIGINAL32-link Haar partition using the existing exact equality. It is not measure-zero conditioning. The outside-cutoff estimate and full-Haar identification are reused directly from1715, not replaced with a numerical truncation.

Actual free energy. normalizedPartition_positive proves positivity for ALL real t. A complete private logarithmic-slope lemma proves that if f,g>0, f->R>0 and (f-g)/(2t)->L, then (log f-log g)/(2t)->L/R. It reconstructs g->R, uses D=(f-g)/g->0 and the continuous divided slope of log(1+u) at0, handling D=0 without division assumptions. Applying it to the actual normalized partitions gives

    [-log N_(b_t)(1/t^2)+log N_(b_-t)(1/t^2)]/(2t) -> H3(a).

This is a proved logarithmic limit of the ACTUAL partition functions, not differentiation of an assumed asymptotic series. Both signs and fixed arbitrary amplitudes are retained. No fixed-beta third boundary derivative or parameter-derivative/large-beta interchange is asserted.

Verification:
- build: PASS, 28.263452299986966 seconds.
- audit: PASS, 41.39796489998116 seconds.
- checks: PASS, 31.215293000015663 seconds.
- axiom-ledger: PASS, 48.60287969998899 seconds.

Complete root build:7044 jobs. Canonical COMPLETE safe-Foundation transitive Lean.collectAxioms audit:55716 declarations, allowing only propext, Classical.choice and Quot.sound. ALL39 public types were printed unabridged and reviewed:29 theorem proofs,9 definitions and1 abbreviation. The complete five source bodies and the private log_odd_limit proof were read. The COMPLETE persisted Foundation/AxiomAudit.lean run passed. No sorry/admit/new mathematical axiom/native_decide, trust/config/compiler/version change, resource increase, hidden stochastic hypothesis or weakened verification gate was introduced. Local elaboration repairs reconciled equivalent Pi/module instances and the actual log composition point1+0 using existing default resources.

ALL22 independent Lean examples passed: raw Pauli/quaternion factors, orientation signs, actual volume preservation and affine involution, separate quadratic/density invariance, universal sign cancellation, the simultaneous-sign counterexample, transformed integrability, actual signed integrals, normalized and ORIGINAL unpinned full-Haar odd limits, positivity and actual free-energy limit. A conditional nonzero-H3 test excludes extension of that punctured odd quotient to the whole neighborhood, where its total Lean quotient has value0 at0. It does NOT prove H3 nonzero. One test-only limit-at-point proof was repaired to eq_of_tendsto_nhds before execution; no mathematical source/resource change was needed.

Independent exact rational diagnostic reconstructed32 links/72 faces and checked eight different rational amplitude triples, arbitrary fluctuations and BOTH harmonic and arbitrary centers: sum_s C(affine(s,h,Y))=8C(h), plus exact separate-color quadratic invariance about the harmonic center. Reflection about zero is explicitly WRONG for the nonzero-boundary density: at amplitudes(1,1,1), the rational raw face energy changes from2171839/579084 to1636045/193028. The candidate harmonic cubic remains31877443263/69438734552 times xyz in this independent diagnostic. That rational value and its nonvanishing are NOT yet Lean certificates.

An independent fixed-seed actual quaternion112-link72-face importance diagnostic used4096 samples in512 color-sign octets at amplitudes(.4,-.3,.5). Odd cutoff free-energy estimates at t=.04,.02,.01 were -0.027504077162262414, -0.027534177478237554, -0.027541818198842383, versus diagnostic harmonic value -0.027544375745322553. Octet delta-method sample standard errors were3.0389476703840264e-5,7.5938478089498575e-6,1.8984685486241038e-6. These are floating importance diagnostics, not rigorous quadrature error bounds, true outside-mass bounds, Lean rational evaluations or continuum estimates. Evidence prefix C:/Users/ramir/AppData/Local/Temp/stardust-ym-1716-*.

Authenticated source integrity compared1715's manifest to exact approval a7250190a1e8332e051a3d38e0f4b248d7592762. Among2826 recursive Foundation/root Lean sources, only these five new modules, root imports and persisted AxiomAudit differ. All older mathematics,3 pinned configs,113 baseline originals and21 Yang-Mills originals(20 distinct hashes) remain unchanged. ResearchSources is read-only and uncommitted; existing drafts/history and publication-role separation are preserved.

Exact remaining bottleneck. The harmonic evaluation of I(a), actual normalized odd correction and actual odd FREE-ENERGY limit are NOW VERIFIED, no longer missing. H3 is an exact explicit finite expression using the certified harmonic response; evaluating its actual rational coefficient and proving nonzero in Lean remain open. Prefer a direct checked finite harmonic-response certificate, reusing existing response data where its hypotheses really apply; do not silently project away boundary gradients in a nonlinear cubic. Nonlinear boundary gauge transformations can have second-order jets, so raw linear-cycle projection is not automatically a cubic gauge theorem. Fixed-beta third-response asymptotics, derivative-limit interchange, thermal-bound consequences, stationary physical transfer contraction, physically justified iteration distance, scale/volume-uniform bounds, infinite-volume/continuum existence and a positive four-dimensional Yang-Mills mass gap remain OPEN. No novelty is claimed for classical finite sign averaging or logarithmic calculus.

Exact-commit approval, complete new-history secret scan, guarded PUBLIC two-branch main/research synchronization and independent post-push refs/visibility checks remain closure gates. This pre-commit entry does not assert remote backup already succeeded. Only the user controls visibility. The indefinite focused research goal remains active; Bakry stays paused and the queue unchanged.


## Checkpoint1717 — kernel-certified nonzero actual harmonic cubic and full-Haar odd free energy

October29,2026. Focused Yang-Mills remains ACTIVE, Bakry PAUSED and the queue unchanged. Extends fully audited/two-ref verified checkpoint1716,80961831d2a6de6042287691e42396e5b1c31504. The previous goal turn made substantive mathematical progress and completed its guarded backup; this turn resolved its next actual finite-cell certificate bottleneck. No publication/manuscript/PDF/editorial work was performed; originals were hash-checked only.

Four focused modules: FourCubeHarmonicIntegerData, FourCubeHarmonicResponse, FourCubeHarmonicWordData and FourCubeHarmonicCubicValue. The purpose is to prove, rather than infer from the earlier rational diagnostic, that1716's actual full-Haar odd free-energy correction is NONZERO for the specified three actual boundary rays. This is a32-interior-link,112-total-link,72-face finite-cell statement. It is not a stationary physical transfer estimate or a continuum mass gap.

Direct source certificate. Existing OneSidedIntegerResponseData concerns physical CYCLE inputs. Rather than silently projecting nonlinear cubic boundary data to that domain, a direct32x3 integer witness Xnum was constructed for the THREE ACTUAL raw-quaternion boundary sources. Its denominator is579084 and its origin-direction0 pinned row is0. The80x3 boundary table has just three nonzero entries: low cap index5/color2=-1, chosen upper chord index12/color1=-1, high cap index44/color0=1. boundary_sources kernel-checks their exact equality to the existing native chosen/capHigh/capLow geometry. The table is not a new assumption about a boundary law.

The verified sparse four-link incidence action is reused to prove the actual integer equations

    A Xnum +579084 B Bnum = Rnum,   A^T Rnum=0.

The finite equalities are checked by decide +kernel, not native_decide, compiled floating computation or an external certificate oracle. The rational external solver supplies only candidate integer witnesses; all required identities are rechecked in Lean. No new resource option is present. Initially the larger quantified proposition exceeded default instance synthesis, so the boundary/source row checks were split into their finite rows and the existing sparse incidence theorem reused. Limits/trust/configuration were not raised.

Transport to the ACTUAL harmonic shift. Existing proven interior/face/boundary equivalences, real casts and orientation signs transport the integer residual and normal equations to fullMatrix and the actual boundaryMatrix. The pinned lift preserves the candidate field because its pole is0. Multiplying the full normal equation by the pinned lift transpose, using fullMatrix_lift and the VERIFIED localGram injectivity/inverse, identifies the candidate with response(eta). No gauge projection onto physical cycles is invoked. The boundaryComponent/rawSource comparison retains the exact Pauli permutation and factor2:

    boundaryComponent(1,1,1,a)=2 eta_[1,2,0](a).

Scalar2 is explicitly REAL scalar multiplication, not an unintended natural repeated-addition instance. Dividing the response by2 in the existing harmonicShift convention cancels this factor, giving

    harmonicShift(1,1,1)=chart(Xnum/579084).

This is the pre-existing actual harmonicShift, not a newly defined minimizer chosen to fit the diagnostic.

Ordered word certificate. Equality of signed quadratic incidence matrices is INSUFFICIENT to justify a cubic coefficient. The native wide source-edge embedding and its verified injectivity/row geometry are reused to prove the ordered link correspondence for all72 faces and four slots, including index reversal on flipped faces. The integer word includes the actual +,+,-,- inverse-slot signs and denominator factors for boundary sources. All individual vector components are tied to FourCubeCubicCoordinates.vectors. An exact integer determinant sum is then kernel checked:

    sum_p cubicInt(word_p)=89146927712029176.

Real casting and the cubic denominator identity, together with the actual harmonicShift identification, prove

    harmonicCubic(1,1,1)=31877443263/69438734552 >0.

The public declarations are harmonic_cubic_value and harmonic_cubic_positive. Thus the old external candidate fraction is NOW a Lean theorem for the actual finite-cell cubic. The generic arbitrary-amplitude formula c*xyz remains diagnostic unless separately proved; this checkpoint certifies the concrete amplitudes(1,1,1), which already suffices for nonvanishing.

ACTUAL full-Haar consequence. Reusing1716's proved logarithmic theorem, with N_b(beta)=Z_b(beta)/Z_0(beta) for the actual original finite-cell Haar partition and b_t=movingBoundary(t,1,1,1), actual_free_energy_nonzero_limit establishes through the two-sided punctured REAL neighborhood0:

    [-log N_(b_t)(1/t^2)+log N_(b_-t)(1/t^2)]/(2t)
        ->31877443263/69438734552.

No asymptotic series is differentiated. The positivity and exact normalization, full-Haar cutoff removal and integrable odd limit are inherited from verified1713-1716. This is not merely a Gaussian surrogate or the boundary-only cubic1. It establishes nontrivial odd response of the actual partition along this joint scaling. No fixed-beta third boundary derivative or interchange with the large-beta limit is asserted.

Verification:
- build: PASS, 28.080049199983478 seconds.
- audit: PASS, 47.22004549999838 seconds.
- checks: PASS, 27.536070400004974 seconds.
- axiom-ledger: PASS, 53.809784699988086 seconds.

Full root build:7048 jobs. Canonical COMPLETE safe-Foundation Lean.collectAxioms audit:56016 declarations, permitting only propext, Classical.choice and Quot.sound. ALL44 public types were printed unabridged and reviewed:28 theorem proofs,15 definitions and1 abbreviation; no private helpers or new instances. The complete four source bodies, including all integer witnesses and proof bodies, were read. COMPLETE persisted Foundation/AxiomAudit.lean passed. No sorry/admit/new mathematical axiom/native_decide, older-source/config/toolchain/compiler/trust change, heartbeat/recursion/instance-size increase or weakened audit occurred. One operational deviation was caught: the independent-check runner was started before the canonical audit process had exited, briefly overlapping two read-only Lean invocations. Both terminal handles were retained, both completed successfully on immutable mathematical inputs, and subsequent verification was serialized. These are checkpoint closure timings, NOT isolated benchmark evidence or a build-configuration change.

ALL20 independent Lean examples passed, with no test repair after execution: exact denominator, pinned pole, a nonzero response coordinate=1/3, all three boundary signs and a zero cross-color source, actual response/harmonic identification, actual ordered row transport and inverse signs, a quadratic-norm-versus-determinant counterexample, positivity and sharp rational bounds. In particular the harness proves0.45<H3(1,1,1)<0.46, the genuinely integrable signed correction integral I(1,1,1)<0, eventual positivity of the ACTUAL odd free-energy quotient on the punctured neighborhood, nonexistence of its unpunctured extension to the same positive limit (the total quotient at0 is0), and the corresponding actual normalized partition odd limit. Eventual assertions follow from the proved positive limit; no numerical sign inference is used.

An additional independent exact-rational script reconstructs the ORIGINAL32-link/72-face geometric normal equations without using Lean's Adata normal-equation theorem, parses all96 entries of the new witness, and checks them against the independent canonical pinned solve. Rank31, all96 normal equations, zero pin, cubic31877443263/69438734552 and numerator89146927712029176 agree exactly. Boundary-only cubic is1; changing the high-cap sign WITHOUT recomputing the harmonic response gives -82317237165/69438734552, confirming this diagnostic is sensitive to the chosen signs. That deliberately stale-response test is not a theorem about the correctly re-solved negative-amplitude process. Independent evidence prefix C:/Users/ramir/AppData/Local/Temp/stardust-ym-1717-*; the actual conclusions rest on kernel proofs, not this diagnostic.

Integrity authenticates1716's exact manifest against approval80961831d2a6de6042287691e42396e5b1c31504. Among2830 recursive Foundation/root Lean sources, only these four modules, root imports and persisted AxiomAudit differ. All older mathematics,3 pinned configurations,113 baseline originals and21 Yang-Mills originals(20 distinct hashes) are unchanged. ResearchSources remains unmodified/uncommitted. Existing drafts/history, publication-role separation, master ref and the separate publication branch are preserved.

Exact remaining bottleneck. The actual rational coefficient and its positivity at(1,1,1) are NOW VERIFIED, no longer missing. The joint beta=1/t^2, boundary=t scaling still does not identify a fixed-beta third derivative. A productive next route is to test whether parameter-uniform differentiated density envelopes and quantitative outside derivative bounds can establish that interchange, or yield a sharp obstruction. Before proving this, audit the exact fixed-beta response declarations and their hypotheses. Do not infer a generic c*xyz law, a nonlinear boundary-gauge cubic theorem, a thermal norm contradiction, stationary physical transfer contraction, physically justified iteration distance, scale/volume-uniform control, continuum/infinite-volume existence or a positive Yang-Mills mass gap from this one finite-cell value. All of those claims remain open except where separately certified. Classical exact finite linear algebra and determinant evaluation are not claimed novel.

Exact-commit approval, complete new-history secret scanning, guarded PUBLIC main/research synchronization and independent remote refs/visibility checks remain closure gates; this pre-commit ledger does not assert remote backup succeeded. Only the user controls repository visibility. The indefinite focused research goal remains active.


## Checkpoint1718 — actual thermal-window mixed response and divergent third finite difference

October29,2026. Focused Yang-Mills remains ACTIVE; Bakry PAUSED and queue unchanged. Extends exact audited/two-ref verified checkpoint1717 e26383a9112365b9c511abc157028669781eb7f4. The previous goal turn made substantive progress, closing the actual nonzero rational harmonic certificate. This turn pursues the large-coupling response bottleneck through ACTUAL finite differences, avoiding an unproved parameter-derivative interchange. Publication-role separation is retained; no manuscripts/PDFs/publication directories/editorial README work, and no original-source reading beyond hashes.

Two focused modules: FourCubeHarmonicAmplitude and FourCubeThermalMixedDifference. There is no new gauge-theory infrastructure. They reuse the actual signed cubic, pinned linear response, full-Haar odd limit and exact rational value from1713-1717.

Full amplitude law. Let a=(x,y,z), and scale_a(Y) multiply raw quaternion color0 by x, color1 by y and color2 by z. Direct native boundary formulas prove rawBoundary(a)=scale_a(rawBoundary(1,1,1)), retaining the Pauli permutation boundaryComponent(a,j)=[y,z,x]_j*boundaryComponent(1,1,1,j). Existing response is exactly real-linear under scalar multiplication. Consequently

    harmonicShift(a)=scale_a(harmonicShift(1,1,1)).

The actual full-edge velocities, including the root pin and boundary values, scale in precisely those raw colors. The four ordered face vectors retain their inverse-slot minus signs. Each determinant uses all three colors exactly once, hence

    C(scale_a Y,a)=xyz C(Y,(1,1,1)),
    harmonicCubic(x,y,z)=c xyz,
    c=31877443263/69438734552>0.

These are now actual Lean identities for ALL real amplitudes, including zero and negative amplitudes, not extrapolations from the external rational solver. No division by x,y,z or nonzero-amplitude hypothesis occurs. No nonlinear boundary-gauge projection is assumed. This closes the arbitrary-amplitude cubic law still recorded as diagnostic at1717.

ACTUAL mixed response. Write F_beta(x,y,z)=-log N_(boundaryData(x,y,z))(beta), where N is the pre-existing normalized ORIGINAL finite-cell Haar partition. For a three-variable F, define the explicit eight-corner signed sum

    C_h(F)=sum_(eps in {+1,-1}^3) eps0 eps1 eps2 F(h eps0,h eps1,h eps2),
    D_beta(h)=C_h(F_beta)/(8h^3).

cornerSum is the explicit eight terms with exactly these signs; independent polynomial checks verify the normalization and lower-degree cancellation. No derivative is used in this definition. Define the rescaled response

    T(t)=C_t(F_(1/t^2))/(8t)=t^2 D_(1/t^2)(t).

ray_neg exactly identifies reversal of t with reversal of all three boundary amplitudes; the coupling1/t^2 is even. The full corner sum pairs into FOUR actual odd differences at amplitudes(1,1,1),(1,-1,1),(1,1,-1),(1,-1,-1), weighted+,-,-,+. Each odd limit was already proved for the full Haar integral. Applying the now verified c xyz law gives, through the two-sided punctured REAL neighborhood0,

    T(t) -> c,
    t^2 D_(1/t^2)(t) -> c.

The exact algebraic scaling identity holds for ALL real t, including Lean's total quotient convention at0; the nonzero limit is correctly punctured. The independent tests explicitly refute an unpunctured extension to that same c, since T(0)=0.

Rigorous obstruction. actual_third_difference_lower proves eventually, for every sufficiently small nonzero t,

    D_(1/t^2)(t) > c/(2t^2).

actual_third_difference_diverges proves D_(1/t^2)(t)->+infinity, and no_uniform_thermal_bound proves that for EVERY finite real K it is false that |D_(1/t^2)(t)|<=K eventually. Thus the ACTUAL full-Haar centered mixed THIRD FINITE DIFFERENCE grows linearly with beta on the boundary window h=beta^(-1/2): D_beta(h)/beta->c along the proved inverse-square parameterization. The bounded rescaled T(t) must NOT be confused with the divergent unscaled D. This excludes a fixed uniform bound on this specified finite-cell response; it does not exclude mass-gap estimates or physically different normalizations.

This bypasses derivative-limit interchange for a concrete actual-response statement. It does NOT prove convergence or divergence of the mixed third DERIVATIVE at the origin. A future repeated mean-value/integral bridge would need the actual C3/domain hypotheses. Even with those hypotheses it would initially identify large derivatives at beta-dependent intermediate boundary points, not automatically the origin. No false derivative conclusion is inferred from these finite differences.

Verification:
- build: PASS, 27.692971400014358 seconds.
- audit: PASS, 40.00124529999448 seconds.
- checks: PASS, 27.05064480000874 seconds.
- axiom-ledger: PASS, 49.86123270000098 seconds.

Complete root build:7050 jobs. Canonical COMPLETE safe-Foundation Lean.collectAxioms audit:56066 declarations, allowing only propext, Classical.choice and Quot.sound. ALL30 public types were printed unabridged and reviewed:21 complete theorem proofs and9 definitions, no new private helpers/abbreviations/instances. Both complete source bodies were read. The COMPLETE persisted Foundation/AxiomAudit.lean passed. Targeted builds, full build/canonical audit and final independent checks/persisted ledger were serialized, and every terminal handle checked before the next Lean run. No sorry/admit/new mathematical axiom/native_decide, resource increase, toolchain/config/compiler/trust change or weakened audit was introduced. A recursive simp attempt rewrote the unit-amplitude base into itself; it was replaced by explicit channel-wise linear-response algebra, retaining the default recursion/heartbeat limits. A monotonicity lemma for the wrong multiplicative class was replaced by the real ordered-field cancellation theorem with t^2>=0 explicit.

ALL22 independent Lean examples passed. They verify cornerSum(xyz)=8h^3, cornerSum(x^2+yz+7)=0 and the cubic coefficient with lower-degree contamination; arbitrary-amplitude law, zero/negative/even-color signs, a nontrivial rational amplitude test, actual harmonic/velocity scaling, exact four-pair/eight-corner identity, total zero convention, actual rescaled limit, positive lower bound, divergence, no uniform absolute bound, failure of an unpunctured limit and equivalence to division by beta for t!=0. The first harness execution reported two No goals to be solved errors after already successful tactics; only the redundant trailing TEST tactics were removed, then all checks rerun. Mathematical sources and resources were unchanged for the harness repair.

An independent fixed-seed actual112-link72-face quaternion diagnostic evaluates ALL EIGHT boundary corners, with2048 shifted-Gaussian importance samples/corner grouped in256 color-sign octets. At t=.04,.02,.01 (beta625,2500,10000), T estimates were0.4596319251232911,0.4592077720520449,0.45910632259044126 versus certified c approximately0.4590729290887092. The corresponding unscaled third finite differences were287.2699532020569,1148.0194301301121,4591.063225904412. Octet delta-method sample standard errors for T were0.0006148360015830153,0.0001564518636474127,0.00003929438571345194. Coupled sign-corner data showed zero floating spread among proper-color flips. That numerical symmetry is NOT an exported actual gauge/conjugation theorem. These are cutoff importance diagnostics, not certified quadrature/tail bounds, derivative-limit interchanges or continuum estimates. Actual conclusions rest on kernel proofs and the prior full-Haar cutoff removal. Evidence prefix C:/Users/ramir/AppData/Local/Temp/stardust-ym-1718-*.

Authenticated integrity compares1717's manifest to approval e26383a9112365b9c511abc157028669781eb7f4. Among2832 recursive Foundation/root Lean files, only these two new modules, root imports and persisted AxiomAudit differ. All older mathematics,3 pinned configurations,113 baseline originals and21 Yang-Mills originals(20 distinct hashes) are unchanged. ResearchSources stays read-only/uncommitted, and existing drafts/history, master ref and publication branch remain preserved.

Exact remaining bottleneck. The generic harmonic cubic law and ACTUAL full-Haar mixed thermal finite-difference asymptotic/divergence are NOW VERIFIED and must no longer be listed as merely diagnostic or derivative-conditional. Fixed-beta boundary smoothness and domains, large-beta third DERIVATIVE asymptotics, parameter-uniform differentiated density/tail bounds and a nonlinear gauge-covariant response/transfer interpretation remain open. The saved integrated_mixed_cubic theorem differentiates the SECOND COUPLING RESPONSE at beta=0; it does not supply the required large-beta boundary-derivative interchange. A promising mathematically distinct next route is to establish actual fixed-beta C3 regularity using compact/bounded finite-Haar derivatives and then use a repeated mean-value/integral theorem on this ALREADY proved mixed finite difference. This could force large intermediate-point derivatives without presupposing derivative convergence. State those exact domains and locations, and audit/reuse existing integral-differentiation tools before adding infrastructure. Proper color-flip symmetry may give another useful exact conjugation identity, but its full actual-Haar hypotheses must be proved, not inferred from the diagnostic.

No fixed-beta third derivative-at-zero asymptotic, thermal-bound contradiction beyond the explicit finite-difference bound, stationary physical transfer estimate, physically justified iteration distance, scale/volume-uniform continuum bridge, Yang-Mills existence or mass gap is claimed. Classical linear scaling, determinant algebra and finite-difference/limit reasoning are not claimed novel. Keep the indefinite focused research goal active.

Exact-commit approval, full new-history secret scanning, guarded PUBLIC main/research synchronization and independent remote-ref/visibility checks remain closure gates. This pre-commit ledger does not assert backup already succeeded. Only the user controls visibility.


## Checkpoint1719 — actual fixed-coupling smoothness and large genuine mixed boundary derivatives

October29,2026. Focused Yang-Mills remains ACTIVE; Bakry PAUSED and research queue unchanged. Extends audited/two-ref verified checkpoint1718,5883809af41f138215580482bfa6ae64ef31dfe6. The last mathematical goal turn made substantive progress; the intervening heartbeat only checked reflection eligibility and changed no research state. The stale reflection reservation and active investigation prevented a new reflection session. No publication/manuscript/PDF/editorial work was undertaken; original manuscripts were hash-checked only.

Four focused modules: FourCubeHaarContinuousIntegral, FourCubeBoundarySmoothAction, FourCubeBoundarySmoothPartition and FourCubeMixedMeanValue. The specific bottleneck is1718's missing ACTUAL fixed-beta regularity/domain hypothesis for converting an actual mixed finite difference into a genuine mixed derivative at an intermediate boundary point. The proof does not assume a derivative-limit interchange or a continuum measure.

Actual continuous-function calculus. The existing32-interior-link Haar state space Omega=InteriorState is already compact. Observables=C(Omega,real), with its supremum norm, is a complete normed algebra. Every such observable is genuinely integrable against the EXISTING normalized interiorHaar. haarIntegral is a continuous REAL linear map on this actual space, constructed from integral additivity/scalar multiplication and the bound

    |integral f dmu| <= ||f||_infinity.

No probability measure was substituted, and no Lp representative or default-zero integral outside its domain is used. Evaluation as an algebra homomorphism proves that the Banach-algebra exponential evaluates to the pointwise REAL exponential. Analyticity of the Banach-algebra exponential supplies C-infinity smoothness, and continuous-linear Haar integration composes with it. This is a justified bounded-operator differentiation mechanism, rather than repeated unsupported formal differentiation under the integral.

Actual action-valued smoothness. traceContinuous is the REAL continuous-linear half-trace on the existing2x2 complex matrices. For every actual interior edge e, probe(e,M)(s)=traceReal(M*(s_e))/2 is a continuous-observable-valued REAL linear map in M; finite dimensionality supplies its continuity. The explicit axisMatrix is identified with the ACTUAL SU2 boundary curve using its existing exact cosine/sine formula. Boundary inverses retain the correct negative angles. Every matrix word is proved equal to the native word for the chosen boundaryData, including both inverse factors.

The fixed interior action is continuous on the actual compact Haar state space. The existing EXACT full-cell identity then constructs the observable-valued action as

    A(a)=internalAction+48-sum_(48 ribbons p) probe(ribbonInterior p,wordMatrix(a,p)).

Pointwise action_apply proves A(a)(s)=cellAction(a0,a1,a2,s), with ALL24 internal and48 ribbon faces retained. Smoothness of the finite-dimensional boundary words and continuous-linear probes proves A:real^3->C(Omega,real) is globally C-infinity IN THE SUPREMUM NORM. This is not merely pointwise smoothness of each s-section.

Actual partition/free energy domains. For EACH FIXED real beta, define the Banach-valued exponential integral of -beta*A(a). partition_integral identifies it with the genuine full32-link Haar integral. partition_eq_actual identifies it with the pre-existing partition3, and the verified exact partition3_eq_pinned transports it to the31-link pinned partition. Thus the theorem concerns the ORIGINAL actual finite-cell partition, not a newly defined surrogate. Continuous-linear integration and Banach-algebra smoothness prove the partition is globally C-infinity in all three real boundary angles. The fixed normalizer is positive; the actual normalized partition is positive for EVERY beta and a. Taking its real logarithm proves

    F_beta(a)=-log N_(boundaryData(a))(beta)

is globally C-infinity on real^3 for EVERY FIXED real beta, including0 and negative beta. The public results include actual_partition_contDiff, actual_normalized_contDiff, actual_normalized_positive and actual_freeEnergy_contDiff. No beta-uniform derivative bound or joint large-beta differentiated limit is asserted.

Repeated mean value and ACTUAL mixed derivatives. Define spatialPartial(j,F)(a)=fderiv(real,F,a)(e_j), using the actual coordinate basis. partial_contDiff proves these derivatives retain C-infinity when F is C-infinity. slice_x/y/z identify them with actual scalar derivatives along the coordinate lines. A private one-dimensional mean-value helper has its continuity and open-interval derivative assumptions DISCHARGED from HasDerivAt. The public cube_mean applies the helper THREE times, first in x, then y to the x-partial, then z to that mixed partial. It proves for any globally C-infinity F and h>0 that some point a with |a_i|<h satisfies

    partial_z partial_y partial_x F(a)=C_h(F)/(8h^3),

where C_h is1718's exact eight-corner signed sum. The generic theorem is stated for C-infinity, not advertised as a minimal C3 theorem. The ACTUAL free energy satisfies that hypothesis by the preceding proofs, so actual_cube_mean contains NO remaining hypothetical smoothness or stochastic-domain premise.

Combining it with1718's ACTUAL thermal finite-difference lower bound proves actual_large_derivatives:

    eventually as t->0 from the POSITIVE side,
    exists a in real^3 with every |a_i|<t such that
    partial_z partial_y partial_x F_(1/t^2)(a) > c/(2t^2),
    c=31877443263/69438734552>0.

The coupling is held FIXED when taking each derivative. The resulting intermediate point may depend on t; it is not asserted to be the origin or a canonical/measurable selection. These genuine derivatives are now forced to grow at least linearly in beta SOMEWHERE INSIDE SHRINKING THERMAL BOUNDARY CUBES. This closes a real derivative-location bridge beyond the earlier finite-difference statement, without interchanging differentiation and a large-beta limit. It rules out a beta-uniform bound on this specified mixed derivative throughout those cubes. It does not supply a positive physical mass gap or a stationary transfer spectrum.

Verification:
- build: PASS, 28.95627909997711 seconds.
- audit: PASS, 45.104313799995 seconds.
- checks: PASS, 31.389471699978458 seconds.
- axiom-ledger: PASS, 47.02396670001326 seconds.

Complete root build:7054 jobs. Canonical COMPLETE safe-Foundation Lean.collectAxioms audit:56173 declarations, allowing only propext, Classical.choice and Quot.sound. ALL53 public types were printed unabridged and reviewed:35 complete theorem proofs,16 definitions and2 abbreviations. All four complete source bodies and the private mean helper proof were read. COMPLETE persisted Foundation/AxiomAudit.lean passed. Every Lean target/build/audit/test runner was serialized and its terminal handle checked before the next. No sorry/admit/new mathematical axiom/native_decide, resource increase, older-source/config/compiler/trust/toolchain change or weakened verification was introduced. A default heartbeat limit in nested implicit matrix smoothness composition was resolved by explicit typed factors. C-infinity notation needed the existing ContDiff scope/import. The initially chosen identifier partial is a Lean reserved keyword; it was replaced by spatialPartial before any successful target or audit. Equivalent real-module instances in identity slice derivatives were reconciled with convert!, preserving their ordinary derivative meaning.

ALL20 independent Lean examples passed. They cover actual integrability, integral1=1, continuous-linear scalar/additive integration, pointwise Banach exponential, the actual Haar link-probe mean0, exact actual action and pinned/original partition identities, positive normalization for arbitrary beta/a, C-infinity at beta0, beta=-1 and general beta, smooth first partial and scalar derivative identity, cube-mean normalization on xyz, necessity of a positive nonempty interval, actual intermediate-point identity and thermal derivative lower bound. A final independent Lean example proves there can be no one finite K bounding |mixedDerivative(beta,a)| for all beta and a, by applying the actual cube-mean theorem to the diverging thermal finite differences. The first test run needed explicit simplification of vector entries in the polynomial normalization test before ring arithmetic; its failed log was preserved and only the TEMPORARY TEST repaired. Mathematical sources/resources were unchanged for that repair.

Independent origin-inference audit. To test a tempting INVALID conclusion, consider the explicit generic family, t!=0,

    G_t(x,y,z)=c*sin(x)*sin(y)*sin(z)*r/[t^2*(t^4+r)],
    r=sin(x)^2+sin(y)^2+sin(z)^2.

For each fixed nonzero t it is smooth, real analytic, periodic and bounded by c/t^2, since the denominator is at least t^4 and0<=r/(t^4+r)<=1. Its numerator vanishes to total order5 at the origin, so its third mixed derivative at the origin is IDENTICALLY0. Nevertheless for every fixed amplitude a, G_t(t*a)/t->c*a0*a1*a2: for nonzero a, r(t*a)/t^2->sum a_i^2>0, the rational factor tends to1, and sin(t*a_i)/t->a_i; a zero coordinate makes the expression0 directly. Consequently its normalized eight-corner thermal response also tends to c. Thus even smoothness/real analyticity, periodicity, fixed-t boundedness and the pointwise cubic amplitude law ALONE do not justify the origin conclusion. This is an explicit GENERIC counterexample, NOT an actual Haar partition and NOT a counterexample to actual Yang-Mills origin asymptotics.

The counterexample's degree5 Taylor arithmetic was independently checked with exact rational truncated polynomials at t=1,1/2,1/10,-1/3: the xyz coefficient is0 and the x^3*y*z coefficient is c/t^6. Floating thermal limits were checked at four amplitude triples and t=.04,.02,.01,.005. This counterexample has an elementary analytic justification recorded above and independent exact arithmetic, but NO standalone Lean formalization is claimed here. A preliminary SymPy script could not run because SymPy is absent; it was replaced by the self-contained exact arithmetic check without package installation or environment change. Evidence prefix C:/Users/ramir/AppData/Local/Temp/stardust-ym-1719-*.

Authenticated integrity compares1718's manifest against exact approval5883809af41f138215580482bfa6ae64ef31dfe6. Among2836 recursive Foundation/root Lean sources, only these four modules, root imports and persisted AxiomAudit differ. All older mathematics,3 pinned configs,113 baseline originals and21 Yang-Mills originals(20 distinct hashes) remain unchanged. ResearchSources stays read-only/uncommitted, and all existing drafts/history, publication-role separation, master ref and separate publication branch are preserved.

Exact remaining obligations. Actual fixed-beta global boundary C-infinity regularity, precise ordinary mixed-partial domains and existence of large actual derivatives inside shrinking thermal cubes are NOW VERIFIED; do not list them as conditional gaps. A derivative-at-the-ORIGIN asymptotic still requires actual additional uniform derivative/complex-analytic control or a structural identity that excludes the demonstrated generic boundary-layer mechanism. Do not repeat a pointwise smoothness argument as if it were such a mechanism. Before claiming that an original thermal-norm estimate is refuted, audit its EXACT normalization, derivative directions, gauge quotient and parameter/volume dependencies against this genuine but specified finite-cell derivative. Global color-conjugation identities may be reused where already proved; no pointwise sign diagnostic is a new gauge theorem.

Stationary physical transfer estimates, a physically justified iteration scale, scale/volume-uniform continuum bridges, external Yang-Mills existence and a positive four-dimensional mass gap remain OPEN. Fixed finite-cell C-infinity does not establish any of them. Classical Banach-algebra smoothness, bounded-linear integration and repeated mean value are not claimed novel. The indefinite focused mathematical goal stays active; no campaign transition or publication is authorized by this checkpoint.

Exact-commit approval, complete new-history secret scanning, guarded PUBLIC main/research synchronization and independent post-push remote refs/visibility remain closure gates. This pre-commit ledger does not assert backup already succeeded. Only the user controls repository visibility.


## Checkpoint1720 — actual full-Haar mixed-Hessian budget obstruction; six-face completion candidate

October29,2026. Focused Yang-Mills remains ACTIVE, Bakry PAUSED and queue unchanged. Extends exact audited/two-ref verified checkpoint1719,09ca1f929dccf5de648d554e1ddd140ae1bef990. The previous goal turn made substantive progress by proving actual fixed-beta C-infinity and large intermediate-point third derivatives. This checkpoint addresses the saved MIXED-HESSIAN budget directly rather than claiming it follows from a third-derivative lower bound alone. No manuscript/PDF/publication/editorial work; originals were hash-checked only.

Two Lean modules: FourCubeHessianMeanValue and FourCubeThermalHessianBudget. Define the genuine ordered mixed partial

    H_beta(x,y,z)=partial_y partial_x F_beta(x,y,z),
    F_beta=-log(actual normalized full32-link Haar partition).

Its ordinary derivative domains are supplied by1719's actual global fixed-coupling C-infinity theorem. It is not a conditional one-link integral, a pointwise action derivative or a formal Gaussian observable. The integrated cell is still the EXACT one-sided72-face geometry; this domain is retained explicitly.

Two-stage mean value. The public two_face_mean theorem stops1719's repeated mean-value argument after the x and y steps. For every globally C-infinity F and h>0, some |x|,|y|<h satisfy

    H_F(x,y,h)-H_F(x,y,-h)=C_h(F)/(4h^2),

where C_h is the exact eight-corner signed sum. The continuity, nonempty interval and derivative hypotheses are discharged, and ordered partials are identified with scalar slice derivatives. Applying it to the ACTUAL F_beta gives actual_two_face_mean:

    H_beta(x,y,h)-H_beta(x,y,-h)=2h D_beta(h).

Thus1718's full-Haar thermal response lower bound, beta=1/t^2, proves that for EVERY sufficiently small positive t there exist |x|,|y|<t with

    H_(1/t^2)(x,y,t)-H_(1/t^2)(x,y,-t)>c/t,
    c=31877443263/69438734552>0.

This is an ACTUAL full-Haar mixed-Hessian difference growing at least as c*sqrt(beta) on the thermal corridor. The two mixed Hessians have the SAME x,y. Neither x nor y is asserted to be0. The third derivative-at-origin or a derivative-limit interchange is not used.

Arbitrary reference subtraction. Let B(beta,x,y) be ANY real function, with no boundedness, continuity or beta-uniformity assumption, but independent of z. The two-face difference cancels B exactly. Triangle/order estimates prove that at one of the two faces z=+t or z=-t,

    |H_(1/t^2)(x,y,z)-B(1/t^2,x,y)|>c/(2t).

The public actual_large_deviation proves this eventually for small positive t. actual_deviation_eventually_gt strengthens it to exceed any prescribed finite real K. In particular subtracting an arbitrarily coupling-dependent quadratic/background reference independent of z cannot remove this two-face obstruction. The independent Lean harness specializes B=0 and B(beta,x,y)=H_beta(x,y,0), so it also verifies actual departure from the zero-z reference at the SAME x,y. A z-dependent reference is a DIFFERENT hypothesis; choosing that reference equal to H makes the deviation0, and is not ruled out.

Quadratic budget. For any fixed C>=0 and ANY fixed real C0, at |x|,|y|<t and z=+/-t,

    C*(1/t^2)*(x^2+y^2+t^2)+C0 <=3C+C0.

The divergent actual deviation therefore violates this bound for every sufficiently small positive t at suitable x,y and at least one face. actual_quadratic_budget_violations proves the eventual existential violations; no_eventual_quadratic_budget refutes an eventual bound simultaneously valid throughout both thermal faces. This rules out a coupling-uniform scalar remainder budget C*beta*||a||^2+C0 on this specified actual native full-Haar boundary family, even after arbitrary z-independent reference subtraction. It does NOT refute every possible mass-gap estimate, a beta-dependent C/C0, a different normalization, a restricted boundary submanifold, or a reference with essential z-dependence.

The saved1700 conditional obstruction concerned D_xD_y Fcond(beta;0,0,z) with31 links fixed. The present theorem instead integrates ALL32 links and controls a simultaneous pair of intermediate x,y values inside the thermal window. It neither silently fixes them0 nor identifies these two boundary derivatives with an unproved interior/boundary Delta_xy block in some other gauge-fixed corridor. Such coordinate/gauge/domain identifications remain obligations before applying this theorem to any literal external estimate. No original manuscript was reviewed for this checkpoint.

Verification:
- build: PASS, 30.391308599995682 seconds.
- audit: PASS, 41.0744811000186 seconds.
- checks: PASS, 26.87546380001004 seconds.
- axiom-ledger: PASS, 51.12438090000069 seconds.

Complete root build:7056 jobs. Canonical COMPLETE safe-Foundation Lean.collectAxioms audit:56203 declarations, allowing only propext, Classical.choice and Quot.sound. ALL8 public types were printed unabridged and reviewed:7 full theorem proofs and1 definition. Both complete sources and their TWO private helper proofs (mean and budget_bound) were read. The COMPLETE persisted Foundation/AxiomAudit.lean passed. All Lean targets/build/audits/tests were serialized and terminal handles checked. No sorry/admit/new mathematical axiom/native_decide, resource increase, toolchain/config/compiler/trust change or weakened gate was introduced. Initial target repairs made the curried/uncurried actual free-energy identity explicit, exposed positive-time membership for field algebra, and separated relation signs from absolute-value notation so Lean did not parse a pipeline operator. None changes the mathematical domains or hypotheses.

ALL14 independent Lean examples passed on the first execution. They test exact corner normalization for xyz and x^3*y*z, the latter's zero ordered mixed derivative at x=y=0 despite nonzero corner response, cancellation of a common reference, the essential nonempty interval, exact two-face normalization on a cubic, actual full-Haar mean-value identification and c/t difference, both raw and zero-z-reference deviations, arbitrary references/thresholds, quantified quadratic-budget failure and the C=0 special case with arbitrary C0. These checks expose why intermediate locations and the z-independent reference requirement cannot be dropped. No mathematical or test source was changed after the successful complete build/audit; the new independent research script below does not affect Lean inputs.

Independent standard-six-face investigation. A new self-contained standard-library Python script, tools/stardust_six_plaquette_probe.py, preserves reproducible exact-rational evidence outside ResearchSources and publication directories. It reads/modifies no repository/manuscript/network/Git state and prints only computed JSON. Its source was reviewed and executed successfully; it has NO temporary-helper dependency. Script SHA256: 7fab7b109ae2709100b427e012c49bfa807c32cb495b3d0bf59affedbc434b11.

It enumerates the complete nearest-neighbor4D finite Dirichlet box with vertices[-1,2]^4:256 vertices,768 links and864 elementary plaquettes. Exactly32 links inside{0,1}^4 are treated as integrated variables;736 exterior links are fixed, except the SAME three prescribed raw-quaternion boundary axes. Every integrated link belongs to SIX plaquettes. Exact rational Gaussian elimination verifies96 normal equations and finds full interior Gram rank32. The native origin gauge is lifted; its velocity is(-1/231,-16/2079,-1/231), so reusing the old31-link root pin would change this model.

The script independently reconstructs the72 positive/native active plaquettes, solves their pinned31-coordinate normal equations, and reproduces the ALREADY Lean-certified native cubic31877443263/69438734552. It then adds48 source-free negative-side active plaquettes. Every such added plaquette has exactly one integrated link and three fixed identity links. Their contribution to the Gram is exactly diagonal, with multiplicity

    n_minus(v,a)=#{j!=a : v_j=0}.

Of the remaining pure-exterior plaquettes, each nontrivial one contains at most ONE source edge; their source counts are3 for x,4 for y and3 for z. These combinatorial checks suggest the precise action identity

    S_standard(U;x,y,z)=S_native(U;x,y,z)
      +sum_e n_minus(e)*defect(U_e)
      +3(1-cos x)+4(1-cos y)+3(1-cos z).

THIS IS A CANDIDATE GEOMETRIC IDENTITY, NOT A LEAN THEOREM. Its pure-source terms would have zero mixed xy Hessian, while the48 link penalties genuinely change the integrated law and remove the origin gauge. The rational full-rank solution gives harmonic cubic1784975/2750517, approximately0.6489598137368356, and raw effective energy3467/231. It is NOT the old coefficient and is NOT yet an actual full-Haar asymptotic or a certified Lean coefficient for the standard model.

A second concrete diagnostic verifies32 DISTINCT isolation plaquettes: for an integrated edge in direction a choose transverse j=1 if a=0, otherwise j=0; use the negative plaquette when v_j=0 and the positive plaquette when v_j=1. Each chosen plaquette contains that one integrated link, and its other three edges are fixed identity links and avoid all three sources. This is a promising route to a source-independent sum-of-link-defects coercivity estimate for this DIRICHLET model. That coercivity theorem, the finite geometry and its normal/cubic certificates still require Lean proofs. No mathematical axiom is added from the Python assertions.

The frozen exterior is essential: enlarging or sampling the exterior, preserving arbitrary local gauge freedom, a physical stationary transfer operator and volume/continuum-uniform estimates are NOT supplied by this test. The evidence is an exact jet/combinatorial diagnostic and a candidate for the next direct theorem, not a proof of a standard-lattice integrated Hessian theorem, existence or mass gap. It answers the specific concern that the previous one-sided conditional had five incident faces, without silently calling the old geometry a six-plaquette lattice. Temporary evidence prefix C:/Users/ramir/AppData/Local/Temp/stardust-ym-1720-*; the reproducible script is committed with this checkpoint.

Authenticated integrity compares1719's manifest against approval09ca1f929dccf5de648d554e1ddd140ae1bef990. Among2838 recursive Foundation/root Lean sources, only these two new modules, root imports and persisted AxiomAudit differ. All older mathematics,3 pinned configs,113 baseline originals and21 Yang-Mills originals(20 distinct hashes) remain unchanged. The new research probe is separately reviewed/tested and hashed above. ResearchSources is unmodified/uncommitted; drafts/history, publication-role separation, master and the separate publication branch remain preserved.

Exact next obligation. The ACTUAL native full-Haar thermal mixed-Hessian quadratic budget obstruction, with precise moving x,y and arbitrary z-independent subtraction, is NOW VERIFIED. Do not list it as a merely conditional one-link or third-derivative inference. The most concrete next step toward the standard4D question is the minimal negative-side completion: prove the displayed geometric action decomposition and isolation coercivity using the existing actual32-link Haar state space, then build the correct unpinned96-dimensional Gaussian/cubic certificate and full-Haar limit if productive. Do NOT reuse the31-link pin or dimension93. Reuse actual bounded-linear integration/smoothness and determinant/sign machinery where their hypotheses match. First test/prove this specific standard-cell bridge rather than creating a broad gauge library.

Fixed-origin derivative asymptotics, a literal gauge-fixed corridor Delta_xy identification, stationary physical transfer estimates, physically justified iteration scales, scale/volume-uniform continuum limits, external Yang-Mills existence and a positive mass gap remain OPEN. Neither a finite Dirichlet Gram gap nor a local response obstruction decides them. No novelty is claimed for classical mean-value, triangle-bound or finite Gaussian tools. The indefinite focused research goal stays active; no campaign transition is made.

Exact-commit approval, full new-history secret scan, guarded PUBLIC main/research backup and independent remote refs/visibility checks remain closure gates; this pre-commit ledger does not assert remote backup succeeded. Only the user controls repository visibility.


## Checkpoint1721 — actual standard Dirichlet-box global coercivity and Haar tails — October29,2026

Focused Yang-Mills remains ACTIVE. This checkpoint closes the isolation-coercivity part of1720's standard-lattice bridge, rather than adding an assumed positive quadratic form to the old five-face model. No reflection/publication session, manuscript/PDF review or campaign transition occurred.

PROVED in Foundation/FourCubeDirichletBox.lean: the actual nearest-neighbor box has vertices Fin4^4 (physical coordinates[-1,2]^4), all864 admitted canonical plaquettes, the existing32 integrated Interior links inside{0,1}^4, and all other links identity except the three explicitly located exterior sources. Those source values are ARBITRARY SU(2) elements. The label lookup, interior embedding and three source labels are verified. face_steps_no_wrap proves that the totalized modular step NEVER wraps on an admitted face; this is a Dirichlet box, not a periodic torus. The ordered group word has signs++--. No root is pinned.

For each integrated edge e, isolation chooses transverse j=1 when its direction is0 and j=0 otherwise. Depending on the vertex coordinate, it chooses a negative-side or positive-side plaquette. isolation_labels verifies the exact ordered lookup: precisely one slot is the interior edge e and all other slots have label none, hence actual identity links for every source assignment. The32 witnesses are distinct by isolation_injective; isolation_word is U_e or its inverse, and their defects agree. These are kernel-checked group-valued identities, not just incidence or Gaussian-jet tests. The existing concrete32-point enumeration is reused. Four private eight-point certificate blocks respect unchanged default heartbeat/recursion settings; no trust/resource increase, native_decide or new axiom was introduced.

The substantive global theorem global_coercivity, for every32-link state s and every source assignment b, is

    sum_e (1 - halfTrace(s e)) <= S_box(b,s).

It follows by embedding the32 distinct isolation plaquettes into the ACTUAL864-face Wilson sum and using nonnegativity of every remaining Wilson defect. coordinate_bound controls every link, including the former gauge pole, with constant1. This differs from the old pinned72-face bound because the action and boundary geometry genuinely differ; it is not an improvement claim for an unchanged law.

PROVED in Foundation/FourCubeDirichletHaar.lean: the actual action is measurable and lies in[0,1728]. Zero action forces all32 integrated links to identity for arbitrary source values; at identity sources the vacuum is exactly the unique zero. The Boltzmann weight is integrable for EVERY real beta against the existing actual32-link product SU(2) Haar probability. For beta>=0 and every real epsilon, every integrated edge satisfies the source-uniform unnormalized bound

    integral_{defect(U_e)>=epsilon} exp(-beta*S_box(b,U)) dHaar(U)
      <= exp(-beta*epsilon).

No normalized concentration, coupling-uniform partition lower bound, physical stationary transfer or infinite-volume conclusion is asserted.

Verification: complete7058-job root build PASS in66.3243511s; canonical transitive audit of ALL56279 safe Foundation declarations PASS in46.7041124s, permitting only propext/Classical.choice/Quot.sound. All41 public types (22 theorems,16 definitions,3 abbreviations) and all six private proof helpers were reviewed with complete sources. The isolation_mem pretty printer reached its default recursion limit; the preserved raw fallback printed its complete universal membership type, which was independently reviewed. No printing/compiler limit was raised and no mathematical hypothesis was hidden. Twelve independent Lean checks PASS in33.3533264s; complete persisted AxiomAudit PASS in54.6197691s. The failed target/full-build/test logs are retained under the temporary1721 prefix. Failures were elaboration-only: dependent finite equality reduction, bounded certificate factoring, a duplicated local transparency annotation, update_self lemma spelling, absolute-value token spacing, pointwise real products and a test-only function equality. No failed mathematical claim was silently weakened.

Independent standard-library EXACT rational quaternion tests enumerate the864 physical faces separately from the Lean definitions: all32 integrated links have six incident faces; each single nonidentity link has action6*defect; eight noncommuting configurations (four distinct) satisfy the global inequality. Three single-source tests give TOTAL face counts6/5/6, while PURELY EXTERIOR face counts remain3/4/3 as in1720. The first independent test incorrectly used the latter counts for the whole action; it failed and was corrected, with its original script preserved. This correction changes no Lean theorem or source. The exact diagnostic is evidence, not a replacement for the Lean proof. Files: C:/Users/ramir/AppData/Local/Temp/stardust-ym-1721-independent.py/json and preserved initial-failed script; checks.lean/log, audit.lean/log and verification timings share that prefix.

Authenticated source integrity compares1720's manifest against approval d91b542a0b2d93c58caf2a5f77267c2f9eaf052f. Of2840 recursive Foundation/root Lean sources, ONLY these two new modules plus root imports and persisted AxiomAudit differ. All older mathematics, three pinned configs,113 baseline originals and21 Yang-Mills originals(20 distinct hashes) remain unchanged. The committed six-plaquette probe retains SHA256 7fab7b109ae2709100b427e012c49bfa807c32cb495b3d0bf59affedbc434b11. ResearchSources remains read-only/uncommitted; publication artifacts, historical drafts and unrelated branches are preserved.

Exact remaining standard-box obligation: prove the full action decomposition into the native72-face action, the48 negative-side diagonal defects and the separable3/4/3 exterior-source costs. Then certify the NEW32-link normal equations/cubic and the UNPINNED96-dimensional actual Haar asymptotic. The diagnostic coefficient1784975/2750517 and raw energy3467/231 remain DIAGNOSTIC, not Lean-certified full-Haar response theorems. The old31-link pin, exponent93 and coefficient31877443263/69438734552 cannot be reused for this changed law. New coercivity now supplies the specific global control needed for that finite-box tail argument; reuse existing determinant/sign, Gaussian and bounded-linear Haar calculus only with matching domains.

Stationary physical transfer estimates, physically justified iteration distances, a literal gauge-fixed corridor Hessian identification, fixed-origin response asymptotics, fluctuating exteriors, scale/volume-uniform continuum limits, external Yang-Mills existence and a positive physical mass gap remain OPEN. This is a precise finite Dirichlet-box bridge, not the four-dimensional Millennium claim; no novelty assertion is made for classical positivity or Haar integration. The indefinite focused objective remains active.

Exact-commit receipt, complete new-history secret scanning, guarded PUBLIC main/research synchronization and independent exact remote-ref/visibility checks remain closure gates. This pre-commit ledger does not claim remote backup has succeeded. Repository visibility is controlled exclusively by the user.


## Checkpoint1722 — exact48-face nonlinear negative completion and unsupported-link obstruction — October29,2026

Focused Yang-Mills remains ACTIVE. This is concrete progress on1721's standard-box action decomposition, NOT its completion or a campaign transition. Foundation/FourCubeNegativeCompletion.lean uses the ACTUAL standard Dirichlet box, existing32 integrated links and arbitrary three exterior SU(2) sources.

PROVED: pairs indexes(e,j) with j different from the edge direction and v_j=0. There are48 such pairs. lower(e,j) is the admitted canonical plaquette with that transverse coordinate lowered to physical-1. lower_labels verifies the exact ordered group-valued lookup: the only nonidentity-capable link is e, in slot2 when a<j and slot1 otherwise; the other three links are source-free identity. lower_defect therefore identifies its actual Wilson defect with defect(U_e), uniformly in arbitrary source values. lower_injective proves all48 witnesses are distinct, and negative_faces_subset embeds their image into the864 actual plaquettes. negative_faces_card=48 is verified, not inferred from a floating rank or face-count analogy.

The main nonlinear theorem negative_action_identity is EXACT for every state/source assignment:

    S_negative(b,U) = sum_e n_minus(e)*(1-halfTrace(U_e)),
    n_minus(e) = #{j != direction(e) : v_j=0}.

This proves the predicted diagonal penalty at the actual SU(2) action level, beyond the previously tested quadratic Gram correction. negative_action_le identifies it as a nonnegative subsum of the full actual Wilson action. Full geometric exhaustiveness/partition into native72, this48-face image and exterior faces still requires proof; the image definition and its membership/count do not silently certify that larger partition.

PROVED scope obstruction: pole_multiplicity=3, whereas topEdge=((0,1,1,1),0) has multiplicity0. For ANY SU(2) value U, the state spike(U), identity except at topEdge, has negativeAction=0 for EVERY source assignment b. For U!=1, negative_spike_no_control proves that this negative part cannot even bound that link defect with coefficient1. The negative completion therefore cannot replace the native contribution in the decomposition or the already verified FULL-box global coercivity theorem. All claims concern the actual nonlinear finite action; no Gaussian, probability or continuum assumptions are added.

Verification: complete7059-job root build PASS in116.6955040s. Canonical complete transitive safe-Foundation axiom audit PASS for56313 declarations in41.7048581s, only propext/Classical.choice/Quot.sound. All21 public types(13 theorems,8 definitions), the complete source and all33 private helpers were reviewed. The32 pointwise finite-label certificates plus their assembly reuse the verified existing32-point enumeration; factoring respects unchanged default heartbeat/recursion limits. There is no native_decide, new axiom, suppressed error or theorem weakening. Pretty-print recursion fallback affected lower_mem and negative_faces_subset; the complete explicitly named raw types were also printed/reviewed in the independent-check log, without raising any limits. Twelve independent Lean checks PASS in29.5505580s; complete persisted AxiomAudit PASS in47.2088071s. Earlier target/build/test failures are preserved: bounded-certificate elaboration, finite-set transparency, beta reduction in a rewrite, over-splitting numeric group-word cases, explicit concrete edge membership and a test-only pole unfolding. These are compiler/proof-elaboration repairs, not mathematical counterexamples.

Independent EXACT standard-library quaternion tests enumerate the physical box separately. The48 negative faces contain exactly one integrated edge and no source; their diagonal identity passes eight noncommuting configurations(four distinct). The independently checked multiplicity histogram is0:4,1:12,2:12,3:4. A nonidentity spike on a zero-weight link gives zero negative action. A separate nonlinear test builds24 inner and48 native ribbon group words directly, with their actual order, and confirms on eight configurations(four distinct) the COMPLETE proposed identity

    S_box = S_native72 + S_negative
      +3*defect(b0)+4*defect(b1)+3*defect(b2).

This full identity remains TESTED/OPEN in Lean; only its negative component is proved at this checkpoint. Evidence: C:/Users/ramir/AppData/Local/Temp/stardust-ym-1722-independent.py/json and stardust-ym-1722-full-decomposition-test.py/json. Neither an exact finite test nor quadratic/cubic jets replace universal native/exterior transport proofs.

Authenticated integrity compares1721's manifest against approval83ccb7627316539f59fb36fef057b4aa757929fc. Of2841 recursive Foundation/root Lean sources, only this new module, root import and persisted AxiomAudit differ. Every older mathematical source, three pinned configs,113 baseline originals and21 Yang-Mills originals(20 distinct hashes) remain unchanged. The committed six-plaquette probe retains SHA256 7fab7b109ae2709100b427e012c49bfa807c32cb495b3d0bf59affedbc434b11. ResearchSources stays read-only/uncommitted. No manuscript/PDF/public-exposition work, reflection admission, publication-branch change or research-queue modification occurred.

Next exact obligation: finish the universal native72-word transport and complete disjoint plaquette partition/exterior3/4/3 source costs, then combine with negative_action_identity. Reuse OneSidedSourceRows.row_geometry, embedFace_bijective and the existing ordered native words rather than inventing another curvature model. Only then certify the NEW32-link normal equations/cubic and UNPINNED96-dimensional actual Haar asymptotic. The diagnostic1784975/2750517 coefficient and3467/231 raw energy remain unproved full-Haar claims; do not reuse the old31-link pin, exponent93 or old coefficient. Standard-box thermal Hessian obstruction, stationary physical transfer, fluctuating exteriors, physically justified iteration scales, scale/volume-uniform limits and positive physical mass gap remain OPEN. No novelty claim or Millennium conclusion is made. The indefinite focused objective remains active.

Exact-commit approval, new-history secret scan, guarded PUBLIC main/research backup and independent exact remote-ref/visibility verification remain closure gates; this pre-commit ledger does not assert remote success. Visibility remains exclusively user-controlled.


## Checkpoint1723 — exact native72 nonlinear transport, three-source dictionary and120/744 action split — October29,2026

Focused Yang-Mills remains ACTIVE. Foundation/FourCubeNativeTransport.lean advances the actual standard-box action decomposition; it does NOT declare the exterior source-cost formula or the new full-Haar response completed. Every32-link state remains unpinned. No manuscript/PDF/public-exposition work or campaign transition occurred.

Literal theorem reuse: FourCubeMovingOddAction.fullAction_rows applies to an ARBITRARY FullEdge->SU(2) field; its statement has no chart or pin hypothesis despite other definitions in its file. Combine that exact nonlinear row sum with OneSidedSourceRows.row_geometry and OneSidedCapComplex.embedEdge_injective/embedFace_bijective. liftVertex translates physical coordinates by1 into the box representation; lift_shift proves its compatibility with actual stepping at native face bases. No second gauge model or Gaussian approximation is introduced.

PROVED: nativeFace embeds all72 native canonical plaquettes injectively into the864 admitted box faces. translated_rows transports the exact ordered edge slots, including reversal when flipped=true. In the reversed case the canonical group word is the inverse of the original word; reverse_defect uses a genuine NONCOMMUTATIVE group identity and trace-inverse invariance. It never reorders noncommuting factors by a commutative argument. native_defect proves the actual Wilson defects agree termwise. native_action_identity identifies their complete subsum with the old actual fullAction evaluated on the actual pulled field.

The pull preserves every integrated link, including the former pole. Its restriction to every boundary edge is INDEPENDENT of all32 integration variables: an old boundary edge cannot translate to a core edge, by the two verified edge-embedding injections. No finite-state enumeration or probabilistic independence assumption replaces that proof. boundary_formula explicitly identifies the three nonidentity-capable boundary entries with the SAME high cap, chosen chord and low cap as FourCubeIntegratedCubic. source_alignment verifies their exact physical locations. boundary_angles proves the original boundaryData(x,y,z) is recovered from b=![axis0(x),axis1(y)^-1,axis2(z)^-1]. Thus native_angles identifies this subsum with the ORIGINAL cellAction(x,y,z,s), rather than redefining a lookalike native law.

PROVED: the native72 faces and the verified negative48 face image are disjoint. Their retainedFaces union has120 faces, lies in the actual box, and its complement exteriorFaces has744 faces. action_partition gives the exact nonlinear identity for arbitrary source values and every interior state:

    S_box(b,s) = S_native(boundary(b),s)
      +sum_e n_minus(e)*defect(s e) + exteriorAction(b,s).

The last term is the ACTUAL sum over the744-face complement. The name exteriorFaces is a set-complement definition, not a theorem that its labels contain no integrated edge. Neither state independence nor the3/4/3 source-cost formula for this remainder is assumed. Its source-only identification is the precise remaining geometric obligation. In particular, this identity alone does NOT transfer the old native Haar cubic/Hessian obstruction to the different full-box law.

Verification: complete7060-job root build PASS in28.3847388s; canonical transitive audit of ALL56385 safe Foundation declarations PASS in46.7814683s, only propext/Classical.choice/Quot.sound. All38 public types(25 theorems,13 definitions), complete saved source and all three private helpers were reviewed. Raw fallback types were explicitly printed/reviewed for nativeFace_mem, native_faces_subset and retained_subset after the standard pretty printer reached its default recursion limit; no print/compiler limit was raised. Twelve independent Lean checks PASS in27.7342459s. Complete persisted AxiomAudit PASS in47.5848574s. Target failures/logs are retained under the temporary1723 prefix: projection inference, eager finite-set expansion, explicit finite/Nat inequalities, and dependent-if source-angle simplification. They were repaired with typed projections, local transparency control and narrowly scoped congruence; no theorem hypothesis changed, axiom was introduced, check was suppressed or resource setting increased.

Independent standard-library EXACT quaternion tests check all48 original ribbon words against their physical canonical box orientation on eight configurations(four distinct):384 nontrivial ordered-word comparisons PASS, including192 reversed-word comparisons. The script also retains the earlier exact full nonlinear decomposition tests. Initial tautological inner-word self-comparisons were removed and are not counted as independent evidence. Evidence: C:/Users/ramir/AppData/Local/Temp/stardust-ym-1723-independent.py/json; the initial redundant script is preserved separately. This evidence does not substitute for the universal Lean word/angle theorems or certify the still-open exterior formula.

Authenticated integrity compares1722's manifest with approval55d6d71d9307e2400a3a8fdb1e18219c414b107f. Of2842 recursive Foundation/root Lean sources, ONLY this new transport module, root import and persisted AxiomAudit differ. All older mathematical sources, three pinned configs,113 baseline originals and21 Yang-Mills originals(20 distinct hashes) are unchanged. The committed six-plaquette probe retains SHA256 7fab7b109ae2709100b427e012c49bfa807c32cb495b3d0bf59affedbc434b11. ResearchSources remains read-only/uncommitted; drafts, publication artifacts, unrelated branches, queue and reflection reservations remain untouched.

Exact next obligation: prove every admitted face outside retainedFaces has NO integrated edge label; prove such a face has at most one source edge; compute the three surviving counts3/4/3. Then establish exteriorAction(b,s)=3*defect(b0)+4*defect(b1)+3*defect(b2) and combine action_partition with native_angles. Do not label the remaining source formula proved merely because eight exact tests pass. Only afterward certify the changed32-link normal equations/cubic and UNPINNED96-dimensional actual Haar asymptotic. The diagnostic1784975/2750517 coefficient and3467/231 energy remain unproved full-Haar claims. Native31-link pin/exponent93 and old response coefficients do not apply to the full standard-box law.

Standard-box integrated thermal Hessian obstruction, stationary physical transfer, fluctuating exteriors, physically justified iteration distances, scale/volume-uniform continuum limits and a positive physical Yang-Mills mass gap remain OPEN. No novelty is claimed for classical group, incidence or finite-sum tools. The indefinite focused research goal stays active. Exact-commit approval, complete new-history secret scanning, guarded PUBLIC two-branch synchronization and independent exact remote-ref/visibility checks remain closure gates; this pre-commit ledger does not assert remote backup succeeded. Only the user controls visibility.


## Checkpoint1724 — COMPLETE exact standard Dirichlet action decomposition — October29,2026

Focused Yang-Mills remains ACTIVE. This checkpoint resolves the exact finite-box decomposition left OPEN at1720--1723. It does NOT resolve the changed Gaussian/full-Haar asymptotic, a stationary-transfer estimate or physical mass gap. The actual model retains all32 unpinned SU(2) integration variables, all864 admitted nearest-neighbor plaquettes and the same three arbitrary exterior source values. No research queue, publication artifact, manuscript/PDF or reflection reservation is changed.

PROVED in Foundation/FourCubeCoreIncident.lean: Core is the pure coordinate predicate for an integrated edge location. coreFaces has EXACT cardinal120, checked by Lean kernel reduction of the finite coordinate definition. The already verified native72 and negative48 images are explicitly included in coreFaces, using the old wideInterior geometry, the true edge embeddings and lower_labels. Inclusion plus independently proved equal cardinality establishes retained_eq_core; cardinality ALONE is not used as a substitute for inclusion. Thus exterior_no_core and exterior_no_interior_label prove every one of the744 complementary faces has no integrated edge label. exterior_filter identifies this complement with a pure-coordinate filter, avoiding a large circular membership certificate in the image sets.

PROVED in Foundation/FourCubeExteriorSources.lean: SourceMatch is pointwise equality of a box edge address with one of the three existing source edges; source_match_iff proves exact semantic equality, not an approximate geometric test. hits indexes(SLOT,SOURCE) pairs. A kernel-checked zero-cardinality certificate for badFaces proves that every exterior face has AT MOST ONE such pair, simultaneously excluding two different sources and a repeated occurrence of one source. Independent kernel-checked sourceMultiplicity counts are exactly3,4,3. These compact coordinate/cardinality certificates use neither native_decide nor an unverified numerical axiom. Both computable decidability instances are included in the public-type and axiom review.

word_source_sum is a universal nonlinear SU(2) theorem for every exterior face and EVERY interior/source assignment: its group word is identity, one source, or that source's inverse. The existing trace-inverse identity makes its defect equal the corresponding source defect. No commutativity of distinct source matrices is assumed. Finite sum reordering and exact integer-to-real multiplicity transport give exterior_source_identity:

    exteriorAction(b,s)=3*defect(b0)+4*defect(b1)+3*defect(b2).

This remainder is therefore genuinely independent of all32 integrated variables; it is no longer an unexplained function named exteriorAction.

The completed universal theorem full_action_identity now proves

    S_box(b,s)=S_native(boundary(b),s)
      +sum_e n_minus(e)*defect(s e)
      +3*defect(b0)+4*defect(b1)+3*defect(b2).

full_angle_identity applies the EXACT previously proved original boundary dictionary and FourCubeWilsonCubic.axis_trace, giving for b=![axis0(x),axis1(y)^-1,axis2(z)^-1]:

    S_box(b,s)=cellAction(x,y,z,s)+sum_e n_minus(e)*defect(s e)
      +3*(1-cos x)+4*(1-cos y)+3*(1-cos z).

This is an ACTUAL finite nonlinear Wilson-action identity, not only its expectation, quadratic incidence form, formal Taylor jet or a proposed manuscript correspondence. The geometric/action decomposition objective is CLOSED at this checkpoint. The source potential is separable and even under simultaneous angle reversal; the independent Lean checks verify the latter algebraic fact. Factorization of actual Haar partitions and the new96-dimensional limit remain separate obligations, not silently included in this statement.

Verification: complete7062-job root build PASS in64.8332973s. Complete canonical transitive audit PASS for56443 safe Foundation declarations in43.9617203s, only propext/Classical.choice/Quot.sound. All34 public types(24 theorems,8 definitions,TWO instances), complete saved sources and all three private proof helpers were reviewed. Named complete fallback types for native_core, negative_core and retained_core_subset were also printed/reviewed in the independent check log; no resource limit was raised. Thirteen independent Lean checks PASS in31.7860433s; complete persisted AxiomAudit PASS in49.6837161s. Target/test failures are preserved under the temporary1724 prefix: finite predicate unfolding, Fin/Nat coordinate conversion, opaque finite-set aliases, a misqualified EXISTING axis_trace theorem and eager finite-set expansion in a scratch test. The repairs change no mathematical hypothesis, toolchain, trust setting or compiler resource setting and suppress no errors. No new axiom, sorry or native_decide is introduced.

Independent EXACT standard-library rational quaternion tests reconstruct the physical grid separately:120 core-incident faces=disjoint72 native plus48 negative;744 exterior faces; zero multi-hit exterior faces; source counts3/4/3;734 source-free exterior faces. Eight noncommuting configurations(four distinct) satisfy the complete proposed decomposition. These are independent tests, while the universal completed action identities above are Lean proofs. Evidence: C:/Users/ramir/AppData/Local/Temp/stardust-ym-1724-independent.py/json and checks.lean/log, audit.lean/log, timings and preserved failed logs under the same1724 prefix.

Authenticated integrity compares1723's manifest with approvalc42479afd089635a8d1a2413171a851366faa8b2. Of2844 recursive Foundation/root Lean sources, only these TWO new modules, root imports and persisted AxiomAudit differ. Every older mathematical source, three pinned configs,113 baseline originals and21 Yang-Mills originals(20 distinct hashes) remain unchanged. The committed six-plaquette probe retains SHA256 7fab7b109ae2709100b427e012c49bfa807c32cb495b3d0bf59affedbc434b11. ResearchSources remains read-only/uncommitted, with historical drafts and the separate publication branch preserved.

Next exact bottleneck: use this completed reduction to connect the ACTUAL32-link Haar partition to the native action with the NEW diagonal penalty and separable source scalar. Prove the correct32-link Gram positivity/normal equations, harmonic cubic and UNPINNED96-dimensional full-Haar asymptotic using existing Gaussian, quaternion-word, sign/determinant and bounded-linear integration tools. The diagnostic coefficient1784975/2750517 and raw energy3467/231 remain DIAGNOSTIC/OPEN as full-Haar statements. The new positive penalty changes the law, covariance and harmonic mean: neither the old31-link pin/exponent93 nor coefficient31877443263/69438734552 may be transferred. Positivity or pointwise action domination does not by itself order mixed free-energy Hessians. Retain the proved negative-only unsupported-link counterexample.

This finite Dirichlet conditional freezes the exterior; it does not supply a fluctuating-exterior law, stationary physical transfer obstruction, physically justified iteration scale, volume/scale-uniform continuum construction or positive physical Yang-Mills mass gap. Those remain OPEN. No novelty is claimed for classical coordinate, group or finite-sum tools. The indefinite focused goal stays active. Exact-commit approval, full new-history secret scan, guarded PUBLIC two-branch backup and independent exact remote-ref/visibility checks remain closure gates; this pre-commit ledger does not assert remote success. Visibility is exclusively user-controlled.


## Checkpoint1725 — actual completed Haar law, pre-scalar coercivity and positive FULL32 Gram — October29,2026

Focused Yang-Mills remains ACTIVE. Build on1724's completed exact864-face action decomposition, rather than returning to a surrogate or claiming the new Haar limit already exists. All32 interior links remain genuine SU(2) variables. The only role of the old distinguished pole in the Gram proof is its coordinate address; no state is pinned and no gauge-orthogonality hypothesis is imposed. No campaign, manuscript/PDF, publication artifact, reflection reservation or source original is changed.

PROVED in Foundation/FourCubeCompletedHaar.lean: completedAction is the native72-face action with the exact negative-side diagonal penalty, BEFORE the744-face source scalar. Every one of the32 distinct isolation plaquettes belongs to retainedFaces, by its actual interior label, the verified Core predicate and retained_eq_core. The positive-sum argument on this120-face set proves completed_coercivity:

    sum_e defect(U_e) <= completedAction(b,U),

UNIFORMLY in all three arbitrary source values. completedAction is measurable and lies in[0,240]. This is stronger control than merely coercivity of S_box after adding the source scalar. It is a concrete input for the unpinned moving-boundary Haar domination problem, not yet a96-dimensional dominated-convergence theorem.

The standard and completed weights/partitions are defined on the EXISTING actual32-link product SU(2) Haar probability, not a new abstract measure. Both Boltzmann weights are genuinely integrable for EVERY real beta. Both partitions are strictly positive. The exact identity is

    Z_standard(beta,b)=exp(-beta*sourceCost(b))*Z_completed(beta,b),
    sourceCost(b)=3*defect(b0)+4*defect(b1)+3*defect(b2).

normalized_density proves actual normalized Haar densities coincide pointwise after removal of this scalar. observable_identification states an explicit weighted-integrability domain for arbitrary observables f: integrability of f*completedWeight implies integrability of f*standardWeight AND equality of their normalized integrals. Thus this is a genuine finite conditional-law/observable reduction, not an accidental equality of totalized divergent Bochner integrals. It identifies the standard law with the native-plus-DIAGONAL law, NEVER with the old native72 law alone.

For unscaled free energy F=-log Z, free_energy_split is F_standard=beta*sourceCost+F_completed. sourceCost_reversal proves the original three-angle source cost is even under simultaneous sign reversal. odd_free_energy consequently proves EXACT equality of standard and completed odd free-energy differences, for every real fixed beta and every triple of angles, with NO derivative/limit interchange. It may later be applied at beta=1/t^2. The diagonal penalty still changes the harmonic mean and covariance; the old31-link coefficient is not restored by scalar cancellation.

PROVED in Foundation/FourCubeCompletedGram.lean: define the NEW32-by32 real matrix

    Gamma = OneSidedPhysicalProjection.fullGram + diagonal(n_minus).

The verified fullGram_eq_gram and native gram_energy give the exact quadratic identity f^T Gamma f = realEnergy(extend f)+sum_e n_minus(e)*f_e^2. Nonnegativity of the two terms and the coefficient n_minus(pole)=3 show that a zero-energy field has zero pole value. The existing native kernel_classification then forces the ENTIRE32-field to vanish. Its zero pole value is DERIVED from zero energy, not assumed as a pin. quadratic_positive, gram_hermitian and gram_posDef prove strict positive definiteness on the FULL32-coordinate space. This is a completed INCIDENCE Gram theorem; the actual unpinned quaternion-chart second-variation/96-dimensional Haar limit still needs its own verification.

Verification: complete7064-job root build PASS in43.5754232s; canonical complete transitive safe-Foundation axiom audit PASS for56516 declarations in43.5110214s, only propext/Classical.choice/Quot.sound. All44 public types(30 theorems,14 definitions) and both complete saved sources were reviewed; there are no private proof helpers. The complete named isolation_retained type was also printed/reviewed in the independent log after the standard pretty-printer fallback, without raising any limits. Fifteen independent Lean checks PASS in27.1779758s, including normalized mass1, the genuinely admissible constant-observable expectation2 and positivity on the formerly null native gauge vector. Complete persisted AxiomAudit PASS in47.2840679s. The only target repairs were token spacing before interiorHaar and qualification of the existing pointwise Matrix.mulVec_diagonal lemma; their failed logs remain. No new axiom, sorry, native_decide, suppressed error, toolchain/resource change or weakened statement was introduced.

Independent EXACT rational quaternion/incidence tests rebuild the physical box separately. Eight nonlinear configurations(four distinct) satisfy the stronger completed coercivity and upper bound240. The full32 rational Gram has32 strictly positive exact LDL pivots; all diagonal entries are6; the old native gauge energy is0 and its completed energy is12. A useful STRONGER DIAGNOSTIC identity holds entrywise in this reconstruction:

    Gamma = inner-face Gram +3*I.

This sharper formula is NOT YET a Lean theorem and is not a volume-uniform claim. It suggests a clean scalar fiber-count/Hodge route for the next proof: upper-ribbon and negative-side transverse multiplicities sum to3. The current formal theorem is full32 strict positivity, not an asserted sharp eigenvalue bound. Evidence: C:/Users/ramir/AppData/Local/Temp/stardust-ym-1725-independent.py/json, checks.lean/log, audit.lean/log, timings and preserved target logs.

Authenticated integrity compares1724's manifest with approvalf274a28755edf83b99ab8f9371b7862cbdd2cb7e. Of2846 recursive Foundation/root Lean sources, only these TWO new modules, root imports and persisted AxiomAudit differ. Every older mathematical source, three pinned configs,113 baseline originals and21 Yang-Mills originals(20 distinct hashes) remain unchanged. The committed six-plaquette probe retains SHA256 7fab7b109ae2709100b427e012c49bfa807c32cb495b3d0bf59affedbc434b11. ResearchSources is read-only/uncommitted; historical drafts, the publication branch and preserved master remain untouched.

Exact next obligation: connect the changed full32 incidence Gram to the actual UNPINNED quaternion chart; certify the new source normal equations/harmonic cubic and the96-dimensional full-Haar limit. Investigate the diagnostic inner-Gram+3I structure when it directly simplifies that problem. The new candidate1784975/2750517 cubic and3467/231 raw energy remain DIAGNOSTIC/OPEN as full-Haar assertions. Reuse generic finite-Gaussian, quaternion odd-word, sign/determinant and bounded-linear Haar integration tools with matching domains. Source-scalar cancellation and positive Gram alone do not prove cubic asymptotics, fixed-origin derivatives or mixed-Hessian ordering. Do not reuse the old31-coordinate pin, exponent93 or coefficient31877443263/69438734552.

The source-uniform coercivity and positive Gram proved here concern this finite frozen-exterior Dirichlet cell; they are not established uniformly for larger blocks or fluctuating exteriors. Gauge-invariant stationary physical transfer estimates, physically justified iteration scales, scale/volume-uniform continuum limits and a positive physical mass gap remain OPEN. Distinguish sampler relaxation, local quadratic control and quantum mass gap. No novelty is asserted for classical group, Gram, scalar-factor or Bochner tools. The indefinite focused objective stays active. Exact-commit approval, new-history secret scanning, guarded PUBLIC two-branch synchronization and independent exact remote-ref/visibility checks remain closure gates; this pre-commit ledger does not assert remote success. Repository visibility remains exclusively user-controlled.


## Checkpoint1726 — exact thin-cell transverse mass3 and a genuine larger-box obstruction — October29,2026

Focused Yang-Mills remains ACTIVE. This checkpoint both strengthens1725's finite-cell control AND tests the specific proposed extension toward actual larger four-dimensional lattices. It does not change the campaign or conclude a quantum mass-gap theorem. Original manuscripts, publication artifacts, reflection reservations and all earlier mathematical obstructions remain preserved.

PROVED in Foundation/FourCubeTransverseMass.lean: upperFiberEquiv identifies the actual48 upper ribbons with their edge/transverse-direction fibers. For EVERY integrated edge, the positive transverse multiplicity plus the exact negative-side multiplicity equals3. transverse_sum proves the corresponding weighted identity for EVERY real function h, including signed h; no positivity assumption is smuggled into the fiber count. Applying it to link defects proves the exact NONLINEAR vacuum identity

    completedAction(identity sources,s)=internalAction(s)+3*sum_e defect(s e).

At identity sources the exterior scalar is zero, so this is also the actual864-face standard-box vacuum action. The identity is uniform over ALL32 unpinned SU(2) links, beyond a formal quadratic expansion.

Applying the same fiber identity to h(e)=f(e)^2 gives quadratic_mass and gram_lower_three:

    Q_completed(f)=innerCurlEnergy(f)+3*sum_e f(e)^2,
    f^T Gamma f >=3*sum_e f(e)^2.

This formally resolves the quantitative quadratic content of the previous diagnostic inner-Gram+3I structure. The exported statements are the exact quadratic identity and bound; no separate literal matrix-equality declaration is claimed. The nonlinear mass3 identity is a VACUUM/identity-source result, not an asserted source-uniform3 bound for arbitrary moving sources. The source-uniform1 coercivity of1725 remains valid. This coefficient comes from three transverse frozen-boundary plaquettes per link; it is not identified as a physical quantum mass.

PROVED in Foundation/LargerDirichletGaugeObstruction.lean: construct actual oriented unit links on the integer4D lattice. The larger integrated core has vertices{0,1,2}^4 and EXACTLY216 links; the containing box has vertices[-1,3]^4 and all2400 canonical unit plaquettes. The finite index maps are proved injective and their counts are kernel-checked. core_edges_iff proves that the integrated finite set is exactly the stated coordinate domain, so frozen-exterior conditions are not replaced by an informal address claim.

For ANY SU(2) element U, let g(v)=U only at the genuinely interior vertex(1,1,1,1), and g(v)=1 elsewhere. The actual links are g(v)*g(v+e_a)^-1. flat proves every unit plaquette word is identity by noncommutative group cancellation and commuting coordinate shifts. frozen_exterior proves EVERY link outside the216-link core remains identity, globally, not merely outside an arbitrarily selected action subset. center_link is U on a specific integrated link. Hence, for every U!=1, core_energy_positive and action_zero give

    sum_core defect(link_U)>0,
    WilsonAction(link_U,ALL2400 box plaquettes)=0.

no_link_coercivity rigorously rules out c*sum_core defect<=WilsonAction for EVERY positive c on this actual larger unpinned Dirichlet core. exists_flat_nontrivial supplies an explicit nonempty SU(2) witness via axis0(pi), with frozen exterior, full zero action and positive core link energy. The flatness theorem holds for ALL unit plaquettes and the zero-action theorem for ANY finite plaquette collection; the conclusion does not arise by omitting inconvenient faces.

Mathematical implication and limit: the thin-cell raw-link coercivity cannot be extended unchanged even to this single larger box without treating interior gauge freedom. The32-link cell has no genuinely interior gauge vertex, whereas the216-link core does. This precisely rules out one naive volume-extension route from the thin-cell mass3. It is NOT a no-go theorem for gauge-invariant observables, a legitimate gauge-fixed estimate, Markov-sampler Poincare/relaxation, a physical stationary transfer operator or the Yang-Mills mass gap. Raw Wilson potential energy is not a kinetic Dirichlet form; zero potential on a gauge orbit does not by itself prove a spectral gap vanishes. Pure-gauge flatness is classical and no novelty is claimed for it.

Verification: complete7066-job root build PASS in31.7093037s; canonical complete transitive audit PASS for56597 safe Foundation declarations in40.2161441s, only propext/Classical.choice/Quot.sound. All42 public types(21 theorems,17 definitions,4 abbreviations), both complete saved sources and the single private predecessor-core helper were reviewed unabridged. Fifteen independent Lean checks PASS in28.9022973s, including actual standard vacuum action, both finite counts, frozen-exterior/central-link/flatness conditions, no-coercivity at c=3, explicit witness existence and the thin native-gauge lower bound12. Complete persisted AxiomAudit PASS in49.2537338s. Target failures were finite-set/equivalence elaboration and coordinate-product substitution issues; repaired with explicit predicates/projections and local transparency, without changing statements or compiler/trust/resource settings. Failed target logs remain under the1726 prefix. No axiom, sorry, native_decide or error suppression was added.

Independent EXACT rational quaternion tests separately reconstruct both physical grids. Eight thin-cell nonlinear configurations(four distinct) satisfy S_vac=innerAction+3*sum defects, and an explicitly signed scalar h satisfies the transverse identity. Four larger-box gauge witnesses(q_x,q_y,q_x*q_y,-1) have2400 identity plaquette words, zero Wilson action,1784 frozen exterior box links and exactly8 nonidentity integrated links. Their core energies are16/5,16/5,128/25,16. These exact tests support the universal Lean counterexample, not a replacement for it. Evidence: C:/Users/ramir/AppData/Local/Temp/stardust-ym-1726-independent.py/json, checks.lean/log, audit.lean/log, timing files and preserved failed target logs.

Authenticated integrity compares1725's manifest with approval53419070968e0228d32750d06a0915a24fc9053d. Of2848 recursive Foundation/root Lean sources, only these TWO new modules, root imports and persisted AxiomAudit differ. Every older mathematical source, three pinned configs,113 baseline originals and21 Yang-Mills originals(20 distinct hashes) remain unchanged. The committed six-plaquette probe retains SHA256 7fab7b109ae2709100b427e012c49bfa807c32cb495b3d0bf59affedbc434b11. ResearchSources remains read-only/uncommitted, and the independent publication branch/preserved master are not altered.

Next exact obligation remains the new full32 source normal equations/harmonic cubic and actual UNPINNED96-dimensional quaternion-Haar limit. The stronger quadratic control can simplify that specific finite-cell problem. Do NOT infer a volume-uniform physical estimate from it; the new larger-core gauge obstruction must survive every subsequent proposal. Any larger-volume extension must explicitly justify gauge-invariant/physical domains or legitimate gauge treatment, rather than importing external existence or mass-gap axioms. The candidate1784975/2750517 cubic remains DIAGNOSTIC as a full-Haar assertion. Scalar removal leaves the harmonic mean/cubic unchanged but shifts the raw Schur energy: the full-box diagnostic3467/231 includes the pure-source quadratic constant10 at unit amplitudes; the corresponding completed diagnostic is1157/231. Neither Gaussian-energy limit value is asserted Lean-proved here. The old31-link pin,93 exponent and31877443263/69438734552 coefficient remain inapplicable to the changed32-link law.

Stationary physical transfer estimates, physically justified iteration distance, fluctuating-exterior and continuum/volume-uniform constructions, and a positive physical mass gap remain OPEN. This specific failed raw-link extension is resolved by an explicit counterexample; it is not a campaign stopping claim or a blanket impossibility theorem. The indefinite focused goal remains active. Exact-commit approval, new-history secret scan, guarded PUBLIC two-branch synchronization and independent exact remote-ref/visibility checks remain closure gates; this pre-commit ledger does not assert remote success. Visibility is controlled exclusively by the user.

## Checkpoint1727 — unique actual completed full32 source response — October29,2026

Focused Yang-Mills remains ACTIVE. Checkpoint1726, 9ef6110e8c13acbcfb9636d86daf635419bcb17b, is now closed: the guarded sync succeeded and independent GitHub GETs at2026-10-29T13:45:44-04:00 verified BOTH authorized main/research refs at that exact commit, visibility PUBLIC/private=false. The separately advancing publication branch and preserved master were not modified. Its larger-core gauge obstruction remains a constraint on every proposed physical extension; Bakry remains paused and no queue or reflection state changes.

PROVED in Foundation/FourCubeCompletedIntegerData.lean: a new exact integer witness with denominator2079 for the completed full32 source problem. Xnum has32 rows and3 source components; Rnum has72 native residual rows; Mnum is identified with the actual negative transverse multiplicity. residual_sparse/residual_equations certify the actual ordered row incidence, using the existing independently identified boundary sources. normal_sparse/normal_equations certify ALL96 equations

    sum_p A[p,i]*R[p,j]+M[i]*X[i,j]=0.

The diagonal term is essential; these are not the former pinned/native normal equations. The certificates use kernel-checked decide, with sparse-row transport to full sums, and no altered resource/compiler/trust settings.

PROVED in Foundation/FourCubeCompletedResponse.lean: transport the integer witness via the existing bijections and sign identities to the ACTUAL geometric fullMatrix and boundaryMatrix. eta is the actual three-source boundary field inherited from the previously verified source identification. residual_eq and full_normal identify both the native residual and its completed diagonal correction. With Gamma=fullMatrix^T*fullMatrix+diag(multiplicity), forcing=-fullMatrix^T*boundaryMatrix*eta, gram_normal establishes

    Gamma*candidate_j=forcing_j.

gram_injective follows from the verified strict positive definiteness; unique_response identifies EVERY full32 solution with this explicit witness. No zero coordinate is assumed. origin_response proves the origin's three raw component values are (-1/231,-16/2079,-1/231). An independent Lean test shows any field pinned to zero there cannot solve even source0's equation. Thus reusing the old31-variable pin would be a concrete mathematical error for the completed law, rather than a harmless gauge convention.

Verification: complete7068-job root build PASS in26.3124070s; canonical COMPLETE transitive safe-Foundation audit PASS for56768 declarations in47.3950325s, only propext/Classical.choice/Quot.sound. All25 public types(15 theorems,9 definitions,1 abbreviation), both complete saved sources and every finite witness were reviewed unabridged; there are no private helpers. Twelve independent Lean checks PASS in44.0713859s, including all three source equations, exact origin values, impossibility of a zero-pinned solution, uniqueness and the quantitative Gram lower bound. Complete persisted AxiomAudit PASS in48.8479209s. The sole failed response target needed explicit unfolding of the natural/integer/real weight cast; its log is preserved. No axiom, sorry, native_decide, suppressed error, enlarged limit or changed hypothesis was introduced.

Independent EXACT rational testing reconstructs the full physical864-face box and its32-link source system directly, without importing the diagnostic probe or Lean incidence tables. It verifies all96 equations against the saved witness, rejects the zero-pinned origin, and checks four separate rational link perturbations increase raw quadratic energy by exactly6/49. The raw energy3467/231 and completed energy1157/231 remain independently tested diagnostics, not newly exported Lean energy-limit theorems. Evidence: C:/Users/ramir/AppData/Local/Temp/stardust-ym-1727-independent.py/json, checks.lean/log, audit.lean/log, timing files and preserved target logs.

Authenticated source integrity compares1726's manifest to its exact approval. Of2850 recursive Foundation/root Lean sources, ONLY these two new modules, root imports and persisted AxiomAudit differ. All earlier mathematical sources, three pinned configuration files,113 baseline originals and21 Yang-Mills originals(20 distinct hashes) remain unchanged. The committed six-plaquette probe remains SHA256 7fab7b109ae2709100b427e012c49bfa807c32cb495b3d0bf59affedbc434b11. ResearchSources stays read-only/uncommitted. Publication artifacts, historical drafts and reflection reservations remain untouched.

Next exact obligation: use this now-verified UNPINNED response to certify the new harmonic cubic, and prove the actual96-dimensional quaternion-Haar scaling and odd free-energy limit. The candidate1784975/2750517 remains OPEN as a full-Haar coefficient. The current theorem concerns the completed quadratic source equations; it does not establish a quaternion-chart second variation or stochastic asymptotic by itself. Reuse generic quaternion odd-word and per-link Haar/chart tools, not the old31-coordinate lift or exponent93. The existing per-link chart defect bound and completed source-uniform coercivity suggest a direct full32 cutoff domination route; that route is not proved in this checkpoint.

No volume-uniform coercivity follows:1726's actual larger216-link flat-gauge counterexample survives. Gauge-invariant stationary transfer estimates, physically justified iteration distance, legitimate gauge treatment, fluctuating exteriors, continuum/infinite-volume bounds and a physical Yang-Mills mass gap remain OPEN. Distinguish classical linear algebra, the exact finite-cell response verified here, diagnostic coefficients and unresolved physical bridges. No novelty or campaign-completion claim is made. Exact-commit approval, secret scanning, guarded PUBLIC two-branch sync and independent remote-ref/visibility checks remain closure gates; this pre-commit ledger does not claim a backup not yet observed. Visibility is exclusively user-controlled.

## Checkpoint1728 — actual unpinned32 chart cubic and source-uniform cutoff domination — October29,2026

Focused Yang-Mills remains ACTIVE. Checkpoint1727, 650df2ca3faa1a4f35f21f29dc3bcfc2a2be0bd4, is closed: guarded sync succeeded and independent GitHub GETs at2026-10-29T13:53:10-04:00 verified BOTH authorized main/research refs at that exact commit with PUBLIC visibility/private=false. The independently advancing publication branch and preserved master were not modified. Bakry stays paused; no campaign, publication or reflection duties are changed.

PROVED in Foundation/FourCubeFullChartOdd.lean: Coordinates is the full32-link field Interior->Triple, with NO pole pin or Free-coordinate lift. state(Y,t) is the ACTUAL per-link Haar hemisphere chart at t*Y. The external sources are the original moving axes. links_zero, links_hasDerivAt and links_parity verify the required actual matrix jets and reversal. Generic factors/slopes, the already verified arbitrary-field fullAction_rows, and SU2QuaternionOddWord.matrix_word_odd_limit yield native_odd_limit for EVERY full32 field Y and all three source amplitudes.

diagonal_even proves the negative-side completion is EXACTLY EVEN under t reversal. completed_native, standard_completed, completed_odd_identity and standard_odd_identity identify the actual completed120-face and standard864-face action differences with the native72-face odd action. The exterior scalar sourceCost is also exactly even; no asymptotic approximation is used to remove either scalar. completed_odd_limit and standard_odd_limit therefore apply to the actual new full32 law's chart paths, not the former pinned31-link law.

PROVED in Foundation/FourCubeCompletedCubic.lean: field uses the UNIQUE completed source response certified1727 on ALL32 links. word is the ACTUAL ordered four-factor velocity, transported with the verified row/address/flip dictionary. Its integer cubic total is5831513325 and denominator2079. Kernel-checked finite arithmetic, exact determinant scaling and the geometric dictionary prove

    cubicCoefficient(field,1,1,1)=1784975/2750517>0.

standard_action_odd_limit and completed_action_odd_limit prove, along this specific verified source-response chart ray,

    (S_standard(t)-S_standard(-t))/(2*t^3) ->1784975/2750517,
    (S_completed(t)-S_completed(-t))/(2*t^3) ->1784975/2750517.

These are genuine POINTWISE nonlinear SU(2) ACTION limits. They do NOT yet assert a Haar-integrated free-energy coefficient, that the chart quadratic is the certified incidence quadratic, or that a pointwise limit commutes with integration. The candidate coefficient is now a proved response-ray action coefficient; its full-Haar interpretation remains OPEN. The old31-coordinate/93-dimensional law and coefficient31877443263/69438734552 are not substituted anywhere.

PROVED in Foundation/FourCubeFullChartDomination.lean: mass(Y)=sum_e(chartRate(Y_e)-1)=sum_e |Y_e|^2 is nonnegative and scales quadratically. On the explicit per-link cutoff chartRate(Y_e)<=2, local_completed_lower proves mass(Y)/4<=completedAction(b,state(Y,1)) for EVERY source b. For beta>=0, beta*t^2=1 and chartRate(t*Y_e)<=2, scaled_completed_lower and completed_weight_bound give

    mass(Y)/4<=beta*completedAction(b,state(Y,t)),
    completedWeight(beta,b,state(Y,t))<=exp(-mass(Y)/4).

This source-uniform cutoff estimate uses the actual32-link completed coercivity and the verified per-link chart defect bound. It does not use the old pinned bound1/372, and is not a volume-uniform estimate. It is POINTWISE UNNORMALIZED domination on the cutoff, not the entire integration argument or a normalized concentration theorem. Product Haar transport, Jacobian/scaling, measurable cutoff treatment, off-cutoff tails, positive limiting normalization and domination of the odd quotient are separate obligations.

Verification: complete7071-job root build PASS in27.0727342s; canonical COMPLETE transitive safe-Foundation audit PASS for56830 declarations in44.3978151s, only propext/Classical.choice/Quot.sound. All44 public types(31 theorems,12 definitions,1 abbreviation) and all THREE complete saved sources were reviewed unabridged; there are no private helpers or pretty-printer fallbacks. Fourteen independent Lean checks PASS in44.6739959s, including the actual standard864-action expression, completed limit, exact coefficient/positive sign, unpinned origin, parity and genuine admissible cutoff cases. Complete persisted AxiomAudit PASS in51.0805149s. Target failures involved chart-derivative projection, explicit angle unfolding, ambiguous reused rowSign, mass-sum parenthesization and scalar associativity/finite-type transparency. They were repaired with explicit definitions and local opacity; the failed logs remain. No changed axiom, sorry, native_decide, raised proof limit, suppressed error, altered configuration or weakened hypothesis was introduced.

Independent80-digit Decimal testing reconstructs all864 physical plaquettes directly, using the exact32 response values, quaternion multiplication and independently evaluated sine/cosine chart sources. The odd quotients at t=0.1,0.01,0.001 are approximately0.6463197012,0.6489333651,0.6489595492, approaching the proved0.6489598137; final error is2.64491313e-7. The same three cases satisfy the explicit cutoff and scaled completed lower bound. These are numerical diagnostics, not interval certificates or replacements for the universal Lean limits/bounds. No numerical dependency was installed; the standard-library Decimal implementation was used after mpmath was unavailable. Evidence: C:/Users/ramir/AppData/Local/Temp/stardust-ym-1728-independent.py/json, checks.lean/log, audit.lean/log, timing files and preserved failed target logs.

Authenticated integrity compares1727's manifest with its exact commit approval. Of2853 recursive Foundation/root Lean sources, ONLY these three new modules, root imports and persisted AxiomAudit differ. All earlier mathematical sources, three pinned configuration files,113 baseline originals and21 Yang-Mills originals(20 distinct hashes) are unchanged. The committed six-plaquette probe retains SHA256 7fab7b109ae2709100b427e012c49bfa807c32cb495b3d0bf59affedbc434b11. ResearchSources stays read-only/uncommitted; publication artifacts, historical drafts, reflection reservations and preserved master remain untouched.

Next exact obligation: actual full32 quaternion-chart second variation and96-dimensional Haar Gaussian scaling, then justify the odd-quotient integral and identify its Gaussian cubic expectation. The existing per-link coordinateLaw/chart_map_coordinateLaw are reusable; the old productField/Free-specific31-index transport is not directly the new law. Reuse the per-link theorem and finite product measure machinery with Interior. The new cutoff bound is available, but the true96-dimensional scaling and tail normalization still need proof. Even with a proved integrated cubic, stationary physical transfer estimates, physically justified iteration distances and continuum/infinite-volume scale control remain separate OPEN bridges. Checkpoint1726's actual larger216-link pure-gauge obstruction still forbids naive raw-link volume coercivity. No novelty, physical mass gap or campaign completion is asserted. Exact-commit approval, secret scan, guarded PUBLIC two-branch sync and independent remote-ref/visibility checks remain closure gates; this pre-commit ledger does not claim unobserved remote success. Visibility remains exclusively user-controlled.

## Checkpoint1729 — actual full32 Haar observable transport and96-dimensional cutoff integral — October29,2026

Focused Yang-Mills remains ACTIVE. Checkpoint1728, 3569701b384834bd08b518f205cc0d89f6a9d767, is closed: guarded sync succeeded and independent GitHub GETs at2026-10-29T14:05:28-04:00 verified BOTH authorized main/research refs at that exact commit, PUBLIC visibility/private=false. Publication history advances independently; preserved master, Bakry pause, campaign priorities and reflection reservations remain unchanged.

PROVED in Foundation/FourCubeFullHaarCoordinates.lean: build the actual Interior-indexed product of the EXISTING one-link coordinateLaw, with all32 SU(2) links retained. chartField and coordinateField are actual measurable maps. joint_restriction, coordinateField_map and chartField_map identify this product measure EXACTLY with the existing full32 interiorHaar restricted to the joint positive hemisphere. lintegral_joint_chart and lintegral_joint_density give the corresponding nonnegative observable identities. productCoordinateLaw_density identifies the actual96-coordinate Lebesgue density as the32-fold product of the already verified one-link chartDensity. The one-link coordinateLaw/chart maps, positivity, integrability and coordinate-law rectangle integrals are REUSED, not reintroduced as new foundations.

field_finrank proves Module.finrank(R,Interior->Triple)=96. integral_rescale establishes the correct absolute Jacobian |t|^96 for nonzero t. This is the unpinned32-link law; no old31-link product measure,93 exponent or gauge pin is imported as an identification. The finite product rectangle helper is proved on the actual full index set and is included in the transitive audit.

PROVED in Foundation/FourCubeFullHaarCutoff.lean: integrable_joint_iff is an exact real-observable domain equivalence between IntegrableOn(f,jointHemisphere,interiorHaar) and integrability of productDensity(Y)*f(chartField(Y)). observable_transport returns BOTH that genuine integrability and the actual real integral identity, assuming f measurable and integrable on the joint hemisphere. Thus this is not merely a totalized equality for possibly divergent Bochner integrals.

physicalCutoff explicitly requires positive half trace and chartRate(coordinates(U_e))<=2 for EVERY one of32 links. Its measurability, inclusion in the actual joint hemisphere, and exact chart preimage coordinateCutoff are proved. cutoff_observable_transport requires measurability and integrability of f ON THIS CUTOFF, and returns integrability of the coordinate-cutoff density and the actual cutoff integral equality. No global integrability assumption on arbitrary f is silently substituted for the stated domain.

For arbitrary sources b and EVERY real coupling beta, density is the actual cutoff completed Boltzmann density times the actual32-link Jacobian. density_integrable follows from the proved finite full-Haar Boltzmann integrability and the exact transport theorem. scaledDensity(b,beta,t) remains genuinely integrable for EVERY nonzero scale t, including negative scales and negative beta. localPartition_rescale proves the exact ACTUAL full-Haar cutoff partition identity

    localPartition(b,beta)=|t|^96*integral_R96 scaledDensity(b,beta,t).

This rescaling is exact, not an asymptotic claim. The underlying product density is positive and continuous, bounded by its value at zero, and

    productDensity(0)=(1/(2*pi^2))^32,
    productDensity(t*Y) -> (1/(2*pi^2))^32 as t->0.

For beta>=0 and beta*t^2=1, scaledDensity_nonneg, scaledDensity_bound and gaussian_majorant_integrable prove a SINGLE genuinely integrable Lebesgue majorant on ALL96 coordinates:

    0<=scaledDensity(b,beta,t,Y)<=productDensity(0)*exp(-sum_e |Y_e|^2/4).

The indicator supplies zero off the rescaled cutoff. This upgrades1728's pointwise cutoff weight control to an actual rescaled, integrable Haar-coordinate density. It does not by itself prove convergence of that density: the actual full32 chart quadratic limit is still required. Nor does it yet bound the divided odd Boltzmann correction or control the Haar integral outside physicalCutoff after normalization.

Verification: final complete7073-job root build PASS in57.2538597s; canonical COMPLETE transitive safe-Foundation audit PASS for56886 declarations in46.3718506s, only propext/Classical.choice/Quot.sound. All43 public types(32 theorems,10 definitions,1 finite-measure instance), both complete saved sources and the single private rectangle-integral helper were reviewed unabridged, with no pretty-printer fallback. Thirteen independent Lean checks PASS in42.9111584s, including finrank96!=93, the exact zero Jacobian, a nonconstant actual link-trace observable with a verified integrability bound, negative coupling/negative scale, actual rescaled cutoff normalization and an integrable Gaussian envelope. Complete persisted AxiomAudit PASS in50.0120807s. Earlier target failures were an incorrectly qualified measurable half trace, explicit indicator elaboration and a cardinality simp choice; repaired without altering domains or compiler/resource/trust settings. A duplicated one-link lemma was removed in favor of direct reuse, and complete build/audit gates reran on the final sources; previous passing logs/timings remain under before-reuse. No new axiom, sorry, native_decide, suppressed error, enlarged limit or changed configuration was introduced.

Independent standard-library testing integrates the one-link radial SU(2) chart density numerically and tensors32 factors. The computed chartRate<=2 mass is0.0908450569081047, matching1/4-1/(2*pi), and its32-fold product is about4.6306466422e-34. At scales0.5,1,2,-2, the96-dimensional rescaling ratios are1 to the tested precision; replacing96 by93 produces8 at0.5 and1/8 at+/-2. Exact rational evaluation separately checks positive Jacobian ratios bounded by1 and exact t-reversal at the new verified response field. These are quadrature/rational diagnostics, NOT an asserted new Lean theorem evaluating cutoff Haar mass or a substitute for the universal measure identities. Evidence: C:/Users/ramir/AppData/Local/Temp/stardust-ym-1729-independent.py/json, checks.lean/log, audit.lean/log, timing files and preserved failed target logs.

Authenticated source integrity compares1728's manifest to its exact commit approval. Of2855 recursive Foundation/root Lean sources, ONLY these two new full32 Haar modules, root imports and persisted AxiomAudit differ. All earlier mathematical sources, three pinned configuration files,113 baseline originals and21 Yang-Mills originals(20 distinct hashes) remain unchanged. The six-plaquette probe retains SHA256 7fab7b109ae2709100b427e012c49bfa807c32cb495b3d0bf59affedbc434b11. ResearchSources stays read-only/uncommitted. No publication artifact, manuscript, PDF, editorial README, reflection reservation or preserved master is modified.

Next exact obligation: prove the actual unpinned32 quaternion-chart quadratic action limit, connect it with the completed Gram and the verified source response, and apply dominated convergence using the now-PROVED actual coordinate transport,96 scaling and common majorant. Then prove positive Gaussian normalization and off-cutoff Haar tail estimates, control the divided odd quotient and identify its actual Gaussian cubic expectation using verified color-sign algebra. The number1784975/2750517 remains proved as the response-ray POINTWISE action coefficient, not yet as a Haar-integrated free-energy coefficient. The full96-dimensional Haar asymptotic is NOT declared complete merely because its exact coordinate formula and domination are established.

Physical stationary transfer estimates, justified iteration distance, volume/continuum uniformity and a physical Yang-Mills mass gap remain separate OPEN bridges. The larger216-link pure-gauge obstruction continues to forbid naive raw-link volume coercivity. These finite product/measure/Haar tools are classical; no novelty or campaign completion is asserted. Exact-commit approval, secret scan, guarded PUBLIC two-branch sync and independent remote-ref/visibility checks remain closure gates; this pre-commit ledger does not claim remote success before it is observed. Visibility is exclusively user-controlled.

## Checkpoint1730 — actual unpinned32 quadratic limit and unrestricted completed-Haar leading asymptotic — October29,2026

Focused Yang-Mills remains ACTIVE. Checkpoint1729, 17ac6b1e8b73b64971dcd76b54a5dcf680e38e54, is closed: guarded sync succeeded and independent GitHub GETs at2026-10-29T14:21:30-04:00 verified BOTH authorized main/research refs at that exact commit, PUBLIC visibility/private=false. The independently advancing publication branch and preserved master were not modified. No queue, role, Bakry-pause or reflection-accounting change occurs.

PROVED in Foundation/FourCubeFullChartQuadratic.lean: use the actual full32 hemisphere-chart links and original moving external axes, NOT the old31-variable pin. pauliVelocity retains the exact per-link SU2HemisphereJets.frame, including factors2 and coordinate permutation. The generic SU2FourCurveJetTransfer.trace_component_jets yields actual four-link smoothness and zero/first/second jets for EVERY native face. face_actual and native_face_sum identify these scalar trace actions with the existing actual ordered SU(2) Wilson words. Taylor's little-o remainder yields the punctured native quadratic action limit.

chart_defect identifies each actual hemisphere-link defect with1-weight. Its zero/first/second jets give defect(t*Y)/t^2 -> sizeSq(Y)/2. The exact negative-side multiplicities then yield diagonal_quadratic_limit. Summing both parts proves, for EVERY full32 field Y and fixed three source amplitudes x,y,z,

    completedRay(Y,x,y,z,t)/t^2 -> completedQuadratic(Y,x,y,z)/2.

completedQuadratic is EXPLICIT: the sum of all72 native signed Pauli-vector row norms squared divided by4, plus sum_e negativeMultiplicity(e)*rawSizeSq(Y_e). It is the actual new path's quadratic coefficient, not an assumed old Hessian. completed_boltzmann_limit follows. Every divided limit uses nhdsWithin0 of the punctured line; no invalid unpunctured totalized0/0 limit is asserted. Three short private helpers establish the needed actual scalar weight/curve smoothness and Taylor quotient; they do not assume any new stochastic or Yang-Mills axiom.

PROVED in Foundation/FourCubeFullHaarGaussianLimit.lean: thermalDensity is the1729 ACTUAL96-dimensional rescaled cutoff-Haar density with beta=1/t^2 and b(t)=angles(t*x,t*y,t*z). The limiting density is

    G_xyz(Y)=J0*exp(-completedQuadratic(Y,x,y,z)/2),
    J0=(1/(2*pi^2))^32.

Its continuity, positivity, integrability and common integrable Gaussian majorant are proved. eventually_cutoff, the actual quadratic Boltzmann limit and verified Jacobian convergence give thermalDensity_tendsto. Dominated convergence proves the ACTUAL integral limit, not just probe convergence. gaussian_integral_positive proves0<R_xyz=integral G_xyz<infinity BEFORE any normalization. actual_cutoff_partition_limit gives

    localPartition(b(t),1/t^2)/|t|^96 ->R_xyz.

Bounded measurable coordinate tests with an explicit finite bound M have both unnormalized and normalized cutoff-density integral convergence. These results concern the stated actual finite Haar-coordinate densities. No separate Mathlib IsGaussian instance or already-identified mean/covariance matrix is claimed: recognition of the explicit quadratic density in terms of the certified Gamma/source response remains a precise next bridge.

PROVED in Foundation/FourCubeFullHaarAsymptotic.lean: outside_energy shows ANY configuration outside the full32 physicalCutoff has completedAction(b,U)>=1/4 for EVERY source b. This follows from source-uniform completed coercivity and the verified per-link small-defect chart-rate lemma. outside_bound integrates the ACTUAL full32 Haar law and gives, for beta>=0,

    0<=outsidePartition(b,beta)<=exp(-beta/4).

The probability-Haar bound applies to the whole complement, without an unproved union normalization. The exact partition split and an audited exponential-versus-power limit prove outsidePartition(b(t),1/t^2)/|t|^96 ->0. Hence full_partition_limit establishes the genuine UNRESTRICTED32-link completed-Haar leading asymptotic

    Z_completed(1/t^2,b(t))/|t|^96 ->R_xyz>0.

normalized_outside_limit is deduced ONLY AFTER this positive full normalization: outsidePartition/Z_completed ->0. No unnormalized tail estimate is mistaken for normalized concentration. These statements concern the completed action with its exact source-scalar removal. The original864-face standard normalized law is already identified with this law by1725; its UNNORMALIZED standard partition also contains the known source scalar and is not asserted to have the SAME leading coefficient R_xyz here.

Verification: complete7076-job root build PASS in31.4438512s; canonical COMPLETE transitive safe-Foundation audit PASS for56960 declarations in43.7618753s, only propext/Classical.choice/Quot.sound. All44 public types(33 theorems,11 definitions), all THREE complete saved sources and FOUR private proof helpers were reviewed unabridged; no pretty-printer fallback occurred. Thirteen independent Lean checks PASS in41.7537048s, including a raw unit-link defect coefficient1/2, actual full partition syntax, limiting integral positivity, concrete outside-cutoff axis(pi) configuration, normalized constant-observable convergence and actual normalized tail decay. Complete persisted AxiomAudit PASS in52.0919532s. Preserved target failures were explicit weight/angle namespaces, smooth constant subtraction, finite-sum unfolding, real exponential continuity, zero-Jacobian constant identification, natural-versus-real powers and explicit function-division cancellation. Repairs changed no hypotheses or proof limits. No axiom, sorry, native_decide, error suppression, toolchain/configuration change or raised resource limit was introduced.

Independent exact rational jets and80-digit Decimal paths reconstruct all864 physical plaquettes without importing Lean incidence tables. Three full32 fields are tested: the certified response, zero, and an unpinned origin spike. Their EXACT diagnostic completed quadratic values are1157/231,7,13, and exact cubic values1784975/2750517,1,1. Symmetrized actual action quotients and odd quotients at t=0.01,0.001 converge to the respective half-quadratic/cubic values; final quadratic errors are about1.10e-7,1.04e-6,3.29e-6. Two separate exact source-free root-link witnesses have real parts3/5 and-1 and actual full864-face completed actions12/5 and12, both outside cutoff and above the1/4 barrier. Numerical log-barrier checks show why the polynomial96 normalization must be retained before an exponentially small tail bound becomes useful. These are independent tests, not claimed uniform error bounds or Lean evaluation of the new Schur energy. Evidence: C:/Users/ramir/AppData/Local/Temp/stardust-ym-1730-independent.py/json, checks.lean/log, audit.lean/log, timing files and all preserved failed target logs.

Authenticated integrity compares1729's manifest with its exact commit approval. Of2858 recursive Foundation/root Lean sources, ONLY these three new actual quadratic/Gaussian/asymptotic modules, root imports and persisted AxiomAudit differ. All earlier mathematical sources, three pinned configuration files,113 baseline originals and21 Yang-Mills originals(20 distinct hashes) remain unchanged. The six-plaquette probe retains SHA256 7fab7b109ae2709100b427e012c49bfa807c32cb495b3d0bf59affedbc434b11. ResearchSources remains read-only/uncommitted; no manuscript, PDF, editorial README, publication artifact, preserved master or reflection reservation is modified.

Next exact bottleneck: identify the actual Pauli-row completedQuadratic with the raw full32 Gamma/source quadratic, and show its mean is the verified unpinned candidate. Then dominate the DIVIDED ODD Boltzmann correction in the96-dimensional chart, identify its Gaussian cubic expectation using the existing algebraic color-sign averaging, and control the off-cutoff first-order quotient. The source-uniform exponential tail bound is now available for that last step, but leading-order convergence alone does not prove the first-order signed integral. The number1784975/2750517 is still only a PROVED POINTWISE response-ray cubic coefficient; its actual Haar-integrated odd free-energy value remains OPEN. No fixed-origin mixed derivative or integrated covariance ordering follows merely from this leading asymptotic.

The full96-dimensional LEADING completed-Haar partition asymptotic is now proved; the cubic/derivative objectives are NOT declared complete. Gauge-invariant stationary physical transfer estimates, physically justified iteration distance, larger/fluctuating blocks, volume/continuum uniformity and a physical Yang-Mills mass gap remain separate OPEN bridges. The larger216-link pure-gauge obstruction remains intact and forbids naive raw-link volume coercivity. No novelty or campaign-completion claim is made for these classical finite-dimensional jet/Laplace tools. Exact-commit approval, secret scanning, guarded PUBLIC two-branch backup and independent exact remote-ref/visibility checks remain closure gates; this pre-commit ledger does not assert remote success before observing it. Visibility remains exclusively user-controlled.

## Checkpoint1731 — actual full32 Hessian center and exact color-sign cubic cancellation — October29,2026

Focused Yang-Mills remains ACTIVE. Checkpoint1730, eaafeb3729a84f2c3a3e42df5a3122b5dc93b623, is closed: guarded sync succeeded and independent GitHub GETs at2026-10-29T14:41:37-04:00 verified BOTH authorized main/research refs at that exact commit, PUBLIC visibility/private=false. Publication history advances independently. Preserved master, Bakry pause, campaign priorities, source originals and reflection reservations remain unchanged.

PROVED in Foundation/FourCubeCompletedSquare.lean: work on ALL32 scalar interior coordinates with actual fullMatrix A, actual boundaryMatrix B and the verified negative-side diagonal penalty. energy(f,eta)=dot(Af+B eta,Af+B eta)+penalty(f). The real incidence/matrix bridge, exact cross pairing and symmetric completed Gram give energy_expansion. For ANY m satisfying Gamma*m+coupling(eta)=0, completed_square proves

    energy(f,eta)=energy(m,eta)+quadratic(f-m).

Strict positivity of the completed quadratic gives unique_minimizer and energy_minimal. candidate_normal directly reuses1727's certified full32 source response. The native residual alone is NOT assumed orthogonal: its cross term cancels the diagonal penalty's cross term. An independent Lean test proves the concrete unit-source value (A^T*rval_0)(pole)=1/77, hence nonzero; this test is recorded in1731-checks.lean/log rather than claimed as an additional exported declaration. It explains exactly why importing the old native/pinned residual-orthogonality proof unchanged would fail.

PROVED in Foundation/FourCubeFullQuadraticCenter.lean: scalar_incidence and residual_color reuse d1_split, actual row_formula and the existing full/boundary matrix maps. frame_row, frame_length and pauli_raw verify the actual Pauli-to-raw conversion, including lengthSq(frame(u))/4=sizeSq(u). Thus face_raw/native_colors/diagonal_colors identify the ACTUAL1730 chart quadratic, with no factor/permutation assumption, as

    completedQuadratic(Y,x,y,z)=sum_a energy(Y_a,rawBoundary_a(x,y,z)).

The existing raw_boundary_scale is reused. center(x,y,z) is amplitude_a*candidate_a on EACH of32 links; center_normal proves its correct full Gram equations for EVERY real source amplitude, including negative/zero amplitudes. centered_energy and fluctuation_zero_iff give

    completedQuadratic(Y,x,y,z)=completedQuadratic(center,x,y,z)+fluctuation(Y-center),
    fluctuation>=0, fluctuation=0 iff the entire96-coordinate field is0.

unique_center proves the actual quadratic has exactly this minimizer. center_unit identifies it with1728's already verified unpinned cubic witness. In particular the origin raw coordinate is-1/231 for unit source0, not an assumed zero pin; a separate check gives-2/231 at source amplitudes(2,-1,3). This closes1730's exact actual-Hessian/Gram/center bridge. A literal Mathlib IsGaussian object or an unbounded first-moment integral theorem is not additionally asserted here.

PROVED in Foundation/FourCubeFullColorSymmetry.lean: construct raw-color sign reflections on the actual Interior32->Triple space. The per-coordinate measure-preserving negation theorem and finite product measure theorem prove96-dimensional Lebesgue preservation; the affine maps about any center are involutive homeomorphisms and volume preserving. fluctuation_reflect plus the verified centered-energy identity show actual completedQuadratic invariance under these affine maps about center(x,y,z). Consequently gaussianDensity_affine preserves the ACTUAL limiting density from1730. This is a Lebesgue/limiting-density symmetry; no invariance of the finite-t Haar Boltzmann density, gauge transformation or physical transfer operator is assumed.

rawVelocity_affine and vectors_affine connect these full32 maps to the actual ordered plaquette velocity vectors. Reusing the EXISTING generic determinant cubic_sign_sum, actual_cubic_sign_sum and weighted_cubic_sign_sum prove EXACT POINTWISE identities

    sum_s cubic(affine_s(h,Y))=8*cubic(h),
    sum_s cubic(affine_s(center,Y))*G(affine_s(center,Y))=8*cubic(center)*G(Y).

The integral_affine equality is supplied by the actual measure-preserving homeomorphism. It does NOT certify integrability of an arbitrary unbounded cubic observable; that domain obligation remains explicit. No finite sign sum is mistaken for a completed stochastic or integral reconstruction theorem.

unit_center_cubic and reuse of the existing generic amplitude/determinant scaling prove center_cubic_amplitudes for EVERY real x,y,z:

    cubicCoefficient(center(x,y,z),x,y,z)=(1784975/2750517)*x*y*z.

This now concerns the PROVED center of the ACTUAL new quadratic, rather than a merely diagnostic response ray. It remains an algebraic/pointwise coefficient, not yet a theorem that the actual full-Haar odd free energy has this value. Polynomial/cubic integrability and first-order signed limit exchange must be established before integrating the weighted sign identity.

Verification: complete7079-job root build PASS in27.1410954s; canonical COMPLETE transitive safe-Foundation audit PASS for57033 declarations in45.0480204s, only propext/Classical.choice/Quot.sound. All58 public types(47 theorems,11 definitions), all THREE complete saved sources and the single private quadratic-negation helper were reviewed unabridged, with no pretty-printer fallback. Thirteen independent Lean checks PASS in43.7468322s, including the actual raw-color energy bridge, exact completed square, unique center, nonzero origin, negative/zero amplitudes, full96 measure preservation, actual density/cubic sign identities and the NONZERO native residual1/77. Complete persisted AxiomAudit PASS in49.6624008s. Target failures were collisions with topological residual/Set.center, an explicit color-function equality, missing generic cubic namespace and an uninstantiated rewrite that recursively rematched unit amplitudes. They were repaired by qualification and instantiated rewriting, not enlarged recursion/heartbeat limits. Failed logs remain. No axiom, sorry, native_decide, suppressed error, changed compiler/trust/resource setting or weakened hypothesis was introduced.

Independent exact Fraction tests reconstruct all864 physical plaquettes, including all130 active core/source faces and explicitly zero inactive contributions. Six completed-square cases combine three amplitude triples(1,1,1),(2,-1,3),(0,2,-3) with a dense rational perturbation and an unpinned origin spike. All48 raw-color affine reflections preserve the exact completed quadratic and their cubic average equals the center cubic. The independent center energies1157/231,2798/99,15349/693 remain diagnostic exact-rational evaluations, not newly claimed Lean Schur-value declarations. Center cubics are1784975/2750517,-3569950/916839,0, agreeing with the UNIVERSAL amplitude theorem. Evidence: C:/Users/ramir/AppData/Local/Temp/stardust-ym-1731-independent.py/json, checks.lean/log, audit.lean/log, timing files and preserved failed target logs.

Authenticated integrity compares1730's manifest with its exact commit approval. Of2861 recursive Foundation/root Lean sources, ONLY these three new full32 square/center/color modules, root imports and persisted AxiomAudit differ. Every earlier mathematical source, three pinned configuration files,113 baseline originals and21 Yang-Mills originals(20 distinct hashes) remain unchanged. The six-plaquette probe retains SHA256 7fab7b109ae2709100b427e012c49bfa807c32cb495b3d0bf59affedbc434b11. ResearchSources remains read-only/uncommitted; no manuscript, PDF, editorial README, publication artifact, preserved master or reflection reservation is modified.

Next substantive target: bound the DIVIDED ODD Boltzmann correction and prove its genuine96-dimensional integral limit, then integrate the now-PROVED weighted color-sign identity on its verified domain. A potentially simpler route is available: source-uniform completed coercivity bounds BOTH reversed cutoff paths by the SAME exp(-mass/4), unlike the previous native/pinned source-dependent exponential loss. Combining the generic quaternion odd-word identity and per-link scaled imaginary-coordinate bounds SHOULD yield a cubic-polynomial times Gaussian envelope, approximately1728*J0*budget(Y,x,y,z)^3*exp(-mass/4). This envelope estimate and its use for the signed limit are PROPOSED/UNVERIFIED here, not a result of the current checkpoint. Reuse the old polynomial-versus-exponential absorption argument with the new actual domain, rather than rebuilding Gaussian foundations.

Also prove the first-order off-cutoff quotient negligible using1730's uniform exponential barrier; zeroth-order normalized tail decay alone is insufficient for a cubic free-energy coefficient. Full-Haar odd free-energy value1784975/2750517*xyz, fixed-origin mixed derivatives and integrated covariance/ordering remain OPEN. The full96-dimensional LEADING completed-Haar asymptotic remains verified1730. Gauge-invariant stationary physical transfer, justified iteration distances, volume/continuum uniformity and a physical Yang-Mills mass gap remain separate OPEN bridges. Preserve the actual larger216-link pure-gauge obstruction and every earlier failed-route qualification. No novelty or campaign-completion claim is made for classical completed-square/reflection tools. Exact-commit approval, new-history secret scan, guarded PUBLIC two-branch sync and independent exact remote-ref/visibility checks remain closure gates; this pre-commit ledger does not claim unobserved remote success. Visibility is exclusively user-controlled.


## Checkpoint1732 — actual full32 signed odd cutoff-Haar integral and exact cubic value

October29,2026; focused Yang-Mills remains ACTIVE. Previous checkpoint1731,81f6fed05222b440c591c338766ecd9ebf894bce, closed both authorized remote refs and independently confirmed PUBLIC at15:00:57EDT. This checkpoint follows its exact full96 quadratic-center/color-symmetry bridge. It does not revert to the pinned31-link surrogate.

PROVED in Foundation/FourCubeFullOddEnvelope.lean: mass_squares identifies mass(Y) with all96 raw coordinate squares. With budget=1+mass(Y)+|x|+|y|+|z|, the generic one-link imaginary-coordinate bounds and quaternion ordered-word odd identity yield actual_odd_bound/completed_odd_bound <=1728*budget^3. Only generic per-link/word tools are reused; no pinned coordinate norm, center or residual-orthogonality assumption is imported. cutoff_neg verifies that the two reversed paths share exactly the same cutoff. scaled_exponent_bound uses source-UNIFORM completed coercivity to bound BOTH exponents by -mass/4. Thus completed_boltzmann_odd_bound proves

    |[exp(-C(t)/t^2)-exp(-C(-t)/t^2)]/(2t)|
      <=1728*budget(Y,x,y,z)^3*exp(-mass(Y)/4).

The exponent contains no source-dependent loss. The polynomial budget and its integrability constant DO still depend on the amplitudes; no globally amplitude-independent integral norm is claimed. wider_gaussian_integrable follows by scaling the existing full96 Gaussian majorant, and cubic_weight_integrable absorbs the cubic budget using exp(budget/8). No new Gaussian foundation is introduced.

PROVED in Foundation/FourCubeFullOddIntegral.lean: completed_boltzmann_odd_limit combines the actual completed quadratic and cubic limits through the existing dslope-of-exp argument. oddDensity is the DIFFERENCE OF ACTUAL full32 thermal densities divided by2t. Its exact common-cutoff formula includes the real stereographic Jacobian. oddDensity_bound supplies the genuine integrable envelope1728*J0*budget^3*exp(-mass/4) for every nonzero t and every full32 coordinate field. firstDensity=-cubicCoefficient*gaussianDensity is measurable and genuinely integrable. Dominated convergence proves oddDensity_integral_tendsto and scaled_density_integral_odd_limit on the punctured two-sided real filter. This is an actual signed integral limit, not just a pointwise formal expansion or a finite sign sum.

Only AFTER this integrability proof, the actual full96 measure-preserving affine color reflections justify finite-sum/integral interchange. firstDensity_integral_value proves for ALL real x,y,z

    integral firstDensity(x,y,z) = -(1784975/2750517)*x*y*z*R(x,y,z),
    R=integral actual gaussianDensity >0.

normalized_firstDensity_integral divides by the already-PROVED strictly positive R. actual_cutoff_partition_odd_value connects the result to the actual restricted Haar partition:

    [Z_cutoff(t;x,y,z)-Z_cutoff(-t;x,y,z)]/(2*t*|t|^96)
      -> -(1784975/2750517)*x*y*z*R.

Its96 exponent and32 integrated links, including the formerly pinned origin, are explicit. Boundary angles move with t and inverse temperature is1/t^2. This does NOT assert a fixed-temperature origin mixed derivative. It is not yet the unrestricted full-Haar odd free-energy theorem.

Independent80-digit Decimal tests reconstruct all864 physical plaquettes and actual stereographic/axis quaternion products, subtract the even pure-source cost, and retain the actual product Jacobian. Nine tests combine completed response, zero field and a nonzero unpinned-origin spike with t=0.01,0.001,0.0001. Signed density quotients agree under t reversal, satisfy the proved envelope numerically, and approach -cubic*exp(-quadratic/2). All final errors are<1e-7 and improve by>1000 relative to the first scale. For the response, the observed error is7.8243991488834258e-10 at0.0001. These are independent finite tests, NOT proof of uniform convergence or integral identities; those are supplied by Lean. Evidence: C:/Users/ramir/AppData/Local/Temp/stardust-ym-1732-independent.py/json/log.

Verification: full7081-job root build PASS in27.7960685s; canonical COMPLETE transitive safe-Foundation audit PASS for57090 declarations in43.4015676s, only propext/Classical.choice/Quot.sound. All35 new public types(31 theorems,4 definitions), both complete saved proof sources, and their local helper arguments were reviewed unabridged. No new private declarations. Nine independent Lean checks verify the96-dimensional domain, genuine integrability, zero-source cancellation, negative amplitude value3569950/916839, sign reversal and the actual cutoff partition type. Independent Lean checks PASS in39.4883451s; complete persisted AxiomAudit PASS in51.3103006s. No axiom, sorry, native_decide, changed heartbeat/recursion/trust/toolchain/resource setting or suppressed error. Local target repairs concerned namespaces, explicit quotient normalization, unfolding thermalDensity at an integral rewrite, and a redundant tactic; they are not mathematical obstructions.

Authenticated integrity compares1731's manifest with its exact commit approval. Of2863 recursive Foundation/root Lean sources ONLY these two new full32 modules, root imports and persisted AxiomAudit differ. All earlier sources, three pinned configuration files,113 baseline originals and21 Yang-Mills originals(20 distinct hashes) remain unchanged. The committed probe SHA256 remains7fab7b109ae2709100b427e012c49bfa807c32cb495b3d0bf59affedbc434b11. ResearchSources is read-only/uncommitted. No manuscript/PDF, publication artifact, editorial README, master, queue or reflection reservation was modified.

Next substantive obligation: prove the FIRST-ORDER off-cutoff remainder negligible, requiring the stronger barrier exp(-1/(4t^2))/|t|^97->0, then combine with this actual cutoff signed integral and the positive full leading partition limit. The existing zeroth-order tail limit does not itself discharge the divided odd quotient. A logarithmic limit argument needs positivity on the punctured filter, since the scaled partition's totalized value at0 is0; do not silently use an all-t positivity hypothesis. Only after these bridges may the actual unrestricted completed/standard odd free-energy value be claimed. Standard versus completed sourceCost is even and already has an exact cancellation theorem, but their unnormalized leading constants must not be conflated.

Full-Haar odd free energy, fixed-origin mixed derivatives, integrated covariance/ordering and actual stationary physical-transfer/spectral implications remain OPEN. This closes1731's polynomial integrability and cutoff odd-limit obligations without claiming a continuum limit, scale/volume-uniform bound, physical mass gap or novelty of the classical dominated-convergence tool. Preserve the larger-box pure-gauge obstruction. Exact-commit approval, secret scan, guarded public two-branch synchronization and independent exact remote-ref/visibility checks remain closure gates; this pre-commit ledger does not claim unobserved remote success. Visibility remains exclusively user-controlled.


## Checkpoint1733 — unrestricted actual full32 Haar odd free energy and nonlinear source ordering

October29,2026; focused Yang-Mills remains ACTIVE. Checkpoint1732,215fc7294cbba738fcfa941d9e27db74f5ecee8c, closed with both authorized refs independently verified at19:22:26UTC and PUBLIC unchanged. Its first guarded run reported an aggregate remote-ref mismatch at19:19:09UTC while both research refs already matched; a safe unchanged retry succeeded at19:21:54UTC. No visibility/ref rewriting or sync-policy change was used. Exact closure evidence is stardust-ym-1732-remote-check.json in the local temporary evidence directory.

PROVED in Foundation/FourCubeFullHaarOddAsymptotic.lean: exponential_first_order_limit strengthens the old96-power barrier to exp(-1/(4t^2))/|t|^97->0. Its private even-power49 argument reuses the existing inverse-square limit and Mathlib exponential asymptotics. outside_first_order_limit holds for EVERY moving boundary map b:real->Fin3->SU2, with NO continuity or measurability assumption on that parameter map: the already-verified pointwise source-uniform outside-energy barrier supplies the required bound. Its signed quotient outsidePartition(b(t),1/t^2)/(t*|t|^96) tends to0 on the two-sided punctured filter.

outside_odd_limit combines two such arbitrary moving-source estimates. full_partition_odd_limit now genuinely joins1732's96-dimensional signed cutoff integral with the first-order off-cutoff remainder, proving for the UNRESTRICTED actual32-link completed-Haar partition

    [Z_C(t)-Z_C(-t)]/(2*t*|t|^96)
      -> -(1784975/2750517)*x*y*z*R(x,y,z),  R>0.

No zeroth-order tail limit is substituted for this first-order obligation. There is no pinned31-link integration or cutoff-only conclusion in this theorem.

PROVED in Foundation/FourCubeFullHaarOddFreeEnergy.lean: the private log_odd_limit requires positivity EVENTUALLY on the punctured filter, not positivity at every real parameter. The actual scaled partition Z(t)/|t|^96 is totalized to0 at t=0, so an all-t-positive premise would be false. The dslope-log argument proves the needed logarithmic derivative limit from actual positive normalization and actual odd partition convergence. completed_free_energy_odd_limit proves

    [F_C(1/t^2,b(t))-F_C(1/t^2,b(-t))]/(2t)
      -> (1784975/2750517)*x*y*z.

standard_free_energy_odd_limit then reuses1725's EXACT even source-cost cancellation to prove the SAME coefficient for the actual STANDARD864-face Wilson action and its full32 Haar partition. All boundary sources are the existing physical angles(t*x,t*y,t*z). No equality of unnormalized completed/standard leading Gaussian constants is assumed.

standard_free_energy_eventually_gt and standard_partition_eventually_lt give a concrete nonlinear consequence: for ANY real x,y,z with x*y*z>0 and all sufficiently small positive t, actual standard F(b(t))>F(b(-t)) and actual standard Z(b(t))<Z(b(-t)), at inverse temperature1/t^2. This is actual finite-box source ordering along a specified low-temperature scaling, NOT fixed-beta mixed differentiation, a covariance-sign theorem, reflection-positivity failure, stationary transfer contraction or a physical mass gap. The strict inequality rules out an EXACT source-reversal-even boundary replacement along this path; an asymptotic Gaussian comparison with a quantified permissible error requires a separate theorem. The nonzero odd coefficient must be respected by any proposed more accurate reference estimate.

This completes the full-Haar cubic-value obligation left open at1730-1732. The actual new coefficient1784975/2750517 belongs to the full32 completed/standard action; the older pinned31 coefficient31877443263/69438734552 belongs to a different law and is not reused as its value. The larger216-link pure-gauge counterexample still forbids naive volume-uniform raw-link coercivity. No physical existence or mass-gap assertion is added as an axiom.

Independent diagnostic: NumPy reconstructs all864 physical plaquettes,130 active faces, all32 integrated links and the full Gram matrix directly from incidence. With seed1733,64 full96 Gaussian draws and all8 color reflections give512 points. Actual stereographic and axis quaternion products, even pure-source subtraction, product Jacobian and Gaussian importance weights are evaluated at t=0.01,0.005,0.002 for amplitudes(1,1,1),(2,-1,3),(0,2,-3). The final observed odd free-energy quotients are0.6489585385781593,-3.8937335191668865,0; targets are0.6489598137368356,-3.8937588824210136,0. Errors are1.2752e-6,2.5364e-5,0. The first-order barrier logarithm reaches-1174.9434 at0.0125; the same bound can be VERY LARGE at moderate t, so no useful finite-scale uniform rate is inferred. These are FINITE IMPORTANCE DIAGNOSTICS, not certified Haar quadrature, error bars, an integrated proof or a new Gaussian construction. The actual theorem is Lean-verified independently of samples. Evidence: C:/Users/ramir/AppData/Local/Temp/stardust-ym-1733-independent.py/json/log.

Verification: complete7083-job root build PASS in29.2330142s; COMPLETE canonical transitive safe-Foundation audit PASS for57106 declarations in41.9091361s, only propext/Classical.choice/Quot.sound. All8 unabridged public theorem types, both complete saved sources and BOTH private exponential/logarithmic helpers were reviewed. Eight independent Lean checks PASS in40.3104583s; complete persisted AxiomAudit PASS in51.3571774s. The eight independent Lean checks cover arbitrary moving source maps, the97-power limit, zero/negative/unit source coefficients, actual standard partition/free-energy ordering and an EXPLICIT REFUTATION of all-t positivity for the scaled partition by evaluation at0. A targeted congr tactic initially unfolded too much finite-box structure and reached default recursion depth; exact congrArg on the scalar quotient resolved it without raising any limit. No new axiom/sorry/native_decide, suppressed error, altered semantics, toolchain/trust/compiler/resource/heartbeat/recursion setting or weakened audit gate.

Authenticated integrity compares1732's manifest against its exact commit approval. Among2865 recursive Foundation/root Lean sources only the two new full32 odd-tail/free-energy modules, root imports and persisted AxiomAudit differ. Every earlier proof source, three pinned configuration files,113 baseline originals and21 Yang-Mills originals(20 hashes) remain unchanged. The physical probe SHA256 remains7fab7b109ae2709100b427e012c49bfa807c32cb495b3d0bf59affedbc434b11. ResearchSources is read-only/uncommitted. No manuscript/PDF, editorial README, publication artifact, campaign queue, reflection reservation or preserved master was modified.

Next substantive focus: connect this nonzero ACTUAL boundary response to the precise comparison/error hypothesis used by a proposed gauge-invariant block transfer, rather than expanding a general gauge library. Test whether a source-even Gaussian reference can achieve an error smaller than the observed order t=beta^(-1/2) in its stated functional domain; a free-energy scalar discrepancy alone does NOT establish an H1/operator-norm error or spectral obstruction. Review exact reusable native stationary-transfer/gauge-projection theorems before introducing such a bridge. Fixed-beta origin mixed derivatives, integrated covariance ordering, fluctuating exterior blocks and volume/continuum-uniform transfer control remain OPEN. The existing local gauge-invariant slow modes and coupling-dependent finite-count decay results remain valid, neither proved nor refuted anew by this boundary coefficient. No campaign-completion or physical mass-gap claim. Exact approval, new-history secret scanning, guarded PUBLIC two-branch synchronization and independent exact remote-ref/visibility checks remain separate closure gates; this pre-commit entry does not claim unobserved remote success. Visibility stays exclusively user-controlled.


## Checkpoint1734 — actual comparison-error obstruction and a sharp normalization counterexample

October29,2026; focused Yang-Mills remains ACTIVE. Previous checkpoint1733,accd3ab3eed6b13fa16c2f2f46fca9f9b0c96f26, closed guarded sync at19:34:48UTC and both authorized refs/PUBLIC independently at19:35:18UTC. This checkpoint tests the proposed route from the actual full32 odd boundary response to a heat-reference comparison obstruction. It preserves1733's physical864-face standard action and every earlier stationary/gauge result.

PROVED in Foundation/FourCubeActualErrorBudget.lean: rayFreeEnergy is the ACTUAL standard full32 Haar free energy along beta=1/t^2 and the physical three-source path; coefficient=(1784975/2750517)*xyz. ray_odd_limit directly reuses1733. paired_error_lower proves: for xyz>0, if a COMMON scalar reference r(t) approximates BOTH reversed actual free energies with allowance e(t), then eventually for positive t

    e(t)>coefficient(x,y,z)*t/2.

No continuity, positivity or Gaussian character of r is assumed. no_common_reference_contraction combines this actual lower bound with the ALREADY VERIFIED YMBlockHeatContractionObstruction.necessary_error_budget, rather than duplicating the general rate theorem. It refutes eventual simultaneous validity of BOTH scalar error bounds AND referenceFactor(gap,curvatureScale,1/t^2)+e(t)<1. The necessary heat-reference error budget is O(t^2), whereas the actual paired scalar discrepancy forces order t. The theorem has exact hypotheses; it does NOT assert that an operator/H1 comparison allowance controls these scalar free energies.

The attempt to supply that missing implication from normalized Gibbs-law error ALONE fails, rigorously. PROVED in Foundation/FourCubeScalarCalibration.lean: define comparison weight w_lambda(U)=exp(lambda)*w_standard(U) on the SAME actual32-link Haar space. Its genuine integral is Z_lambda=exp(lambda)*Z_standard>0 for every real lambda,beta and every three-source SU2 boundary. weight_integrable, observable_eq and the reused actual standard_integrable theorem preserve the exact domain of arbitrary weighted-integrable observables. Normalized densities are POINTWISE equal, while F_lambda=F_standard-lambda. The comparison weight is explicitly a new calibrated object, NOT a modification of the actual Wilson action or original research results.

standardLaw and calibratedLaw are actual withDensity measures on the full32 Haar space. Both are PROVED probability measures; calibratedLaw_eq proves equality of the measures, not merely matching finitely many tests or a formal normalized ratio. density_error_zero is the actual integral of an identically zero absolute density difference. unit_shift_counterexample and no_free_energy_bound_from_density_error prove for EVERY real beta,boundary and finite K that unit free-energy error cannot be bounded by K times this normalized L1 density error, which is zero. Thus absolute partition normalizations cannot be recovered from the normalized law alone.

The sharper ACTUAL-response counterexample uses calibration(t)=[F_standard(t)-F_standard(-t)]/2. balanced_value and balanced_even prove its calibrated free energy is exactly [F_standard(t)+F_standard(-t)]/2 and exactly even. balanced_normalized_density and calibratedLaw_eq retain the original normalized law at EACH source configuration. balanced_odd_zero is exact at every t, while calibration_error_limit proves

    [F_standard(t)-F_balanced(t)]/t -> (1784975/2750517)*xyz.

The calibration depends on exact original free energies; it is a legitimate nonidentifiability counterexample, not a practical computational reference, Gaussian approximation or physical Hamiltonian construction. Evenness of its scalar partition/free energy does NOT make its complete weight or normalized kernel source-even. No equality of the original laws at opposite sources is claimed. Consequently the conditional scalar-budget obstruction is valid, but an UNCONDITIONAL normalized-operator obstruction from this odd coefficient alone is NOT established. A physical unnormalized transfer may retain precisely the scalar information discarded by conditional-law normalization; this counterexample does not refute such a transfer estimate or a physical mass gap.

Independent tests: exact Fraction reference masses(1/2,1/3,1/6), weights(1,3,2) give Z=11/6 and probabilities(3/11,6/11,2/11), unchanged exactly after multiplying all weights by5. An80-digit check of the ACTUAL beta=0 Haar weight (identically1, Z=1) verifies unit calibration gives F=-1 and the SAME unit normalized density. Eleven independent Lean checks additionally prove these beta=0 identities, actual probability-law equality, the arbitrary-K L1 counterexample, exact balanced evenness, actual calibration error limit and a NONVACUOUS instantiation of paired_error_lower with reference=F_balanced and e=|calibration|; its two error premises hold identically by algebra. Thus the rate theorem is not tested only on impossible zero-error assumptions.

Four finite physical-box importance diagnostics reuse1733's864-face/130-active-face/32-link construction,512 color-antithetic points and actual Jacobians at amplitudes(1,1,1),(2,-1,3), t=.01,.002. Calibrated normalized-density errors are at floating-point roundoff (0 to8.6e-16), while scalar free-energy errors range.0012979 to.0389313. The illustrative factor exp(-t^2)+e exceeds1 in each case. These remain FINITE IMPORTANCE DIAGNOSTICS, not certified Haar quadrature, error bars or proof inputs. The genuine law equality and asymptotic obstruction are supplied by Lean. Evidence: C:/Users/ramir/AppData/Local/Temp/stardust-ym-1734-independent.py/json/log and checks.lean/log.

Verification: complete7085-job root build PASS in31.3081306s; canonical COMPLETE transitive safe-Foundation axiom audit PASS for57167 declarations in47.6524927s, only propext/Classical.choice/Quot.sound. All29 unabridged public types(20 theorems,9 definitions), both COMPLETE saved source bodies and all local normalization/integrability/filter arguments were reviewed. No new private declarations. Eleven independent Lean checks PASS in39.2564099s; complete persisted AxiomAudit PASS in53.8057439s. A local id-versus-identity-function elaboration issue was repaired explicitly. No axiom/sorry/native_decide, altered theorem semantics, suppressed errors, toolchain/trust/resource/heartbeat/recursion changes or partial-audit substitution.

Authenticated integrity compares1733's manifest with its exact audit approval. Among2867 recursive Foundation/root Lean sources ONLY these two new actual-error/calibration modules, root imports and persisted AxiomAudit differ. Every earlier source, three pinned configs,113 baseline originals and21 Yang-Mills originals(20 hashes) remain unchanged. The physical probe retains SHA2567fab7b109ae2709100b427e012c49bfa807c32cb495b3d0bf59affedbc434b11. ResearchSources remains read-only/uncommitted; no manuscript/PDF, publication artifact, editorial README, queue, reflection reservation or preserved master is modified.

Next substantive mechanism: the existing FourCubeThermalMixedDifference.cornerSum is a GENERIC eight-corner scalar operator, although that module's old physical free-energy/c coefficient is pinned31-specific and INAPPLICABLE here. Reuse only cornerSum and generic mean-value tools where justified. Test the actual full32 eight-corner contrast using1733's ALL-amplitude odd limit and pair opposite corners. Such a contrast cancels scalar terms missing any one of the three sources, including separated left/right endpoint factors under a JUSTIFIED source split. An arbitrary JOINT three-source calibration can still remove it, so allowed normalizations must be identified precisely. This is a candidate way to retain genuine interaction data after the present normalization counterexample, not yet a proved projective/gauge/physical-transfer invariant.

Do not repeat generic minorization or enlarge a broad gauge library. Audit the actual physical placement of the three source edges and admissible endpoint/Doob factors before interpreting a corner contrast as transfer geometry. Nonlinear boundary holonomies could themselves generate an odd term in a Gaussian-inspired reference; do not assume every legitimate reference is source-even. The calibrated comparison object's positivity does not construct a Gaussian reference. Fixed-beta mixed derivatives, normalized-transfer/H1 error control with retained scalar data, volume/continuum uniformity and a physical mass gap remain OPEN. Preserve the larger216-link pure-gauge obstruction and all verified local slowing/iteration results. No novelty or campaign-completion claim is made for the classical scalar normalization principle. Exact-commit approval, secret scan, guarded PUBLIC two-branch synchronization and independent remote-ref/visibility checks remain closure gates; this pre-commit ledger does not claim unobserved backup success. Visibility is exclusively user-controlled.


## Checkpoint1735 — actual full32 mixed interaction, calibration invariance, and endpoint-split obstruction

October29,2026; focused Yang-Mills remains ACTIVE. Previous checkpoint1734,150a98f953215d8db33a246cc3f945d12b0a7f7e, closed guarded sync at19:49:07UTC and independent BOTH-ref/PUBLIC verification at19:49:29UTC. The present checkpoint tests whether a genuine joint boundary interaction survives the scalar-calibration counterexample. It also tests, rather than assumes, the physical source split needed to interpret that invariant.

PROVED in Foundation/FourCubeFullMixedInteraction.lean: reuse ONLY the GENERIC FourCubeThermalMixedDifference.cornerSum; its old pinned31 free energy and31877443263/69438734552 coefficient are NOT imported as the actual new law. Four verified full32 standard odd limits, paired at opposite corners, prove actual_thermal_mixed_limit:

    cornerSum(F_standard(1/t^2,.,.,.),t)/(8*t) -> c,
    c=1784975/2750517>0.

This is the actual standard864-face/32-integrated-link Haar partition/free energy from1733, not another surrogate or an unjustified derivative interchange. corner_pairwise_invariant proves exact cancellation of arbitrary A(x,y)+B(y,z)+C(z,x), without continuity, boundedness or measurability assumptions. actual_counterterm_limit and actual_counterterm_eventually_positive allow arbitrary scale-dependent A(t,x,y),B(t,y,z),C(t,z,x). Thus even unbounded pairwise scalar counterterms cannot erase the thermal joint interaction. This is a finite-difference theorem along beta=1/t^2, NOT a fixed-beta third derivative at the origin.

PROVED in Foundation/FourCubeProjectiveInteraction.lean: for any strictly positive scalar function K(x,y,z), define the eight-corner ratio R as the product at(+++, +--, -+-, --+) divided by the product at(+-+, ++-, ---, -++). ratio_positive proves its positivity and nonzero denominator before log_ratio identifies log(R) with cornerSum(log K). ratio_pairwise_invariant proves EXACT multiplicative invariance under K->exp(A(x,y)+B(y,z)+C(z,x))*K. Every positive pairwise scalar factor can be written exponentially; no finite or probabilistic sign average is substituted for this positive ratio identity.

The actual scalar kernel(beta,x,y,z) is standardPartition(beta,angles(x,y,z)), with proven positivity for every real beta and source. It is NOT a constructed Markov kernel, square transfer operator, physical Hamiltonian or Gauss-law Hilbert space. actual_log_ratio, actual_log_ratio_limit and actual_calibrated_log_ratio_limit prove

    log(R_actual(1/t^2,t))/(8*t) -> -c,

unchanged by arbitrary scale-dependent pairwise exponential factors. actual_ratio_eventually_lt_one proves R_actual<1 at all sufficiently small positive t. A nonzero local logarithmic coefficient supplies NO scale-independent spectral contraction. An arbitrary JOINT three-source calibration, such as1734's, can still change this ratio; the theorem is NOT invariance under every endpoint or gauge operation.

The PHYSICAL ENDPOINT INTERPRETATION fails for the raw source grouping, and that obstruction is now explicitly verified. sourceEdge enumerates the ACTUAL high/chord/low edges in FourCubeDirichletBox. all_spatial_sources_same_time proves: for ANY coordinate axis tau, if all three source-edge directions differ from tau, their base vertices have the SAME tau coordinate. With tau=0 the chord is temporal; with tau=2 the high and low edges are temporal. With tau=1 or3 all three are spatial but lie on the SAME slice (physical time0 or1 respectively). Independent Lean checks also verify their literal directions and three-edge incidence on the actual(0,2) cap plaquette.

Consequently these three raw spatial source variables cannot simply be assigned across two axis-aligned temporal endpoints. When they all belong to one endpoint, a complete endpoint scalar factor may depend jointly on all three and need NOT cancel in the eight-corner contrast. This closes the proposed automatic two-endpoint interpretation NEGATIVELY, not the finite interaction theorem. It does NOT exclude a different source placement, actual temporal Haar integration, a justified gauge/holonomy reparametrization, an oblique construction or a proper physical transfer. Such mechanisms must be constructed, not assumed. In particular the algebraic pairwise invariant is NOT yet a physical projective or gauge invariant of the four-dimensional transfer.

Independent exact Fraction tests use eight positive rational corner values: R=714/715, unchanged under unequal row/column factors AND all three arbitrary positive pairwise factor tables. A genuine joint+++ factor2 changes R to1428/715. Independent enumeration of all four coordinate-time choices confirms the exact source-direction/slice obstruction. Finite physical-box importance tests (all864 faces,130 active faces,32 links,512 color-antithetic points) give thermal corner responses.6489279417751126 and.6489585385781593 at t=.01,.002, versus c=.6489598137368356. These are diagnostics only, NOT certified Haar quadrature, a physical gap estimate or Lean proof inputs. Evidence: C:/Users/ramir/AppData/Local/Temp/stardust-ym-1735-independent.py/json/log; its geometry table reports the implication if-all-spatial-then-same-slice.

Verification: FINAL complete7087-job root build PASS in42.9399055s; canonical COMPLETE safe-Foundation transitive axiom audit PASS for57201 declarations in49.3802024s, only propext/Classical.choice/Quot.sound. All26 public types(17 theorems,9 definitions), both COMPLETE saved sources and all local positivity/log/filter/finite-geometry arguments were reviewed unabridged. No new private declarations. Twelve independent Lean checks PASS in46.6292581s; complete persisted AxiomAudit PASS in52.0469174s. Independent checks include the actual full32 coefficient, arbitrary pairwise cancellation, constant-kernel ratio1, exp(xyz) log ratio8, genuine beta=0 actual partition ratio1, actual calibrated limit, existence of a positive-scale ratio<1 and the no-two-spatial-slices source obstruction. The earlier verification of the24-declaration version was NOT reused for the changed final proof: adding the substantive source-geometry obstruction triggered complete changed-input re-verification. Wrapper simplification was repaired through explicit pointwise filter congruence. No sorry/new axiom/native_decide, trust/toolchain/resource/heartbeat/recursion change, suppressed error or weakened hypothesis.

Authenticated integrity compares1734's manifest with its exact audit approval. Of2869 recursive Foundation/root Lean sources ONLY these two new full32 mixed-response/projective-ratio modules, root imports and persisted AxiomAudit differ. All earlier source bodies, three pinned configuration files,113 baseline originals and21 Yang-Mills originals(20 hashes) remain unchanged. The committed physical probe retains SHA2567fab7b109ae2709100b427e012c49bfa807c32cb495b3d0bf59affedbc434b11. ResearchSources remains read-only/uncommitted; no manuscript/PDF, editorial README, publication artifact, campaign queue, reflection reservation or preserved master is changed.

Next concrete bottleneck: construct or identify a CORRECT temporal boundary split before crediting this coefficient with any transfer consequence. Existing OneSidedBlockIncidence already supplies the32-edge/24-face unit4-cube geometry; YMFiniteWilsonVacuum.ground_exists supplies actual finite-product-Haar positive eigenfunctions for h*kinetic*h, but NOT automatic gauge projection, physical source identification or a volume-uniform gap. A theorem-level reuse audit should test a minimal genuinely split time slab (spatial boundary fields, actual temporal link integration or justified projection) and its homogeneous spatial half-weight. Do not build a broad gauge library or repeat generic eigenfunction existence simply to increase declaration count. A finite harmonic/coercive comparison would still require uniformity and proper gauge treatment; the larger216-link pure-gauge obstruction remains intact.

The scalar normalization counterexample1734, actual local stationary slow modes and coupling-dependent iteration theorems remain preserved. Fixed-beta mixed derivatives, physically valid endpoint/gauge invariants, actual homogeneous4D transfer comparison, scale/volume/continuum control and a positive physical mass gap remain OPEN. The current successful finite interaction and failed raw endpoint identification are both retained. No novelty or campaign-completion claim. Exact approval, new-history secret scan, guarded PUBLIC two-branch synchronization and independent remote-ref/visibility checks remain separate closure gates; this pre-commit ledger does not claim unobserved remote success. Visibility remains exclusively user-controlled.


## Checkpoint1736 — correctly split homogeneous Wilson cube slab, actual temporal Haar kernel and gauge-invariant positive eigenfunction

October29,2026; focused Yang-Mills remains ACTIVE. Previous1735,f885d0145c6c685d92e47fdef03618d23db074c2, closed guarded sync at20:09:12UTC and independent BOTH-ref/PUBLIC verification at20:10:54UTC. Its raw-source endpoint-split obstruction is preserved. The present development addresses that concrete missing geometry, not a broad gauge library or another source-frame reinterpretation.

PROVED in Foundation/CubeTemporalSlab.lean: use the EXISTING actual unit4-cube incidence geometry, with coordinate3 as time. A spatial slice has8 vertices,12 oriented edges and6 plaquettes. The two endpoint fields U,V are independent unrestricted12-link SU2 states. The temporal field g has8 SU2 vertex/link values. faces_split, faces_disjoint and injective embeddings identify ALL24 actual unit4-cube plaquettes as6 lower spatial,6 upper spatial and12 temporal. Forty-eight spatial plus48 temporal link-slot equalities verify the actual ordered plaquette words BEFORE any group rearrangement. The actual temporal word is

    U_e * g_target * V_e^-1 * g_source^-1
      = U_e * (gaugeAction(g,V)_e)^-1,
    gaugeAction(g,V)_e = g_source * V_e * g_target^-1.

No boundary source is mislabeled as a separate physical endpoint. No temporal link is frozen, no root link is pinned, and no old31/32-link source-frame partition is identified with this new endpoint integral. Outside the admitted24-face geometry the link map is merely totalized; all used slots are certified.

PROVED in Foundation/CubeWilsonSlab.lean: spatialAction is the sum of6 actual Wilson defects; temporalAction sums12. full_action identifies the EXISTING FourCubeWilsonCubic.innerAction on all24 actual faces with S(U)+S(V)+T(U,V,g). half_action_full proves the TRANSFER half-boundary convention explicitly:

    H(U,V,g)=S(U)/2+T(U,V,g)+S(V)/2
      = full24Action - [S(U)+S(V)]/2.

This does NOT silently change a standalone full24-face action into one with half weights. The homogeneous trace weight has the SAME beta in h_beta(U), the temporal term and h_beta(V), with h_beta=exp((beta/2)*sum6 halfTrace(spatialWord)). trace_weight_factor proves EXACTLY

    h_beta(U)*exp(beta*sum12 halfTrace(temporalWord))*h_beta(V)
      = exp(18*beta)*exp(-beta*H).

The18 factor is12 temporal plus two spatial halves of6, not24 or36. trace_integral_factor preserves it under actual temporal Haar integration. This supplies a correctly normalized homogeneous spatial weight, absent from a pure-heat-only reference.

gaugeHaar and boundaryHaar are actual finite-product SU2 Haar probability measures on8 and12 factors. The weight is jointly measurable, genuinely integrable, and uniformly positive at EACH fixed beta. The ACTUAL scalar integral kernel is

    K_beta(U,V)=integral_g exp(-beta*H(U,V,g)) dHaar_8(g).

Theorems prove joint measurability and exp(-36|beta|)<=K_beta<=exp(36|beta|), valid for every real beta and every endpoint. These are coarse finite-volume existence bounds, NOT a coupling-uniform mixing estimate. Integrability is proved before positivity/integral comparisons; no formal or totalized integral is substituted for a missing domain.

PROVED in Foundation/CubeSlabGauge.lean: spatial plaquette words transform by conjugation, so the actual six-plaquette spatial action is invariant. Temporal left/right word identities retain all noncommutative order. Pointwise weight identities plus ACTUAL product-Haar changes g->a*g and g->g*a prove independent gauge invariance in BOTH endpoints:

    K_beta(a.U,V)=K_beta(U,V)=K_beta(U,b.V).

This is not row-normalization of an unprojected kinetic kernel. The temporal integration already implements these finite endpoint gauge averages. Swap/inverse words and temporal Haar inversion also prove K_beta(U,V)=K_beta(V,U). The SU2 inversion-preserving helper is proved from compact probability-Haar uniqueness for the actual NONCOMMUTATIVE law; no abelian inversion instance or new invariance axiom is assumed.

positive_ground_exists DIRECTLY REUSES YMPositivePower.positive_eigenfunction_exists for THIS new measurable kernel and actual12-link boundary Haar. It constructs lambda>0 and a measurable psi with strictly positive lower bound exp(-36|beta|)/exp(36|beta|), finite upper reciprocal, and the genuine integral equation

    integral_V K_beta(U,V)*psi(V) dHaar_12(V)=lambda*psi(U).

Kernel left gauge invariance and lambda>0 then prove psi(a.U)=psi(U) for EVERY finite vertex gauge field a. This is an actual constructed bounded gauge-invariant positive eigenfunction, not a GroundData assumption or an external vacuum axiom. Its bounds deteriorate as beta grows. No uniqueness, leading-spectrum classification, selfadjoint L2 operator realization, positive-DEFINITE transfer operator, native stationary Markov realization, Hamiltonian, scale-uniform spectral gap or continuum field is claimed from this theorem. Symmetry and pointwise positivity are explicitly NOT confused with operator positive definiteness.

Independent exact Fraction tests construct noncommuting rational UNIT quaternions for all12+12 endpoint links,8 temporal links and8 independent gauge values. Three distinct fields independently reconstruct every actual4D plaquette and verify full_action, the half-action identity and bounds, left/right gauge changes and swap/inverse action equality EXACTLY. Twelve beta cases(0,1,-2,7/3) verify the18beta exponent factor. Diagnostic full/half action decimals are6.3164682204/4.2772139627,.4707178818/.3515349340,.1626907960/.1133298126; the identities use exact fractions, not those rounded displays. No Haar quadrature or spectrum is inferred from these finite probes. Evidence: C:/Users/ramir/AppData/Local/Temp/stardust-ym-1736-independent.py/json.

Verification: complete7090-job root build PASS in31.2595424s; canonical COMPLETE transitive safe-Foundation audit PASS for57389 declarations in44.2350688s, only propext/Classical.choice/Quot.sound. All77 public types(45 theorems,23 definitions,7 abbreviations,2 probability instances), all THREE complete saved sources, both private geometric/Haar-inversion proofs and the private finite-coordinate equality instance were reviewed unabridged. Sixteen independent Lean checks PASS in47.0210931s; complete persisted AxiomAudit PASS in60.8543290s. The sixteen independent Lean tests cover counts, actual24-face and half-action identities,18beta normalization, zero-beta weight/kernel1, symmetry/positivity, BOTH gauge invariances, pure-gauge vacuum-orbit equality, genuine product probabilities and a constructed lambda/psi with psi>0, the actual integral equation and full gauge invariance.

Elaboration repairs were explicit finite-case normalization for opaque decision casts, parentheses keeping1-halfTrace INSIDE each sum, scalar/measure wrapper normalization, gauge-VALUE rewrites avoiding nested vertex substitutions, and the missing noncommutative Haar inversion proof. The fixed-endpoint measurability inference initially unfolded too much and hit the DEFAULT heartbeat limit; explicit parameter maps and LOCAL irreducibility of weight/measure wrappers resolved it. No heartbeat or recursion increase, global build/configuration change, altered theorem semantics, error suppression, axiom/sorry/native_decide or partial-audit substitution was used. Historical large option settings in old imported sources remain untouched; none was introduced here.

Authenticated integrity compares1735's manifest with its exact audit approval. Of2872 recursive Foundation/root Lean sources ONLY these THREE new split-slab modules, root imports and persisted AxiomAudit differ. All earlier sources, three pinned configs,113 baseline originals and21 Yang-Mills originals(20 hashes) remain unchanged. The committed physical probe retains SHA2567fab7b109ae2709100b427e012c49bfa807c32cb495b3d0bf59affedbc434b11. ResearchSources stays read-only/uncommitted; no manuscript/PDF, editorial README, publication artifact, queue, reflection reservation or preserved master changes.

The concrete new comparison problem is now correctly posed on this homogeneous nonlinear unit-slab kernel, rather than the seven-link surrogate or the invalid three-source endpoint grouping. Next reuse the existing ground-transform/stationary-law machinery to construct the native stationary probability and L2 action for the ACTUAL kernel, then test a physically justified quantitative route. Keep operator positivity, spectral ordering and domains explicit. A spatially confined Gaussian reference may behave differently from the old pure-heat deficit, but that bridge is still OPEN: the independent cube/oscillator pretest in stardust-ym-1736-cube-pretest.py/json is NOT a Lean-verified spectrum or nonlinear comparison theorem. It suggests spatial curl rank5 with candidate nonzero eigenvalues4/6 and scalar Gaussian ground ratios.17157/.12702; these are proposed reference data, not results about K_beta.

Before transferring a Gaussian estimate, verify exact gauge quotient/residual symmetry, Wilson jet coefficients, normalizations and convergence topology. A finite-cell harmonic margin cannot settle volume/continuum uniformity; large-volume soft modes and the retained216-link pure-gauge obstruction remain essential. Gauge-invariant slow modes in the earlier model are preserved, but their0<t<=1 LOWER hypotheses do not automatically apply to a homogeneous spatial weight with t=beta. This checkpoint constructs a genuinely split finite4D slab and resolves its finite kernel/gauge/existence obligations; it does NOT prove the Millennium mass gap or finish Yang-Mills. No novelty claim is made for classical Haar or positive-kernel existence machinery. Exact approval, secret scan, guarded PUBLIC two-branch synchronization and independent remote-ref/visibility checks remain closure gates; this pre-commit ledger does not claim unobserved remote success. Visibility remains exclusively user-controlled.


## Checkpoint1737 — actual homogeneous Wilson-slab stationary ground transform

Focused Yang-Mills remains ACTIVE; no campaign transition or physical mass-gap claim. Checkpoint1736 (033d0dde297291a3e6a3cb24b403a4a10fde9ea3) closed its exact audit/secret-scan/guarded backup gates: both authorized main and research refs were independently read at that commit at2026-10-29T20:49:37.678903+00:00, with PUBLIC visibility and preserved master. Evidence: TEMP/stardust-ym-1736-remote-check.json. An earlier automatic backup failed its aggregate remote-ref check; the subsequent terminal successful run and independent reads, rather than the earlier failure or a lock, establish closure.

Foundation/CubeSlabGround.lean constructs the actual native probability law for checkpoint1736's homogeneous unit4D Wilson slab. GroundData explicitly records the positive eigenvalue, globally bounded positive measurable eigenfunction, actual twelve-link-Haar eigen-equation, and gauge invariance. ground_nonempty PROVES an inhabitant using CubeSlabGauge.positive_ground_exists; ground chooses from that proved type. No missing ground-state input is postulated. This is the specific new slab, not the historical seven-link surrogate.

For every real beta, the real density is K_beta(U,V)*psi(V)/(lambda*psi(U)), relative to actual boundaryHaar. The verified density is jointly measurable, strictly positive and genuinely integrable in each row, with row integral1. transition is a real ProbabilityTheory.Kernel constructed withDensity, and transition_markov proves its probability property. stationary is the actual probability with density psi^2/Z, with Z>0 and the exact integral formula. Pointwise detailed balance, independent left/right endpoint gauge invariance, exact ground-transformed pairings, stationarity for EVERY bounded measurable probe and reversible bounded-core pairings are proved. The bounded Fubini argument first proves integrability on the actual product Haar measure; no formal exchange of divergent integrals is used. The existing SignedDensityProbabilitySampling, YMPositiveKernel and earlier seven-link ground-transform proof patterns are reused. These are classical probability/ground-transform constructions; no novelty is claimed for them.

The object constructed is an actual finite-volume stationary Markov transition, with a proved available ground function, rather than a row-normalized scalar kernel or conditional GroundData existence claim. It does NOT establish spectral ordering/uniqueness of a physical vacuum, positive semidefiniteness of the Wilson transfer operator, an actual L2 operator realization, a uniform gap, reflection positivity, infinite-volume/continuum limits, or a four-dimensional quantum field theory. Symmetry and strictly positive kernel entries alone do not prove operator positivity. Physical beta>=0 and limiting requirements remain separate from the mathematical all-real-beta construction.

Verification: complete7091-job root build PASS in44.5252248s; canonical COMPLETE transitive safe-Foundation axiom audit PASS for57463 declarations in45.6723589s, only propext/Classical.choice/Quot.sound. All27 public declarations (one structure, six definitions, twenty theorems), its complete printed structure/fields and the FULL saved source with all THREE private integrability/mass helpers were reviewed unabridged. Twelve independent Lean checks PASS in41.7284887s; complete persisted Foundation/AxiomAudit.lean PASS in56.9457096s. Tests instantiate constructed ground(beta), actual probability and Markov instances, row normalization, detailed balance, both endpoint gauge changes, stationarity and reversibility; an explicitly constructed beta0 ground has density1, normalizer1 and exactly Haar transition averages. No change of heartbeat, recursion, compiler, trust, toolchain, caching or scheduling was made. Initial elaboration repairs made pointwise function products explicit and corrected absolute-value notation; no mathematical premise was weakened or error suppressed.

Independent exact Fraction tests use a symmetric two-state reference with nonconstant positive ground psi=(2,1), base probability(1/2,1/2), lambda3. They obtain stationary(4/5,1/5), transition[[5/6,1/6],[2/3,1/3]], exact normalization/stationarity/detailed balance and16 reversible probe pairs. Three positive rescalings of psi preserve both laws. Raw row normalization instead sends the proposed stationary law to(47/70,23/70), a concrete independent check against confusing these normalizations. These finite rational tests are NOT SU(2) Haar quadrature or Wilson spectral evidence. TEMP/stardust-ym-1737-independent.py/json retains the calculations.

Authenticated integrity:2873 recursive Foundation/root sources; only the new CubeSlabGround module, root import and persisted AxiomAudit differ from the approved1736 manifest. All earlier mathematical sources, three pinned configurations,113 baseline original manuscripts,21 Yang-Mills originals(20 distinct hashes), and the committed six-plaquette probe remain byte-identical. ResearchSources remains unmodified/uncommitted. No manuscript/PDF, publication directory, editorial README, research queue, reflection accounting or preserved master is changed.

Next substantive obligation is to realize THIS stationary transition on actual L2 and identify its gauge-invariant sector before quantitative spectral comparison. Reuse existing coupled-law/adjoint machinery rather than postulating an operator. Then test whether homogeneous spatial confinement changes the earlier surrogate slowing, with exact gauge quotient, Wilson expansion and convergence hypotheses. Existing Gaussian-reference cube eigenvalue pretests remain unverified candidate data, not a bridge theorem; large-volume soft modes and the retained pure-gauge coercivity obstruction still obstruct naive extensions. No finite-cell construction establishes a continuum mass gap. Exact-commit approval and guarded PUBLIC two-branch synchronization, followed by independent remote reads, remain closure gates; this pre-commit ledger does not claim unobserved backup success. Repository visibility remains exclusively user-controlled.


## Checkpoint1738 — actual slab L2 transfer; gauge-variant raw-link modes are killed

Focused Yang-Mills remains ACTIVE. Checkpoint1737 a7b2006ce77bb238879b73821a83c0af1f0997a7 is fully audited and BOTH authorized PUBLIC research refs were independently verified at that commit at2026-10-29T21:03:10.427889+00:00, after terminal guarded success21:03:01.786251UTC. An initial aggregate remote check failed; fresh reads showed the mathematical refs already exact, and an unchanged guarded retry then passed. Preserve that failure as evidence; never infer terminal success merely from matching mathematical refs while the script reports failure. TEMP/stardust-ym-1737-remote-check.json records closure. Publication and master histories were not altered.

Foundation/CubeSlabL2.lean now realizes checkpoint1736/1737's ACTUAL homogeneous unit4D Wilson slab transition on its own stationary L2 probability space. The ground is available from CubeSlabGround.ground(beta); no missing GroundData existence axiom is introduced. edgeLaw is the genuine stationary compProd transition law. Bounded continuous product probes and proved reversibility establish exact swap invariance; its two coordinate marginals are the actual stationary law. Their pullbacks are linear isometries. operator=L*R uses the existing HilbertRepresentation.predictableAdjoint; it is a bounded self-adjoint contraction on all of the actual stationary L2, with its true coupled-law pairing and native-kernel integral pairing for EVERY L2 input/test. operator_toLp further proves exact agreement with actual Markov integration on every bounded measurable input. No invented Hilbert space, unverified marginal, postulated transfer operator or substitution of the old seven-link law is used. The reusable proof patterns are explicitly SU2SevenLinkL2Transfer plus HilbertRepresentation and Mathlib compProd/Lp machinery; this classical realization is not a novelty claim.

A substantive candidate test is resolved: the transition measure itself is unchanged under ANY source endpoint gauge; consequently every literal one-step output has a pointwise gauge-invariant representative. A pointwise native eigenfunction at nonzero eigenvalue must be gauge invariant. For each actual one of the12 spatial links, the raw halfTrace(V_e) FAILS the pointwise nonzero-eigenvalue equation. More strongly, the actual native transfer sends it EXACTLY to zero at every endpoint and every real beta, and operator_linkTrace_zero proves its annihilation IN THE ACTUAL stationary L2 space. This is not merely a formal or finite-quadrature cancellation. The proof constructs a coordinatewise measurable boundary gauge equivalence, proves it preserves the full twelve-link Haar product, uses the genuine gauge-invariant ground-transform density, and flips the SU(2) center at one endpoint. General globally gauge-odd functions have the same native cancellation.

The independent Lean checks derive the useful all-L2 consequence: every operator output is orthogonal to each single-link trace, using self-adjointness and actual L2 annihilation. Thus these particular raw modes cannot serve as the surviving slow physical trials. This does NOT prove a gap on the gauge-invariant sector, does not remove gauge-invariant loop modes from earlier counterexamples, and does not identify the whole nullspace or assert that a killed class has nonzero L2 norm without a separate proof. The pointwise eigenfunction theorem is NOT silently upgraded to arbitrary ae representatives. Nor does raw-link trace cancellation prove absence of all first Gaussian chaos in a gauge-fixed residual representation; that different claim requires a justified quotient and residual-conjugation analysis.

Independent exact center-subgroup enumeration uses8 vertices,12 edges,6 faces,4096 center-valued link states and256 vertex gauges. There are128 distinct gauge actions and32 orbits, all with128 states. EVERY link-trace sum vanishes on EVERY orbit, whereas each face signature is constant on its orbit; the32 orbit signatures are distinct. Each raw trace has discrete square norm1 despite zero gauge average. This checks the geometry and distinguishes raw-link from closed-face observables, but is NOT full SU(2) Haar quadrature, a proof about the SU(2) quotient dimension, or Wilson spectral evidence. TEMP/stardust-ym-1738-independent.py/json preserves the exact integer calculation.

Verification: complete7092-job root build PASS in29.0027150s; canonical COMPLETE transitive safe-Foundation audit PASS for57504 declarations in44.1256602s, only propext/Classical.choice/Quot.sound. All31 public declarations(23 theorems,6 definitions,2 L2 abbreviations), FULL saved source, TWO private integration/Haar helpers and SIX private topology/probability instances were reviewed unabridged. Fifteen independent Lean checks PASS in49.5377940s; complete persisted Foundation/AxiomAudit PASS in60.8855145s. Default200000-heartbeat elaboration initially rejected a broad congruence and an insufficiently typed product-Haar argument; exact density rewriting and an explicit single-SU2 sandwich helper resolved both. A typed cylinder measurability expression and the current conditional-rewrite names resolved remaining elaboration errors. No heartbeat/recursion increase, altered mathematical premise, global compiler/configuration change, error suppression or partial-audit substitution was used.

Authenticated integrity:2874 recursive Foundation/root sources. Only the new actual CubeSlabL2 source, root import and persisted axiom ledger differ from the exact approved1737 manifest. Every earlier mathematical source, three pinned configurations,113 baseline originals,21 Yang-Mills originals(20 hashes) and committed six-plaquette probe remain byte-identical. ResearchSources is read-only/uncommitted. No manuscript/PDF/publication directory, editorial README, campaign queue, reflection reservation or preserved master was changed.

The concrete remaining bottleneck is a quantitative estimate on surviving gauge-invariant modes of THIS homogeneous operator, strong enough for its actual stationary L2 topology. Contraction<=1 alone gives no strict physical gap; self-adjointness alone gives no positive-semidefinite transfer. Correct quotient/Haar transport, Wilson jets and a nonlinear norm/resolvent comparison are still missing for the tentative spatially confined Gaussian reference. The cube's proposed Gaussian ratios and curl ranks are still preliminary independent data, not a Lean spectral comparison. Large-volume soft modes, scale/coupling relations, physical beta>=0, reflection positivity and continuum/infinite-volume bounds remain separate obligations. A finite-cell L2 realization and raw-gauge-mode cancellation do NOT establish the Millennium mass gap. Next prefer actual gauge-invariant plaquette/loop trial estimates or a decisive nonlinear comparison obstruction over more abstract operator infrastructure. Exact-commit approval, guarded secret scan/two-branch PUBLIC sync and independent remote reads remain closure gates; this pre-commit entry does not claim unobserved backup success. User alone controls repository visibility.


## Checkpoint1739 — the old center witness is pure gauge; invariant transfer still agrees

Focused Yang-Mills remains ACTIVE. Checkpoint1738 5e1ec571b48fdde1fa82ebbe201db1728320ce4d closed every gate: BOTH authorized PUBLIC research refs were independently verified at that exact commit at2026-10-29T21:16:29.836268+00:00, after terminal guarded success21:15:59.201417UTC. TEMP/stardust-ym-1738-remote-check.json is exact evidence. No publication or master history was altered.

A specific missing physical bridge now has an explicit counterexample. Foundation/CubeCenterProjection.lean defines the actual twelve-link all-minus-I center field C and an eight-vertex checkerboard gauge a(v)=(-I)^(coordinate-sum parity). checker_center PROVES gaugeAction(a,I)=C on every admitted spatial cube edge. Thus C and I are the SAME actual full-vertex gauge orbit. The actual projected kernel satisfies K(C,V)=K(I,V) and K(U,C)=K(U,I), with positive denominator. Its four-point center ratio K(I,I)K(C,C)/(K(I,C)K(C,I)) is EXACTLY1 for EVERY real beta.

This is compared with BOTH relevant unprojected objects. The existing Fin12 kinetic theorem remains valid with center ratio exp(48beta). More pointedly, the actual homogeneous slab weight w_beta(U,V,g=1), including its correctly shared spatial actions, has the SAME raw ratio exp(48beta): spatialAction(I)=spatialAction(C)=0; the four temporal actions are0,24,24,0. Temporal Haar averaging changes this actual raw witness to1. For beta>0 the inequality is strict. This does not refute the earlier unprojected kinetic/spatial-multiplier theorems; it REFUTES their direct promotion via this center witness to a projective or physical spectral obstruction for the actual gauge-averaged slab. Endpoint multiplication and genuine gauge integration must not be confused. Nor is it a claim that every possible projected cross-ratio is bounded, that its supremum is1, or that its volume-uniform diameter is controlled.

The complementary positive result prevents an opposite error. Foundation/CubeInvariantTransfer.lean proves, for EVERY bounded measurable gauge-invariant f and every endpoint U, the EXACT identity integral_V K_beta(U,V) f(V) dHaar12 = integral_V w_beta(U,V,1) f(V) dHaar12. The proof first constructs a genuine integrable joint function on Haar12 x Haar8 with bound exp(36|beta|)|B|, then applies Fubini and the already-verified measure-preserving boundary gauge substitution. The unaveraged weight is the same original homogeneous defect weight, not a new approximate kernel or an unspecified normalization.

Consequently the constructed invariant positive ground psi solves the SAME unaveraged integral eigen-equation with the SAME lambda. For bounded measurable gauge-invariant f the actual ground-normalized Markov transfer is exactly integral_V w_beta(U,V,1) psi(V)f(V) dHaar12 /(lambda psi(U)). Thus gauge averaging can change this global pointwise center witness while preserving transfer action on the physical invariant CORE. This is a useful exact reuse bridge to the unaveraged weighted link calculus, not an operator-norm estimate or an automatically completed-domain theorem. It does not assert equality on arbitrary gauge-variant inputs. The earlier raw-link annihilation, actual L2 construction and genuine invariant-loop obligations are preserved.

Thirteen independent Lean checks instantiate the constructed ground(beta), prove psi(C)=psi(I), equality of the actual transition measures at C/I, and the normalized transition DENSITY's center ratio1. They also check the actual projected/raw ratios, strict positive-beta comparison and raw ground equation. Crucially, explicit spatial plaquette traces are proved measurable, bounded by1 and gauge invariant via the already-verified word covariance/trace conjugation; BOTH the unnormalized integral reduction and actual ground-normalized transfer formula are tested on these concrete physical loop probes. The temporary test initially omitted its noncomputable annotation; adding it repaired compilation without changing any mathematical source. Initial checkerboard elaboration failures were opaque finite-function/edge proof casts: explicit three-coordinate witnesses, exposed edge admissibility and kernel-checked decision proofs reject invalid oriented-edge cases. No additional axiom or altered hypothesis is used.

Independent exact integer enumeration checks all256 center-valued vertex gauges. The four actual raw corner actions are0,24,24,0, giving the exponent48; all four averaged center-subgroup action polynomials are IDENTICAL, with actions/counts0:2,6:16,8:30,10:48,12:64,14:48,16:30,18:16,24:2. The checkerboard flips all12 edge signs. A triangle diagnostic has different positive/negative-center action histograms(0:2,4:6 versus2:6,6:2), illustrating why the bipartite geometry matters. These finite subgroup polynomials are NOT full SU(2) Haar quadrature, a spectral estimate, or a general theorem about other topologies/boundary gauges. The full actual SU(2) conclusion comes from the Lean gauge-orbit/Haar proofs. Evidence: TEMP/stardust-ym-1739-independent.py/json.

Verification: complete7094-job root build PASS in66.7994764s; canonical COMPLETE transitive safe-Foundation audit PASS for57536 declarations in47.2950556s, only propext/Classical.choice/Quot.sound. All13 public declarations(11 theorems,2 definitions), BOTH complete saved sources and all THREE private center/integration helpers were reviewed unabridged. Thirteen independent Lean checks PASS in41.9501257s; complete persisted Foundation/AxiomAudit PASS in46.8832692s. No compiler/resource/trust/toolchain/cache change, heartbeat/recursion increase, error suppression, native_decide, sorry or partial-audit substitution. Authenticated integrity covers2876 recursive Foundation/root sources: only these two new modules, root imports and persisted audit entries differ from the approved1738 manifest. Every older mathematical source, three pinned configs,113 baseline originals,21 Yang-Mills originals(20 hashes) and the six-plaquette probe remain byte-identical. ResearchSources stays read-only/uncommitted. No manuscript/PDF, publication directory, editorial README, queue, reflection reservation or preserved master changes.

Assessment: the classical bipartite center-gauge mechanism supplies a repository-specific decisive failure of one proposed obstruction bridge; no novelty claim is made for that mechanism or Haar projection. The actual physical spectral problem remains OPEN, not disproved or solved by the collapsed witness. Next use the proved invariant-core reduction to test gauge-invariant plaquette/loop trials or a justified homogeneous Gaussian comparison. Global raw projective extrema and raw single-link modes no longer supply the needed physical obstruction. Nonlinear norm/resolvent control, exact gauge quotient/Haar transport, residual symmetries, large-volume soft modes and coupling/physical-distance scaling remain substantive obligations. No reflection-positivity, positive-semidefinite transfer, uniform gap, continuum limit or Millennium mass gap is established here. Exact-commit approval, guarded secret scan/two-branch PUBLIC sync and independent remote reads remain closure gates; this pre-commit entry does not claim unobserved backup success. Visibility is exclusively user-controlled.


## Checkpoint1740 — global nonlinear spatial control modulo actual cube gauge

Focused Yang-Mills remains ACTIVE. Checkpoint1739 10e301f932ace3bb81d4e7506bfe5f64ce9cc6ee closed its exact approval/secret-scan/guarded sync gates; BOTH authorized PUBLIC research refs were independently verified at that commit at2026-10-29T21:38:04.147733+00:00 after terminal guarded success21:37:19.593068UTC. TEMP/stardust-ym-1739-remote-check.json records exact closure. Preserve the center-witness failure and the separate proved invariant-core transfer identity.

The missing spatial control has a valid MODULO-GAUGE version on the actual twelve-link spatial cube. Foundation/CubeAxialSlice.lean defines five actual chord edges a=(010,axis0), b=(001,axis0), c=(011,axis0), d=(001,axis1), e=(101,axis1), with the seven complementary axial-tree links equal to1. Finite label/readback and a bijection of the six actual spatial faces are kernel-certified. The six EXACT noncommutative spatial words are a^-1; b e c^-1 d^-1; b^-1; a c^-1; d^-1; e^-1. Their signs and order are retained; no commutative or quadratic replacement is made.

Writing delta(Q)=1-halfTrace(Q), the actual spatial action on this slice is EXACTLY delta(a)+delta(b)+delta(a c^-1)+delta(d)+delta(e)+delta(b e c^-1 d^-1). Reuse FourCubePinnedCoercivity.defect_nonneg/defect_inv/defect_zero_iff and FourCubeBoundaryCoercivity.defect_mul. The existing global group inequality gives delta(c)<=3(delta(a c^-1)+delta(a)), so the five-coordinate energy E(q)=sum_i delta(q_i) satisfies E(q)<=4 S_spatial(axialState(q)) for EVERY five-tuple of SU(2) elements. This is a global nonlinear bound with an explicit finite constant, not a local Hessian estimate; no optimality of4 is claimed.

Foundation/CubeAxialGauge.lean constructs the rooted gauge R_U(v) from the ACTUAL tree-path products in coordinate order0->1->2. Its value at the origin is1. For EVERY original cube state U, reconstruction proves gaugeAction(R_U,U)=axialState(gamma(U)), where gamma reads the five transformed chord values. Existing spatial_action_invariant transfers the bound to ALL U: E(gamma(U))<=4 S_spatial(U). No gauge fixing or canonical-representative assumption is imposed on the input U. This is a valid replacement for the impossible raw-link coercivity, not a revival of that failed argument.

Residual symmetry is explicitly proved. Under any vertex gauge a, R_(a.U)(v)=a(0) R_U(v) a(v)^-1 and gamma(a.U)_i=a(0) gamma(U)_i a(0)^-1. The five coordinates are COVARIANT under root conjugation, not individually invariant. Their trace-defect energy IS invariant, by the verified SU(2) conjugation identity. Flatness is also completely characterized on this cube: S_spatial(U)=0 iff there EXISTS an actual vertex gauge carrying U to the vacuum. The forward proof constructs R_U and uses the positive chord bound/defect_zero_iff; the reverse proof uses actual gauge invariance. This neither classifies flat fields on other topologies nor assumes unrestricted gauges in boundary-fixed problems.

Sixteen independent Lean checks confirm face bijection, actual chord readback, all six word formulas, slice and all-state coercivity, explicit reconstruction, both residual covariance identities and gauge-invariant energy. They derive two useful consequences: each canonical loop defect is bounded by4 S_spatial(U), and each chord's halfTrace is an invariant loop observable despite covariance of the group-valued coordinate. They also check root anchoring and preserve the exact raw-coercivity obstruction: the all-center field C is NOT the vacuum, has raw-link defect24 and spatial action0, but has canonical reduced defect0. This illustrates precisely why the new bound does not conflict with the earlier pure-gauge counterexamples.

Independent exact Fraction calculations use genuinely noncommuting rational UNIT quaternions for all12 links and8 vertex gauges. Three distinct fields reconstruct exactly, satisfy all SIX ordered word identities, preserve action under arbitrary gauges, and verify residual root conjugation of each reduced chord. The exact rational inequalities E<=4S hold; rounded diagnostic E/S values are.8216672885,.6130854249,.7244209654, not sharp-bound evidence. Arbitrary rational pure-gauge fields and the all-center field reduce EXACTLY to identity chords; the latter retains raw defect24. These are algebraic independent checks, NOT Haar quotient transport, stochastic sampling, a spectral estimate or a substitute for the Lean proofs. Evidence: TEMP/stardust-ym-1740-independent.py/json.

Verification: complete7096-job root build PASS in28.5393628s; canonical COMPLETE transitive safe-Foundation axiom audit PASS for57612 declarations in45.5442200s, only propext/Classical.choice/Quot.sound. All21 public declarations(12 theorems,8 definitions,1 abbreviation), BOTH complete saved sources, SIX private helper proofs, THREE private actual tree-edge definitions and the private computable finite-vertex equality instance were reviewed unabridged. Sixteen independent Lean checks PASS in47.2223134s; complete persisted Foundation/AxiomAudit PASS in56.5227784s. Initial finite proof repairs exposed quantified indices and rejected impossible oriented edges AFTER group normalization; explicit vector-update equalities resolved function-valued vertex labels in the residual covariance proof. No mathematical premise was weakened, resource limit increased, error suppressed, trust/toolchain/compiler/cache configuration changed, or partial audit substituted. Only kernel-checked finite decisions are used, never native_decide.

Authenticated integrity covers2878 recursive Foundation/root sources: only these two new axial modules, root imports and persisted audit entries differ from the exact approved1739 manifest. Every older mathematical source, three pinned configs,113 baseline originals,21 Yang-Mills originals(20 hashes) and the committed six-plaquette probe remain byte-identical. ResearchSources remains read-only/uncommitted. No manuscript/PDF/publication artifact, editorial README, queue, reflection accounting or preserved master changes.

This is useful finite-cell nonlinear confinement modulo gauge, not a Yang-Mills mass gap. The classical rooted-tree construction and defect inequalities are reused without a novelty claim. The next concrete bottleneck is genuine Haar transport from12 independent link variables to7 tree variables plus5 chord variables, with the residual root conjugation retained. Measurable/probability quotient transport, Gibbs concentration and a native spectral/temporal comparison are NOT inferred from the algebraic reconstruction. The singular residual orbit at the vacuum cannot be treated by silently subtracting3 Gaussian dimensions. The endpoint action's six ordered words still contain nonlinear interactions. Actual kinetic metric, temporal/root-gauge integration, operator-norm or resolvent convergence, large-volume soft modes, coupling/physical-distance scaling, positive transfer/reflection positivity and continuum/infinite-volume limits remain separate obligations. The retained larger-box raw-link counterexample remains unchanged; the factor4 result is ONLY this fixed actual cube. Prefer the specific Haar/concentration bridge over broad gauge infrastructure. Exact-commit approval and guarded PUBLIC two-branch sync with independent remote reads remain closure gates; this pre-commit entry does not claim unobserved backup success. Repository visibility remains exclusively user-controlled.


## Checkpoint1741 — actual native ground-state law concentrates near the flat gauge orbit

Focused Yang-Mills remains ACTIVE. Checkpoint1740 7eb46187b87ac52fb876d7a2301ca689ceeebc53 closed exact approval/secret-scan/guarded sync gates; BOTH authorized PUBLIC research refs were independently verified at that commit at2026-10-29T21:57:14.629196+00:00, after terminal guarded success21:55:27.877370UTC. TEMP/stardust-ym-1740-remote-check.json is exact closure evidence. Preserve the actual fixed-cube modulo-gauge bound, residual conjugation and flatness characterization.

The new concentration theorem concerns the ACTUAL stationary probability pi_beta=psi_beta^2/Z_beta against twelve-link Haar, constructed from the actual homogeneous, temporal-Haar-integrated slab K_beta and its proved available positive ground. It is NOT a spatial Gibbs-law replacement, a hypothetical vacuum, or an assumed eigenfunction. Constants below are uniform over all GroundData(beta), hence apply in particular to the constructed ground(beta), and are unchanged by positive rescaling of psi.

Foundation/CubeLowActionBlock.lean verifies continuity of the actual halfAction on(State x State)x Gauge and its zero value at the vacuum. Every fixed eta>0 has open identity neighborhoods B,D with halfAction(U,V,a)<=eta for U,V inB,a inD. Actual product Haar has strictly positive real mass on these open sets. Restricting the actual temporal integral toD constructs a positive k_eta, independent of beta, with K_beta(U,V)>=k_eta exp(-beta eta) onBxB for every beta>=0. These are genuine nonzero-Haar blocks, not pinned-coordinate approximations. The same source proves the global spatial envelope K_beta(U,V)<=exp(-beta A(U)/2), using the nonnegative temporal action and other endpoint action. Every normalization is that of the actual DEFECT kernel; its eigenvalue must not be silently replaced by the exponentially rescaled trace-kernel eigenvalue.

Foundation/CubeGroundMass.lean uses positivity to obtain a native eigenvalue lower bound with no spectral-positivity or variational assumption. For any such block, integrate the actual eigen-equation overB and compare its positive restricted mass mB=integral_B psi: lambda mB>=k_eta Haar(B) mB. Genuine integrability is reused from the existing density-integral construction; global psi.lower>0 and Haar(B)>0 justify cancellation of mB. Thus for EVERY eta>0, lambda_beta>=c_eta exp(-beta eta), with c_eta>0 independent of beta and of the selected positive ground. This is a small exponential-rate bound, not a polynomial estimate or a quantified Gaussian normalization.

The eigen-equation and spatial envelope imply lambda psi(U)<=exp(-beta A(U)/2)*m, where m=integral psi. Mathlib variance_eq_sub/variance_nonneg on the actual Haar probability gives m^2<=Z. Integrating the squared estimate against the actual psi^2/Z law proves pi_beta(A>=eps)<=exp(-beta eps)/lambda_beta^2 for beta>=0. Taking eta=eps/4 yields, for each FIXED eps>0, a positive C_eps with pi_beta(A>=eps)<=C_eps exp(-beta eps/2), uniformly for beta>=0 and every actual GroundData(beta). Therefore the actual constructed stationary laws satisfy pi_beta(A>=eps)->0 as beta->+infinity.

Foundation/CubeGroundOrbit.lean proves measurability of the actual reduced-coordinate energy E(U)=sum_i(1-halfTrace(gamma(U)_i)), using the finite rooted-gauge products. Checkpoint1740's global E<=4A gives the genuine native bound pi_beta(E>=eps)<=C'_eps exp(-beta eps/8) and its limit0 for every fixed eps>0. The events are measurable and E is already proved gauge invariant. Combined with the exact flatness characterization, this is concentration near the flat gauge orbit in the stated action/canonical-energy sense. It does not establish a weak limit to a specified orbit measure, Gaussian fluctuation scale, path law, convergence of correlations or an operator-norm limit.

Twenty-one independent Lean checks PASS: twelve instantiate the actual constructed ground(beta), positive blocks, native eigenvalue bound, eigenfunction spatial decay, native action tails and their limits, measurable canonical energy and native canonical-energy concentration. Nine SEPARATE finite-state diagnostics verify exact algebra and limiting formulas for P(q)=[[1-q^3,q^3],[q,1-q]], pi(q)=(1,q^2)/(1+q^2), centered f=(-q^2,1). For0<q<1/2 the rows are positive and normalized; detailed balance, normalization/centering and BOTH eigen-equations are checked. For the two-point action A=(0,2), the nontrivial eigenvalue1-q-q^3 tends to1 while pi(1) tends to0. This guards against inferring a uniform gap from even a concentrating reversible law with a unique minimum. It is NOT a counterexample satisfying the actual Wilson kernel envelope, nor a new formal finite-chain library declaration. A temporary diagnostic's pointwise-continuity expression required annotation; the successful rerun changed no mathematical source.

Independent Fraction tests construct exact rational positive symmetric kernels and their actual ground-normalized Markov matrices. Four instances compare pairs of reversible chains with IDENTICAL concentrating stationary distributions and very different gaps (the slow-chain parameter is t=q^2); local eigenvalue and mass-square bounds are checked exactly. The prototype ground law differs from the spatial Gibbs law (at q=1/4, tail1/257 versus1/17), independently guarding against the forbidden substitution. Fast/slow gaps at that instance are255/256 and257/4096; at q=1/256 they are4294967295/4294967296 and4294967297/281474976710656. The slow inverse-ground kernel violates the Wilson spatial envelope, so these reference tests do not refute a future slab-specific spectral estimate. Evidence: TEMP/stardust-ym-1741-independent.py/json; no SU(2) Haar quadrature or actual Wilson spectral data are inferred.

Verification: complete7099-job root build PASS in37.8846868s; canonical COMPLETE transitive safe-Foundation audit PASS for57625 declarations in77.9394025s, only propext/Classical.choice/Quot.sound. All12 public theorem types, all THREE complete saved sources, ELEVEN private helper proofs and FIVE private topology/open-Haar-positivity instances were reviewed unabridged. Twenty-one independent Lean checks PASS in72.0292594s; complete persisted Foundation/AxiomAudit PASS in79.8696526s. An initial default-heartbeat neighborhood elaboration timeout was repaired by an explicit zero-action identity and LOCAL irreducibility of action/measure wrappers; typed product neighborhoods, restricted-set/measure arguments, qualified private helpers and the explicit event inequality resolved the other elaboration failures. No resource limit was raised, hypothesis weakened, error suppressed, toolchain/trust/compiler/cache configuration changed or partial audit substituted.

Authenticated integrity covers2881 recursive Foundation/root sources: only these THREE new native-concentration modules, root imports and persisted audit entries differ from the approved1740 manifest. All older mathematics, three pinned configurations,113 baseline originals,21 Yang-Mills originals(20 hashes) and the committed six-plaquette probe remain byte-identical. ResearchSources stays read-only/uncommitted. No manuscript/PDF/publication artifact, editorial README, queue, reflection accounting or preserved master changes.

This is a concrete finite-cell native ground-law theorem with an exact domain and convergence statement; no novelty claim is made for the classical positivity/Haar/variance mechanisms. Constants depend on eps and the fixed cube; there is NO uniform eps->0 or volume control, polynomial lambda rate, rescaled Gaussian tightness, native spectral gap or continuum conclusion. The generic concentrating slow chain shows why stationary concentration is not the missing kinetic estimate. A promising NEXT specific test is whether the same envelope and eigenvalue estimate give an actual L2 operator-tail bound outside A>=delta, with all ground-density transport and unbounded-input domains verified; it must not be inferred from probability tails alone. Exact Haar transport to five chord variables, the residual root-gauge integration/kinetic metric, local norm/resolvent comparison, large-volume soft modes, physical-distance/coupling scaling, reflection positivity and infinite-volume/continuum limits remain open. Keep the focused campaign and every earlier obstruction. Exact approval, guarded secret scan/two-branch PUBLIC sync and independent remote reads remain closure gates; this pre-commit entry does not claim unobserved backup success. Visibility remains exclusively user-controlled.


## Checkpoint1742 — actual native L2 action-tail localization and two-sided compression

Focused Yang-Mills remains ACTIVE. Checkpoint1741 cfa5f2b32470fc4d2c4d0dff8bc7bb8f970dc9c2 closed its exact approval and guarded PUBLIC two-branch synchronization; independent remote reads at2026-10-29T22:28:48.251415UTC verified both authorized refs, PUBLIC visibility, preserved master and a clean tracked worktree. Evidence: TEMP/stardust-ym-1741-remote-check.json. No original manuscript or publication artifact was reviewed or changed for this checkpoint.

The concrete question left by1741 is now answered positively for the ACTUAL fixed homogeneous Wilson slab operator on its native stationary L2 space. Probability-tail concentration alone was insufficient. The proof uses the additional actual kernel envelope, its symmetry, the actual positive ground, and complete weighted domains. Write mu for twelve-link Haar, psi for d.function, lambda for d.value, Z=integral_mu psi^2, pi=psi^2 mu/Z, A for spatialAction, and P for CubeSlabL2.operator d. No Gibbs-law replacement, hypothetical eigenfunction, bounded-core completion assumption or spectral positivity is introduced.

Foundation/CubeNativeL2Domain.lean proves integrable_iff for arbitrary real observables and ae_iff for arbitrary predicates: native integrability is equivalent to integrability of psi^2 f against mu, and pi and mu have exactly the same null sets. These follow from the actual normalized withDensity measure and strict positivity of psi. For measurable f in native L2, weighted_memLp proves psi f belongs to Haar L2; weighted_square_integral proves integral_mu(psi f)^2=Z*norm_native(f)^2. The actual Haar probability variance identity gives weighted_abs_integral_bound: integral_mu psi|f|<=sqrt(Z)*norm_native(f). No uniform lower bound on psi in beta is needed for these norm identities.

Foundation/CubeOperatorTail.lean applies K_beta(U,V)<=exp(-beta A(V)/2), obtained from the verified envelope and actual symmetry, to tail-supported inputs. transfer_tail_bound is a pointwise bound for the actual transition integral. pairing_tail_bound holds for EVERY native L2 pair f,g, assuming only that f vanishes almost everywhere on A<eps; null-set transport is explicit. Reusing the existing all-L2 operator_kernel_pairing and exact stationary integral, the ground factors cancel. Testing against the actual output proves norm_tail_bound: norm(Pf)<=exp(-beta eps/2)/lambda*norm(f). This is an all-domain Hilbert-space estimate, not an assertion inferred from bounded probes or a small stationary event.

Foundation/CubeOperatorLocalization.lean constructs tailPart as the genuine measurable indicator component in native L2, proves its almost-everywhere representative and contraction, and obtains operator_tailPart_bound uniformly for ALL inputs. For every fixed eps>0, operator_tailPart_exponential gives C_eps>0, independent of beta>=0, choice of actual GroundData and input, with norm(P tailPart_eps f)<=C_eps exp(-beta eps/4) norm(f). It uses1741's lambda>=c_(eps/4) exp(-beta eps/4). Constants remain fixed-cell and threshold dependent. No shrinking-threshold or volume-uniform rate follows.

Foundation/CubeNativeCompression.lean proves the cutoff pairing identity, uses actual self-adjointness of P to prove output_tail_bound with the SAME factor, and defines lowPart=f-tailPart. lowPart_norm is contractive. compression_error proves, for ALL native L2 f and beta>=0,
  norm(Pf-lowPart_eps(P(lowPart_eps f)))<=2 exp(-beta eps/2)/lambda*norm(f).
Together with the preceding eigenvalue lower bound this gives exponentially small full-space compression error at every fixed positive threshold. The bounds are stated directly for all native classes; no new abstract gauge-theory or Hilbert-Schmidt library is required. This genuinely localizes the global finite-cell operator question near the flat orbit. It supplies neither the low-action kinetic comparison nor a positive uniform spectral gap.

Fifteen independent Lean checks passed: eleven actual-domain checks include weighted integrability/norm identity, Haar/native null sets, all-L2 pairings, two-step input/output estimates, unit-input compression, and the useful consequence that a nonzero native eigenvector SUPPORTED in the tail has abs(eigenvalue)<=exp(-beta eps/2)/lambda. Four separate generic checks prove the two low-action eigen-equations, the tail eigen-equation and the slow-eigenvalue limit below. Initial test-only scalar positivity and multiplication-order elaboration errors were repaired without changing mathematical sources.

Independent exact Fraction tests cover702 positive symmetric finite-kernel/ground pairs with varying positive ground scales, eigenvalue scales and mixing parameters. They verify the actual eigen-equation, native square-ground law, exact ground-factor cancellation, the native tail-column squared norm, and the two-sided compression Frobenius bound. These are diagnostic finite matrices, not SU(2) quadrature or actual Wilson spectrum. Evidence: TEMP/stardust-ym-1742-exact-tests.py/json.

The next inference was independently challenged. A generic three-state reversible model has psi=(1,1,q), pi=(1,1,q^2)/(2+q^2), b=q^2(1-q^2)/2, e=q^4, P=[[1-b-e,e,b],[e,1-b-e,b],[(1-q^2)/2,(1-q^2)/2,q^2]], lambda=1/4 and K_ij=3 lambda psi_i P_ij/psi_j. The two first states have zero action and the third is the tail. Its centered low-action eigenvector (1,-1,0) has eigenvalue r(q)=1-b-2e tending to1. Nevertheless its native tail mass tends to0, the kernel is symmetric and bounded, and its tail row/column envelope a=3 lambda q/2 gives a/lambda=3q/2 tending to0. Thus vanishing operator tails can coexist with a slow mode INSIDE the low-action region. Fifty-seven exact rational positive/reversible instances verify all row sums, detailed balance, the eigen-equation, kernel bounds and tail-norm estimate; four Lean algebra/limit checks supplement them. This is NOT a Wilson-slab counterexample or a theorem ruling out its local mixing. It identifies the precise missing mechanism. Evidence: TEMP/stardust-ym-1742-local-slow-tests.py/json and1742-checks.lean/log.

Verification: complete7103-job root build PASS in106.4854141s; canonical COMPLETE transitive safe-Foundation axiom audit PASS for57654 declarations in74.5692274s, only propext/Classical.choice/Quot.sound. All18 public types(16 theorems,2 definitions), all FOUR complete saved sources, the private weighted-integrability helper and both private probability instances were reviewed unabridged. Fifteen independent Lean checks PASS in41.1047141s; complete persisted Foundation/AxiomAudit PASS in72.5867440s. Default resources/trust/toolchain/compiler/cache settings are unchanged. Scalar-domain, pointwise-function and positive-norm cancellation elaboration repairs did not weaken any mathematical hypothesis or suppress any error.

Authenticated integrity covers2885 recursive Foundation/root sources: only these FOUR new localization modules, root imports and persisted audit entries differ from the exact approved1741 manifest. Three pinned configurations,113 baseline original files,21 Yang-Mills originals(20 distinct hashes), all older mathematics and the committed six-plaquette probe remain byte-identical. ResearchSources remains read-only/uncommitted. No manuscript/PDF/publication directory, editorial README, queue, reflection accounting or preserved master change. Classical measure transport/Cauchy--Schwarz/cutoff arguments are reused without a novelty claim.

NEXT bottleneck: quantitative control of the compressed low-action operator in the ACTUAL quotient/temporal geometry. Exact twelve-Haar to seven-tree/five-chord transport, residual root conjugation and temporal integration, the correct kinetic metric, shrinking-scale Gaussian or resolvent comparison, and possible low-action slow modes require proof. The current fixed-threshold estimates do not control the fluctuation scale. Do not infer a physical mass gap, coupling-dependent physical distance contraction, reflection positivity, large-volume uniformity or infinite-volume/continuum existence. Preserve every earlier raw-coercivity and finite-surrogate obstruction. Exact approval, guarded secret scan/two-branch PUBLIC sync and independent remote checks remain closure gates; this pre-commit record does not assert an unobserved remote success. Visibility is controlled exclusively by the user.


## Checkpoint1743 — exact original-tree/reduced-chord Haar law and native Wilson domains

Focused Yang-Mills remains ACTIVE. Checkpoint1742 dad850274f3530f3cf2545e6f9b98c74089ef6f7 passed exact approval and terminal guarded PUBLIC synchronization at2026-10-29T22:58:29.141542UTC. Independent fresh remote reads at22:58:43.558540UTC verified BOTH authorized refs at that commit, PUBLIC visibility, preserved master and a clean tracked worktree; see TEMP/stardust-ym-1742-remote-check.json. Its genuine full-native L2 localization/compression estimate is preserved. The concrete remaining reduction was an actual Haar change of variables, rather than assuming a field-dependent gauge preserves product Haar.

That reduction is now PROVED. The useful simplification is to KEEP the seven original tree-link variables, not first replace them by anchored vertex-gauge variables. Foundation/CubeHaarSplit.lean splits the actual twelve-edge index set by chordLabel=none, using Mathlib's measurable finite-Pi equivalence and its proved measurePreserving_piEquivPiSubtypeProd. TreeState carries actual seven-link product Haar and RawChords the complementary product Haar. indexedChord/readChords and a verified finite-index equivalence identify the latter with the five specified actual chord edges. split_preserving and readChords_preserving preserve the normalized measures. rawState_tree/rawState_chord give exact readback. rooted_tree_only proves the actual rooted gauge depends ONLY on those original tree links. No Haar invariance under an unproved field-dependent map is used.

Foundation/CubeReducedHaar.lean proves the actual reduced coordinate map measurable. For each FIXED tree configuration t, conditional_formula writes its ith reduced chord as R_t(source_i) c_i R_t(target_i)^-1. The five raw c_i are distinct independent Haar variables. Actual left/right Haar invariance and measurePreserving_pi prove conditional_preserving for EVERY t. Mathlib MeasurePreserving.skew_product, with joint measurability checked, then proves joint_preserving:
  (U -> (originalTree(U),reduced(U))) pushes boundaryHaar EXACTLY to treeHaar product chordHaar.
The marginal reduced_preserving pushes the original twelve-link Haar EXACTLY to five independent SU(2) Haar chords. integral_reduced transports arbitrary measurable real observables, including integrable unbounded ones. This is a genuine probability/measure theorem, not merely an algebraic reconstruction, marginal heuristic or numerical change of coordinates.

Foundation/CubeChordTransfer.lean connects this law to the ACTUAL gauge-averaged homogeneous Wilson slab. axial_measurable checks the section. kernel_reduced proves K_beta(U,V)=K_beta(axial(reduced U),axial(reduced V)) using the EXISTING actual endpoint gauge invariances and reconstruction. The kernel on the right STILL CONTAINS the full eight-temporal-link Haar integral. This does not permit the forbidden replacement of the raw Wilson weight by its restriction to both axial endpoints, nor removal of temporal variables. function_reduced proves actual positive grounds psi(U)=psi(axial(reduced U)). normalizer_chords proves the exact native Z=integral_chordHaar psi(axial q)^2: the original tree integration has normalized gauge volume one, with no guessed Jacobian or missing prefactor.

native_integrable_iff proves, for every measurable chord observable f, native Integrable(f o reduced) iff Integrable(psi(axial q)^2 f(q)) against chord Haar. native_memLp_iff proves the corresponding FULL native L2 domain iff Integrable(psi(axial q)^2 f(q)^2). These are genuine domain equivalences, not statements inferred from equality of total Bochner integrals. native_integral_chords gives its exact native square-ground integral divided by Z. eigen_chords transports the actual constructed positive eigen-equation to five Haar chords. transition_chords expresses the ACTUAL native transition integral of f(reduced V) as the five-chord integral with K_beta(axial(reduced U),axial r), psi(axial r), and denominator lambda psi(axial(reduced U)). These formulas hold for any actual GroundData(beta); the relevant integrability domains are separate explicit theorems. No spatial Gibbs law or assumed ground is substituted.

Sixteen independent Lean checks passed. They verify seven/five index cardinalities by kernel-checked finite computation, rooted tree independence, conditional/joint/marginal pushforward equalities, unbounded Haar integrability transport, measurable-event probabilities, actual positive reduced normalization, native L1/L2 domains, a derived exact native L2 norm identity, the actual ground eigen-equation and transition formula, kernel symmetry, and simultaneous root-conjugation invariance of psi(axial q). The last test constructs the actual constant vertex gauge on the axial section. It guards against silently treating the five group-valued chords as individually gauge invariant. Residual conjugation is retained; the singular vacuum orbit does not justify subtracting three Gaussian dimensions.

Independent exact noncommutative Q8-subgroup diagnostics use the ACTUAL twelve edges, seven tree edges, five ordered chords and six ordered plaquette words. Thirty-two tree configurations verify tree-only rooted products and inverse reconstruction. All160 conditional one-coordinate maps are permutations. For two distinct original-tree configurations, exhaustive enumeration of8^5 raw chord states gives65536 joint states: the reduced maps are bijective, and the ACTUAL ordered-face action agrees pointwise with the axial action. Their action histograms agree exactly: counts by action0,2,3,4,5,6,7,8,9,10,12 are1,90,480,2895,7200,11436,7200,2895,480,90,1. A SEPARATE rank-one probe psi=2^(-action) has identical exact weighted sums and native mean in both enumerations: sum psi^2=599657633/16777216 and mean first-chord defect=375640418/599657633. This probe is not the actual Wilson ground and the subgroup is not continuous SU(2) Haar. The continuous theorem is the Lean proof above. No actual Wilson spectrum or temporal integral quadrature is claimed. A test-only late-bound generator initialization was corrected before successful enumeration. Evidence: TEMP/stardust-ym-1743-independent.py/json.

Verification: complete7106-job root build PASS in60.4509675s; canonical COMPLETE transitive safe-Foundation audit PASS for57695 declarations in88.7582759s, only propext/Classical.choice/Quot.sound. All33 public types(19 theorems,7 definitions,4 abbreviations,3 probability instances), THREE complete final sources, FOUR private helper proofs and TWO private definitions were reviewed unabridged. Sixteen independent Lean checks PASS in48.6114579s; complete persisted Foundation/AxiomAudit PASS in77.6619497s. Explicit Pi coordinate actions/product arguments resolved elaboration; native L2 square-integrability needed an explicit stationary measure. No mathematical premise was weakened, resource setting raised, error suppressed or toolchain/trust/compiler/cache configuration changed. Finite decisions use decide +kernel, never native_decide.

Authenticated integrity covers2888 recursive Foundation/root sources: only these THREE new exact Haar/native-reduction modules, root imports and persisted audit differ from the exact approved1742 manifest. Every older mathematical source, three pinned configurations,113 baseline originals,21 Yang-Mills originals(20 hashes) and the committed six-plaquette probe remain byte-identical. ResearchSources remains read-only/uncommitted. No manuscript/PDF/publication artifact, editorial README, queue, reflection accounting or preserved master changes. The construction reuses classical product-Haar and skew-product facts; no novelty claim is made.

The fixed-cell operator can now be studied on the correct five-chord Haar integration domain with actual native density and temporal integration intact. This closes the specific measure-transport bottleneck left in1740–1742. It does NOT give a local Gaussian approximation, polynomial eigenvalue normalization, shrinking-threshold control, low-action mixing or a uniform spectral gap. NEXT substantive question: quantitatively control the actual temporal Haar integral near the flat orbit and identify its correct kinetic quadratic form in these coordinates, or prove a sharper native normalization/tail bound that makes such a comparison legitimate. Preserve residual simultaneous conjugation. Do not promote the tentative curl-rank/eigenvalue/oscillator diagnostics to actual operator convergence. Larger-volume soft modes, coupling-dependent physical distance, reflection positivity/positive transfer, continuum and infinite-volume constructions remain independent obligations. Keep all prior raw-coercivity and slow-surrogate counterexamples, including1742's low-action slow-mode model. Exact approval, guarded secret scan/two-branch PUBLIC synchronization and independent remote reads remain closure gates; this pre-commit entry does not claim unobserved backup success. Visibility remains user-controlled.


## Checkpoint1744 — actual slab Hessian, attained temporal elimination, and the correct generalized modes

Focused Yang-Mills remains ACTIVE. Checkpoint1743 34412f70664e6f4cb6f0df10a2d6304ac590e1bd closed exact approval/guarded PUBLIC synchronization at2026-10-29T23:18:12.552550UTC; independent fresh reads23:18:19.990052UTC verified BOTH refs, PUBLIC visibility, preserved master and a clean tracked worktree. Evidence: TEMP/stardust-ym-1743-remote-check.json. Its exact original-tree/five-chord Haar transport and native L1/L2 domains are retained. This checkpoint tackles the next concrete kinetic bottleneck, not a replacement research campaign.

The theorem-level reuse audit distinguished several different objects. FiniteSchoenberg.entrywise_exp_psd is an existing genuine finite-matrix positivity result, but no all-L2 integral-kernel positivity bridge for the actual stationary slab was inferred from it. YMReflectionPositiveShift.reflected_psd concerns its specified exp(-abs(time)) reference covariance, not the actual gauge kernel. FourCubeFullHaarGaussianLimit and FourCubeFullChartQuadratic explicitly use completedQuadratic=nativeQuadratic+diagonalQuadratic and a cutoff; their actual statements remain correct, but that extra completion and their different block geometry prevent direct substitution for the unmodified homogeneous slab. The pursued route reuses SU2FourWordVariation.action_hasDerivAt, actionSlope_hasDerivAt, signed_slope_second_zero and actual exponential-membership results to identify the correct slab second variation first. Existing Schur-completion ideas are applied with the actual new incidence matrices; no old pinned Hessian or Gaussian law is silently relabeled.

Foundation/CubeSlabSecondVariation.lean constructs actual SU(2)-valued exponential rays logState(X,t) and logGauge(Z,t), with Pauli generators normalized exactly as the existing library. For all original twelve-link velocities X,Y and all eight-vertex velocities Z, ray(X,Y,Z,t) is the ACTUAL halfAction of those fields. second_variation proves
  deriv(deriv ray)(0)=spatialQuadratic(X)/8+spatialQuadratic(Y)/8+temporalQuadratic(X,Y,Z)/4,
where spatialQuadratic is the six-face sum of lengthSq(curl X), and temporalQuadratic is the twelve-edge sum of lengthSq(X_e-Y_e+Z_target-Z_source). The spatial coefficients include the TWO required shared boundary half weights. This is an equality of derivatives of the actual group-valued action, not a guessed quadratic model. In particular, its effective coefficient in a Taylor expansion would be ONE HALF this Hessian, not the Hessian itself. A uniform Taylor estimate or integral-limit interchange is NOT asserted here. constant_gradient and temporal_constant_shift prove the three constant vertex-velocity directions are exact zero modes of the temporal QUADRATIC form.

Foundation/CubeTemporalSchur.lean verifies the actual finite geometry before elimination. edgeEnum bijects the twelve actual edges; vertexEnum lists the seven non-root vertices. Certified D is the anchored graph gradient, B inserts the SAME five chord velocities as the verified axial Haar section, and C is the actual six-face curl of that section. Exact rational certificates verify the pinned Laplacian inverse, response, residual orthogonality, kinetic/spatial Gram matrices and the generalized mode data; they are checked in Lean's kernel, then transported to real matrices through the rational ring homomorphism. Python-generated entries are candidates until these proofs succeed, not numerical premises.

Writing A for responseMatrix and R=B+D A, response_exact, orthogonal_exact and metric_exact prove D^T R=0 and W=R^T R. completed_square proves for EVERY real five-vector x and seven-vector z:
  normsq(Bx+Dz)=x^T W x+normsq(D(z-Ax)).
Both minimum_attained and energy_lower_bound follow with exact normalization. The kinetic matrix W is NOT the identity. Its rows, multiplied by24, are
  [10,-2,-4,1,-1];[-2,10,-4,-5,5];[-4,-4,10,5,-5];[1,-5,5,10,-4];[-1,5,-5,-4,10].
Ignoring this metric and diagonalizing the raw chord curl Gram in ordinary Euclidean coordinates would solve a different quadratic problem.

The model is explicitly tied back to ACTUAL velocities. temporal_component identifies every original edge component with Bx+D anchor(Z), where anchor(Z)_v=Z_v-Z_root. temporal_energy_actual gives the three-color sum of these scalar energies, and temporal_actual_lower supplies its exact lower bound. fillGauge/anchor_fill realize every seven-relative-vertex velocity vector by an actual eight-vertex field with root zero. temporal_actual_minimum therefore attains the lower bound in the ACTUAL gauge-velocity space, rather than merely in an unrelated scalar surrogate. Other representatives differing by a constant remain available; no constant mode is discarded or assigned a spurious Gaussian inverse.

curl_component, spatial_exact and spatial_energy_actual identify H=C^T C with the ACTUAL axial spatial Hessian. generalized_exact proves W M=H. mode_diagonal and mode_basis_inverse give an invertible basis with M S=S diag(4,4,4,6,6) and S S_inverse=I. Thus the former tentative4/6 reference calculation is now an exact verified generalized spatial-to-temporal Hessian decomposition (three scalar modes4 and two6, each with the three color components). These numbers are NOT eigenvalues of the actual native stationary Markov transfer operator. No Gaussian spectral ratio, physical mass gap or nonlinear contraction follows from this finite-matrix identity alone.

The main bridge is second_variation_axial_lower and second_variation_axial_minimum. For all actual axial boundary velocities x,y, minimizing over ACTUAL temporal vertex velocities gives the attained effective Hessian
  sum_color(x^T H x)/8+sum_color(y^T H y)/8+sum_color((x-y)^T W(x-y))/4.
The full identity is a rigorous starting point for a properly normalized kernel comparison. It keeps the temporal gradient and the residual global symmetry; it does not substitute the raw weight at identity temporal links for the actual integrated kernel.

Eighteen independent Lean checks passed, covering the actual second variation, constant gradients/shifts, the completed square, attained scalar and actual-vertex minima, derived kinetic nonnegativity, actual edge/curl identifications, all three colors, generalized modes and inverse basis, the full two-boundary attained Hessian, and its zero/constant-velocity consequences. Independent Fraction tests use64 unrelated rational input/vertex configurations and verify the actual anchored edge gradients, full Schur square identity, attained minimum, W M=H and the mode basis/inverse. Independently coded quaternion exponentials for three noncommuting original X/Y/Z configurations test the ACTUAL six spatial faces and twelve temporal words. Central second differences at t=1/32,1/64,1/128 converge with approximately quadratic errors; final errors are.0005153805,.0005371215,.0007762350. The predicted Hessians are23.16613839,28.12608737,35.53774235. Numerical checks are corroboration, not substitutes for Lean derivatives.

A useful limitation is independently visible: Z->Z+c preserves the exact Hessian, but the ACTUAL finite-t nonlinear ray values generally change (differences at t=.2 were.0075012584,.0000035002,-.0008595176). Therefore constant-shift invariance of the quadratic form must not be promoted to an unproved nonlinear identity in logarithmic coordinates. This is not a contradiction to exact group gauge invariance. Evidence: TEMP/stardust-ym-1744-independent.py/json; exact matrix candidates and finite-geometry generation in1744-matrices.py/json and eigenbasis.py.

Verification: complete7108-job root build PASS in36.4578738s; canonical COMPLETE transitive safe-Foundation audit PASS for57786 declarations in75.0031131s, only propext/Classical.choice/Quot.sound. All49 public types(24 theorems,23 definitions,2 abbreviations), BOTH complete saved sources, SEVENTEEN private helper proofs, SIXTEEN private definitions, ONE private row abbreviation and ONE private finite-vertex equality instance were reviewed unabridged. Eighteen independent Lean checks PASS in26.7533391s; complete persisted Foundation/AxiomAudit PASS in48.3374077s. Early inverse-coercion, finite-function/sum and vector-index elaboration errors, including one default-heartbeat inference timeout, were repaired by actual SU2 inverse equalities, explicit derivative arguments, typed sums and standard vector head/tail lemmas. No resource limit was raised, hypothesis weakened, error suppressed, native_decide used or toolchain/trust/compiler/cache setting changed.

Authenticated integrity covers2890 recursive Foundation/root sources. Only these TWO new actual-Hessian/Schur modules, root imports and persisted audit differ from the exact approved1743 manifest. Every older mathematical source, three pinned configurations,113 baseline originals,21 Yang-Mills originals(20 distinct hashes) and the committed six-plaquette probe remain byte-identical. ResearchSources stays read-only/uncommitted. No manuscript/PDF/publication artifact, editorial README, queue, reflection accounting or preserved master changes. This reuses classical finite jet and Schur mathematics with exact actual-slab identification; no novelty claim is made.

NEXT rigorous gap: the actual temporal Haar integral, not another reference eigencalculation. The identity-temporal Hessian does not by itself justify integration over the full constant-gauge critical orbit, a uniform rescaled Taylor bound, domination/off-cutoff estimates, polynomial native eigenvalue normalization or native operator-norm/resolvent convergence. An exact root/relative temporal-Haar split and justified residual-conjugation averaging may be needed before a21-relative-variable Laplace comparison; the three global gauge directions and singular boundary-vacuum orbit remain explicit. The beta^-18 normalization suggested by dimension bookkeeping remains UNPROVED. Native shrinking-scale tightness and low-action mixing remain open, as do actual operator PSD/reflection positivity, larger-volume soft modes, physical-distance/coupling scaling and continuum/infinite-volume existence. Retain1742's low-action slow-mode counterexample: a correct local reference and small operator tails are not a completed mass-gap argument. Exact approval, guarded secret scan/two-branch PUBLIC sync and independent remote checks remain closure gates; this pre-commit entry does not claim unobserved backup success. Only the user controls visibility.


## Checkpoint1745 — polynomial actual Haar ground normalization and shrinking native action windows

Focused Yang-Mills remains ACTIVE. The preceding actual-Hessian/attained-Schur checkpoint1744,85ea7cafe0f52efd0359fb4dde52f6011891334a, closed guarded PUBLIC synchronization at2026-10-29T23:55:24.841831UTC; independent fresh reads23:55:55.425302UTC verified BOTH mathematical refs, PUBLIC visibility, preserved master and clean tracked state(TEMP/stardust-ym-1744-remote-check.json). Its correct kinetic Hessian is retained. This checkpoint addresses the actual integrated-kernel normalization and shrinking-tail bottleneck; it does not compute a reference spectrum or resume another campaign.

Foundation/SU2HaarSmallCap.lean uses the verified ACTUAL hemisphere pushforward and integrable chart density, not an asserted Gaussian approximation. Set cap(t)={U: defect(U)<=3t^2} and alpha=1/(4*pi^2). mass_lower proves p(t)=Haar.real(cap(t))>=alpha*t^3 for0<=t<=1. A Lebesgue coordinate box[-t,t]^3 maps into this cap; its volume is8t^3 and the actual density is at least1/(32*pi^2) there. The constant is only integrated on this finite box, not incorrectly assumed globally Lebesgue integrable. chart_defect_upper is a global exact bound. No asymptotic measure substitution occurs.

Foundation/CubePolynomialGround.lean defines boundaryBox by ALL FIVE REDUCED chords in cap(t). CubeReducedHaar.reduced_preserving gives its exact boundary-Haar mass p(t)^5; the eight-vertex temporalBox has exact Haar mass p(t)^8. The actual fully gauge-averaged kernel reduction CubeChordTransfer.kernel_reduced is essential: original boundary links need not lie in small caps. For axial reduced endpoints and capped temporal links, exact group-defect inequalities give each spatial action<=648t^2, temporal action<=1296t^2, and ACTUAL halfAction<=1944t^2. Restriction of the genuine temporal Haar integral therefore gives kernel_block:
  K_beta(U,V)>=p(t)^8*exp(-1944*beta*t^2), for U,V in boundaryBox and beta>=0.
The positive-block theorem for the actual positive ground then yields eigenvalue_cap_lower:
  lambda_beta>=p(t)^13*exp(-1944*beta*t^2).
Writing C=alpha^13*exp(-1944)>0, eigenvalue_polynomial proves lambda_beta>=C*t^39 whenever0<t<=1, beta>=0, beta*t^2<=1. This applies to EVERY actual GroundData beta, including the existing constructed ground. Its native stationary law remains psi^2/normalizer times boundary Haar; no Gibbs stationary law was substituted. The exponent39 is deliberately nonsharp: all EIGHT temporal links were restricted, including the three global constant-gauge directions. No beta^-18 normalization is claimed.

Foundation/CubeLogWindow.lean takes beta=1/t^2 and w(t)=80t^2*log(1/t). window_nonnegative and window_tendsto_zero prove the precise shrinking window for0<t<=1, with a genuine real limit at0. The exact exponential identity exp(-beta*w(t)/2)=t^40 and the polynomial lower bound give eigenfactor_window<=C^-1*t. input_tail and output_tail hold for EVERY class of the actual stationary native L2 space. compression proves
  norm(P_beta f - low_w(P_beta(low_w f))) <=(2/C)*t*norm(f).
compression_tendsto_zero is convergence of these actual error NORMS uniformly for arbitrary unit-bounded dependent choices F(t) in the varying native spaces. It does not identify distinct Hilbert spaces or assert convergence to a Gaussian operator. stationary_tail additionally proves the actual psi-squared stationary probability of action>=w(t) is at most(C^-1*t)^2; stationary_tail_tendsto_zero proves that probability tends to zero. This last result reuses CubeGroundMass.action_tail_eigenfactor with a separate exponential-square identity, retaining the actual ground-data domains.

Equivalently for beta>=1, the proved scale is w=40*log(beta)/beta, the conservative eigenvalue lower power is beta^(-39/2), and the operator error is bounded by(2/C)*beta^(-1/2). These are algebraic readings of the t-parameter theorems, not additional formal beta-to-infinity declarations. The corresponding angle window has the extra sqrt(log(beta)) factor. Thus this is genuine shrinking-action concentration/localization, but NOT tightness in a bounded rescaled Gaussian-radius ball. The constant is extremely poor(log C approximately-1991.7848); no practical finite-coupling effectiveness, sharp asymptotic, physical correlation length or mass gap is asserted.

Independent tests:42 exact Fraction-valued noncommuting SU(2) cases test actual six-face and twelve-temporal-word action bounds and endpoint gauge covariance. In36 gauge-transformed cases, some original boundary links leave the raw caps while the reduced chords remain capped, directly checking the indispensable distinction between reduced and raw restrictions. Twelve numerical cap-mass checks use the independently integrated actual chart density;99 log-domain checks verify the window exponents and scalar majorant without underflow of exp(-1944). They do not estimate actual ground eigenvalues or operator spectra. Evidence: TEMP/stardust-ym-1745-independent.py/json. Twenty independent Lean applications include cap positivity, actual block masses and kernel, the CONSTRUCTED native ground lower bound, arbitrary-ground input/output localization, derived unit-ball compression, error-norm convergence on dependent native spaces, and actual stationary-tail concentration/convergence.

Final-source verification: complete7111-job root build PASS in45.3583800s; canonical COMPLETE transitive safe-Foundation audit PASS for57837 declarations in47.1213401s, accepting only propext/Classical.choice/Quot.sound. All27 public types(21 theorems,6 definitions), all THREE complete saved source files and NINE private helper proofs were reviewed unabridged. Twenty independent Lean checks PASS in28.6436046s; the complete persisted Foundation/AxiomAudit PASS in60.8888199s. Measure unfolding/toReal powers, the natural exponent cast and dependent-parameter rewriting were repaired without changing theorem statements. No sorry, new axiom, native_decide, resource-limit increase, suppressed error or toolchain/compiler/cache change was introduced. The preliminary successful build/audit preceded the added stationary-law consequence and is NOT used to certify final sources; every final gate was rerun.

Authenticated source integrity covers2893 recursive Foundation/root sources. Only these THREE new Haar/ground/window modules, root imports and persisted audit differ from the exact approved1744 manifest; all older mathematical sources, three configurations,113 baseline originals,21 Yang-Mills originals(20 distinct hashes) and the existing six-plaquette probe remain byte-identical. ResearchSources is read-only/uncommitted. No manuscript/PDF/public-exposition work, editorial README, campaign queue or reflection accounting changed. No novelty claim is made. Exact-commit approval, secret scanning, guarded two-branch synchronization and independent post-push reads remain closure gates; this pre-commit entry does not claim unobserved remote success. Visibility remains exclusively user-controlled PUBLIC.

NEXT concrete question: remove the artificial temporal ROOT cap while preserving the actual Haar integral and global conjugation average. The candidate g_v=h_v*c with h_root=1 should require seven relative caps and a free Haar root, potentially replacing p^13 by p^12; this remains UNPROVED until the measure-preserving split and exact noncommuting action identities are verified. A pointwise identity with c=1 is NOT available for arbitrary endpoints. The verified Hessian and present shrinking tails still leave uniform Taylor domination on the critical orbit, local kernel/ground comparison, bounded-radius tightness, actual native operator/resolvent or spectral convergence and low-action mixing open. The earlier low-action slow-mode counterexample remains valid: small tails alone supply no gap. Scale/volume-uniform four-dimensional estimates and continuum/infinite-volume existence remain unresolved; no finite-cell result is promoted to a physical mass gap.


## Checkpoint1746 — retain the temporal root orbit; actual twelve-cap normalization

Focused Yang-Mills remains ACTIVE. Checkpoint1745 dd48fc754ec7731a067524d47dda8b220c31e1f2 closed guarded PUBLIC synchronization at2026-10-30T00:22:19.736804UTC; independent fresh reads00:22:29.435953UTC verified BOTH mathematical refs, PUBLIC visibility, preserved master and clean tracked worktree(TEMP/stardust-ym-1745-remote-check.json). Its polynomial ground bound and native shrinking-window concentration are retained. This checkpoint resolves the artificial three-dimensional root restriction in that lower bound and verifies the exact remaining conjugation average; it does not infer an actual transfer spectrum from a reference Hessian.

Foundation/CubeTemporalRootHaar.lean constructs coordinates on the ACTUAL eight-link temporal Haar space. For root r=(0,0,0), let c=g_r and h_v=g_v*c^-1 at the seven non-root vertices, with anchored(h)_r=1. split_preserving first separates original root and non-root coordinates. Conditional right-Haar preservation and the existing skew-product theorem then prove joint_preserving: g maps to(c,h) with EXACT product law Haar_SU2 times seven independent Haar laws. This is not an assertion that a field-dependent transformation preserves a measure without proof. assemble(c,h)_v=anchored(h)_v*c reconstructs g exactly; assemble_preserving transports the product law BACK to the original temporal Haar law. integral_split gives the actual real Bochner change of variables for measurable observables, with the usual total-integral convention. The independent integrable-observable check also verifies genuine integrability under pullback.

The relative-cap cylinder requires only h_v in cap(t)={U:defect(U)<=3t^2}. cylinder_mass proves its ACTUAL temporal Haar mass is p(t)^7, p(t)=Haar.real(cap(t)); the root is unrestricted. relative_count=7 is checked in Lean's kernel. An independent Lean test proves EVERY constant temporal field g_v=c lies in this cylinder for every real t, including roots far from identity. Thus no positive-mass global orbit is silently replaced by a point or given a spurious Gaussian normalization.

Foundation/CubeRootGround.lean identifies the exact noncommuting action. temporal_word_assemble proves
  temporalWord(U,V,assemble(c,h))=temporalWord(U,gaugeAction(const(c),V),anchored(h)).
halfAction_assemble retains both spatial half-weights and uses the existing actual spatial gauge invariance; weight_assemble follows for all real beta. kernel_root_average proves the FULL actual kernel is the product-Haar integral of the anchored weight with second endpoint conjugated by c. kernel_root_iterated proves the corresponding integral over c of the relative-link integral. Its Fubini step uses actual weight_integrable and assemble_preserving, so it is not a merely formal iterated integral. No claim is made that the anchored integrand is independent of c. The correct global conjugation average is retained for all endpoints and all beta.

The existing verified cap estimates are reused: CubePolynomialGround.axial_link_bound is now public with its original proof and exact type; action_cap_upper is a public wrapper around its existing private spatial and temporal estimates. No earlier theorem hypothesis or result is changed. Conjugation preserves link defect, so if both axial boundary fields are capped, action_cylinder_upper proves the same ACTUAL halfAction<=1944t^2 on the seven-relative-cap cylinder, uniformly for every root c. Restricting the genuine temporal integral gives
  K_beta(U,V)>=p(t)^7*exp(-1944*beta*t^2)
on the ACTUAL reduced five-chord boundary block. Original boundary links still need not be capped; the previously proved kernel_reduced transport remains essential.

Combining this with boundary-block Haar mass p(t)^5 and the actual positive-ground block theorem proves eigenvalue_cap_lower:
  lambda_beta>=p(t)^12*exp(-1944*beta*t^2).
Let alpha=1/(4*pi^2) and C_root=alpha^12*exp(-1944)>0. eigenvalue_polynomial proves
  lambda_beta>=C_root*t^36 whenever0<t<=1,beta>=0,beta*t^2<=1.
Thus at beta=1/t^2 it proves the beta^-18-SCALE LOWER BOUND suggested earlier by dimensional bookkeeping, now for the genuine integrated kernel and actual constructed positive ground, not an assumed Gaussian model. This is NOT a matching upper bound, a sharp prefactor, a full Laplace asymptotic, ground-function convergence or a spectral-gap theorem. The conservative action constant remains1944 and the constants are not practically sharp.

The actual native operator bridge is also verified. At the EXISTING window w(t)=80t^2*log(1/t), eigenfactor_window bounds exp(-beta*w/2)/lambda_beta by C_root^-1*t^4. compression yields the full native-L2 estimate
  norm(P_beta f-low_w(P_beta(low_w f))) <=(2/C_root)*t^4*norm(f)
for every actual GroundData(1/t^2) and EVERY native L2 class f. stationary_tail bounds the ACTUAL psi-squared stationary probability of action>=w by(C_root^-1*t^4)^2. These improve1745's O(t) operator and O(t^2) probability estimates to O(t^4) and O(t^8) on the same shrinking action window. They still do not give tightness inside bounded rescaled Gaussian-radius balls; the logarithmic window remains. The earlier genuine convergence statements remain valid; no unidentified common Hilbert space is assumed.

Independent tests in TEMP/stardust-ym-1746-independent.py/json use288 exact noncommuting Fraction quaternion configurations with arbitrary Q8 and rational roots. Reconstruction, conjugation defect preservation, the exact assembled action identity and uniform1944t^2 bound all pass. In204 cases some raw temporal links lie OUTSIDE the caps; in240 cases fixing the root to identity changes the exact pointwise halfAction. These are explicit tests of the invalid pointwise simplification, not claims of an integrated spectral obstruction. Twenty-two independent Lean checks cover actual joint and inverse Haar transports, integrable pullback, integral identity, seven-coordinate cardinality/mass, arbitrary constant-root membership, noncommuting word/full-action identities, genuine product and iterated kernel integrals, cap-cylinder action bound, actual kernel block and positive ground lower bound, its application to the CONSTRUCTED ground, and all-native-L2 compression/actual stationary probability estimates. No Monte Carlo or numerically inferred Haar law is used as a proof premise.

Final verification: complete7113-job root build PASS in26.7417967s; canonical COMPLETE transitive safe-Foundation audit PASS for57908 declarations in44.5873200s, allowing only propext/Classical.choice/Quot.sound. All46 new/exposed public types(30 theorems,10 definitions,4 abbreviations,2 probability instances), BOTH complete new sources, the entire modified CubePolynomialGround source, SIX private helper proofs across these files and TWO private local finite/equality instances were reviewed unabridged. Twenty-two independent Lean checks PASS in31.9466555s; complete persisted Foundation/AxiomAudit PASS in58.8249494s. A root-subtype Fintype instance mismatch was repaired by a coherent explicit local instance; composition and measurable-domain arguments were made explicit. One default-heartbeat inference timeout was repaired by local opacity for the weight and an explicit domain map, not by raising limits. No sorry,new axiom,native_decide,suppressed error,toolchain/compiler/cache/resource change or mathematical hypothesis weakening occurred.

Authenticated integrity covers2895 recursive Foundation/root sources. Relative to approved1745, only these TWO new root-orbit modules, the old cap-bound public interface/wrapper, root imports and persisted audit differ. Every other older mathematical source, three pinned configurations,113 baseline originals,21 Yang-Mills originals(20 distinct hashes) and the six-plaquette probe remain byte-identical. ResearchSources remains read-only/uncommitted. No publication/manuscript/PDF/editorial README, campaign queue or reflection accounting changes. This is classical Haar disintegration and elementary cap mathematics applied with exact actual-slab identification; no novelty claim is made. Exact commit approval, secret scanning, guarded two-ref PUBLIC synchronization and independent post-push checks remain closure gates; this pre-commit entry does not claim unobserved remote success. Visibility remains controlled exclusively by the user.

The next bottleneck is now more precise. Root-Haar splitting and the beta^-18-scale LOWER normalization are no longer missing. What remains is a matched integrated estimate and controlled rescaled local kernel/ground comparison, uniformly in the FREE conjugation parameter and on the relevant fluctuation region. The actual generalized Hessian from1744 is reusable only after retaining this average and the correct boundary half-weight coefficients. Its4/6 generalized modes are not actual transfer eigenvalues. Small action tails do not control mixing within the window; preserve the existing low-action slow-mode counterexample. Native operator/resolvent or spectral convergence, actual PSD/reflection positivity, physically justified coupling-dependent distances, volume-uniform four-dimensional control and continuum/infinite-volume existence remain open. No physical mass gap or continuum claim follows from this finite-cell lower bound.


## Checkpoint1747 — global actual temporal confinement, its raw-gauge obstruction, and a scalar Haar upper reduction

Focused Yang-Mills remains ACTIVE. Checkpoint1746 69f374a385bfb5f29392bd985f724a00351220e9 closed guarded PUBLIC synchronization at2026-10-30T00:38:48.598124UTC; independent fresh metadata/ref reads00:39:05.307198UTC verified BOTH mathematical branches, PUBLIC visibility, preserved master and clean tracked state(TEMP/stardust-ym-1746-remote-check.json). Its actual free-root Haar decomposition and beta^-18-scale LOWER ground bound are retained. This checkpoint attacks the previously missing global domination/upper-normalization mechanism, not a separate research campaign or reference eigencalculation.

Foundation/CubeTemporalConfinement.lean proves a global NONLINEAR estimate on the actual common axial tree. For arbitrary five-chord boundary fields q,r and arbitrary eight-link temporal field g, let T=temporalAction(axialState(q),axialState(r),g), c=g_root and h_v=g_v*c^-1 at the seven relative vertices. The boundaries are unrestricted in size. temporal_tree_word identifies each tree temporal word with the inverse of gaugeAction(g)(1) on that tree edge, because BOTH axial boundary tree links are identity. The existing exact rooted_covariant identity reconstructs h_v^-1 from a tree path of at most three links. Reusing FourCubePinnedCoercivity.defect_triple and positivity of every actual temporal plaquette defect yields relative_defect:
  defect(h_v)<=9*T,
and energy_bound:
  E_relative(h)=sum_seven defect(h_v)<=63*T.
The constants are conservative; no sharpness is claimed. The free root is unrestricted and the estimates are GLOBAL in the relative temporal group variables, not small-coordinate or Hessian inequalities. halfAction_lower retains the two actual shared spatial half-weights:
  (A(q)+A(r))/2+E_relative(h)/63<=halfAction(axial(q),axial(r),g).
weight_bound gives the corresponding global factorized Boltzmann domination for every beta>=0. zero_temporal_constant proves that T=0 forces g to be a CONSTANT group-valued field, with its root value still arbitrary. It does not assume that q,r are independent of this constant or identify the constant with1.

The necessary gauge qualification is formalized, not hidden. flat_temporal_zero proves T(gaugeAction(a)(1),1,a)=0 for EVERY vertex gauge field a. flipGauge is1 at the root and minusOne at the seven other vertices; flip_energy proves E_relative(relative(flipGauge))=14. Consequently no_raw_temporal_coercivity(C) disproves, for EVERY real constant C, the assertion that E_relative(relative(g))<=C*T(U,V,g) holds for ALL original boundary representatives U,V. This is an explicit pure-gauge counterexample in the actual slab, not a surrogate stochastic model. It does NOT contradict the common-axial-tree theorem. It explains why pointwise raw-link coercivity cannot substitute for the verified gauge-averaged reduction.

Foundation/CubeHaarUpper.lean defines the genuine scalar SU(2) Haar integral
  J(s)=integral_SU2 exp(-s*defect(U)) dHaar(U).
For s>=0, laplace_integrable, laplace_pos and laplace_le_one prove actual integrability and0<J(s)<=1. relative_integral, using1746's actual relative-Haar transport and Mathlib's finite-product Bochner theorem, computes the exact seven-variable integral as J(s)^7. Combining this with the GLOBAL temporal domination proves kernel_axial_upper. spatial_reduced and the already verified actual kernel_reduced then transport it to EVERY original boundary field:
  K_beta(U,V)<=exp(-beta*A(U)/2)*exp(-beta*A(V)/2)*J(beta/63)^7.
This final statement is valid for arbitrary original representatives; it does not falsely transport the raw temporal energy bound itself. The full temporal Haar integral and residual global conjugation average remain present.

The spatial estimate is equally actual. CubeAxialGauge.coercive_mod_gauge gives E_chord(reduced(U))<=4*A(U), while CubeReducedHaar supplies the EXACT five-chord Haar law. boundary_integral_upper therefore proves
  integral_boundary exp(-beta*A(U)/2) dHaar(U)<=J(beta/8)^5.
Finally eigenvalue_upper proves for EVERY actual positive GroundData beta and beta>=0:
  lambda_beta<=J(beta/63)^7*J(beta/8)^5.
It integrates the actual positive eigenfunction equation, uses genuine weighted integrability and the positive Haar integral of psi, and cancels that positive scalar. No assumed Rayleigh principle, ground-function asymptotic, Fubini interchange on an uncontrolled domain or new existence axiom is used. The existing constructed ground is an explicit independently checked application.

This is a rigorous scalar-factor UPPER REDUCTION, not yet a matched beta^-18 upper estimate. A verified J(s)<=C*s^(-3/2) estimate would give the matching finite-cell upper power after scaling, but that scalar bound has NOT been established by this checkpoint. Its proof must use the ACTUAL Haar law, e.g. the existing hemisphere chart density with a valid local/exterior split, rather than assuming a Gaussian law or using a false global affine-chart quadratic bound. No upper asymptotic, prefactor, actual spectral gap, physically meaningful contraction distance, volume-uniform estimate or continuum mass gap is asserted.

Independent exact tests in TEMP/stardust-ym-1747-independent.py/json cover96 noncommuting Fraction quaternion configurations with unrestricted boundary chords and temporal fields. Both the individual9*T and total63*T estimates pass; the largest observed E_relative/T was the exact rational46220516640000/54705078467371, not an optimal constant claim. An independently assembled pure-gauge configuration has ACTUAL T=0 and E_relative=14, corroborating the new formal obstruction. Twenty-one independent Lean checks cover actual tree words, global individual/total/action/weight estimates, arbitrary pure-gauge cancellation, the explicit14-energy witness and no-constant obstruction, the surviving zero-action constant orbit, genuine scalar positivity/normalization(J(0)=1), exact relative Haar integral, actual axial AND arbitrary-representative kernel domination, boundary Haar reduction, arbitrary and CONSTRUCTED positive-ground upper bounds, and compatibility with1746's lower bound. They do not numerically estimate a transfer spectrum or assume a radial Haar density formula.

Final verification: complete7115-job root build PASS in29.0833333s; canonical COMPLETE transitive safe-Foundation audit PASS for57953 declarations in48.7062879s, allowing only propext/Classical.choice/Quot.sound. All22 public types(19 theorems,3 definitions), BOTH entire saved sources and SEVEN private helper proofs were reviewed unabridged. Twenty-one independent Lean checks PASS in32.4004959s; complete persisted Foundation/AxiomAudit PASS in50.9035155s. One default-heartbeat inference timeout in the conditional tree bound was repaired by an explicit conditional helper and local opacity for defect; no limit was raised. Explicit defect/action, finite-product, composition and measure arguments repaired elaboration failures without changing mathematical assumptions. No sorry,new axiom,native_decide,suppressed error,toolchain/compiler/cache/resource change or weakened hypothesis was introduced.

Authenticated integrity covers2897 recursive Foundation/root Lean sources. Only these TWO new actual-confinement/upper modules, root imports and persisted audit differ from exact approved1746. ALL older mathematical sources, three pinned configurations,113 baseline originals,21 Yang-Mills originals(20 distinct hashes) and the six-plaquette probe remain byte-identical. ResearchSources is read-only/uncommitted. No manuscript/PDF/publication/editorial README, queue or reflection-accounting changes. The tree-path and Haar-product mathematics is classical; this checkpoint identifies its exact applicability and explicit obstruction for the actual slab, with no novelty claim. Exact-commit approval, secret scanning, guarded two-branch PUBLIC synchronization and independent post-push reads remain closure gates; this pre-commit entry does not claim an unobserved backup success. Visibility stays exclusively user-controlled.

NEXT: establish the scalar Haar Laplace upper estimate using genuine chart/mass bounds, then test a matched integrated-kernel comparison retaining the free-root conjugation. A separate theorem-level reuse audit identified a possible operator shortcut: multiplication f->psi*f/sqrt(Z) should conjugate the actual native operator to K/lambda on boundary-Haar L2, potentially avoiding a prior proof of pointwise ground-FUNCTION convergence. Existing CubeNativeL2Domain.weighted_memLp,weighted_square_integral and ae_iff prove important domain/norm ingredients; GaussianHalfDensityUnitary is a concrete proof pattern, not an already instantiated theorem for this slab. A complete actual all-L2 unitary/operator identity is still UNPROVED here. Any spectral comparison must also map native constants to psi/sqrt(Z) and respect the corresponding orthogonal complement. Existing generalized Hessian4/6 modes are not actual native eigenvalues. Local rescaled domination, operator convergence, low-action mixing, larger-volume soft modes and the continuum/infinite-volume construction remain separate open obligations. Preserve the earlier low-action slow-mode counterexample and all frozen campaigns.


## Checkpoint1748 — actual scalar Haar Laplace control and matched slab normalization powers

Focused Yang-Mills remains ACTIVE. Checkpoint1747 70fa490e542b5285d1aa7cf65435477d6841ce1e closed guarded PUBLIC synchronization at2026-10-30T00:59:00.323682UTC; independent fresh metadata/ref reads00:59:07.978310UTC verified BOTH mathematical refs, PUBLIC visibility, preserved master and clean tracked worktree(TEMP/stardust-ym-1747-remote-check.json). Its global actual relative-temporal confinement, pure-gauge obstruction and scalar-factor kernel/ground upper reduction are retained. This checkpoint resolves the remaining scalar estimate and matches the previously verified normalization LOWER power. It does not infer a mass gap from an unnormalized eigenvalue.

Foundation/SU2HaarLaplaceUpper.lean works with the ACTUAL SU(2) Haar law and J(s)=integral exp(-s*defect(U)) dHaar(U), not an assumed Gaussian distribution. localCut is the measurable set defect(U)<1/4; localCut_subset proves it lies in the positive hemisphere. local_integral transports the exact local real Bochner integral through FourCubeHaarProductCoordinates.chart_map_coordinateLaw and its withDensity formula. The original Haar restriction and indicator are explicit, and the measure is only restricted to its proven hemisphere domain. The complement, including the other hemisphere, is not discarded.

Inside this set, FourCubeHemisphereCoercivity.small_defect_chartRate and coordinates_chart give chartRate(y)<=2. The existing local_defect_lower then gives defect(chart(y))>=(chartRate(y)-1)/4, while the actual density is bounded by chartDensity(0). local_weight_bound proves the resulting domination INCLUDING the cutoff indicator; integrable Gaussian domination establishes the genuine weighted local integrability before applying integral_mono. A global affine-chart quadratic lower bound is neither used nor assumed; the previously verified obstruction to such a bound remains intact.

The three-dimensional Gaussian mass G(a)=integral_R^3 exp[-a*(chartRate(y)-1)/4] is finite and positive for a>0. gaussian_rescale proves G(a/t^2)=t^3*G(a) for t>0, using Measure.integral_comp_smul on the ACTUAL Triple=Fin3->R with finrank3. The older93-dimensional field-rescaling theorem is not misapplied to this space. local_integral_upper and exterior_integral_upper give, for s>0,
  J(s)<=chartDensity(0)*G(s)+exp(-s/4).
The exterior estimate uses actual Haar probability on the ENTIRE cutoff complement, where defect>=1/4. It requires no uncontrolled Gaussian extension there.

exterior_scaled_upper proves for a>0 and0<t<=1:
  exp[-a/(4t^2)]<=(64/a^2)*t^3.
Its elementary proof derives exp(x)>=x^2/4 from Real.add_one_le_exp(x/2), multiplies by exp(-x), and uses t^4<=t^3. No asymptotic exchange or unproved tail hypothesis enters. Define D(a)=chartDensity(0)*G(a)+64/a^2>0. laplace_scaled_upper consequently proves the genuine quantitative bound
  J(a/t^2)<=D(a)*t^3
for every a>0 and0<t<=1. The constants are deliberately conservative; no sharp scalar constant or numerical prefactor is asserted.

Foundation/CubeMatchedGround.lean instantiates a=1/63 and1/8 in the existing actual Haar-factor reductions. Write D_T=D(1/63),D_B=D(1/8),C_upper=D_T^7*D_B^5>0. kernel_upper proves for ALL original boundary representatives U,V:
  K_(1/t^2)(U,V)<=D_T^7*t^21*exp[-A(U)/(2t^2)]*exp[-A(V)/(2t^2)].
The ACTUAL temporal Haar integral, its seven relative variables and the free global root/conjugation average are retained. boundary_integral_upper bounds the actual original boundary-Haar integral of exp[-A/(2t^2)] by D_B^5*t^15, using the verified five-reduced-chord law, not a replacement Gibbs probability.

For EVERY actual GroundData(1/t^2), eigenvalue_upper now proves lambda<=C_upper*t^36. Combining it with1746's actual lower constant C_lower=alpha^12*exp(-1944)>0 gives normalization_bounds:
  C_lower*t^36<=lambda_(1/t^2)<=C_upper*t^36, 0<t<=1.
rescaled_value_bounds proves C_lower<=lambda/t^36<=C_upper. The existing constructed ground is an explicit independently checked application. Thus the formerly conditional beta^-18-SCALE matching upper and lower powers are now established for the genuine integrated slab normalization. The Lean declarations retain beta=1/t^2; reading t^36 as beta^-18 is algebraic reparameterization. This does NOT prove convergence of lambda/t^36, determine its limiting prefactor, prove ground-function convergence or yield an eigenvalue ratio/spectral gap for the normalized stationary operator P. In particular P has its own stationary eigenvalue1, which must not be confused with this lambda of the unnormalized Haar kernel.

Independent diagnostics in TEMP/stardust-ym-1748-independent.py/json use32768-panel deterministic angular Haar quadrature and30 tests over a=1/63,1/8,1 with ten scales each. Haar normalization at zero, scalar/exterior majorants and Gaussian-rescaling diagnostics pass. Ten additional log-domain factor-product diagnostics examine J(1/(63t^2))^7*J(1/(8t^2))^5/t^36; the last logarithm was56.3885418053 at t=1/512. These calculations are NOT a rigorous quadrature-error certificate, an eigenvalue computation or a Lean premise. The formal proof independently uses the actual verified chart law and exact measure identities. Twenty independent Lean checks cover cutoff measurability/hemisphere inclusion, actual Bochner chart transport, finite Gaussian domains/positive masses/scaling, local and FULL exterior bounds, the scalar estimate, arbitrary-original-field kernel bound, original boundary-Haar bound, arbitrary and constructed positive-ground upper/lower/rescaled bounds, a uniform explicit upper constant and consistency of the two constants.

Final verification: complete7117-job root build PASS in27.1083803s; canonical COMPLETE transitive safe-Foundation audit PASS for57991 declarations in47.2770717s, only propext/Classical.choice/Quot.sound. All27 public types(21 theorems,6 definitions), BOTH complete saved sources and FIVE private helper proofs were reviewed unabridged. Twenty independent Lean checks PASS in33.2376423s; complete persisted Foundation/AxiomAudit PASS in61.7703287s. Finrank-argument inference, an indicator's membership argument and elementary additive/reciprocal equality orientations were made explicit. No heartbeat/recursion limit was raised, error suppressed, hypothesis weakened, sorry/new axiom/native_decide introduced or toolchain/compiler/cache/resource setting changed.

Authenticated integrity covers2899 recursive Foundation/root Lean sources. Only these TWO new actual-Haar/matched-ground modules, root imports and persisted audit differ from exact approved1747. ALL older mathematical sources, three pinned configurations,113 baseline originals,21 Yang-Mills originals(20 distinct hashes) and the six-plaquette probe remain byte-identical. ResearchSources remains read-only/uncommitted. No publication/manuscript/PDF/editorial README, campaign queue or reflection-accounting changes. The local Haar/Laplace estimates are classical mathematics with exact actual-slab instantiation; no novelty claim is made. Exact-commit approval, secret scanning, guarded two-branch PUBLIC synchronization and independent post-push checks remain closure gates; this pre-commit entry does not claim unobserved remote success. Visibility is controlled exclusively by the user.

The next actual bottleneck is spectral OPERATOR comparison. The normalized powers now match the rescaled boundary Jacobian: fifteen boundary dimensions plus the kernel's t^21 factor match lambda's t^36. This is a useful structural cancellation, not yet an operator convergence theorem. A fully verified all-native-L2 half-density unitary could identify P with K/lambda on boundary-Haar L2 and avoid requiring a separate prior ground-FUNCTION limit. The needed precise transport, inverse/surjectivity and actual integral intertwining still require proof; reuse CubeNativeL2Domain and existing unitary/operator machinery first. Uniform local kernel convergence must retain the global conjugation average,1744's correct Schur metric and actual shared-half-weight coefficients. Present global confinement and matching normalization may supply domination, but a Hilbert--Schmidt/norm limit, physical mean-zero spectral comparison and actual gap remain UNPROVED. No four-dimensional volume-uniform estimate, physical-distance/coupling scaling, continuum/infinite-volume construction or Millennium mass-gap result follows from these finite-cell bounds. Preserve the pure-gauge/raw-coercivity and low-action slow-mode counterexamples.


## Checkpoint1749 — actual full-L2 ground unitary and literal normalized Haar operator

Focused Yang-Mills remains ACTIVE. Checkpoint1748 20c046cb5b80a153a78fb35e9c539b4776f4af89 closed guarded PUBLIC synchronization at2026-10-30T01:16:13.862200UTC; independent fresh metadata/ref reads01:16:31.216729UTC verified BOTH mathematical refs, PUBLIC visibility, preserved master and clean tracked state(TEMP/stardust-ym-1748-remote-check.json). Its genuine scalar Haar estimates and matched normalization powers remain unchanged. This checkpoint establishes the previously missing ALL-DOMAIN operator bridge, so the actual stationary transfer can be compared through its symmetric Haar kernel without postulating a ground-function limit.

Foundation/CubeGroundUnitary.lean reuses CubeNativeL2Domain.weighted_memLp,integrable_iff,ae_iff and weighted_square_integral. For every ACTUAL GroundData beta, with actual stationary probability pi=psi^2/Z times boundary Haar, transport(f)=psi*f/sqrt(Z) and inverse(F)=sqrt(Z)*F/psi are proved on the FULL real L2 quotient spaces. forward_memLp needs no bounded input. backward_memLp proves the exact inverse domain by multiplying its square by psi^2, cancelling the strictly positive psi and obtaining Z*F^2, which is integrable under actual Haar. The actual positive ground and positive normalizer, not a new measure-equivalence assumption, justify every cancellation and null-set transport.

Forward linearity, both inverse identities and norm preservation are proved using the actual almost-everywhere representatives in their respective measures. unitary is a genuine LinearIsometryEquiv from the native stationary L2 space onto boundary-Haar L2; unitary_coe and unitary_symm_coe identify its actual pointwise representatives. There is no dense bounded-core hypothesis, finite-grid replacement or incomplete observable extension. GaussianHalfDensityUnitary supplied a concrete proof pattern, but its different Gaussian law and raised local options were NOT imported as a generic theorem or copied into this proof. The present domains and normalization are separately verified for this actual slab using its existing weighted-domain machinery.

Foundation/CubeHaarOperator.lean then constructs haarOperator=U*P*U_inverse, where P is the ALREADY CONSTRUCTED actual native stationary operator. rawKernel(beta,F)(U)=integral_V K_beta(U,V)*F(V) dHaar(V). For EVERY Haar L2 class F and EVERY boundary state U, raw_integrable proves genuine integrability of that inner integral from the actual global kernel bound and finite-Haar L2-to-L1 inclusion. raw_measurable,raw_bound and raw_memLp provide the actual measurable L2 output; raw_pairing_integrable proves the outer pairing with every Haar L2 test G is integrable. Thus subsequent identities are not vacuous total-Bochner equalities standing in for missing domains.

inverse_transfer identifies the literal transition integral of every native inverse image. Combining the previously verified ALL-native-L2 operator_kernel_pairing, actual stationary_integral and the exact half-density cancellations proves haarOperator_kernel_pairing:
  inner(haarOperator(F),G)=(1/lambda)*integral_U G(U)*(integral_V K_beta(U,V)*F(V) dHaar(V)) dHaar(U).
normalizedRaw is the actual Haar L2 class of rawKernel/lambda. haarOperator_eq_normalizedRaw proves STRONG equality with that class for EVERY Haar L2 input, using all test vectors. This identifies the transported bounded operator with the literal normalized integrated Wilson kernel, not just an abstract conjugation or a pointwise core formula. The theorem applies to the existing constructed ground as well as every actual GroundData beta. No external existence or mass-gap assertion is assumed.

haarOperator_contraction,haarOperator_symmetric and haarOperator_selfadjoint transfer the verified actual Hilbert-space properties through U. oneClass is the actual native constant-one class; groundVector=U(oneClass) has representative psi/sqrt(Z), norm1, and is fixed by haarOperator. centered_iff proves the EXACT physical centering condition:
  integral f d pi=0 iff inner(U(f),groundVector)=0.
Consequently the relevant Haar complement is the complement of psi/sqrt(Z), not automatically the Haar-mean-zero complement of1. haarOperator_norm proves the FULL operator norm is exactly1 because this normalized stationary vector is fixed. This is not a gap result. The gap concerns its orthogonal complement, and no strictly smaller norm there is asserted. An independent Lean application also checks norm(lambda*haarOperator)=lambda, consistent with its actual unnormalized Haar kernel; this does not compute a second eigenvalue.

Independent diagnostics in TEMP/stardust-ym-1749-independent.py/json use192 exact rational reversible three-state examples with nonuniform stationary weights1/27,1/27,25/27 and ground normalizer9. They check the sqrt(Z) normalization, inverse identities, actual matrix conjugation, weighted norms, kernel pairings and the ground-complement/mean identity. The vector(25,0,-1) is native-centered but has Haar mean8, showing concretely why unweighted constant centering cannot be substituted in that model. These finite models are ONLY independent algebra diagnostics; no actual SU(2) domain, kernel or spectral statement is inferred from them. The actual slab statements are proved in Lean. Twenty-four independent Lean checks cover full-domain forward/backward membership and round trips, isometry, inner/outer actual kernel integrability, self-adjointness/contraction, literal inverse transition, weak AND strong actual normalized-kernel identities, both AE representatives, actual normalized/fixed ground vector, physical centered-space equivalence, norm1 and raw scaling, the actual constructed ground for every real beta, exact native intertwining and invariance of the ground complement.

Final verification: complete7119-job root build PASS in29.7167813s; canonical COMPLETE transitive safe-Foundation audit PASS for58092 declarations in44.5389245s, only propext/Classical.choice/Quot.sound. All44 public types(32 theorems,11 definitions,1 abbreviation), BOTH complete saved sources, THREE private helper proofs and THREE private probability/kernel instances were reviewed unabridged. Twenty-four independent Lean checks PASS in28.1402476s; complete persisted Foundation/AxiomAudit PASS in56.6941004s. Pointwise Pi addition/multiplication, real inner-product and explicit beta arguments were made explicit. A default-heartbeat inference timeout was traced to a missing explicit OPERATOR argument in opNorm_le_bound and repaired by supplying it. No heartbeat/recursion limit was raised, error suppressed, hypothesis weakened, sorry/new axiom/native_decide introduced or toolchain/compiler/cache/resource setting changed.

Authenticated integrity covers2901 recursive Foundation/root Lean sources. Only these TWO new actual-unitary/Haar-operator modules, root imports and persisted audit differ from exact approved1748. ALL older mathematical sources, three pinned configurations,113 baseline originals,21 Yang-Mills originals(20 distinct hashes) and the six-plaquette probe remain byte-identical. ResearchSources stays read-only/uncommitted. No publication/manuscript/PDF/editorial README, campaign queue or reflection-accounting changes. Ground half-density transport is classical mathematics; its exact full-domain instantiation and actual-kernel identification here carry no novelty claim. Exact-commit approval, secret scanning, guarded two-branch PUBLIC synchronization and independent post-push checks remain closure gates; this pre-commit entry does not claim an unobserved backup success. Visibility remains exclusively user-controlled.

NEXT actual bottleneck: a justified rescaled Haar-kernel operator comparison and its PHYSICAL ground complement, not another assumption of ground-function convergence. The new exact unitary removes that prior prerequisite from a norm-based route. The actual five-reduced-chord Haar transport should supply an L2 isometric embedding via compMeasurePreserving; its adjoint may isolate the zero gauge-fiber directions without constructing a broad new gauge library. Reuse existing HilbertRepresentation/adjoint machinery before implementing extra conditional expectations. Then the t^15 boundary Jacobian, t^21 integrated kernel and t^36 actual normalization match, but local kernel convergence, global-conjugation averaging, uniform domination and an actual Hilbert--Schmidt/operator-norm limit still require proof. Present generalized4/6 Hessian modes are not actual transfer eigenvalues. Full norm1 is not a mean-zero contraction estimate, and positivity preserving is not an established positive-semidefinite/reflection-positive operator claim. Preserve the raw pure-gauge and low-action slow-mode counterexamples. Four-dimensional volume-uniform control, physically justified coupling/distance scaling, continuum/infinite-volume existence and a physical mass gap remain open.


## Checkpoint1750 — actual nonlocal temporal remainder is negligible after t^21 normalization

Focused Yang-Mills remains ACTIVE. Prior checkpoint1749 723283c4e85e484e2b745ff8c4f5f9035695c4bf closed guarded synchronization at2026-10-30T01:38:46.050687UTC; independent metadata/ref reads01:39:30.322466UTC verified PUBLIC visibility, BOTH mathematical refs, preserved master and clean tracked state. Its exact full-native/Haar-L2 unitary, literal normalized kernel and physical ground-complement identity are unchanged. The present proof resolves the nonlocal temporal-chart remainder required for a subsequent actual rescaled-kernel comparison; it does not assume or establish the local limiting kernel.

Foundation/CubeTemporalExterior.lean defines localRegion by requiring each of the SEVEN relative temporal variables g_v*g_root^(-1) to have defect<1/4. localRegion_measurable proves actual measurable restriction. assemble_mem proves that every global root c is unrestricted: assemble(c,h) belongs exactly when all seven h_v do. No pointwise c=1 restriction, missing Haar-root integral or arbitrary-raw-boundary confinement is introduced. Exterior and interior are genuine restricted integrals of the ACTUAL Wilson weight on canonically reduced boundary fields. kernel_split transports their sum to the ACTUAL kernel for arbitrary original U,V via the existing exact kernel_reduced theorem. Their integrability comes from the already verified full weight_integrable, not a formal total-integral convention.

On the exterior, one relative defect is at least1/4, hence E_rel>=1/4. Split the global confinement exponent as
  exp(-beta*E_rel/63) <= exp(-beta/504)*exp(-beta*E_rel/126), beta>=0.
This keeps all seven product-Haar Laplace factors while extracting fixed exponential suppression. exterior_upper proves, for EVERY original boundary pair,
  exterior(beta,U,V) <= exp(-beta*A(U)/2)*exp(-beta*A(V)/2)*exp(-beta/504)*J(beta/126)^7.
The envelope is genuinely integrable; relative_integral integrates over actual gauge Haar with the free root retained. A raw temporal confinement claim on arbitrary original representatives remains false, as previously proved; the reduced-coordinate definition is essential.

For beta=t^(-2),0<t<=1, existing genuine SU(2) Haar Laplace estimates give J(beta/126)^7 <= D(1/126)^7*t^21. Thus scaled_exterior_upper proves
  exterior(t^(-2),U,V)/t^21 <= exp(-A(U)/(2*t^2))*exp(-A(V)/(2*t^2))*C*exp(-1/(504*t^2)),
where C=D(1/126)^7>0. The boundary weights survive the stronger estimate. scaled_exterior_polynomial also supplies the boundary-independent modulus C*(64/(1/126)^2)*t^3. All constants are explicit and independent of U,V,t; sharpness is not claimed. The prior scalar exterior O(t^4) estimate alone could NOT justify division by t^21; integrating the preserved seven-factor envelope repairs that exact gap without new high-order exponential machinery.

scaled_exterior_tendsto_zero establishes right-hand t->0 convergence for ARBITRARY boundary families U(t),V(t), with no boundedness, measurability or convergence assumption on those families. The parameter domain and positive denominator are explicit. scaled_kernel_error_tendsto_zero proves that (K_(t^-2)(U(t),V(t))-interior_(t^-2)(U(t),V(t)))/t^21 tends to0. This is an ACTUAL kernel approximation, not an auxiliary Gaussian-measure statement. It licenses replacing the kernel by its local relative-Haar integral when proving a later scaled limit; it does NOT supply that limit, a Hessian spectral identification, or a ground-complement operator contraction.

Independent tests: ten Lean applications check root freedom, fixed energy cost, true restricted integrability, nonnegative kernel error, interior<=kernel, absolute-error identification and the normalized absolute-error limit for arbitrary moving boundaries. TEMP/stardust-ym-1750-independent.py/json separately checks512 exact rational unit-quaternion root/relative reconstructions and exponent inequalities, five arbitrary root choices including nonidentity roots, and100 scalar log-domain decay diagnostics. These are algebra/scaling diagnostics only, not proof premises for actual Haar integration or evidence of an actual transfer spectrum. Lean separately verifies those integral and convergence statements.

Final gates: complete7120-job root build PASS in27.3626949s; canonical COMPLETE transitive audit PASS for58111 safe Foundation declarations in44.1286351s, only propext/Classical.choice/Quot.sound; all16 public types(12 theorems,4 definitions), the entire saved source and its private envelope-integrability helper reviewed unabridged. Ten independent Lean checks PASS in42.6914697s; complete persisted AxiomAudit PASS in59.9030587s. Measurable-set preimage and namespace elaboration were repaired, and the nonnegative convergence lower bound was correctly restricted to positive t. No new axioms/sorry/native_decide, increased heartbeat/recursion, suppressed errors or changed toolchain/resources. Existing style warnings were not suppressed.

Authenticated integrity covers2902 recursive Foundation/root Lean sources, against exact approved1749: only this new module, root import and persisted audit differ. All older mathematical sources,three pinned configurations,113 baseline archive originals,21 Yang-Mills originals(20 distinct hashes) and the six-plaquette probe are byte-identical. ResearchSources remains read-only/uncommitted. No publication/manuscript/PDF/editorial README work, campaign-queue or reflection-accounting changes. This elementary exponential-splitting argument has no novelty claim. Exact-commit approval, history secret scanning, guarded two-branch synchronization and independent fresh public metadata/ref verification remain closure gates; no unobserved remote success is claimed here. Repository visibility is exclusively user-controlled.

NEXT: the nonlocal temporal remainder is now discharged. Prove genuine seven-variable local chart transport/rescaling, actual two-jet convergence retaining the global conjugation average, and an integrable Gaussian envelope for the LOCAL scaled integral. Then seek justified operator-norm/Hilbert--Schmidt convergence using the actual full-L2 unitary and five-reduced-chord Haar geometry. The t^15 boundary Jacobian and t^21 temporal kernel match t^36 normalization, but dimensional matching is not operator convergence. Physical ground projection/complement control, actual spectral contraction, volume-uniform four-dimensional extension, physically justified coupling/distance scaling, continuum/infinite-volume existence and a physical mass gap remain open. Preserve the previous pure-gauge and low-action slow-mode counterexamples; full operator norm1 and generalized Hessian4/6 modes remain distinct from the required mean-zero spectral estimate.


## Checkpoint1751 — actual local relative-Haar kernel, exact scaling and a uniform integrable envelope

Focused Yang-Mills research continues. Prior checkpoint1750 7202c902b19b57c036cb2b90d06472aa3a6fd497 closed guarded synchronization at2026-10-30T01:56:39.521487UTC; independent fresh metadata/ref reads01:56:48.864206UTC verified PUBLIC visibility,BOTH mathematical refs,preserved master and clean tracked state. Its actual exterior/t^21 vanishing theorem is unchanged. This checkpoint constructs the missing LOCAL integral representation and uniform domination needed to justify a later actual kernel limit. No Gaussian limit or physical spectral gap is assumed.

Foundation/CubeRelativeChart.lean instantiates the existing verified scalar Haar hemisphere transport for the ACTUAL seven relative variables. Field=RelativeIndex->Triple has finrank21, proved using relative_count and Mathlib finite-product linear algebra. chartField_map transports the product coordinate law to the actual relativeHaar restricted to its seven-fold hemisphere. density(Y)=product_v chartDensity(Y_v) is measurable, nonnegative and integrable; chartLaw_density proves the genuine withDensity identity by finite-product measure uniqueness, reusing the scalar density and integral facts. The older31-link/93-dimensional cell theorem is not misapplied to this geometry. integral_local retains the stricter defect<1/4 cutoff in every link and proves its exact integral identity; integral_rescale proves the absolute Jacobian |t|^21 for every nonzero real t. Generic measurable-observable Bochner identities are distinguished from the actual integrability proved below.

Foundation/CubeLocalKernel.lean constructs the ACTUAL local scaled integrand. mass(Y)=sum_v(chartRate(Y_v)-1), exactly the sum of21 coordinate squares. local_energy_lower proves mass/4<=E_rel ONLY on the actual cutoff. Together with the earlier global temporal confinement, nonnegative boundary actions and the exact root/relative assembly, scaled_action_lower proves mass(Y)/252 <= t^(-2)*halfAction for EVERY pair of axial boundary chords, EVERY global root c, and every NONZERO real t satisfying the cutoff. No Hessian of a modified/completed action is substituted for the nonlinear slab.

scaledDensity(t,U,V,c,Y) is the actual product density at tY times the actual Wilson weight at beta=t^(-2), restricted by the actual seven-relative cutoff, with original boundaries U,V canonically reduced as required by the confinement theorem. Joint measurability in(c,Y), fixed-root measurability and nonnegativity are proved. The exact bound
  0<=scaledDensity(t,U,V,c,Y)<=rho(0)^7*exp(-mass(Y)/252), t!=0,
is UNIFORM in arbitrary original U,V, the root c and nonzero t. gaussian_integrable proves the envelope is genuinely integrable on the21-dimensional Euclidean field using existing scalar Gaussian integrability. scaledDensity_integrable proves the fixed-root domain for EVERY c; scaledDensity_joint_integrable proves the joint domain under actual Haar(c) times Euclidean volume. The cutoff is essential; no false global affine-chart quadratic bound is introduced.

interior_root_iterated uses actual measure-preserving root/relative assembly and genuine joint integrability before Fubini. interior_root_chart then transports the exact local actual kernel to the coordinate density, preserving all seven cutoff factors. interior_scaled and interior_scaled_joint establish, for t>0,
  interior(t^-2,U,V)/t^21 = integral_c integral_Y scaledDensity(t,U,V,c,Y)
                        = integral_(c,Y) scaledDensity(t,U,V,c,Y).
The root remains a full Haar average. No c=1 shortcut, missing density factor, extra root Jacobian or unverified domain substitution is present.

kernel_limit_of_local_limit is an explicitly CONDITIONAL bridge. For arbitrary boundary families U(t),V(t), if the actual scaledDensity converges almost everywhere on Haar(c) times Euclidean(Y) as t->0+ to L(c,Y), then the actual full kernel divided by t^21 converges to integral L. The proof verifies every dominated-convergence hypothesis using the constructed uniform envelope and then restores the exterior using checkpoint1750. This theorem does NOT assert that the pointwise limit exists, identify L with an actual Hessian Gaussian, or establish operator-norm/spectral convergence. Its precise outstanding premise is the local pointwise density limit. No measurability or convergence assumption on the parameter-indexed boundary families is hidden; each fixed-parameter joint integrand is measurably constructed independently.

Independent checks:16 Lean applications verify dimension/cardinality, the sum of21 squares and the constant-field mass7*a^2, actual product density, local hemisphere containment, envelope integrability/positive Gaussian mass, nonlinear bound with its exact domain, joint and fixed-root integrability, true Fubini/scaling, absolute domination and the conditional actual-kernel implication. TEMP/stardust-ym-1751-independent.py/json tests512 configurations using the actual12 temporal edges and six spatial plaquette quaternion words:382 satisfy the local cutoff and130 do not. All tested local exponents and log-domain density bounds pass. The root changes the sampled actual action by up to4.007205590754351, illustrating why it cannot simply be fixed in these diagnostics. Those finite floating-point tests are NOT proof premises, a formal root-dependence theorem, a novelty claim or spectral/continuum evidence.

Final verification: complete7122-job root build PASS in29.2795657s; canonical COMPLETE transitive audit PASS for58171 safe Foundation declarations in51.9816831s, only propext/Classical.choice/Quot.sound. All37 public types(28 theorems,8 definitions,1 abbreviation), BOTH entire saved sources,FIVE private helpers andONE private finite-measure instance reviewed unabridged. All16 independent Lean checks PASS in37.1509745s; complete persisted AxiomAudit PASS in47.3202751s. Repairs included finite-sum parentheses, distinct21/93-dimensional namespace selection, explicit measurable constant pairing maps, weight positivity and local opacity of large geometric/density definitions during inference. Default heartbeat/recursion limits were retained. The two independent-test repairs were a final ring step and the correct MeasureTheory.integral_exp_pos namespace; no mathematical source was changed to accommodate a test. No sorry/new axiom/native_decide/error suppression, changed mathematical hypothesis, toolchain or resource setting. Existing style/deprecation warnings were not suppressed.

Authenticated integrity:2904 recursive Foundation/root sources checked against exact approved1750; only these two new modules,root imports and persisted audit differ. All older mathematical sources,three configurations,113 baseline archive originals,21 Yang-Mills originals(20 distinct hashes) and the six-plaquette probe remain byte-identical. ResearchSources is unmodified/uncommitted; publication/manuscript/PDF/editorial README,queue and reflection accounting are untouched. The user revoked the previously supplied AGENTS.md instructions during verification; this checkpoint preserves the direct user research, verification, source-integrity and public-backup requirements without editing those instructions. Exact approval, history secret scan, guarded atomic fast-forward two-branch synchronization and independent fresh metadata/ref verification remain closure gates; no unobserved remote success is asserted by this pre-commit entry. Visibility is user-controlled exclusively.

NEXT bottleneck: establish the actual pointwise local density limit for scaled boundary chord charts while retaining the free conjugating root. Reuse actual SU2HemisphereJets and matrix two-jet comparison with SU2FourWordVariation rather than assuming the older completed-cell quadratic form is the actual slab. Verify the exact axial reduction of the chosen boundary chart families; prove eventual cutoff membership and density prefactor convergence, then the real action quotient/Hessian limit for each root. The current uniform envelope already supplies DCT once those premises are proved. Subsequent Hilbert--Schmidt/operator-norm convergence on the correctly reduced boundary space and physical ground projection/complement estimates remain open. Matched t^21,t^15,t^36 powers, full native/Haar unitary and the generalized4/6 Hessian modes are not actual ground-complement contraction. Four-dimensional volume-uniform estimates, physical coupling/distance scaling, continuum/infinite-volume existence and a physical mass gap remain unresolved. Preserve all earlier raw-gauge and slow-mode counterexamples.


## Checkpoint1752 — unconditional actual boundary-chart kernel asymptotics with positive finite prefactor

Focused Yang-Mills research continues. Prior1751 5e14e2db7375998bf16ed9187703882f61d5d21f closed guarded synchronization at2026-10-30T03:00:19.170091UTC; independent fresh metadata/ref reads03:00:29.539098UTC verified PUBLIC visibility,BOTH mathematical refs,preserved master and clean tracked state. The present checkpoint discharges1751's LOCAL POINTWISE LIMIT premise for actual fixed rescaled boundary-chart families. It does not declare the physical transfer comparison or the mass-gap campaign complete.

The main verified theorem is Foundation.CubeKernelLimit.kernel_tendsto. For EVERY fixed pair X,Y of five real coordinate triples, let B_X(t)=axialState(i->hemisphereChart(t*X_i)), similarly B_Y. Let A_(X,Y,c,Z)(t) be the ACTUAL homogeneous Wilson halfAction on these boundaries and temporal field assemble(c,chartField(tZ)), with all seven relative triples Z and the genuine free root c. Define Q(X,Y,c,Z)=d²A/dt² at0. Then
  t^(-21)*K_(t^-2)(B_X(t),B_Y(t)) -> kappa(X,Y)
  kappa(X,Y)=integral_(c,Z) rho(0)^7*exp(-Q(X,Y,c,Z)/2) d(Haar(c) times volume(Z)),
as t->0+. limitDensity_integrable and limit_integral_positive prove this is a genuine finite, strictly positive integral for EVERY X,Y. No hL, external existence, Gaussian law or unidentified-domain hypothesis remains in this actual fixed-boundary-chart kernel limit.

Foundation/CubeChartAction.lean proves rooted_axial and reduced_axial exactly: the actual seven tree links of an axial field are1, so canonical reduction recovers its five chords. This closes the prior unproved identification of the boundary chart families used by scaledDensity. Boundary and relative temporal matrix paths are C2 by the genuine hemisphere chart formula. Actual spatial and temporal plaquette actions are C2 through the existing traceAction_contDiff, retaining the actual four matrix factors and their adjoints; no completed-cell action or added diagonal term is substituted. action_contDiff is the actual homogeneous halfAction, with the original one-half spatial boundary weights.

At t=0, both actual boundaries are1 and the temporal field is the constant c for EVERY c. action_zero proves the actual action is0 there. Its global nonnegativity makes0 a local minimum, giving action_first_zero without assuming traceless velocity coordinates or fixing c. The standard scalar C2 Taylor theorem then proves action_quotient_limit: A(t)/t²->Q/2 on the punctured real neighborhood. secondVariation is defined by the actual double derivative; C2 and the Taylor result establish its genuine meaning rather than treating an arbitrary total derivative symbol as an unverified Hessian.

Foundation/CubeKernelLimit.lean proves the exact density prefactor tends to rho(0)^7 and, for every FIXED Z, all seven relative links eventually satisfy the actual defect<1/4 cutoff. reduced_axial identifies the actual density with rho(tZ)*exp(-A(t)/t²) on that cutoff. scaledDensity_tendsto proves the local pointwise limit for EVERY c,Z. It uses Real.exp explicitly and right-hand t->0+ topology. The whole Haar root average remains; the argument needs pointwise smoothness for each c plus the already verified uniform integrable bound, not an unproved uniform Taylor remainder.

The limiting density is shown almost-everywhere strongly measurable as a pointwise limit of the actually measurable scaled densities. Its bound by rho(0)^7*exp(-mass(Z)/252) proves genuine integrability on Haar(root) times the21-dimensional Euclidean field. secondVariation_lower transfers the actual nonlinear confinement through the Taylor limit and proves mass(Z)/252<=Q/2 for all X,Y,c,Z. The limiting density is strictly positive at EVERY c,Z; its support is the whole nonzero product measure, proving the integral is strictly positive. Combining the previously verified actual dominated-convergence bridge and1750's discarded exterior estimate proves kernel_tendsto unconditionally for these boundary families. An independent Lean application derives the relative asymptotic ratio tending to1 by dividing by this positive prefactor.

PRECISE LIMITATION: Q is the actual second variation, but this checkpoint has NOT identified it with a particular explicit mixed quadratic form, proved its full51-variable Hessian representation, diagonalized it, evaluated kappa in closed form or identified any transfer eigenvalue. Do not call an explicit Gaussian kernel calculation completed merely because the exponent is an actual second derivative with Gaussian domination. The theorem is POINTWISE for fixed X,Y. Uniform estimates over varying boundary-coordinate sets, Hilbert--Schmidt/operator-norm convergence, actual ground projections/complements and an actual physical contraction remain separate obligations.

Independent mathematical investigation in .lake/stardust-1752-independent.py/json tests the candidate coefficient
  a_c(X,Y,Z)=1/4*sum_spatial_faces(|dX|²+|dY|²)
            +1/2*sum_temporal_edges|X_e+Z_head-R_c(Y_e)-Z_tail|²,
where chord velocities vanish on tree edges,Z_root=0 and R_c is actual unit-quaternion conjugation. The candidate is intended to equal Q/2, but that identity is NOT YET LEAN-VERIFIED. Across256 rational-velocity/unit-quaternion choices its coarse temporal coercivity holds in exact rational arithmetic. At t=2^-14, the actual quaternion action/t² differs from the candidate by at most0.0005218815803544885; the actual log-density discrepancy is at most0.0005219514295475847. The candidate's observed root effect is2349/200, while it is root-independent at zero boundary velocities as expected. The actual rooted cube graph's7x7 Laplacian determinant computes exactly to384 by rational elimination. This determinant is not yet identified in Lean with the actual limiting action or a kernel normalization. These diagnostics are NOT proof premises, a formal formula for Q, spectral evidence or a novelty claim. Preserve them as a concrete next verification target.

All18 independent Lean applications passed: exact axial reduction/tree anchoring, actual chart and ray zero values with arbitrary root, C2 actual action, vanishing first derivative, punctured Taylor limit, actual temporal coercivity/nonnegativity of Q, eventual cutoff, local density limit, limiting integrability/positive prefactor, unconditional actual kernel limit, positive-prefactor relative ratio and absolute limiting envelope. They do not claim the explicit candidate quadratic formula is proved.

Final gates: complete7124-job root build PASS in34.5510345s; canonical COMPLETE transitive safe-Foundation audit PASS for58222 declarations in55.2427623s, only propext/Classical.choice/Quot.sound. All34 public types(27 theorems,6 definitions,1 abbreviation),BOTH complete saved sources andTWO private helpers reviewed unabridged. All18 independent Lean checks PASS in48.6795953s; complete persisted AxiomAudit PASS in58.0515567s. Tree identities were exposed through explicit actual edges instead of inaccessible private names. Large ray definitions were made locally opaque during inference and pointwise trace identities made explicit; default heartbeat/recursion limits remained unchanged. Filter domains, Real.exp versus generic exp, measure namespaces and product-measure positivity were supplied explicitly. No new mathematical axiom/sorry/native_decide, suppressed error, weakened statement or changed toolchain/resource configuration. Existing style/deprecation warnings remain unsuppressed.

Authenticated integrity against exact approved1751 covers2906 recursive Foundation/root Lean sources. Only the two new modules,root imports and persisted audit differ. All older mathematical sources,three configurations,113 baseline archive originals,21 Yang-Mills originals(20 distinct hashes) and the six-plaquette probe remain byte-identical. ResearchSources is unmodified/uncommitted. No publication/manuscript/PDF/editorial README,queue or reflection-accounting edits. The previously supplied AGENTS.md remains noncontrolling following the user's revocation; direct research/verification/integrity/public-backup instructions are preserved. Exact-commit approval, history secret scanning, guarded atomic fast-forward two-branch synchronization and independent fresh metadata/ref verification remain closure gates; no unobserved remote success is claimed here. User alone controls repository visibility.

NEXT: verify the concrete mixed quadratic coefficient INCLUDING R_c and the correct spatial half-weights against actual Q; reuse existing actual Schur/Hodge machinery only after the exact identification. Separately transport the actual five-chord boundary Haar chart and show a genuine kernel Hilbert--Schmidt/operator-norm limit using available two-boundary confinement and the full native/Haar unitary. The positive pointwise prefactor kappa is not convergence of lambda/t^36 or the actual stationary ground function. The older generalized4/6 Hessian modes are not actual transfer eigenvalues. Volume-uniform four-dimensional estimates, physical coupling/distance scaling, continuum/infinite-volume existence and physical mass gap remain open. All prior pure-gauge/slow-mode counterexamples and unresolved obligations are retained.


## Checkpoint1753 — explicit actual mixed matrix quadratic form and root-conjugated limiting kernel

Focused Yang-Mills research continues. Prior1752 f23126e6ab96a97781b8656eda7cd4871e395340 closed guarded synchronization at2026-10-30T11:07:16.915781UTC; independent fresh metadata/ref reads11:07:28.105535UTC verified PUBLIC visibility,BOTH mathematical refs,preserved master and clean tracked state. This checkpoint resolves the next exact bottleneck: identifying1752's actual double-derivative exponent with an explicit mixed trace form, retaining the free temporal root and spatial half-sharing. It does not assert a physical mass gap or operator-norm limit.

Foundation/SU2MatrixJetTransfer.lean exports trace_second for four arbitrary skew-Hermitian2x2 matrix velocities B_i and actual C2 component paths P_i with value1,first jet B_i and second jet B_i² at0. It proves
  d²/dt² traceAction(P(t)) at0 = -ReTr((B_0+B_1-B_2-B_3)²)/2.
This reuses the existing actual four-word exponential variation and matching-two-jet chain rule. Unlike the earlier Pauli-coordinate-only transfer theorem, it accepts the actual conjugated matrix velocity c*B*c^*. No unproved three-dimensional adjoint-coordinate map, broad rotation library or changed mathematical axiom is needed. The exported theorem requires the exact C2/jet/skew hypotheses; all are separately established for the actual slab paths below.

Foundation/CubeMixedForm.lean defines E_X(e) as the actual hemisphere generator of its boundary chord,zero on tree edges; H_Z(v) is the actual relative generator,zero at the root. Ad_c(B)=c*B*c^*. Let
  C_X(p)=E_X(e_0)+E_X(e_1)-E_X(e_2)-E_X(e_3),
  T_(X,Y,c,Z)(e)=E_X(e)+H_Z(head(e))-Ad_c(E_Y(e))-H_Z(tail(e)).
The explicit real matrix polynomial is
  M(X,Y,c,Z)= -1/8*sum_spatial_p ReTr(C_X(p)²)
             -1/8*sum_spatial_p ReTr(C_Y(p)²)
             -1/4*sum_temporal_e ReTr(T_(X,Y,c,Z)(e)²).
secondVariation_eq proves that the ACTUAL Q(X,Y,c,Z)/2 from1752 equals this M for EVERY real boundary coordinate pair X,Y, EVERY c in the actual SU(2) group and EVERY relative coordinate field Z. These are the original six spatial faces and twelve temporal edges,not a completed-cell action or an auxiliary loop surrogate. The factors1/8,1/8,1/4 are in the matrix trace normalization; they include both the spatial one-half sharing and the Taylor one-half factor.

The proof constructs actual edge,anchored vertex and root-conjugated component jets. Actual SU(2) unitarity proves conjugation preserves squares; multiplication by constant matrices commutes with the two derivatives on their established C2 domains. Skew-Hermitian generator and conjugate properties are verified. The existing exact temporal_word_assemble identity moves the free root into the second boundary as an ACTUAL conjugation. It does not set the root to1. Actual spatial/temporal rows and their weights are then summed with verified derivative-sum identities. Every remaining derivative symbol in the main equality is thereby evaluated; the explicit exponent is no longer merely an unevaluated second derivative.

mixedForm_lower transfers the prior nonlinear confinement and proves mass(Z)/252<=M for all X,Y,c,Z. limitDensity_eq identifies the actual limiting density with rho(0)^7*exp(-M). CubeMixedForm.kernel_tendsto proves the unconditional fixed-boundary-chart actual kernel asymptotic
  t^-21*K_(t^-2)(B_X(t),B_Y(t)) -> integral_(c,Z) rho(0)^7*exp(-M(X,Y,c,Z)),
with the complete Haar-root average and Euclidean21-dimensional relative integral. The prior finite,strictly positive prefactor and genuine integrability apply to this explicit expression; independent Lean applications check the transfer. This remains a POINTWISE fixed-X,Y result,not a kernel operator or spectral theorem.

Independent .lake/stardust-1753-independent.py/json checks256 rational matrix/quaternion configurations. Complex2x2 matrices are represented by pairs of rational real/imaginary parts; all products,adjoints,traces and comparisons are exact rational arithmetic. The explicit matrix trace form agrees in every case with the proposed real-coordinate expression
  1/4*sum_faces(|curl X|²+|curl Y|²)+1/2*sum_edges|X_e+Z_head-R_c(Y_e)-Z_tail|²,
and its coarse temporal coercivity holds. Both unitary identities are checked. A diagnostic with equal single-chord boundary velocities and zero Z gives the matrix coefficient1 at the identity root and3 at a quaternion half-turn root. This literal example has NOT yet been instantiated as a Lean SU(2) counterexample; report it as exact independent algebra evidence rather than an additional formal theorem. The general matrix trace identification IS Lean-proved. The equivalence with a chosen three-dimensional rotation-coordinate convention,its component Schur reduction and explicit determinant normalization remain separate formal connections; no numerical test is a Lean proof premise.

All12 independent Lean checks passed: exact actual second-variation identification,coercivity/nonnegativity,actual Taylor limit with the explicit exponent,limiting density identity,genuine integrability and strictly positive prefactor,unconditional explicit kernel limit,zero root velocity,zero tree velocity,identity adjoint and the zero-field form. The zero-field check required explicit generator/edge/vertex simplification in the test file only; no mathematical source was changed for it.

Final verification: complete7126-job root build PASS in27.6861681s; canonical COMPLETE transitive safe-Foundation audit PASS for58240 declarations in46.6236660s,only propext/Classical.choice/Quot.sound. All11 public types(5 theorems,6 definitions),BOTH entire saved sources and all private definitions/helper proofs were reviewed unabridged. All12 independent Lean checks PASS in42.5961392s; complete persisted AxiomAudit PASS in53.1328701s. Repairs made constant derivative types,pointwise beta reduction,associativity,finite function sums and negative sums explicit. Default heartbeat/recursion limits were retained. No new axiom/sorry/native_decide,error suppression,weakened hypothesis,changed toolchain or resource setting. Style warnings remain unsuppressed.

Authenticated integrity against exact approved1752 covers2908 recursive Foundation/root Lean sources. Only the two new modules,root imports and persisted audit differ. All older mathematical sources,three configurations,113 baseline archive originals,21 Yang-Mills originals(20 distinct hashes) and the six-plaquette probe remain byte-identical. ResearchSources remains unmodified/uncommitted. No publication/manuscript/PDF/editorial README,queue or reflection-accounting changes. The previously supplied AGENTS.md is noncontrolling under the user's revocation; direct research,verification,source-integrity and public-backup instructions continue. Exact approval,history secret scanning,guarded atomic fast-forward two-branch synchronization and independent fresh metadata/ref checks remain closure gates; no unobserved remote success is asserted here. Repository visibility is exclusively user-controlled. No novelty claim is made for classical matrix/two-jet algebra.

NEXT: connect this ACTUAL mixed matrix form to the existing actual temporal Schur geometry while retaining Ad_c. The fixed-root Gaussian calculation must subsequently be integrated over c; dropping that average is unsupported. For a spectral comparison,transport the actual five-chord Haar L2 domain and its15-dimensional local chart,prove a justified two-boundary Hilbert--Schmidt/operator-norm limit and control the PHYSICAL ground projection/complement using the exact native/Haar unitary. Pointwise kernel convergence is insufficient for these operator conclusions. The older generalized4/6 modes are not actual transfer eigenvalues. Large-volume soft modes,volume-uniform four-dimensional bounds,physical coupling/distance scaling,continuum/infinite-volume existence and physical mass gap remain open. Preserve the earlier raw-gauge/slow-mode counterexamples and all conditional/open bridges.


## Checkpoint1754 — actual root adjoint, attained Schur minimum and fixed-root Gaussian integration

Focused Yang-Mills research continues. Prior1753 c0fcf3c1eb4ebbae7ef65bfc91fad707d4de24dd closed guarded synchronization at2026-10-30T11:27:39.476878UTC; independent fresh metadata/ref reads11:27:56.610651UTC verified PUBLIC visibility,BOTH mathematical refs,preserved master and clean tracked state. The present checkpoint connects the ACTUAL mixed form to the existing verified spatial/temporal Schur geometry and integrates out the seven relative temporal variables. It retains the full outer Haar root and changes no earlier mathematical result.

Foundation/SU2RootAdjoint.lean uses the already verified quaternion/SU(2) representation,its multiplication/adjoint identities and actual inverse recover map. rotate(c,y) is the imaginary coordinate triple of recover(c)*pure(y)*star(recover(c)). A direct quaternion calculation proves its real part is0. generator_rotate proves that its genuine hemisphere generator is EXACTLY c*generator(y)*c^*. The map is real-linear and preserves sizeSq(y),using the actual unit-quaternion norm of recover(c). This establishes the precise coordinate bridge needed by the Schur theorem. No abstract unidentified rotation,external group-existence claim or broad SO(3)/gauge library is introduced; no determinant/orientation or group-action theorem beyond the proved identities is asserted.

Foundation/CubeRootSchur.lean reuses the SAME actual five-chord section,twelve-edge incidence,seven anchored vertices and six spatial faces already certified in CubeTemporalSchur. frameField(X) is the existing normalized Pauli frame of X. rotatedField(c,Y) is its frame AFTER the just-verified root rotation. gaugeField(Z) is the actual relative Pauli field anchored at0 at the root. mixedForm_frames identifies1753's explicit ACTUAL matrix trace coefficient with the established spatial and temporal real-component energies,with factors1/16,1/16,1/8 in Pauli normalization. The second boundary appears as rotatedField(c,Y),not falsely as Y for every c.

Let H be the verified spatial curl Gram matrix,W the verified temporal Schur metric,D the actual anchored gradient and A the existing response matrix. For each Pauli component a,set d_a=frameField(X)_a-rotatedField(c,Y)_a. The exact effective cost is
  E(X,Y,c)=sum_a frameField(X)_a^T H frameField(X)_a/16
          +sum_a frameField(Y)_a^T H frameField(Y)_a/16
          +sum_a d_a^T W d_a/8.
completed_square proves M(X,Y,c,Z)=E(X,Y,c)+R(X,Y,c,Z),where
  R=sum_a |D*(anchor(gaugeField Z)_a-A*d_a)|²/8.
effective_lower gives the true lower bound for all actual relative Z. The explicit center converts the Pauli response through the verified inverse frame into ACTUAL coordinate triples. center_anchor proves its exact response relation; minimum_attained proves this minimum is attained by such an actual Z,not just a scalar surrogate or unrestricted auxiliary field. effective_nonnegative follows from attainment and the previously verified actual coercivity.

Foundation/CubeSchurIntegral.lean defines the root- and boundary-independent residual form T(Z)=sum_a |D*anchor(gaugeField Z)_a|²/8 and C_T=integral_Z exp(-T(Z)). shifted_form proves
  M(X,Y,c,Z)=E(X,Y,c)+T(Z-center(X,Y,c)).
The zero-boundary identification T(Z)=M(0,0,1,Z) is verified; this uses root1 ONLY to name the universal residual at zero boundary,not to replace the root in the actual general kernel. Continuity and the existing mass(Z)/252 lower bound prove genuine integrability of exp(-T). temporalConstant_positive proves 0<C_T,with finiteness supplied by temporal_integrable. C_T remains a precisely defined integral; no unverified determinant or numerical normalization is substituted.

Translation is performed in the ACTUAL21-dimensional relative coordinate field with its actual Euclidean volume. No Pauli-frame change of integration variable or unexplained2^21 factor occurs. fixed_root_integral and fixed_root_integrable prove,for EVERY original fixed coordinate pair and EVERY actual root,
  integral_Z exp(-M(X,Y,c,Z)) = exp(-E(X,Y,c))*C_T.
The joint limiting integrability is reused from the actual kernel construction before Fubini. root_weight_integrable then proves the remaining exp(-E) is genuinely integrable under actual Haar(c). The final CubeSchurIntegral.kernel_tendsto gives the unconditional actual pointwise scaling limit
  t^-21*K_(t^-2)(B_X(t),B_Y(t))
    -> rho(0)^7*C_T*integral_(c in SU2) exp(-E(X,Y,c)) dHaar(c), t->0+.
Thus all seven relative variables have been integrated rigorously,while the genuine root average survives. The normalized constants and integral domains are actual ones. This is a fixed finite-slab kernel theorem,not a continuum existence,mass-gap or actual stationary spectral theorem.

Independent .lake/stardust-1754-independent.py/json performs256 exact rational tests using the actual12-edge,7-anchored-vertex,6-spatial-face incidence geometry reconstructed independently from the cube. Rational elimination constructs the gradient response and Schur metric; orthogonality is checked. Every tested root rotation preserves norms. The actual mixed coefficient equals the effective cost plus nonnegative residual; the constructed actual relative center attains the cost. Subtracting that center yields the same zero-boundary/root-independent residual in every case. All tests also confirm nonnegativity of the effective cost. These are independent algebra diagnostics,not proof premises or evidence for a transfer spectrum/continuum theorem.

All20 independent Lean checks passed: exact root conjugation,real linearity and norm preservation; actual component-energy identification; root-dependent completed square,lower bound and explicit center relation; attained minimum and nonnegative effective cost; shifted universal residual; zero-boundary residual identity; Gaussian integrability/positive constant; fixed-root integral and its domain; root Haar domain; the factorized actual kernel limit; direct equality at the explicit center; and exp(-E)<=1. No partial or conditional operator statement is presented as completed spectral reconstruction.

Final gates: complete7129-job root build PASS in59.5962846s; canonical COMPLETE transitive safe-Foundation audit PASS for58280 declarations in45.8225153s,only propext/Classical.choice/Quot.sound. All30 public types(19 theorems,11 definitions),ALL THREE complete saved sources and all private helpers/definitions were reviewed unabridged. All20 independent Lean checks PASS in40.7611521s; complete persisted AxiomAudit PASS in51.2700225s. Repairs qualified the quaternion repr,added the necessary Schur import,made simplifier order/inverse-frame arithmetic/dependent conditionals explicit,and supplied the exact Fubini direction and translation function. Real.exp composition and finite coordinate continuity were made explicit. Default heartbeat/recursion limits retained; no new axiom/sorry/native_decide,error suppression,weakened hypothesis,toolchain or resource change. Existing style/deprecation warnings remain unsuppressed.

Authenticated integrity against exact approved1753 covers2911 recursive Foundation/root Lean sources. Only the three new modules,root imports and persisted audit differ. All older mathematical sources,three configurations,113 baseline archive originals,21 Yang-Mills originals(20 distinct hashes) and the six-plaquette probe remain byte-identical. ResearchSources remains unmodified/uncommitted. No publication/manuscript/PDF/editorial README,queue or reflection-accounting edits. The previously supplied AGENTS.md remains noncontrolling under the user's revocation; direct research,verification,source-integrity and public-backup requirements remain. Exact approval,history secret scan,guarded atomic fast-forward two-branch backup and independent fresh metadata/ref checks are closure gates; no unobserved remote success is claimed here. Only the user controls repository visibility. No novelty claim is made for classical adjoint/Schur/Gaussian identities.

NEXT primary bottleneck: turn this actual pointwise root-averaged kernel into a justified L2/operator comparison. Reuse the exact native/Haar unitary and five-chord Haar transport; prove the local15-dimensional boundary chart/half-density identification,two-boundary Gaussian domination and a Hilbert--Schmidt/operator-norm limit with genuine off-chart control. Do not replace varying Hilbert spaces by an unproved identification. The universal Gaussian constant cancels in a normalized operator; evaluating its classical determinant formula is lower priority than that actual operator bridge. The current generalized4/6 Hessian modes are still NOT actual transfer eigenvalues. Root averaging may remove noninvariant color sectors,but the projection/spectral statement requires proof after the operator bridge. Fixed-volume Gaussian positivity does not supply volume-uniform four-dimensional control. Large-volume soft modes,physical coupling/distance scaling,continuum/infinite-volume existence and physical mass gap remain open. Preserve all earlier raw-gauge/slow-mode counterexamples and unresolved bridges.

## Checkpoint1755 — actual boundary Gaussian domination and squared-L2 kernel limits

Focused Yang-Mills remains ACTIVE. Previous1754 ca8bf09bf5ba0ea8834da27a3cbb404a7c710015 has exact guarded synchronization receipt2026-10-30T11:54:45.186705UTC; independent fresh GitHub reads11:54:54.052224UTC verified BOTH authorized mathematical refs,PUBLIC visibility,unchanged master and clean tracked state. This checkpoint advances the actual transfer-operator bottleneck from pointwise kernel convergence to squared-L2 convergence on fixed Euclidean boundary coordinates. No campaign/queue/role change or publication work.

Foundation/CubeBoundaryKernelL2.lean retains the ACTUAL integrated Wilson kernel of the homogeneous finite slab,including the free temporal root. Boundary=Fin5->Triple has15 real coordinates; its paired domain has30. Define m(X)=sum_i(chartRate(X_i)-1),the sum of the15 coordinate squares. The expanding local cutoff C_t requires chartRate(t*X_i)<=2 for ALL five chords. This set is measurable and eventually contains every fixed X as t->0. For nonzero t and X in C_t,scaled_spatial_lower proves
  m(X)/16 <= t^-2 spatialAction(boundaryRay(X,t)).
It directly reuses the already verified hemisphere defect lower bound and actual nonlinear five-chord axial coercivity. This is not a Taylor approximation or an unverified extension of Hessian coercivity.

For0<t<=1 and X,Y in C_t,the previously established actual temporal-kernel upper bound yields
  K_(t^-2)(boundaryRay(X,t),boundaryRay(Y,t))/t^21
    <= C_T^7 exp(-m(X)/32) exp(-m(Y)/32),
where C_T is CubeMatchedGround.temporalConstant (the established upper-bound constant,NOT CubeSchurIntegral.temporalConstant). localKernel extends this by ZERO outside C_t x C_t. Measurability,nonnegativity,the pointwise root-averaged Schur limit,an integrable squared Gaussian envelope,and genuine MemLp2 domains for BOTH localKernel and limitKernel are proved. integral_sq_error_tendsto then proves
  integral_(X,Y) |localKernel_t(X,Y)-limitKernel(X,Y)|^2 -> 0.
The proof uses verified dominated convergence on the fixed30-dimensional product volume,with the4*envelope^2 majorant. The separately proved MemLp2 domains prevent interpreting a total Bochner integral equal to0 outside its true domain as a convergence result.

The limit remains EXACTLY
  limitKernel(X,Y)=rho(0)^7*C_rel*integral_c exp(-effective(X,Y,c)) dHaar(c),
with the attained actual Schur cost and positive universal relative Gaussian mass C_rel from1754. It retains the full outer Haar average; no literal root=1 substitution or generalized4/6-mode transfer eigenvalue assertion is made.

Foundation/CubeBoundaryHaarL2.lean inserts the correct endpoint Haar half-density factors. density(X)=product_(i:Fin5) rho(X_i) is positive,continuous and bounded by rho(0)^5. halfDensity_t(X,Y)=sqrt(density(tX)*density(tY)) is continuous,bounded by rho(0)^5,and tends to rho(0)^5. The weighted kernel halfDensity_t*localKernel_t and its limit rho(0)^5*limitKernel BOTH belong to L2; integral_sq_error_tendsto proves their squared-L2 difference tends to0. The15-dimensional rescaling Jacobian power is separate from these half-densities. Together with the temporal t^21 normalization it motivates t^36 scaling,but this checkpoint DOES NOT assert an already proved chart/unitary identification or full operator-norm theorem.

An independent Lean counterexample verifies that the spatial coercivity cannot be extended by silently dropping C_t:at t=1 and all five X_i=(16,0,0),m(X)/16=80 while the actual spatial action is at most12. The local estimate therefore fails outside its specified hypotheses. Existing raw-gauge counterexamples remain intact. Independent exact rational diagnostics additionally tested1024 local fields and512 pairs against the actual six noncommutative plaquette words,scaled spatial bound,half-weight exponents and Haar half-density ratios. They separately verify rational unit-quaternion chart hypotheses and the cutoff-omission diagnostic;they do NOT numerically approximate a temporal Haar integral,prove a spectral gap or serve as proof premises.

Verification:complete7131-job root build 60.830146300s;complete58345-declaration safe Foundation transitive axiom audit 45.938472300s;all16 independent Lean checks 42.421432100s;complete persisted AxiomAudit 52.435312200s. All44 public unabridged types (35theorems,9definitions),both complete final mathematical sources and private helpers were reviewed. Only propext,Classical.choice,Quot.sound occur. No new axiom,sorry,native_decide,limit increase,toolchain/resource change or suppressed verification error. Development repairs concerned qualified names,finite-sum normalization,explicit indicator codomain/product volume,exponential-square associativity and explicit dominated-convergence limit types. All final gates apply to the final saved sources.

Source integrity:.lake/stardust-1755-working-checkpoint.json is authenticated against the exact approved1754 manifest and covers2913 recursive Lean/root files. Only the two new boundary-L2 modules,root imports and AxiomAudit differ. All earlier mathematics,three configurations,113 baseline archive originals,21 Yang-Mills originals with20distinct hashes and the original six-plaquette probe are unchanged. ResearchSources remains read-only/uncommitted. No manuscript,PDF,README,queue,reflection-accounting or visibility change.

Next decisive obligations:identify the actual five-chord Haar L2 reduction and the local chart half-density compression as genuine operators on their full L2 domains;control the off-chart complement relative to t^36 and the actual lambda lower bound;then deduce operator-norm/spectral convergence from the proved kernel L2 estimate. Pointwise convergence alone is no longer the missing estimate,but full-operator convergence remains unproved here. An exact chart measure/partial-isometry theorem and a quantitative complement bound cannot be replaced by calling the weighted formula a unitary. The actual invariant-sector spectrum and ground projection still need proof;root averaging may change which Gaussian modes survive. Large-volume soft modes,uniform4D bounds,physical coupling/distance scaling and continuum/infinite-volume existence and mass gap remain unresolved. These finite-cell estimates establish no physical mass-gap claim or novelty claim.

## Checkpoint1756 — full-L2 actual chord factorization and normalized original-Haar exterior control

Focused Yang-Mills remains ACTIVE. Prior1755 561599857c15df193f8cb3fa58cc4f66911294c6 closed guarded synchronization at2026-10-30T12:08:59.271879UTC;independent fresh GitHub reads12:09:25.202035UTC verified PUBLIC visibility,BOTH mathematical refs,preserved master and clean tracked state. This checkpoint resolves TWO necessary actual-operator obligations left by1755,without substituting a finite loop or Hessian surrogate for the integrated homogeneous Wilson slab.

Foundation/CubeChordOperator.lean constructs the actual chord Haar L2 space and the isometric embedding I into the original boundary Haar L2 using CubeReducedHaar.reduced_preserving and Mathlib Lp.compMeasurePreserving. Its Hilbert adjoint J=I* is a contraction,J I=id,and P=I J is a selfadjoint idempotent. For EVERY Haar L2 input F,the actual normalized operator A=CubeHaarOperator.haarOperator(d) has an output in range I. The proof constructs a genuine measurable bounded chord representative q->rawKernel(F,axialState(q))/lambda and verifies its MemLp2 domain. It uses actual endpoint gauge invariance,not a claim that arbitrary original observables are functions of the five chords.

Consequently P A=A and,by the already verified actual selfadjointness,A P=A. Define B=J A I. factorization proves the equality of continuous linear maps A=I B J on the ENTIRE original Haar L2 space. intertwines gives I B=A I;kills_orthogonal gives A F=0 whenever J F=0,and pull_zero_iff_orthogonal identifies that condition with orthogonality to every I f. The independent Lean check also verifies A(F-PF)=0 for arbitrary F. B is selfadjoint and contractive. The transported actual ground pulls back to an actual fixed unit chordGround,so norm(B)=1. This is the full operator norm and DOES NOT assert a nontrivial physical spectral gap. ground_complement_iff preserves the actual Haar ground complement; eigen_iff transfers eigen-equations for vectors in the embedded chord space. No theorem asserts all original Haar functions are reduced,and no nonzero-spectrum comparison on a varying chart is assumed.

The same module proves the LITERAL chord-kernel identity for every chord L2 input:
  (B f)(q)=integral_r K_beta(axialState(q),axialState(r))*f(r) dChordHaar(r)/lambda
almost everywhere. The inner kernel product is integrable for EVERY q,the literal raw output belongs to MemLp2,and the outer pairing with any chord L2 g is integrable. chordOperator_kernel_pairing proves its exact iterated-integral pairing with normalization by the ACTUAL supplied GroundData.value. These are full quotient-space identities,not just bounded-cylinder formulas or unspecified abstract compressions. The existing native/Haar unitary still supplies the connection to the actual stationary operator.

Foundation/CubeBoundaryExterior.lean defines chordRegion by requiring all five chords to lie in the positive hemisphere with chartRate(coordinates(q_i))<=2;region is its inverse image under actual reduction. Both are measurable,and ray_region_iff proves this is EXACTLY1755's expanding Euclidean cutoff along boundaryRay(X,t). Outside region,the actual spatial action is at least1/16. The proof shows that energy<1/4 would force every defect<1/4 and hence every chord into the specified local region,then uses the actual global modulo-gauge coercivity.

Retaining both original boundary halfweights and the established temporal t^21 bound,any pair with EITHER endpoint outside region satisfies
  K_(t^-2)(U,V)/t^36 <= C_error*t,  0<t<=1,
where C_error=CubeMatchedGround.temporalConstant^7*(40320*32^8). This nonsharp bound uses the rigorously verified scalar estimate
  exp(-1/(32t^2)) <= 40320*32^8*t^16,
proved from the eighth exponential-series term. The proof never discards the compensating t^21 temporal normalization before dividing by t^36. discardedKernel is the zero extension of this quotient on the complement of region x region. It has a verified MemLp2 domain and its squared integral tends to0 under the ORIGINAL boundaryHaar.prod boundaryHaar. The complement includes BOTH off-diagonal chart/exterior blocks and the fully exterior block.

Using the existing lambda>=C_lower*t^36 theorem,normalizedDiscarded=(t^36/lambda)*discardedKernel equals the original complement indicator times K/lambda. Its bound is (C_error/C_lower)*t,its MemLp2 domain is verified,and integral_sq_normalized_tendsto proves squared-L2 vanishing for ANY supplied family d(t):GroundData(1/t^2). Ground data are explicit theorem parameters,not newly assumed axioms of continuum existence. This handles the exterior error for the actual stationary operator after the already verified native/Haar transport,but does not itself supply the missing local chart isometry or operator-norm convergence theorem.

Independent diagnostics:128 exact rational finite-Haar-fiber matrix tests check the isometry/adjoint normalization,P^2=P,PA=AP=A,A=I B I*,intertwining,orthogonal-residual annihilation and ground preservation/contraction. Replacing conditional fiber means by sums fails by an explicit factor2 in every case.512 rational actual six-plaquette fields outside the chart satisfy the required original nonlinear energy bound;512 log-domain tests check the exponential-polynomial estimate without underflow. These finite diagnostics are independent checks of normalization/algebra,not a replacement for the Lean SU2/Haar proofs or evidence of a physical mass gap.

Verification:complete7133-job root build 27.370109300s;complete58438-declaration safe Foundation transitive axiom audit 45.153317100s;all21 independent Lean checks 42.333587400s;complete persisted AxiomAudit 51.580893600s. Both complete final saved sources,all private helpers and all57 unabridged public types (44theorems,12definitions,1abbreviation) were reviewed. Only propext,Classical.choice,Quot.sound occur. No sorry,new axiom,native_decide,resource/heartbeat increase,toolchain change or error suppression. Development repairs concerned overly deep extensionality on Lp,explicit AE composition representatives,eta-expansion of measurable kernels,explicit product-set constants,scalar association/normalization and an annotated continuous comparison function. Final gates cover the final saved sources.

Integrity:.lake/stardust-1756-working-checkpoint.json is authenticated against the exact approved1755 manifest;2915 recursive Lean/root sources. Only the two new actual chord-operator/exterior modules,root imports and persisted AxiomAudit differ. All earlier mathematics,three configurations,113 baseline archive originals,21 Yang-Mills originals with20distinct hashes and the six-plaquette probe remain unchanged. No ResearchSources,manuscript,PDF,README,queue,reflection,visibility or research-goal changes.

Remaining concrete bottleneck:construct the exact local15-dimensional Haar-chart half-density partial isometry and prove that its compressed kernel is L2-equivalent to1755's weighted kernel with correct t^15 Jacobian. The full-L2 chord reduction and original-Haar off-chart errors are now proved;do not keep listing them as unproved. Then turn kernel L2 convergence into a proved all-L2 operator-norm comparison,including ground normalization and physical ground-complement spectral control. Root Haar averaging and its invariant sector must remain explicit. No conclusion about true slowing,absence/presence of a physical mass gap,volumeuniform4D estimates,continuum/infinite-volume existence or novelty follows from this finite-cell checkpoint. The large-volume soft-mode and physical-distance-scale obligations remain open.

## Checkpoint1757 — exact15-dimensional boundary Haar chart and full-L2 partial isometry

Focused Yang-Mills remains ACTIVE. Prior1756 9ca574282ce51193877c838797f3444a39cf5493 closed guarded synchronization at2026-10-30T12:29:04.883609UTC;independent fresh GitHub reads12:29:15.574338UTC verified PUBLIC visibility,BOTH mathematical refs,preserved master and clean tracked state. This checkpoint supplies the actual local chart map required by the full operator comparison,building on1755's weighted kernel L2 limit and1756's full chord reduction/original-Haar exterior control. No campaign/queue/publication/goal change.

Foundation/CubeBoundaryChartMeasure.lean instantiates the already verified scalar SU2 Haar hemisphere chart on the actual five boundary chords. chart(X)_i=hemisphereChart(X_i). chartLaw is the product of the five genuine scalar coordinate laws;chart_map proves its pushforward is actual chordHaar restricted to the joint positive hemisphere. chartLaw_density identifies this measure with Euclidean volume weighted by the SAME density(X)=product_i rho(X_i) already used in1755. No independent guessed density or gauge-volume factor is introduced. The actual local chordRegion from1756 is contained in this hemisphere,and its preimage under chart is exactly1755's cutoff at t=1.

integral_local and integral_local_scaled give genuine local Haar integration formulas. In particular,for measurable real f and t>0,
  integral_(q in chordRegion) f(q) dChordHaar(q)
    = t^15 integral_X density(tX) 1_(C_t)(X) f(chords(X,t)) dX.
field_finrank verifies that Boundary=Fin5->Triple has dimension15,and integral_rescale proves its exact |t|^15 change of variables. The temporal t^21 factor is NOT reused as a boundary Jacobian. local_integrable_iff and scaled_local_integrable_iff independently prove the precise integrability equivalences;they do not infer domains from equality of total Bochner integrals. chart_ae_comp and scaled_ae_comp transport actual chord-Haar almost-everywhere identities to Euclidean volume,using the strict positivity of the verified chart density and nonsingular scalar dilation. These null-set results establish that the subsequent map acts on actual L2 quotient classes.

Foundation/CubeBoundaryChartL2.lean constructs the genuine continuous linear map V_t from the ENTIRE chord L2 space into the fixed Euclidean L2 volume space,for each t>0,with representative
  (V_t f)(X)=1_(C_t)(X) sqrt(t^15*density(tX)) f(chords(X,t)).
Measurability and MemLp2 are proved from the transported actual square-integrability domain before forming its toLp class. Linearity uses the verified AE composition identities,not unjustified pointwise substitution of arbitrary representatives. The exact norm and pairing identities are
  norm(V_t f)^2 = integral_(q in chordRegion) f(q)^2 dChordHaar(q),
  inner(V_t f,V_t g) = integral_(q in chordRegion) f(q)g(q) dChordHaar(q).
Hence V_t is contractive. It is not asserted to preserve the full norm of every chord input or to be onto the entire Euclidean L2 space.

backward is the actual Hilbert adjoint V_t*. localClass(f) is the original chordRegion indicator applied to f as a genuine L2 quotient class. backward_forward proves V_t* V_t f=localClass(f) for EVERY chord L2 input. forward_localClass proves V_t localClass(f)=V_t f,and partial_isometry proves the exact equality of continuous linear maps
  V_t V_t* V_t = V_t.
An independent Lean check also derives V_t f=0 iff localClass(f)=0. This is a precise local projection identity,not an unexplained unitary identification between different Hilbert spaces. Identification of V_t V_t* with the COMPLETE Euclidean cutoff subspace and a literal inverse-coordinate representative for V_t* remain separate obligations.

Independent diagnostics:512 exact rational five-chord chart samples check unit-quaternion coordinates,local-domain hypotheses,the square-root density normalization and mixed pairings with the full15-dimensional Jacobian.20 direct radial quadratures for constant/trace-power product observables at t=1,0.5,0.25,0.1,2.5 compare original and rescaled five-chord masses;the largest observed discrepancy is4.235164736271502e-21. Substituting a t^21 boundary Jacobian fails these tests. The diagnostic constant-function local mass is approximately6.187375973323715e-6;this numeric value is NOT a Lean theorem or proof premise. These tests check normalization only,not a temporal Haar integral,physical spectral gap or novelty claim.

Verification:complete7135-job root build 29.974391800s;complete58508-declaration safe Foundation transitive axiom audit 53.411745200s;all16 independent Lean checks 44.523134700s;complete persisted AxiomAudit 53.082623600s. Both complete final saved sources,all private helpers and all39 public unabridged types (30theorems,8definitions,1abbreviation) were reviewed. Only propext,Classical.choice,Quot.sound occur. No new axiom,sorry,native_decide,heartbeat/resource increase,toolchain change or error suppression. Development repairs concerned unfolding IntegrableOn before restricted-measure transport,explicit function equality for rescaling,AE predicate unfolding,linear-map coercion annotation and the exact adjoint/indicator forms. Final gates apply to the final saved sources.

Integrity:.lake/stardust-1757-working-checkpoint.json is authenticated against the exact approved1756 manifest and covers2917 recursive Lean/root sources. Only the two new actual chart-measure/chart-L2 modules,root imports and persisted AxiomAudit differ. All earlier mathematics,three configurations,113 baseline archive originals,21 Yang-Mills originals with20distinct hashes and the six-plaquette probe remain unchanged. No ResearchSources,manuscript,PDF,README,queue,reflection-accounting or visibility edits.

Next actual bottleneck:prove the literal inverse-coordinate formula for the adjoint on all Euclidean L2 inputs,its true domain and V_t V_t*=the Euclidean cutoff projection. Then prove that V_t(bareChordOperator/t^36)V_t* has1755's weighted kernel,with genuine inner/outer integrability. The actual chart map,its Jacobian,domains,initial projection and partial-isometry identity are now proved;do not keep treating those as conjectural. The FULL compressed-kernel identity and subsequent operator-norm/spectral convergence are still unproved.1756 already handles the off-chart original-Haar error both at bare t^36 scale and after actual ground normalization. Keep the full root Haar average explicit and distinguish generalized4/6 Hessian modes from actual transfer eigenmodes. Volumeuniform4D estimates,large-volume soft modes,physical coupling/distance scaling and continuum/infinite-volume existence and mass gap remain open. This finite-cell measure/operator bridge establishes no physical mass-gap or novelty claim.

## Checkpoint1758 — actual full-L2 chart adjoint and compressed Wilson kernel identification

Focused Yang-Mills remains ACTIVE. Prior1757 55cc90b5fbe94ea9205f41a53aa0c62e601d8481 closed guarded synchronization at2026-10-30T12:47:56.770728UTC;independent fresh GitHub reads12:48:05.104165UTC verified PUBLIC visibility,BOTH mathematical refs,preserved master and clean tracked state. This checkpoint resolves the explicit chart-adjoint and compressed-kernel obligations left by1757. It retains the original actual Wilson transfer and free temporal root,without a new research campaign or publication work.

Foundation/CubeBoundaryChartInverse.lean defines coords(q)_i=coordinates(q_i) and the concrete inverse representative
  psi_t(F)(q)=1_chordRegion(q)*F(t^-1 coords(q))/sqrt(t^15*density(coords(q))).
For EVERY Euclidean L2 input F and t>0,the denominator is positive and the representative is measurable and square-integrable under actual chordHaar. The proof establishes its genuine domain before forming inverseClass:under the exact scaled Haar chart,t^15*density(tX)*psi_t(F)(chords(X,t))^2 is exactly the Euclidean cutoff of F(X)^2. Integrability transport from1757 then proves the original Haar domain;zero extension outside chordRegion is checked explicitly.

forward_inverseClass proves V_t inverseClass(F)=cutoffClass_t(F). local_inverseClass proves original local support,backward_cutoff proves the actual adjoint ignores the Euclidean complement,and inverseClass_eq_backward identifies this explicit class with the ACTUAL Hilbert adjoint V_t* for EVERY Euclidean L2 input. backward_coe gives its full AE representative formula. Finally,forward_backward proves
  V_t V_t* F = 1_(C_t) F
as an equality of genuine L2 quotient classes. Together with1757's V_t* V_t=the original local-chord projection,this identifies both initial and final subspaces. It does not falsely make the local chart a unitary on arbitrary full-space inputs.

Foundation/CubeChartCompressedKernel.lean connects these maps to the ACTUAL operator,not just to a guessed Gaussian surrogate. Let B_d be1756's exact normalized five-chord operator K/lambda on all chord L2 inputs. For supplied certified d:GroundData(1/t^2),define the actual rescaled bare compression
  T_t = (lambda/t^36) V_t B_d V_t*.
scaledIntegrand_integrable and rawChord_inverse_scaled prove the genuine scalar change of variables for the original transfer row against the actual adjoint input. kernel_row_integrable proves that EVERY Euclidean L2 F and EVERY X have an integrable literal weighted-kernel row. The proof uses original bounded-K integrability and actual Haar domain transport,not an unproved global L1 assertion for Euclidean L2 functions.

compressed_coe proves the entire-L2 quotient-space identity
  (T_t F)(X)=integral_Y k_t(X,Y)F(Y) dY almost everywhere,
where k_t is EXACTLY1755's CubeBoundaryHaarL2.kernel:
  k_t(X,Y)=1_(C_t x C_t)(X,Y)*sqrt(density(tX)*density(tY))
             *K_(t^-2)(boundaryRay(X,t),boundaryRay(Y,t))/t^21.
The original boundary t^15 Jacobian,the two t^(15/2) half-density factors,and bare operator t^36 scaling cancel precisely to t^-21 in the kernel. All square roots have proved positive denominators. There is no missing gauge volume or doubled boundary Jacobian. The temporal Haar integral,including its root,remains inside the SAME actual K.

raw_memLp proves that the literal row-integral output is genuinely in Euclidean L2;pairing_integrable proves the outer pairing with EVERY Euclidean L2 G is integrable. compressed_kernel_pairing gives the exact iterated integral for all F,G. compressed_ground_independent proves the resulting continuous linear map is independent of which supplied GroundData normalization is used:the lambda factors cancel. compressed_selfadjoint proves actual selfadjointness. These statements do not introduce a new existence axiom,assert positive semidefiniteness merely from a positive kernel,or identify a physical spectral gap.

Independent diagnostics:256 exact rational weighted finite-measure models verify the adjoint formula,initial/final local projections and full compressed-kernel normalization,including exterior original coordinates and two distinct positive normalization choices per case. The lambda factors cancel exactly,and an incorrect t^21 boundary Jacobian fails.512 additional exact rational actual five-chord hemisphere samples verify coordinate inversion,local hypotheses and half-density inverse cancellation. These finite algebra/coordinate diagnostics are independent checks,not an SU2-Haar construction,a physical spectral calculation or Lean proof premises.

Verification:complete7137-job root build 27.966919000s;complete58575-declaration safe Foundation transitive axiom audit 46.639013400s;all18 independent Lean checks 43.389540200s;complete persisted AxiomAudit 54.144526900s. Both complete final saved sources,all private helpers and all31 public unabridged types (23theorems,8definitions) were reviewed. Only propext,Classical.choice,Quot.sound occur. No new axiom,sorry,native_decide,limit/resource increase,toolchain change or error suppression. Development repairs concerned explicit measurable constants,product association,qualified chart weight versus Wilson weight,exact kernel normalization and the existing memLp_congr_ae API. Final gates cover final sources.

Integrity:.lake/stardust-1758-working-checkpoint.json is authenticated against the exact approved1757 manifest and covers2919 recursive Lean/root sources. Only the two new actual chart-inverse/compressed-kernel modules,root imports and persisted AxiomAudit differ. All earlier mathematics,three configurations,113 baseline archive originals,21 Yang-Mills originals with20distinct hashes and the six-plaquette probe remain unchanged. No ResearchSources,manuscript,PDF,README,queue,reflection-accounting or visibility edits.

Next decisive step:prove a quantitative L2-kernel-to-operator-norm estimate on this fixed Hilbert space,then combine1755's genuine weighted-kernel squared-L2 limit with completeness of bounded operators. Since T_t already exists on the whole space,the Cauchy/completeness route may avoid constructing an unrelated generic integral-operator foundation. An appropriate target is norm(T_t-T_s)<=L2norm(k_t-k_s),with Fubini justified by L2 pairing against the tensor G(X)F(Y). This estimate and operator-norm convergence are PLANS,NOT proved in this checkpoint.1756's original-Haar exterior error and1757/1758's full chart identification are now established and must not be relisted as conjectural. Actual ground-normalization asymptotics and physical ground-complement spectral comparison remain subsequent obligations. The root-averaged limiting Schur kernel stays explicit;generalized4/6 Hessian modes are not actual transfer eigenvalues. Volumeuniform4D bounds,large-volume soft modes,physical coupling/distance scaling,continuum/infinite-volume existence and mass gap remain unresolved. No novelty or Millennium claim follows from this finite-cell checkpoint.

## Checkpoint1759 — genuine operator-norm limit of the actual local Wilson compressions

Focused Yang-Mills remains ACTIVE. Prior1758 4d130981a1b3c0d8dec93e32b5483b4f6d8f523c closed guarded synchronization at2026-10-30T13:06:27.197892UTC;independent fresh GitHub reads13:06:34.878003UTC verified PUBLIC visibility,BOTH mathematical refs,preserved master and clean tracked state. This checkpoint upgrades the actual local compressed kernel convergence to OPERATOR-NORM convergence on the fixed Euclidean L2 space. It does not claim a full stationary spectral limit or physical mass gap.

Foundation/CubeKernelOperatorBound.lean constructs the genuine tensor class of G(X)F(Y) for arbitrary Euclidean L2 F,G. Its MemLp2 domain follows by the product integral of their integrable squares,and its norm is exactly norm(G)*norm(F). No finite-measure comp_fst/comp_snd integrability lemma is misapplied to infinite Euclidean volume. For a genuine L2 kernel k,the product k(X,Y)G(X)F(Y) is integrable by L2 duality BEFORE Fubini identifies its product-space inner product with the iterated row pairing.

opNorm_le_of_pairing proves the whole-Hilbert-domain operator bound by testing against A F and handling the zero-norm case separately. Applied to the ACTUAL compressed operators from1758,this gives,for0<t,s<=1,
  norm(T_t-T_s) <= norm(k_t-k_s)_L2.
Here T_t=(lambda/t^36)V_t B_t V_t*,with B_t the actual normalized chord K/lambda operator and k_t the actual weighted Wilson kernel,including its complete temporal Haar root. This is a norm bound for the full continuous linear maps,not a bounded-core or weak test-family claim. It does not replace operator norm by an equal Hilbert-Schmidt norm.

Foundation/CubeCompressedNormLimit.lean forms actual kernel L2 classes and proves that their squared class-norm error equals1755's squared kernel-error integral. The latter's verified convergence,followed by square-root continuity,proves kernelFamily_tendsto in genuine L2. For any supplied positive-parameter family d(t,ht):GroundData(1/t^2),the actual operator family is then Cauchy in OPERATOR NORM near0. The proof exhibits a small-diameter image of parameters where both kernel errors are small;completeness of the bounded-operator space supplies the actual limit. It does not introduce a new generic integral-operator foundation or an unproved Riesz representation premise.

operatorFamily_tendsto and operator_error_bound establish
  T_t -> T_infinity in operator norm,
  norm(T_t-T_infinity) <= norm(k_t-k_infinity)_L2,  0<t<=1.
The squared error bound against the literal squared kernel integral is independently Lean checked. The limit is selfadjoint,independent of the supplied ground-family choices,and identified on EVERY L2 pair F,G by the same genuine root-averaged Schur kernel. No measurable or continuous dependence of arbitrary ground choices is assumed;the actual compressed operator was already proved ground-independent in1758.

The supplied-family theorem is also instantiated WITHOUT an additional existence hypothesis. A theorem-level reuse audit read CubeSlabGround.ground_nonempty and ground,and CubeSlabGauge.positive_ground_exists:the finite-slab positive eigenfunction was already rigorously constructed from YMPositivePower for this actual kernel. actualOperatorFamily and actualLimitOperator use this verified ground construction. actualOperatorFamily_tendsto is therefore a CLOSED operator-norm convergence theorem for the actual rescaled LOCAL Wilson compression. actualLimitOperator_integral_pairing identifies its literal limit kernel for all F,G,and its norm is bounded by the genuine L2 kernel norm. This reuses finite-volume existence;it supplies no continuum Yang-Mills existence assumption.

The limiting kernel stays
  k_infinity(X,Y)=rho(0)^12*C_relative*integral_c exp(-effective(X,Y,c)) dHaar(c).
The free root remains averaged. The arbitrary definition at nonpositive t is irrelevant to the proved t->0+ filter. T_t is the bare local compression divided by t^36;it must NOT be confused with an already normalized full stationary transfer. Positive semidefiniteness,compact spectral separation,ground-vector convergence and a nonzero limiting norm are not asserted by this checkpoint.

Independent tests:512 exact rational finite-weight tensor/Cauchy-Schwarz/operator-action bounds,including32 zero-input cases;128 rank-one cases saturate the kernel bound;512 exact two-parameter Cauchy-modulus tests. An independent Lean counterexample has the positive-entry symmetric matrix[[1,2],[2,1]] and vector[1,-1],whose quadratic form is-2 (or-1/2 with uniform two-point integral weights). Thus pointwise positive kernel does not by itself prove positive semidefiniteness. Another exact diagnostic checks kernel2I on uniform two-point measure:operator norm1 but Hilbert-Schmidt squared norm2. These are generic interpretation safeguards,NOT claims that the actual Wilson kernel has a negative mode. Diagnostics are not proof premises or numerical physical spectra.

Verification:complete7139-job root build 29.072560200s;complete58626-declaration safe Foundation transitive axiom audit 46.686613800s;all20 independent Lean checks 47.446580400s;complete persisted AxiomAudit 60.854699400s. Both complete final saved sources,all helpers and all38 unabridged public types (28theorems,9definitions,1abbreviation) were reviewed. Only propext,Classical.choice,Quot.sound occur. No new axiom,sorry,native_decide,limit/resource increase,toolchain change or error suppression. One development AC-simplifier reached the DEFAULT200000-heartbeat limit;it was replaced by explicit two-step factor rearrangement/cancellation,with no limit increase. Other repairs concerned explicit integral/scalar types,dependent-if rewrite lemmas and the existing fixed-input continuous evaluation map. Final gates cover final sources.

Integrity:.lake/stardust-1759-working-checkpoint.json is authenticated against the exact approved1758 manifest and covers2921 recursive Lean/root sources. Only the two new kernel-operator-bound/norm-limit modules,root imports and persisted AxiomAudit differ. All older mathematics,three configurations,113 baseline archive originals,21 Yang-Mills originals with20distinct hashes and the six-plaquette probe remain unchanged. No ResearchSources,manuscript,PDF,README,queue,reflection-accounting or visibility changes.

Next:use1756's actual original-Haar off-chart kernel bounds to prove the quantitative FULL-operator compression error,then relate lambda/t^36 to norm(actualLimitOperator). The local geometric map,kernel identification AND compressed operator-norm convergence are now proved;do not relist them as unresolved. Positivity/nontriviality of the limit and ground-complement spectral control still require explicit theorems. The finite-cell result alone establishes neither slowing nor a uniform physical gap. Preserve the distinction between generalized4/6 Hessian modes and actual transfer eigenmodes,and retain the root-invariant sector. Large-volume soft modes,volumeuniform4D estimates,physical coupling/distance scaling and continuum/infinite-volume existence and mass gap remain open. No novelty or Millennium claim is made.

## Checkpoint1760 — full compression error and positive stationary normalization limit

Focused Yang-Mills remains ACTIVE. Prior1759 4bfbd6a49a76cdad7736ee1926c96bd0f77696f7 closed guarded synchronization at2026-10-30T13:29:51.794883UTC; independent fresh GitHub reads13:30:00.584625UTC verified PUBLIC visibility, both mathematical refs, preserved master and clean tracked state. This checkpoint resolves the actual full-operator exterior error and the nonzero normalization limit left open at1759. It establishes a normalized LOCAL stationary compression limit. It does not establish a ground-complement spectral gap, physical slowing, or continuum Yang-Mills existence.

Foundation/CubeFullCompressionError.lean uses the actual chord-Haar probability space. errorKernel is the original bare K_(1/t^2)/t^36 multiplied by the complement of chordRegion x chordRegion. Thus it includes both off-diagonal blocks as well as the outside/outside block. The existing1756 original-Haar pointwise bound gives 0<=errorKernel<=C_error*t for0<t<=1. Actual row integrability for every L2 input follows from L2-to-L1 on the probability space; an explicit Cauchy-Schwarz argument proves integral(abs(f))<=norm(f). The pointwise row bound is C_error*t*norm(f). No Euclidean infinite-volume probability-space estimate is substituted here.

The exact AE row identity identifies the error with Q_t-L_t on ALL chord L2, where
  Q_t=(lambda_t/t^36) B_t,
  L_t=V_t* T_t V_t=M Q_t M,
  T_t=(lambda_t/t^36) V_t B_t V_t*.
B_t is the actual normalized chord transfer, M the actual chordRegion projection, and V_t the verified chart partial isometry. The squared L2 row bound on the probability space proves residual_norm_bound:
  norm(Q_t-L_t)<=C_error*t.
This is a full bounded-operator estimate, not a pointwise-kernel convergence claim or a restriction to bounded inputs.

Foundation/CubeGroundNormLimit.lean proves both chart-map contractions, the output-cutoff identity for T_t, and the exact recovery T_t=V_t L_t V_t*. These give norm(L_t)=norm(T_t) without assuming V_t surjective onto all Euclidean L2. Existing chordOperator_norm gives norm(Q_t)=lambda_t/t^36. The reverse triangle inequality then proves normalization_error for every actual GroundData choice:
  abs(lambda_t/t^36-norm(T_t))<=C_error*t.
The1759 operator-norm limit and this error imply groundScale_tendsto:
  lambda_t/t^36 -> norm(T_infinity), t->0+.
Here the canonical ground comes from the EXISTING proved finite-slab ground construction. No free existence or parameter-regularity hypothesis is added. The1758 lower bound C_lower<=lambda_t/t^36 passes to the limit, proving norm(T_infinity)>=C_lower>0 and actualLimitOperator!=0. Nontriviality and normalization asymptotics must no longer be relisted as unresolved.

normalizedOperatorFamily_pos identifies the normalized family EXACTLY with V_t B_t V_t*. Its operator-norm limit is
  S_infinity=T_infinity/norm(T_infinity), norm(S_infinity)=1.
The inverse normalization is justified by the proved positive limiting norm. The limit retains the1759 Haar-root-averaged Schur kernel, including the actual root integral and half-density normalization. This is an actual LOCAL compression of the stationary operator, not an identification of the whole original moving-space transfer with a fixed-space map. Neither convergence of ground vectors nor a ground-complement gap is assumed or proved.

Independent testing:700 exact rational weighted finite-dimensional full residual bounds, allowing empty/full cutoffs and nonuniform probability weights, plus100 exact two-dimensional spectral diagnostics. The off-diagonal matrix[[1,t],[t,1]] has leading eigenvalue1+t, showing that discarded off-diagonal blocks can affect normalization at first order. Independent Lean tests verify this eigenvector identity and the matrix diag(1,1-t), whose second eigenvalue approaches1. Norm-one normalization alone cannot prove a uniform ground-complement gap. These generic diagnostics are interpretation safeguards, not claims about the actual Wilson spectrum. All14 independent Lean checks passed, including the full action bound, squared action bound, exact residual and normalized stationary identification.

Verification:complete7141-job root build 35.473245300s; complete58684-declaration safe Foundation TRANSITIVE axiom audit 53.231941500s; all14 independent Lean checks 49.119361700s; complete persisted AxiomAudit 61.465282600s. Both complete final sources, private helpers, and all31 unabridged public types were reviewed. Only propext, Classical.choice, Quot.sound occur. No new axiom, sorry, native_decide, toolchain/resource change or suppressed error. Development repairs were reserved-keyword naming, explicit argument minimization, rewrite order and existing limit-lemma argument conventions; they were not mathematical obstructions.

Integrity:.lake/stardust-1760-working-checkpoint.json authenticates the approved1759 manifest and covers2923 recursive Lean/root sources. Only the two new full-error/ground-normalization modules, root imports and persisted AxiomAudit differ. All older mathematical sources,3 configurations,113 baseline archive originals,21 Yang-Mills originals with20distinct hashes, and the six-plaquette probe are unchanged. No ResearchSources, manuscript, PDF, README, queue, reflection-accounting or visibility change. This ledger records local successful gates; exact-commit approval and guarded two-ref remote synchronization are recorded separately after commit and are never inferred from local success.

Next bottleneck:determine the actual root-invariant normalized limiting spectrum or prove a sharp actual spectral obstruction. The root-averaged Schur kernel is now connected to the actual normalized stationary compression by verified operator-norm convergence, not only Hessian heuristics. Inspect whether its actual root action yields a Gaussian operator composed with a root-invariance projection and whether that gives explicit admissible ground-complement test functions. Do not promote generalized4/6 Hessian modes to actual transfer eigenmodes without the kernel/domain theorem. Ground-vector convergence, spectral separation or actual slow modes, large-volume soft modes, volume-uniform four-dimensional estimates, physical coupling/distance scaling, continuum/infinite-volume construction and a positive physical mass gap remain open. The finite-cell result supplies none of those conclusions by itself. No external novelty or Millennium claim is made.

## Checkpoint1761 — actual Gaussian channel decomposition with the common Haar root retained

Focused Yang-Mills remains ACTIVE. Prior1760 ee9dd87b56d2650ed3449b320a120fcaff68481f closed guarded synchronization at2026-10-30T13:54:13.271328UTC; independent fresh reads13:54:23.273042UTC verified both authorized mathematical refs, PUBLIC unchanged, preserved master and clean tracked tree. The present question is whether the ACTUAL root-averaged Schur limit admits usable Gaussian spectral analysis. This checkpoint resolves its algebraic mode/kernel identification, not the analytic spectral problem.

The exact rational diagnostic of1759/1760's generalized4/6 modes exposed the need for a KINETIC-ORTHOGONAL basis, rather than treating the original generalized eigenbasis as orthonormal. Foundation/CubeGaussianModes.lean now proves simultaneously
  P^T kinetic P=diag(w),
  P^T spatial P=diag(w*m),
  w=(1,1/4,1/2,2/3,1/2), m=(4,4,4,6,6).
The numerical matrices used in the verification are connected definitionally to the ACTUAL CubeTemporalSchur rational matrices; they are not substituted surrogates. The proof kernel checks every finite entry using ordinary rational/real arithmetic. The explicit synthesis and analysis maps on all five coordinate triples are mutual inverses. Thus the resulting formulas cover EVERY boundary X,Y, not only a proper parametrized subspace.

The coordinate synthesis commutes with the ACTUAL SU(2) root adjoint. Its proof reuses SU2RootAdjoint.rotate_add and rotate_smul, which represent the genuine matrix/quaternion conjugation. spatial_triples and kinetic_triples account for the existing frame(y)=(2*y1,2*y2,2*y0) exactly; its factor4 is essential. effective_channels proves, for every root c,
  effective(Px,Py,c)=sum_i h_i(x_i,y_i,c),
  h_i=(w_i/4)*[m_i*(sizeSq(x_i)+sizeSq(y_i))+2*sizeSq(x_i-R_c y_i)].
channel_gaussian then reuses the ACTUAL norm-preserving root action to prove
  h_i=w_i*(m_i+2)/4*(sizeSq(x_i)+sizeSq(y_i))-w_i*dot(x_i,R_c y_i).
This is a genuine exact Schur-exponent identity, stronger than merely listing generalized Hessian modes. No claim that m_i are transfer eigenvalues is made.

Foundation/CubeGaussianKernelChannels.lean proves actual_kernel_channels for ALL original boundary X,Y:
  k_infinity(X,Y)=rho(0)^12*C_relative*
    integral_c product_i exp(-h_i(analysis(X)_i,analysis(Y)_i,c)) dHaar(c).
actual_operator_channels identifies this formula with the actualLimitOperator pairing on EVERY Euclidean L2 pair F,G, using the already proved genuine kernel/operator domain from1759. This retains one COMMON Haar root outside the product. It is not a product of separately averaged kernels. No unproved root-conditioned factorization, independent-color law, Jacobian, coordinate-volume formula, or Gaussian spectral conjugacy is inserted.

Independent tests:both actual matrix congruences and both inverse identities checked with exact Fractions;500 exact rational full Schur/channel exponent comparisons with genuine rational unit-quaternion rotations about all three axes, including exact rotation norm preservation. A generic two-point common-root example has average(f*g)=5 versus average(f)*average(g)=4; it guards against moving the Haar integral independently through the product, and is explicitly NOT represented as a Haar counterexample for this specific kernel. All12 independent Lean checks passed, including the actual all-L2 operator pairing, mutual coordinate inverses, bijectivity, exact exponent/product identities, and positive weights with modes4/6.

Verification:complete7143-job root build 49.750707200s; complete58719-declaration safe Foundation transitive axiom audit 55.217789300s;12 independent Lean checks 44.680346600s; complete persisted AxiomAudit 54.028309100s. Complete final sources and private helpers, all23 unabridged public types, and audit/test helpers were reviewed. Only propext, Classical.choice, Quot.sound occur. No new axiom, sorry, native_decide, trust/resource increase or toolchain/configuration change. Elaboration repairs concerned private rational-matrix reduction through their actual cast maps, matrix product rewrite association and declaration namespaces; these were not mathematical obstructions.

Integrity:.lake/stardust-1761-working-checkpoint.json authenticates the approved1760 manifest and covers2925 recursive Lean/root sources. Only these two new modules, root imports and persisted AxiomAudit differ. All older mathematics,3 configurations,113 baseline archive originals,21 Yang-Mills originals with20distinct hashes and the six-plaquette probe are unchanged. No ResearchSources, manuscript, PDF, README, queue, reflection-accounting or visibility change. Local gate success is distinct from exact-commit approval and guarded remote closure, which follow this record.

Precise next obligations:construct the actual coordinate-volume/Jacobian and ground-weighted Gaussian L2 equivalences, identify the common-root average as the appropriate invariance projection, and prove the Gaussian transfer/domain intertwining before assigning any spectral meaning to scalar Mehler calculations. FiniteGaussianSpectral supplies actual tensor Hermite coefficients/Parseval/completeness, GaussianMehlerKernel supplies an actual one-dimensional Markov kernel and composition/invariant-measure theorems, and GaussianQuadraticSpectralTransport supplies finite orthogonal source transport; these do not by themselves supply the needed actual15-dimensional weighted-kernel equivalence. The candidate scalar ratio r(m)=(m+2-sqrt(m*(m+4)))/2 and possible invariant quadratic eigenmodes remain UNVERIFIED as actual transfer spectral statements. This offers a concrete test of finite-cell contraction rather than assuming the earlier surrogate slowing persists. Ground-complement spectrum, uniform finite-cell gap or actual slow modes, large-volume soft modes, volume-uniform4D bounds, physical distance/coupling scaling, continuum existence and physical mass gap remain open. No novelty or Millennium claim is made.
