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
