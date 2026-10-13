# Research recovery and convolution checkpoint — 2026-10-13

Initial HEAD: 953e958c2d6ba5ed21deaca4d3a36f813a0c5f95.

Recovery established that six fractional Gaussian milestones and three curvature milestones already succeeded. Their limitations remain in FRACTIONAL_GAUSSIAN_REPORT.md and GAUSSIAN_CURVATURE_REPORT.md. The latest committed audited milestone was FractionalForcingKernel: 4198 jobs and 3113 transitive checks. Archive directories are accessible: 23 fBM files, 10 IBM files (including the added PDF), two SPDE TeX manuscripts. Counts are files, not distinct verified papers.

## Convolution operator milestone

Recovered unfinished Foundation/StochasticKernelConvolution.lean, root import and axiom entries. Prior full build failed in finite_convolution_energy, despite direct Lean compilation passing. Repaired the inner-product expansion with explicit ambient subtype coercions under Lake's configured options.

Let K:E -> fullPredictable be an independently supplied bounded linear map, where E is a real complete Hilbert space. The actual integral is J K, using the established predictable Ito isometry J. Exact norm and inner product, boundedness, product integrability, adjoint K* J*, normal operator K*K, nullspace and full divergence graph membership are proved. The projected closed derivative identity is restricted to the actual derivative domain. No injectivity, isometry or SPDE solution property of K is assumed.

The independently defined finite-rank transform sums continuous scalar functionals times actual predictable fields. Its integral and energy retain every Gram cross term; no independence or orthogonality is assumed. New extensions prove exact operator error ||JK-JL||=||K-L||, equivalence of strong convergence at each parameter, and equivalence of operator-norm convergence. A Galerkin application must still prove its kernel convergence.

Verification: affected Lake target passed; complete Lake build passed (4199 jobs); explicit public types checked; 3130 complete transitive axiom checks, exactly propext, Classical.choice, Quot.sound. No sorry/admit/unsafe/custom axiom occurs in the module. Logs: .lake/campaign-evolution/02-recovery-{target,build,types,axioms}.log.

## Limitations and next obligations

This constructs scalar-valued terminal integrals of bounded predictable transforms, not a concrete semigroup multiplier on a Hilbert-valued integrand domain. Hilbert-valued convolution, nonzero-rate Mittag-Leffler forcing, Caputo existence/uniqueness, trace-class limits and sample continuity remain open. The existing zero-mode energy now supplies a direct initial-time mean-square obstruction target.

IBM remains a major pending campaign: flagship(8).tex uses two-sided scenery with covariance (|z|+|z'|-|z-z'|)/2 and reflected clock X_|Y_t|. A finite-dimensional Gaussian construction must be upgraded to jointly measurable suitable path versions before random-time composition. The bidegree atlas covers low sectors and defers full summability. Observable-domain density and local-time singular estimates remain unproved. No IBM theorem is claimed here.

Pseudoprocess work remains pending; signed kernels do not authorize probability conditional expectation. Black noise and RH excluded. No push, dependency change, source manuscript edit or unrelated document staging.

## Declaration inventory

All names below have prefix OperatorDerivativeRewrite.Foundation.StochasticKernelConvolution. and refer to Foundation/StochasticKernelConvolution.lean.
- `convolution` — line 15
- `convolution_norm` — line 18
- `convolution_inner` — line 21
- `convolution_bound` — line 25
- `convolution_pair_integrable` — line 30
- `convolution_adjoint` — line 34
- `convolution_adjoint_derivative` — line 38
- `convolution_normal` — line 45
- `convolution_zero_iff` — line 52
- `convolution_divergence_graph` — line 56
- `finiteKernel` — line 61
- `finiteKernel_apply` — line 65
- `finite_convolution_apply` — line 69
- `finite_convolution_energy` — line 76
- `convolution_operator_error` — line 92
- `convolution_tendsto_iff` — line 100
- `convolution_operator_tendsto_iff` — line 107

## Fractional forcing initial-time obstruction

Foundation/FractionalForcingObstruction.lean independently proves:
- no_higher_initial_power_bound (line 13): for alpha>1/2 and p>2alpha-1, for every real C and delta>0 there exists 0<t<delta, t<=1, such that C*t^p < ||X_t-X_0||^2 for the actual zero-generator stochasticResponse.
- no_initial_brownian_variance_bound (line 46): for 1/2<alpha<1 the same statement holds with C*t.

The proof uses the actual proved norm and zero-time identities, Gamma positivity, and continuity of t^(p-(2alpha-1)) at zero. It does not assume a scaling law or infer sample-path regularity from second moments. This disproves a uniform initial mean-square O(t^p) estimate above the true exponent in this concrete one-mode model. It does not itself disprove every almost-sure Holder assertion without a separate moment implication.

Verification: targeted Lake build passed; full build 4200 jobs; exact public types checked; full transitive audit 3132 declarations, only propext, Classical.choice, Quot.sound. Logs .lake/campaign-evolution/03-{target,build,types,axioms}.log.

Next: independent two-sided Gaussian scenery and Brownian clock coordinate families on the actual product Gaussian measure. Joint path measurability and continuous modification remain separate before IBM random-time evaluation.

## IBM independent source-law milestone

Foundation/IBMSourceLaws.lean constructs the actual product of two existing countable Gaussian measures. On its first factor, the independently verified H=1/2 real spectral vectors construct two-sided Gaussian scenery. On its second factor, the existing concrete time-vector process constructs the Brownian clock. The scenery covariance is exactly (|s|+|t|-|t-s|)/2 for all real s,t, with mean zero and law N(0,|t|). Both half-lines have Brownian finite-dimensional laws and their entire coordinate families are independent. The entire scenery coordinate family is independent of the entire clock coordinate family; this is proved product-measure independence, not inferred merely from pairwise covariance.

These are pre-Brownian coordinate families. No continuous sample version, jointly measurable time/sample map, IBM random-time composition, source product derivative, local time, fourth variation or singular correction is asserted. Deterministic-time measurability does not close these obligations.

Verification: affected target compiled; exact types of all 21 public declarations checked; full Lake build passed (4201 jobs); all 3153 transitive axiom checks passed with exactly propext, Classical.choice, Quot.sound. Logs .lake/campaign-ibm/01-{target,build,types,axioms}.log. No forbidden proof placeholder, unsafe proof or custom axiom occurs in any of the three recovered/new modules.

### IBM declaration inventory

All names have prefix OperatorDerivativeRewrite.Foundation.IBMSourceLaws. and refer to Foundation/IBMSourceLaws.lean.
- `JointSample` — line 16
- `jointMeasure` — line 18
- `joint_probability` — line 20
- `sceneryBase` — line 24
- `scenery` — line 27
- `clock` — line 29
- `sceneryBase_measurable` — line 31
- `sceneryBase_isGaussianProcess` — line 34
- `sceneryBase_covariance` — line 37
- `scenery_measurable` — line 46
- `clock_measurable` — line 49
- `scenery_clock_independent` — line 53
- `clock_isPreBrownian` — line 59
- `scenery_finite_law` — line 64
- `scenery_isGaussianProcess` — line 74
- `scenery_covariance` — line 79
- `scenery_law` — line 93
- `scenery_centered` — line 105
- `scenery_positive_isPreBrownian` — line 110
- `scenery_negative_isPreBrownian` — line 120
- `scenery_halves_independent` — line 133

## Preservation and final scope

All 58 SHA256 entries in ARCHIVE_MANIFEST_2026-10-12.json match. Both SPDE_MANIFEST_2026-10-12.json entries match. Added IBM EJP2605-044RA0.pdf hash matches its source audit: 5A91914A535AD19BDDF219D7A9AB9F8B5F20A52DD4EC6ED7333AA80B403182BE. Dependency pin files have no diff from initial HEAD. The twelve pre-existing unrelated untracked documents were neither edited nor staged. Existing verified Lean module statements/bodies were not changed; only the previously unfinished convolution module was repaired, new modules added, and import/audit lists extended.

Commits before the final IBM checkpoint: 1aa556d (convolution recovery and convergence), b550ea7 (forcing regularity obstruction). The final IBM mathematical commit also records this report and RESEARCH_READINESS_AND_BACKLOG.md. Forty public declarations total: 17 convolution, two forcing obstruction, 21 IBM source laws. All exact public types were checked independently.

The eight-phase mission remains partial. Completed during recovery: three restricted verified milestones. No full new SPDE or IBM calculus campaign is claimed complete. Next recommended proof: continuous and jointly measurable independent IBM sources, then reflected-clock composition and its second moment. See RESEARCH_READINESS_AND_BACKLOG.md for campaign-by-campaign status, missing source evidence and readiness assessment.
