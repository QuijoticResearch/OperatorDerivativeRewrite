# Integer higher-even-order Xi-flow campaign

A(6) is the first target. A(4) is frozen at mathematical checkpoint `4f36db3a5fcd68b8fc1af7033326995ab0799501`; stopping/report commit `608f13a836e6ad789880c242757d8101809ef08f` was verified on PRIVATE main/research refs before this checkpoint. The authoritative queue is STARDUST_CAMPAIGN_QUEUE.md. Real exponents, their limit, independent A(2), and the final multichannel campaign remain later stages. October 31, 2026 is the hard stop.

## Exact object and verified initial result (checkpoint 1161)

The actual family is
\[
 H_{t,2m}(z)=\int_0^\infty e^{tu^{2m}}\Phi(u)\cos(uz)\,du,
\]
using literally `RiemannQuarticKernel.kernel` and `RiemannQuarticFlow.halfLine`. Here m is a natural number, t is any real number and z any complex number; research priority is m>=2, with m=3 first. Algebraic validity at m=0 or m=1 does not open a separate quadratic campaign. No unverified identity with the completed Xi function is inserted as a hypothesis.

`RiemannEvenDomain.weighted_integrable` proves genuine integrability of every polynomial moment with every real even and linear tilt. `RiemannEvenFlow.jet_hasDerivAt` and `flow_differentiable` prove actual spatial differentiation and entireness by dominated local differentiation. `RiemannEvenEvolution.jet_time_hasDerivAt` proves actual real-time differentiation, using a local time majorant with tilt |t0|+1. `flow_iteratedDeriv` identifies every spatial derivative. `flow_eq_cosine_integral` proves the displayed integral identity. The exact m=2 agreement with the frozen quartic family is `RiemannEvenFlow.flow_quartic` (and `RiemannEvenDomain.weighted_quartic`), both by definitional equality.

The actual evolution theorem is
\[
 \partial_tH_{t,2m}=(-1)^m D_z^{2m}H_{t,2m};\qquad
 \partial_tH_{t,6}=-D_z^6H_{t,6}.
\]
These are Lean `HasDerivAt` theorems for genuine integrals, for every real t and complex z. They are not assertions about a merely formal exponential operator or positive-time stable stochastic law.

## Theorem-level reuse audit

| Existing machinery | Exact use or limitation |
|---|---|
| `RiemannQuarticKernel` and `RiemannQuarticDomain` | Reuse the actual kernel, positivity, continuity, arithmetic exponential envelope and envelope constant. Generic polynomial-versus-exponential decay proves the new integer tilt domains directly. |
| `RiemannQuarticFlow.halfLine` | Reuse the exact measure; no duplicate integration space. The frozen quartic flow is literally the m=2 instance. |
| `ComplexRootExponentialDomain.phase_norm_bound` | Reuse the complex exponential norm estimate. Its stochastic-law integrability results are not the actual growing arithmetic-kernel domain. |
| `BandLimitedEntireCalculus.phase_derivative` | Reuse pointwise Fourier differentiation, then discharge the actual unbounded integral domain separately by the new moment estimates. No band limitation is assumed for this kernel. |
| `HigherEvenHeatTransformLimit.fourier_exponent` | Reuse the verified Fourier-power identity to derive the growing-flow sign, rather than guessing from order. |
| `HigherEvenBandGenerator.generator_tendsto` | Its stable generator is (-1)^(m+1)D^(2m), with explicit bandlimited-test hypotheses. The present growing transform has the OPPOSITE sign (-1)^mD^(2m). At m=3 these are +D6 and -D6 respectively. Positive-time stable process conclusions cannot be transferred unchanged. |
| Quartic saddle/curvature/contour and local cosine zero machinery | The arithmetic-kernel derivatives and abstract local analytic criteria are candidates for reuse with all hypotheses checked. Quartic polynomial coefficients, remainders, stationary equations and uniform matching constants are not automatically sixth-order statements. No A6 zero theorem is proved here. |

## Manuscript and literature audit

The read-only `ResearchSources/a4/ibm_laguerre_polya.tex` gives the growing-multiplier signs and a general polynomial nonpreservation argument at lines461-490. Its literal arithmetic kernel/positive quartic tilt occur at lines521-534. Preserved SHA256: `EAF31754F5F993EF8EB33A1917484D70F6B62F5B37A907AD85F097C3C5589D96`. The new actual PDE verifies the integer sign correspondence on its precise integral domain. The manuscript's generic polynomial nonpreservation claim does not decide eventual zeros of this particular kernel. No manuscript conjecture is accepted as a theorem, and no novelty claim is made.

Primary literature reviewed: Charles M. Newman, *Fourier Transforms with Only Real Zeros*, Proceedings of the AMS61(2),245-251 (1976), [primary paper](https://sites.math.northwestern.edu/~auffing/papers/Newman.pdf), Theorems1-3. Theorem1 contracts a zero strip under a positive Gaussian multiplier, assuming a real even integrable function, sufficient decay, and an initial zero strip. Theorem2 concerns all positive Gaussian dampings of an even nonnegative finite measure. These are quadratic statements; replacing the Gaussian exponent by u6 is not licensed by those theorems. Their hypotheses and multiplier directions must be checked before any application. OCR-garbled product formulas were not used as proof evidence.

## Exact open obligations and next productive target

No expanding A6 real-rootedness window, actual sixth-order saddle theorem, contour dominance theorem, global re-entry result, LP membership or threshold comparison has been established by1161. The first direct target is the actual sixth-order real saddle and its escaping stationary scale. The stationary phase has tilt tu6 and slope6tu5 plus the actual kernel logarithmic slope. Kernel curvature estimates may transfer, but stationary comparison and higher-degree Taylor remainders must be proved anew. Uniform outer and transition zero control must ultimately share compatible scales before any global statement.

The integer integral/evolution theorem is a coherent analytic foundation, but this checkpoint does not declare the conditional real-exponent investigation open. Its mathematical applicability must be assessed explicitly at that later gate; no arbitrary-order zero-localization hierarchy or parameter-uniform limiting theorem is asserted. Local uniform convergence, Hurwitz hypotheses and zero escape are not investigated here.

## Verification

Checkpoint1161 passed the pinned FULL root build5892 jobs and fresh COMPLETE transitive axiom audit35390 declarations, only propext, Classical.choice and Quot.sound. All32 new public declaration types were ACTUALLY READ UNABRIDGED in groups1-10,11-21,22-32; all five definition bodies and all three complete final sources were read. There are27 public theorems and5 definitions; private/generated declarations are also covered by the root audit. Manifest1817 covers every Foundation/root source; frozen sources are unchanged except the reviewed root imports. All107 archived files,43Incoming/42distinct hashes and11fully read A4 manuscripts retain their recorded hashes. No manuscript, pinned dependency, unrelated draft or scanner/cache modification.

Evidence: `.lake/stardust-1161-working-checkpoint.json`, `stardust-1161-full-build.log`, `stardust-1161-audit.log`, `stardust-1161-public-types.json`, `stardust-1161-verification.json`. Original preserved1158 work was not previously certified; this checkpoint completes its fresh full-build/axiom/type/body audit together with the current frozen quartic root. Exact six-path commit, audit receipt and PRIVATE exact-ref verification close this checkpoint.

## Stardust checkpoint 1162 — actual escaping nondegenerate integer-even saddles

October20,2026. Previous goal turn classified PROGRESS: actual integral/evolution checkpoint8029b22481dd6a6405b582787cf05bf953e0c69e was completed, fully audited, committed and privately verified. Integer A6 remains active; no real-exponent, limit, independent A2 or final multichannel branch opened.

NEW Foundation/RiemannEvenRealSaddle.lean proves genuine global maxima of the ACTUAL positive amplitude a_{m,t}(u)=exp(tu^(2m))Phi(u) on u>=0 for every natural m and every real t. For each fixed POSITIVE integer m, ALL global maximizers eventually escape EVERY prescribed fixed compact interval as real t->infinity. This is neither a model critical point nor a selected late-time subsequence. Positivity, continuity, tail decay and compactness are discharged using the actual kernel/domain; the kernel derivative is directly reused rather than duplicated. Escape requires m>0 explicitly.

The exact phase slope is S_{m,t}(u)=2m*t*u^(2m-1)+Phi'(u)/Phi(u). At any positive global maximum it vanishes, with both real and actual complex-kernel stationary equations proved. Its actual derivative is 2m*t*(2m-1)*u^(2m-2)+realLogCurvature(u), using the verified kernel-only log-curvature derivative. No quartic polynomial coefficient is transferred unchanged.

Quantitative actual stationary estimates: at any stationary u>=1,
  4*pi*exp(4u)-12 <= 2m*t*u^(2m-1) <= 4*pi*exp(4u)-8.
For m>0,t>=0,u>=2m, the stationary phase curvature obeys
  deriv S_{m,t}(u) <= -12*pi*exp(4u)-7 < 0.
The proof controls (2m-1)u^(2m-2) by u^(2m-1) on the EXPLICIT order-dependent domain u>=2m, then reuses the kernel log-slope lower bound and log-curvature upper bound. These constants do not imply an order-uniform threshold or domain. Combining escape with this estimate proves that ALL actual global maxima are nondegenerate at EVERY sufficiently late time, with no exceptional-time exclusion. For each R>=0 there is an eventual actual global maximum u>R satisfying both stationarity and strictly negative phase curvature. The m=3 theorem explicitly gives 6tu5+Phi'/Phi=0 and negative curvature for all sufficiently late times, not just generic times.

Exact reusable names: RiemannEvenRealSaddle.exists_global_max; maxima_escape; max_real_stationary; max_complex_stationary; stationary_scale_bounds; stationary_phaseSlope_deriv_upper; eventually_all_maxima_nondegenerate; eventually_exists_nondegenerate_saddle; sixth_order_eventually_exists_nondegenerate_saddle. Frozen QuarticRealSaddle.kernel_hasDerivAt/kernelDerivative_real and QuarticCurvature.realLogSlope_hasDerivAt/realLogSlope_bound/realLogSlope_lower/realLogCurvature_upper are reused on their proved domains. No manuscript claim is used as an assumption or novelty asserted.

Boundary: no uniqueness of the integer-order maximum, nonzero-frequency complex saddle branch, uniform inverse radius, actual contour estimate, integrated Gaussian approximation, A6 real-rootedness window, global re-entry, LP statement or threshold comparison follows yet. Next direct step is the actual complex slope/analytic inverse at these nondegenerate real centers, with precise theta/nonvanishing neighborhoods, followed by higher-order Taylor and contour bounds. This advances actual A6 saddle construction without pretending to have zero control. Parameter-dependent thresholds are retained; the real-exponent/limiting gate remains unopened.

Verification1162: pinned FULL root build PASSED5893 jobs(session83149,terminal0); fresh COMPLETE root transitive axiom audit PASSED35410 declarations(session70748,terminal0), only propext,Classical.choice,Quot.sound. ALL14 new public declaration types ACTUALLY READ UNABRIDGED together from fresh audit output; the single phaseSlope definition body and complete assembled source/proofs reviewed. Separate finite-threshold Lean checks(session32042,terminal0) verify existsT/foralllater/ALLmaxima nondegeneracy and existsT/foralllater/existsactualmax>R with explicit sixth-order stationary equation; standard3 axioms printed. Final standaloneprobe92012 passed; earlier derivative-function normalization and natural-subtraction power rewriting failures were corrected before final success. Intermediate probe56259 passed before the final complex-stationarity addition. No admitted proof/new axiom/native admission.

Manifest1818 covers every Foundation/root source; prior1817 unchanged except the reviewed root import. All107archive,43Incoming/42distinct and11fully read A4 manuscript hashes remain unchanged. No manuscript, pinned dependency, unrelated draft or sync scanner/cache modification. Evidence .lake/stardust-1162-working-checkpoint.json, stardust-1162-full-build.log, stardust-1162-audit.log, stardust-1162-finite-check.log, stardust-1162-public-types.json and stardust-1162-verification.json. Exact four-path mathematical checkpoint, receipt and PRIVATE exact-ref verification follow.
