# IBM manuscript audit and focused campaign

Opened after the final pseudoprocess freeze commit `a69daf025f2c9ef28e39124f2f4a5a301494666f`, 2026-10-18. The indefinite Stardust goal remains active. Manuscripts remain read-only; no manuscript assertion supplies a Lean axiom.

## Exact source and version

The requested `ResearchSources/Incoming/EJP2605-044RA0(2).pdf` is absent. The preserved available source is `ResearchSources/ibm/EJP2605-044RA0.pdf`, 24 pages, 595476 bytes, SHA-256 `5A91914A535AD19BDDF219D7A9AB9F8B5F20A52DD4EC6ED7333AA80B403182BE`. Its title is *A Mollified Itô–Tanaka Formula for Iterated Brownian Motion and Its First-Chaos Dual Closure*. This hash matches the previous read-only source audit. No identity with the absent duplicate version is asserted. The PDF has placeholder journal metadata; publication or acceptance is not inferred.

The Incoming inventory remains a separate baseline: 43 files, 42 distinct hashes. It includes the Clark–Ocone manuscript and `ym_ns_dictionary.tex`; the IBM PDF above is outside Incoming. The previous freeze document's claim that the IBM PDF was included in those 43 files is corrected without changing the inventory or source.

Selective primary review: pages 3, 12, 18–19 and 22, including rendered pages 3, 12, 18 and 22. Fresh text and renders are under ignored `tmp/pdfs/stardust-ibm-1046/`. The older `ResearchSources/ResearchAudits/EJP2605_044RA0_SOURCE_AUDIT.md` is historical analysis, not instructions or a verified theorem. It remains unchanged.

## Actual manuscript obligations and existing Lean coverage

| Obligation | Existing verified foundation | Remaining distinction |
|---|---|---|
| Genuine independent continuous scenery and clock; actual IBM composition | `IBMConstructedSources`, `IBMSourceLaws`, `IBMContinuousComposition` | Already constructed; do not replace by an assumed process. |
| Mollified spatial chain rule, covariance cancellation and finite-horizon integrability | `IBMConstructedChainRule`, `IBMOffsetTranslation`, `IBMBoundaryVariance`, `IBMFiniteHorizonEvaluation` | Spatial chain rules and integrability do not alone prove the complete manuscript Itô–Tanaka decomposition. |
| Fixed-mollifier actual cubic correction and source-divergence recovery | `IBMClockCubicJointTimeL2`, `IBMClockCubicBochnerRecovery` | Actual joint/time L² and graph recovery are verified at fixed mollifier. No uniform shrinking-mollifier bound follows. |
| Spatial negative-Sobolev target and random derivative/boundary assembly | `IBMNegativeSobolevBounded`, `IBMNegativeSobolevRandom`, `IBMDeltaBoundary`, `IBMRandomBoundary`, `IBMDualDistribution` | These are actual Bessel-potential distributions and bounded Bochner maps. Identification of the manuscript's physical white-noise kernel with their inputs and convergence of those actual inputs remain obligations. |
| F1, pages 22–23: cross-sector summability as mollifier vanishes | Gaussian chaos, closed divergence, first-chaos obstruction and fixed-scale recovery | No global uniform weighted sector bound or convergent full correction has been proved here. Fixed-scale recovery cannot be advertised as F1. |
| F2, pages 18–19: random-functional L² limit of the boundary layer | Actual Brownian Tanaka residual, smooth curvature mass realization and continuous mass limit | The manuscript's compactly supported boundary residual must be connected to this actual clock mass with the correct normalization. An expectation limit is insufficient. |
| F3, pages 12 and 22: density of the maximal intrinsic IBM pullback core | Closed source derivative, fiber lift, actual unmollified source derivative below | The joint clock derivative and approximation by IBM-observable elements remain separate. Nonmembership of one observable does not imply nondensity. |

## Discovery1046: actual unmollified partial scenery derivative

`Foundation/IBMUnmollifiedSourceDerivative.lean` reuses the actual source derivative and the existing Bochner closed-operator lift. At each time t it proves:

* The existing class `randomSourceL2 t` belongs to the lifted closed scenery derivative domain. No derivative-domain hypothesis, mollification or new process is supplied.
* Its derivative is the actual Bochner-L² field obtained from the existing first-chaos gradient. Almost every clock sample has the constant scenery gradient given by the embedded Brownian Hilbert direction at `|Y_t|`.
* The gradient norm equals the observable's Bochner-L² norm, hence is finite. This concerns the partial scenery derivative, not a falsely bounded full derivative on all Gaussian observables.
* The actual mollified fields and their actual partial scenery gradients lie in that same closed graph and converge together in Bochner-L² product norm to the unmollified graph pair.
* Almost every section of the constructed continuous-path IBM coordinate agrees with the existing unmollified source class and lies in the scenery derivative domain.

Thus page 12's rationale that unmollified scenery-at-clock evaluation lies outside the scenery derivative domain does not survive the actual partial-source construction. The result does not supply the joint clock derivative, IBM-observable graph approximations, density of the intersection core, or an intrinsic adjoint. F3 itself remains open. The spectral-to-physical-white-noise kernel identification is also not silently assumed by this source-Hilbert proof.

## F2: precise next analytic route, not a completed Lean theorem

Here is a conditional reduction with an explicit topology and normalization. It is a research calculation; the required occupation-field inputs and actual manuscript coefficient identities have not yet been constructed in Lean.

Write v_e(r)=E_X[(X_r^e)^2], a_e(r)=Cov_X(X_r^e,∂_r X_r^e), and Q_j(v)=E[f^(j)(x+sqrt(v)N)] for a standard normal N. For the even mass-one Brownian scenery convolution, direct covariance differentiation suggests

v_e''(r)=2 rho_e(r), a_e(r)=v_e'(r)/2,

b_e(r)=(a_e(r)^2-1/4) Q_4(v_e(r)) + rho_e(r) Q_2(v_e(r)).

These must be proved from the existing actual covariance formula, including the boundary, rather than assumed from the bulk cancellation. On the layer 0≤r≤ce, |a_e|≤1/2 and v_e=O(e). For Schwartz f, Q_2(v_e)→f''(x) uniformly on the layer; the first term has integral O(e). Evenness gives integral_0^infinity rho_e=1/2. Consequently the candidate scalar layer mass is

m_e=integral_0^infinity b_e(r)dr → f''(x)/2.

To turn this into the requested random-functional result, suppose the actual reflected-clock occupation field L_t^r(|Y|), r>0, has the correct occupation identity and is mean-square continuous at the boundary with limit 2 L_t^0(Y). Let C bound integral|b_e| and let eta(e) bound the L²(clock) distance of L_t^r(|Y|) from 2 L_t^0(Y) on 0<r≤ce, with eta(e)→0. Bochner integration and the triangle inequality then give the explicit estimate

‖integral_0^t b_e(|Y_s|)ds - f''(x)L_t^0(Y)‖_L²
≤ C eta(e) + |2m_e-f''(x)| ‖L_t^0(Y)‖_L².

Both terms tend to zero under exactly these hypotheses. The correction's prefactor 1/2 then gives boundary limit (f''(x)/2)L_t^0(Y), whose expectation matches the manuscript's integrated source f''(x)sqrt(t/(2pi)). This is a random L² criterion, not an inference from equality of expectations. A full spatial local-time field is currently not identified in the IBM modules; constructing one merely for this purpose may be avoidable by applying the existing clock C² Itô/Tanaka approximation directly to the averaged mollified scenery function. Prefer that existing-process route if it closes the same estimate with less infrastructure.

No F1–F3 problem is declared solved at this checkpoint. Next priority is the actual F2 boundary coefficient/clock-mass identification, while preserving the distinction between partial scenery regularity and joint intrinsic regularity.

## Discovery1047: actual boundary curvature and its exact half-mass

`Foundation/IBMBoundaryCurvature.lean` closes the deterministic boundary-covariance identification needed in the preceding F2 route. It starts with the actual Gaussian-L² variance already represented by the two-sided Brownian covariance integral. For a continuous mass-one offset kernel it proves the exact scalar formula

V(x)=x+C+2 N(x),

where C is the existing offset covariance constant and N(x)=integral rho(-r) max(-(x+r),0)dr on the fixed offset window. The latter is identified with actual interval primitives when the moving boundary lies inside the window. Fundamental-theorem-of-calculus differentiation gives V'(x)=1-2 integral_a^(-x)rho(-r)dr and V''(x)=2rho(x) there. No local-time field, white-noise kernel identification or manuscript contraction rule is assumed.

For the original normalized smooth IBM bump, not an auxiliary smoothing family, this proves on |x|<R_n:

‖V_n(x)‖² + inner(U_n(x), W_n(x)) = rho_n(x),

inner(U_n(x), V_n(x)) = 1/2 - integral_(-R_n)^(-x)rho_n(-r)dr.

Here U_n is the actual mollified scenery and V_n,W_n its first and second spatial derivative fields; the scalar variance V(x) in the preceding paragraph is a different object. The identities are derived by comparing the actual variance derivatives with the existing Hilbert covariance derivative formulas. The cross-covariance at x=0 is proved zero using the concrete kernel's evenness and exact normalization.

The actual bracket's Lebesgue integral over [0,R_n] is proved exactly1/2. Endpoints are handled through nonatomic interval integral identities. The strict interior pointwise formula is not extended to endpoints by an unjustified substitution. In the positive bulk x>R_n the existing verified covariance cancellation remains applicable.

This verifies the bracket and normalization portion of the F2 calculation. It does not yet identify the general Schwartz-test residual b_n or prove its scalar mass limit, and it does not prove the random L² clock limit. A direct next process-level target is integral_0^t rho_n(|Y_s|)ds→L_t^0(Y) in L² for the already constructed clock and Tanaka mass. This is the boundary contribution for quadratic tests (outside the manuscript's Schwartz class); it would establish a genuine random limit and can serve the general bounded-coefficient argument. Prefer deriving it from the existing clock C² Itô and Tanaka approximations, with actual uniform terminal and predictable-field estimates, rather than assuming an unconstructed spatial local-time field.

## Discovery1048: genuine unweighted clock boundary limit in L²

The preceding process-level target is now verified, not a hypothesis. Write rho_n for the repository's original compact normalized IBM bump, Y for its constructed continuous Brownian clock and v_n(r)=E_X[(X_r^n)^2] for the actual scenery variance. `IBMVarianceClockGeometry` proves v_n is C² on the whole real line and v_n''=2rho_n everywhere. The strict-layer and exterior formulas are joined at the endpoints using actual continuity and Lebesgue almost-everywhere equality. It proves monotonicity of v_n', the global bound |v_n'|≤1, v_n'(0)=0, pointwise v_n'→sgn, pointwise v_n→|·|, and the common growth bound |v_n(r)|≤|r|+2. These facts concern the actual variance, not a surrogate absolute-value smoothing family.

`IBMBoundaryClockLimit` applies the existing Brownian C² Itô theorem to v_n. Its second-derivative bound is allowed to depend on n; no uniform C² bound is asserted. For each n and fixed finite horizon T the exact identity in the actual Gaussian L² space is

v_n(Y_T)-v_n(0) = integral_0^T v_n'(Y_s)dY_s + B_n(T),

where B_n(T)=integral_0^T rho_n(|Y_s|)ds. The stochastic term uses the original completed predictable Brownian integral. Actual Bochner representatives and Fubini identify B_n with this literal time integral along the constructed continuous clock; square integrability of that random functional is proved. Kernel evenness accounts for the reflection.

The actual predictable integrands converge in time/probability L² to sgn(Y); their stochastic integrals converge in Gaussian L² by continuity of the verified Itô map. The terminal values converge in Gaussian L² by the actual scenery approximation and a common square-integrable Brownian majorant. The constant v_n(0) tends to zero. Consequently

B_n(T) → |Y_T|-integral_0^T sgn(Y_s)dY_s = L_T^0(Y)

in Gaussian L² for every fixed T. The target is identified with the coordinate L² class of the previously constructed continuous Brownian mass path. This is a genuine random-functional limit, not a statement about its expectation or an assumed local-time occupation field. No uniform-in-T or almost-sure full-sequence convergence is claimed here.

Scope: this resolves the unweighted mollifier clock limit required for the proposed F2 reduction. The full general Schwartz residual b_n still requires identification of its actual Gaussian averaged coefficients and quantitative control of the coefficient error and bounded shrinking-layer term. Neither F2 in that full generality, cross-sector F1, nor intrinsic-density F3 is declared solved. Next use the new actual L² boundary-mass limit to control those coefficient errors; do not replace them by equality of expectations or introduce a new process/local-time foundation.

## Discovery1049: bounded source-resolved chaos reuse review

At the user's request, reviewed the available *Source-Resolved Chaos Expansions for Iterated Brownian Motion* wrapper `ResearchSources/ibm/main.tex` and selected companion formulas. Its nine body sections are absent; a complete manuscript-specific formalization was not located in the searched workspace/original IBM directory, and a path clarification was requested without stopping useful work. Exact hashes, source references, theorem crosswalk and missing connections are in `IBM_SOURCE_RESOLVED_REUSE_AUDIT.md`. The available source uses X_(Y_t), whereas the current campaign uses X_(|Y_t|). A new verified actual-source covariance test distinguishes them at clock positions1,-1: covariance0 versus1. Reflected mixed-kernel formulas must be rederived.

`IBMBoundaryChaosReuse` directly reuses existing Gaussian number-sector projections: every fixed clock projection of the actual unweighted boundary mass converges in L² to the same projection of the constructed Tanaka mass, with the contraction error bound and actual Bochner time-integral interchange. Existing completeness and Parseval apply to each fixed-scale mass and its limit. No new joint-chaos framework or spatial local-time field is constructed. The companion's second-clock origin kernel passes an independent exact-arithmetic norm test, norm²=T/(6pi), but identification with the actual projected Tanaka mass remains unproved.

This review leaves F1's uniform sector tails/common dual topology and F2's actual general Schwartz coefficient errors open. Fixed-scale occupation projections and numerical variance budgets do not settle them. Next continue the actual F2 weighted residual estimate; this review is not a separate chaos campaign or permission to divert from the Itô–Tanaka objective.

Source-integrity note1049: during this review, archive `ibm/main.tex` changed externally from the inspected source-resolved wrapper SHA256897F68ED… to the energy-framework SHA256 `314D3B33B211ADE564F918C6E2EC363CCEE0C8C9F8D7209B8ECAD8105623283F`. No source write or restoration was performed. The matching original wrapper remains at `C:/Operator/ibm/main.tex`; companion sources, the IBM PDF and Incoming inventory retain their checked hashes. The reuse audit records the two observed versions and binds source references to the inspected wrapper rather than the replacement.

## Discovery1050: actual averaged-coefficient weighted boundary limit

Returned directly to F2 after the bounded chaos reuse review. `IBMBoundaryAveragedCoefficient` constructs, for any globally K-Lipschitz real test phi, the genuine scenery expectation

a_n(r)=E_X[phi(X_r^n)],

where X_r^n is the existing actual Gaussian-L² mollified scenery. Integrability and literal expectation agreement are proved; the scalar coefficient is not an assumed approximation. Continuity follows from actual L² scenery continuity and the verified Lipschitz composition map. On the original kernel layer |r|≤R_n, actual variance geometry yields

|a_n(r)-phi(0)|≤K sqrt(2R_n)=e_n, with e_n→0.

The coefficient error multiplied by the original nonnegative mollifier is globally bounded by e_n rho_n(|r|); support is handled explicitly, including where the mollifier is zero.

`IBMBoundaryWeightedClock` constructs the literal random time integrals of that error on the existing reflected Brownian clock. Their measurability and square integrability are proved, with actual L² classes E_n(T) satisfying

‖E_n(T)‖_L²≤e_n‖B_n(T)‖_L²→0,

using1048's actual B_n(T)→L_T^0(Y). The full weighted path integral W_n(T)=integral_0^T rho_n(|Y_s|)a_n(|Y_s|)ds is proved to equal phi(0)B_n(T)+E_n(T), and its actual L² classes converge to phi(0)L_T^0(Y). The target is also identified with the coordinate class of the constructed continuous mass path. No unproved boundedness hypothesis on the mass sequence or supplied convergence hypothesis on a_n is used. A verified derivative-seminorm Lipschitz bound specializes the result to every actual Schwartz coefficient test.

This closes the weighted mollifier portion of the proposed F2 reduction. It does not yet identify the manuscript's entire b_n. The bounded shrinking-layer term involving ((v_n')²-1) and the averaged fourth derivative still requires its actual random-L² vanishing proof. The general Gaussian Stein identity matching the actual correction expectation to these two coefficient terms also remains to be verified; polynomial moments alone are not substituted for it. F1 and F3 remain open. Next use the existing Brownian zero-occupation theorem and actual bounded coefficient domains for that shrinking-layer remainder, staying within the current Itô–Tanaka campaign.

## Discovery1051: bounded remainder vanishes; the two-term residual closes in L²

`IBMBoundaryLayerRemainder` now proves the previously open shrinking-layer estimate. For a bounded Lipschitz fourth-derivative coefficient test phi_4, its actual scenery average a_4,n is bounded by the same scalar bound M. The actual variance slope satisfies |v_n'|≤1; hence q_n(r)=((v_n'(r))²-1)a_4,n(r)/4 is bounded by M/4. For every fixed r≠0 it is eventually exactly zero, because the original mollifier radius tends to zero and both actual exterior slopes are ±1. These facts are proved from the actual scenery and its variance, not assumed as a kernel template.

For the constructed clock, the literal integrals integral_0^T q_n(|Y_s|)ds are measurable and square integrable, bounded in absolute value by MT/4. Brownian zero occupation at0 and time dominated convergence give almost-sure convergence to0 for each fixed T. A second dominated-convergence argument gives strong random L² convergence. No spatial local-time density, moment hypothesis on an unconstructed field, or exceptional endpoint extrapolation is used.

`IBMBoundaryResidualLimit` combines this with1050's actual weighted kernel integral. For Lipschitz phi_2 and bounded Lipschitz phi_4, it constructs

b_n(r)=rho_n(r) E_X[phi_2(X_r^n)] + ((v_n'(r))²-1)E_X[phi_4(X_r^n)]/4.

It proves that the coefficient also equals the literal covariance form with (Cov_X(U_n,V_n)²-1/4) multiplying the fourth coefficient. Thus the formula is linked to the actual source contractions. The literal time integral along the constructed reflected clock is proved square integrable, agrees with its constructed L² class, and converges strongly in L² to phi_2(0)L_T^0(Y). Both actual Schwartz coefficient domains are instantiated, with their Lipschitz and boundedness conditions discharged by verified Schwartz seminorm bounds.

**F2 status:** the random convergence of the two-term averaged residual is now verified. What remains is the general Gaussian Stein identification equating the manuscript's original correction integrand expectation, E_X[f''(a+U_n)V_n²+f'(a+U_n)W_n], minus its interior term, with this actual b_n when phi_2=f''(a+·) and phi_4=f^(4)(a+·). Until that identity, its domains and shifts are verified, do not declare the full manuscript F2 solved. The existing bounded C¹ scalar Stein theorem and static Gaussian rotation theorem are promising direct reuse; the polynomial moment identities are insufficient by themselves. F1 and F3 remain open. Keep the next main proof on this concrete source-calculus bridge.


## Discovery1052: genuine nonpolynomial diagonal Stein bridge by direct weighted-IBP reuse

Continued the central F2 source-calculus bridge after1051, without opening a separate chaos campaign. `IBMScaledGaussianStein` reuses `HelicalWeightedPressureIBP.stein_integrable` and `centered_second`, which were proved for the quarter-variance Gaussian with genuine weighted integrability. It establishes integrability of bounded continuous tests and their coordinate and coordinate-square products. It then proves first and centered second Stein identities at every real scale a, including a=0. Actual chain rules and integrability of the first two derivatives are discharged from bounded C2 domains; no boundedness of a coordinate times a bounded test is asserted.

`IBMFirstChaosDiagonalStein` identifies the law of the actual source W(u) with the pushforward of that quarter Gaussian by x ↦ 2‖u‖x, proves literal expectation transport, and verifies the bounded composition L2 and weighted L1 domains. For bounded C2 phi with bounded first two derivatives it proves

E[W(u)phi(W(u))]=‖u‖² E[phi'(W(u))],

E[(W(u)²-‖u‖²)phi(W(u))]=‖u‖⁴ E[phi''(W(u))].

The first identity requires only the first derivative bound. The source u is arbitrary, including zero, so no nondegeneracy hypothesis is hidden. These are nonpolynomial actual-source moment identities, rather than a supplied abstract Stein law or polynomial-only check.

F2 still requires the mixed-direction identities for E[phi(W(u))W(v)] and E[phi(W(u))W(v)²], their shifted derivative specialization, and equality with the original correction residual. The already verified conditional Wick projections and singleton source projection provide a direct candidate route; the diagonal identities now supply their analytic test pairings. F1 uniform cross-sector tails and F3 intrinsic density remain open. The source-resolved review remains bounded by its recorded missing body/formalization and reflected-clock convention limitations; no manuscript claim is certified from unavailable sections. Existing source baselines and Incoming inventory are preserved. Keep the next proof on the mixed-direction Stein bridge, not a general joint-chaos campaign.


## Discovery1053: actual mixed Stein identification closes the original F2 residual along the constructed mollifier sequence

The previous turn made verified progress in49b673043e062e8e9ae74a23fb83297260ccf819. Continued the central source-calculus bridge, reusing existing conditional Wick prediction rather than starting a separate chaos campaign. No source file was edited. The43-file Incoming inventory and the four IBM archive version baselines retain their hashes.

`IBMFirstChaosMixedStein` constructs the actual bounded test class phi(W(u)) in Gaussian L2 and proves it belongs to the sigma field generated by W(u). Orthogonal conditional projection preserves its pairings. Existing `conditional_firstChaos_projection`, `conditional_wick_projection` and `FractionalCurrentObservationObstruction.source_projection_single` reduce first and centered second mixed moments to1052's diagonal Stein identities. The coefficient (inner(u,v)/norm(u)^2)*norm(u)^2=inner(u,v) is proved even when u=0; no nondegeneracy hypothesis is introduced. The second Wick scaling identity is proved from actual representatives. Actual L1 integrability is proved for the first and square-weighted mixed products, and the uncentered second identity follows by a justified integral subtraction. Thus for bounded C2 phi and the stated bounded derivatives,

E[V phi(U)]=inner(u,v) E[phi'(U)],

E[V² phi(U)]=norm(v)² E[phi(U)]+inner(u,v)² E[phi''(U)].

`IBMCorrectionStein` uses the existing continuous Schwartz derivative operator recursively to construct every actual derivative test, shifted by an arbitrary real a. It proves their C2 smoothness, derivative identities, seminorm bounds and Lipschitz domains. The actual source correction is integrable and satisfies

E[f''(a+U)V²+f'(a+U)W]
=(norm(v)²+inner(u,w))E[f''(a+U)]+inner(u,v)² E[f^(4)(a+U)].

This holds for arbitrary source directions, including degeneracy, and every actual Schwartz f. The shift and derivative assumptions are discharged, not supplied as unresolved analytic hypotheses.

`IBMOriginalBoundaryResidual` applies that identity to the existing actual mollified scenery triple. It proves globally, including boundary endpoints, that norm(v_n(r))²+inner(u_n(r),w_n(r))=rho_n(r), directly from the verified variance second derivative. The original expectation minus its interior term (1/4)E[f^(4)(a+U_n)] is proved equal to1051's actual two-term residual. It also gives literal expectation agreement in terms of the existing wholeLineScenery and its spatial derivatives, with actual source integrability.

For every fixed Schwartz f, real shift a and finite T, the literal random clock integral B_n=integral_0^T b_n(|Y_s|)ds is square integrable and its actual L2 classes converge strongly to f''(a)L_T^0(Y), where L_T^0 is the previously constructed continuous Tanaka mass coordinate. The correction with its prefactor1/2 converges to (f''(a)/2)L_T^0(Y). This is random-functional L2 convergence of the original correction residual, not an expectation-only or polynomial-only substitute. The proof reuses1050–1051's actual clock estimates and requires no new spatial occupation density or local-time field.

Scope: this closes the F2 identification and fixed-shift, fixed-horizon random L2 limit for the repository's original normalized even bump sequence, radius2/(n+1). It does not prove a continuously indexed epsilon theorem for every external mollifier profile, uniformity over all shifts/horizons, or convergence of the full unaveraged joint-source correction. No such extension is inferred. The source manuscript's open random-functional target now has a genuine verified realization along this concrete approximation. F1 uniform cross-sector summability and F3 intrinsic core density remain open. Keep the next main investigation on a concrete F1 estimate or obstruction for the actual correction in a specified topology, using the existing source primitive and negative-Sobolev machinery; do not inflate fixed-sector convergence into F1. The bounded source-resolved chaos review and its missing-source limitations remain recorded. The indefinite goal stays active; pseudoprocess extension remains frozen.


## Discovery1054: full scenery-averaged correction closes in the entire clock L2 space

The previous goal turn made verified progress in57f75b42236fe2709044090c52826546d28cecd9. Investigated F1 immediately after the concrete F2 checkpoint. The existing `concreteMollifier_uniform_norm_le` is the productive estimate: the actual scenery L2 smoothing error is at most sqrt(R_n), uniformly over all spatial positions. This avoids a new chaos or occupation-density construction.

`IBMAveragedBulkClock` constructs the genuine unmollified source expectation A(r)=E_X[phi(X_r)] as the pairing of the existing Gaussian constant with actual Lipschitz composition. Literal expectation agreement and continuity are proved. The actual mollified expectation A_n already constructed in1050 is identified with the same composition pairing. Cauchy–Schwarz, the verified Nemytskii Lipschitz bound and the existing uniform scenery error give

sup_r |A_n(r)-A(r)| ≤ K sqrt(R_n).

For globally bounded Lipschitz phi, both averages have the same global bound M. The module constructs their literal occupation integrals along the existing reflected continuous clock, proves measurability and L2 membership, and proves the deterministic-to-random norm estimate

norm_L2(integral_0^T (A_n-A)(|Y_s|)ds) ≤ K T sqrt(R_n) → 0.

The auxiliary clock integral/class lemmas only package the existing bounded actual-path integrals and finite-measure Lp bound; they introduce no process, occupation density or new stochastic foundation.

`IBMSceneryAveragedCorrectionLimit` combines this bulk convergence for phi=f^(4)(a+·) with1053's original boundary residual. It constructs the actual random clock functional

P_n(Y)=integral_0^T E_X[f''(a+U_n(|Y_s|))V_n(|Y_s|)^2+f'(a+U_n(|Y_s|))W_n(|Y_s|)] ds,

using the already verified original correction expectation at each spatial position. Its literal representative and L2 domain are proved. The entire clock L2 class converges strongly to

f''(a)L_T^0(Y)+(1/4) integral_0^T E_X[f^(4)(a+X_(|Y_s|))] ds.

The first term is the actual continuous Tanaka mass coordinate. The second is the actual unmollified scenery expectation, not an assumed heat-semigroup coefficient. Every existing fixed clock-sector projection consequently converges by continuity of that projection. Strong convergence in the full clock space is stronger than merely proving convergence of individual clock coefficients.

Precise F1 scope: this proves closure of the full time integral of scenery expectations, including all clock fluctuations, along the same concrete shrinking normalized bump sequence and for each fixed Schwartz test, shift and horizon. It does not yet identify this functional as the zero-scenery projection of a constructed general-Schwartz joint time-integrated correction: the corresponding joint source/time measurability, integrability and Fubini bridge must be verified. Existing joint cubic results are insufficient for a blanket general-Schwartz claim. It does not supply m>=1 higher-source kernel limits, uniform cross-sector tails, or a common global dual norm. Those remain open, as do F3 and arbitrary-profile/uniform-parameter extensions. Next priority is the actual general-Schwartz joint Fubini bridge if it can be closed directly from the existing dyadic fields and growth bounds; otherwise pursue a concrete higher-sector estimate. No new general chaos campaign or source edits. The indefinite goal remains active, pseudoprocess extension frozen.


## Discovery1055: actual joint Schwartz Fubini and clock conditional expectation identified

The previous turn made verified progress in393642e4a4beec16506b8903078f3e6706ce289f. Continued the precise missing F1 averaging bridge. Direct reuse located `IBMFiniteHorizonEvaluation.secondCoefficient_horizon_integrable`, which already proves the required general bounded-test joint time/scenery/clock L1 domain. Reused it instead of rebuilding Gaussian growth infrastructure. Sources and dependency pins remain unchanged.

`IBMGeneralSchwartzFubini` defines the literal general-Schwartz correction from the existing constructed continuous mollified scenery/derivative evaluations, with the already verified shifted derivative tests. It proves joint time/probability measurability and instantiates the existing finite-horizon L1 theorem for every actual Schwartz test, shift, mollifier and finite horizon. The actual time-integrated correction is therefore integrable under the full independent scenery/clock law. At each fixed clock position its actual scenery mean equals1053's Gaussian source correction expectation, by the existing dyadic-coordinate almost-everywhere identities.

Product-measure associativity proves time/scenery integrability for almost every clock sample. Fubini then gives

E_X[integral_0^T actualCorrection_n(X,Y,s)ds]
=integral_0^T E_X[actualCorrection_n(X,Y,s)]ds

for almost every actual clock sample, with no supplied section-integrability hypothesis. The source mean is proved L2(clock), agrees with1054's literal averaged path and inherits its strong L2 limit.

`IBMClockConditionalCorrection` reuses `IndependentInnovationConditioning.conditional_integral` with the existing independent product coordinates. It proves that the genuine conditional expectation of the actual integrable joint correction given the entire clock source sigma field is exactly that source mean. A measure-preserving pullback isometry identifies its joint L2 representative with the lift of1054's averaged class. Thus the actual clock conditional expectations belong to L2 of the full joint law and converge strongly there to the lift of

f''(a)L_T^0(Y)+(1/4) integral_0^T E_X[f^(4)(a+X_(|Y_s|))]ds.

This closes the missing joint Fubini and conditional-mean identification, not just an abstract candidate coefficient. It supplies a genuine zero-scenery conditional block, retaining all clock randomness, along the concrete normalized bump sequence for each fixed test, shift and horizon.

Scope: the full unaveraged general-Schwartz correction has a verified joint L1 domain here, while its conditional expectation has the proved L2 domain and strong limit. This checkpoint does not assert a joint L2 domain or convergence for the full unaveraged correction, identify an orthogonal Hilbert projection whose input domain has not yet been proved, or obtain any higher-source sector limits or uniform cross-sector tail bounds. Conditional expectation is valid on the established L1 domain. F1 remains open beyond this zero-source block; F3 remains open. Next investigate a direct fixed-mollifier joint L2 estimate for the actual Schwartz correction from the existing Gaussian fourth moments and finite-horizon machinery, to make higher-source projections legitimate before seeking their singular limits. No new general chaos infrastructure or source edits. Pseudoprocess extension stays frozen; the indefinite goal remains active.


## Discovery1056: genuine general-Schwartz joint L2 domain and native clock projection

The previous goal turn made verified progress ine3e72c02be8655c9459ed844706819be83657ffe. Continued the concrete domain gap before any higher-source projection. All derivative fields are the existing jointly measurable continuous dyadic modifications, evaluated at the actual independently constructed Brownian clock. No new process or moment law is assumed.

`IBMDerivativeFourthDomain` identifies the actual mollified evaluation with the corresponding existing field, proves source fourth-moment integrability, and uses the verified first-chaos fourth moment to identify its literal source integral with3 times the fourth power of the actual source coefficient norm. Existing fixed-mollifier polynomial coefficient growth and the existing sixth clock moment then give

E_joint[(derivativeField_n,i(t))^4] ≤ C_n,i (1+15 t^3),

with a proved finite nonnegative constant C_n,i. The proof supplies joint integrability by product-measure slicing, not by equality of formal moments. Joint measurability and the continuous time majorant give actual fourth integrability on every finite time/joint-source product measure. All three derivative indices are included. Constants depend on n; no uniform bound is claimed.

`IBMSchwartzJointL2` proves the actual pointwise square estimate for the original general-Schwartz correction H_n,

H_n² ≤ 2 M_2² V_n^4 + 2 M_1² W_n²,

where M_j is the actual derivative Schwartz seminorm bound. The just-proved fourth domain and existing second-moment finite-horizon theorem yield genuine L2 of H_n on time times the independent joint source. Existing finite-measure L2 integration then proves that the actual scalar time integral belongs to joint L2, with its actual energy estimate. The joint equivalence class is constructed from that literal random variable and its representative agreement is verified.

The module applies Mathlib native condExpL2 to that proved joint L2 input and identifies it with1055's measure-preserving lift of the actual scenery-averaged clock class. Thus the previous L1 conditional-expectation identification is now also a legitimate L2 conditional projection of the actual full correction. No assumed input domain or constructed surrogate correction is used. This removes the specific domain caveat in1055 while retaining its strong convergence result for the clock block.

Scope: this is a substantive fixed-mollifier general-Schwartz construction, not a shrinking-mollifier uniform estimate. It does not prove full joint L2 convergence, higher-source sector limits, a common global dual norm, or uniform cross-sector tail summability. F1 beyond the zero-source clock block and F3 remain open. Next investigate an actual higher-source projection or its concrete kernel/energy obstruction using this now legitimate joint L2 input and existing projection/Bochner machinery. Keep the study tied to the original correction and a stated topology, rather than constructing a separate general chaos framework. The43-file Incoming inventory and four recorded IBM source versions preserve their hashes; no source/dependency changes. The indefinite goal remains active and pseudoprocess extension frozen.


## Discovery1057: exact higher-source quartic kernel and independent six-channel normalization tests

The previous goal turn made verified progress inad9e06e70c89cdf4e107074da6939c8fa6c7241c. Moved from the completed fixed-mollifier joint domain to a concrete higher-source kernel test. Selectively examined `ResearchSources/ibm/BidegreeAtlas.tex` around its channel enumeration (approximately848–923); its SHA256409FFE56EDB47DF23DAEEA788CEEC24E1C7ED9FF657BDCB6914708F8FA535D4E remains unchanged. The original source-resolved wrapper/body limitations recorded in1049 remain; this companion is not silently substituted for the missing manuscript body. No source file was edited.

`IBMQuarticSecondChaos` directly reuses the existing actual `IBMEvenCorrectionProjection.squareProduct`, `cubeProduct` and `quarticCorrection`, plus the verified Wick-sector projection. It constructs the centered cross product as an actual L2 class and proves its representative is UV-inner(u,v). Quadratic polarization, scaling and the actual quartic Wick decomposition prove the exact second-source projections of U²V² and U³W. Writing c=norm(u)², q=norm(v)², d=inner(u,v), e=inner(u,w), it proves for the existing quartic correction F=(1/2)U²V²+(1/6)U³W,

Pi_2 F = ((q+e)/2):U²: + 2d:UV: + (c/2)(:V²:+:UW:).

This is a genuine projection identity in the actual Gaussian L2 space, including degenerate and correlated directions, not a supplied tensor-kernel definition. For u=v=w and norm(u)²=1, the projected second-source energy is exactly32. The existing verified first-source projection for this same even quartic correction is exactly zero. This finite Gaussian example shows why first-source parity suppression cannot exclude higher-source energy; it is not asserted to be a realizable IBM derivative triple at a spatial point.

`IBMQuarticSecondGeometry` instantiates the identity with the existing actual mollified IBM source triple, proves its literal dyadic-field representative and identifies all coefficients from actual variance/covariance geometry, including boundary endpoints:

Pi_2 F_n(r) = (rho_n(r)/2):U_n(r)²:
 + c_n'(r):U_n(r)V_n(r):
 + (c_n(r)/2)(:V_n(r)²:+:U_n(r)W_n(r):).

The positive exterior formula has rho_n=0 and c_n'=1; the finite origin layer is retained globally. These remain spectral/source Hilbert Wick classes; no identification with a physical white-noise tensor kernel is assumed.

An independent Gauss–Hermite diagnostic tests the companion's general six-channel coefficients on the actual finite Gaussian model F=f''(a+U)V²+f'(a+U)W with f(x)=exp(-x²), a=.37. The collapsed candidate is

Pi_2 F = ((q+e)Q4+d²Q6):U²:/2 + 2d Q4:UV: + Q2(:V²:+:UW:),

where Qj=E[f^(j)(a+U)]. Six rank-one quadratic test directions span the finite three-dimensional symmetric quadratic space. Orders12,24,40,64,96 independently integrate the source moments and one-dimensional Qj in correlated, zero-observation and collinear cases. At order96 the maximum tested pairing errors are3.11e-15,3.55e-15,4.44e-15 respectively. Omitting the channel involving Q6 causes an error about.597 in the correlated case and4.331 in the collinear case. This is a numerical normalization diagnostic, not a rigorous counterexample or Lean proof of the full Schwartz formula. The quartic exact test has Q6=0, so it cannot validate that channel on its own. Reproducible ignored evidence: `.lake/stardust-1057-kernel-tests.py` and `.json`.

A productive next analytic connection is the formal product-rule observation that the verified quartic expression should equal (1/4) d_r²[c_n(r):U_n(r)²:]. The existing `GaussianQuadraticSourceHodge.mixedTarget` represents the same centered quadratic observable and already has source derivative/divergence graphs. Reuse that result when developing the bridge; its identification with the polarization helper and the needed Gaussian-L2 spatial quadratic derivative/product rule have not been proved here. Investigate whether existing polynomial/source bilinear machinery can establish it and whether it gives a useful bound after the actual clock integration. Spatial r differentiation is not automatically the manuscript white-noise-coordinate w derivative or an H^-1 bound. The full general-Schwartz six-channel identity, actual time-integrated higher-source kernel limits, F1 uniform cross-sector tails/global dual topology and F3 remain open. No separate chaos framework or unrelated campaign is opened. The indefinite goal remains active, with the concrete-family scope and pseudoprocess freeze preserved.


## Discovery1058: actual Gaussian-L2 second spatial primitive for the quartic second-source kernel

The previous turn made verified progress in0b9f8978aef2b6b5d05fa4d4fe1be9bfd4339256. Investigated the concrete derivative structure suggested by1057, reusing the existing centered quadratic source-Hodge target and actual convolution calculus. No source ingestion or manuscript edits. This is a focused supporting operator connection for F1, not a new chaos campaign.

`IBMQuadraticSpatialCalculus` proves that1057's quadratic polarization helper is exactly `GaussianQuadraticSourceHodge.mixedTarget`. Its source derivative and divergence graphs, paired by the existing `GaussianNumberSectors.graph_duality`, give the exact norm identity

norm(:UV:)²=norm(u)² norm(v)²+inner(u,v)².

Cauchy–Schwarz supplies a finite bilinear bound norm(:UV:)≤2 norm(u)norm(v). The actual centered product is proved linear in each source direction and packaged as a bounded bilinear map. Mathlib's native bilinear derivative rule then gives an actual Gaussian-L2 spatial product rule and the derivative of the second Wick power. This proves the analytic quadratic rule from existing source adjoint machinery; no unrestricted multiplication on all L2 variables or samplewise differentiation is used.

`IBMQuarticSecondPrimitive` uses the existing first-chaos embedding adjoint, whose composition with that embedding is the identity, to transfer the already verified whole-line scenery convolution derivative to its actual source coefficients. The zero and first scenery coefficient curves are therefore proved to have their actual first and second derivative coefficients as spatial derivatives. These are genuine source-Hilbert HasDerivAt statements, not freely chosen derivative candidates.

For the original normalized bump and actual scenery variance c_n, define the Gaussian-L2 curve

P_n(r)=(1/4)c_n(r):U_n(r)²:.

The module proves its explicit first derivative, then differentiates it again using the bounded quadratic rule and the verified c_n''=2rho_n. Comparing with1057's exact projected kernel yields, at every real r including both layer endpoints and the origin,

deriv(deriv(P_n))(r)=Pi_2(spatialQuartic_n(r)).

Thus the actual quartic second-source correction is a second spatial derivative of a concrete actual random-field primitive. The expression is globally valid before a singular limit; it is not an expectation identity or a formal distributional template. This makes explicit how the covariance contraction and origin-layer terms combine under differentiation.

Scope and next question: the derivative coordinate is the scenery evaluation position r, whereas the manuscript H^-1 closure uses its physical white-noise coordinate w. No equality of these coordinates, physical spectral/tensor isometry, H^-1 norm bound, or pairing with an unconstructed clock local-time field is inferred. The next productive test is whether the primitive's existing smoothing control yields a rigorously stated spatial weak convergence and whether that estimate survives the actual clock-time integration; a second derivative alone does not guarantee the needed bound for a rough clock occupation input. Reuse the verified actual clock process and Bochner integration instead of assuming a spatial density. General-Schwartz six-channel projection identification, higher-source singular limits, F1 uniform cross-sector tails/global dual topology and F3 remain open. The concrete-family and fixed-parameter scope, source hashes and pseudoprocess freeze are preserved; the indefinite goal remains active.


## Discovery1059: actual quartic higher-source kernel has a specified spatial weak limit

The previous turn made verified progress in4fef463efaecec68eeca01aead42ce16ede7fe03. Tested the newly verified primitive in a precise deterministic spatial topology, without identifying it with the manuscript white-noise-coordinate dual norm or the clock occupation input. No source/dependency changes or unrelated exploration.

`IBMQuarticPrimitiveLimit` constructs the actual unmollified source coefficient by applying the existing first-chaos embedding adjoint to the constructed source scenery. The existing genuine mollifier L2 convergence and continuity of that adjoint prove convergence of the actual mollified coefficients. Existing Wick continuity and actual variance convergence then give pointwise strong Gaussian-L2 convergence

P_n(r)=(1/4)c_n(r):U_n(r)²: → P_0(r)=(1/4)|r|:X_r²:.

The formal P_0 uses the just-defined actual adjoint source coefficient; no new random process or Gaussian law is supplied. The module proves continuity of these actual Gaussian-L2 curves and the common global bound norm(P_n(r))≤(|r|+2)². The bound is derived from1058's verified centered-product norm, the actual coefficient variance and existing global variance bound. The same bound passes to P_0. Bochner dominated convergence proves that every finite-interval continuous deterministic spatial test integral of P_n converges strongly in Gaussian L2.

`IBMQuarticSpatialWeakLimit` proves continuity and hence all finite-interval integration domains of the actual projected quartic kernel. It reuses the existing coefficient-continuity theorem and bounded centered-product map. Two justified vector-valued integrations by parts give, for every C2 scalar psi with psi(a)=psi(b)=psi'(a)=psi'(b)=0,

integral_a^b psi(r) Pi_2 F_n(r) dr = integral_a^b psi''(r) P_n(r) dr.

Consequently for a≤b the actual projected kernel test integrals converge strongly in Gaussian L2 to integral_a^b psi''(r)P_0(r)dr. This is a genuine higher-source weak spatial limit with its test class, endpoint conditions and probability topology fully stated and verified; it is not an assumed distributional kernel limit. It retains the actual mollifier origin layer through1058's global derivative identity.

Limits of this result: the test is deterministic and clamped C2, with each fixed interval and test. No operator-norm/Sobolev norm convergence is asserted. In particular a random clock occupation object is not a C2 test, and the spatial coordinate r is not the manuscript physical white-noise coordinate w. This result alone therefore does not close time-integrated F1 or provide a global cross-sector topology.

The next focused investigation should return to the actual reflected-clock correction rather than extending deterministic test spaces without a concrete estimate. A promising structural route is to compare the full quartic second-source correction, including its separate origin term, with the reflected-clock Ito identity for the primitive P_n. Formally the second projection of f(U_n), for f(z)=z^4/24, is P_n; the second projection of f'(U_n)V_n should be P_n'. Thus the full origin-plus-one-half-time-integral correction may be tied to a terminal primitive and its actual clock martingale. The required actual projection/clock-Ito identifications and joint energy estimates are not proved here. Do not drop the origin term, infer convergence of the clock stochastic integral from terminal convergence, or mistake this polynomial test for the general-Schwartz F1 theorem. Use existing reflected-clock and Gaussian Ito machinery if productive. Full general-Schwartz six-channel identification, higher-source clock-integrated limits and cross-sector tails, noise-coordinate dual identification and F3 remain open. Source hashes, fixed concrete mollifier scope and pseudoprocess freeze are preserved; the indefinite goal stays active.


Further targeted research calculation1059 (not a Lean result): consider first averaging the full second-source correction over the clock, the (2,0) direction. The candidate half-line occupation mean is w_T(r)=2 integral_0^T p_s(r)ds. If its actual Gaussian-kernel identities and the required integrability are verified, w_T(0)=2 E[L_T^0], w_T'(0+)=-2 and w_T''(r)=4p_T(r) for r>0 suggest

P_n'(0)E[L_T^0]+(1/2)integral_0^infinity w_T(r)P_n''(r)dr
=E_Y[P_n(|Y_T|)]-P_n(0).

The first boundary terms cancel exactly in this conditional calculation. This is a promising direct route for the clock-averaged higher-source block, which may be preferable to constructing a new full vector-valued reflected Ito theorem. The Gaussian heat/occupation-mean identities, endpoint decay, Bochner domains, actual correction origin projection and equality with the genuine clock expectation are obligations, not assumptions to add to a claimed result. No such identity or (2,0) limit is certified here. Prioritize investigating this narrow heat-kernel/clock-average route using existing laws and boundary mass before expanding stochastic infrastructure.


## Discovery1060: actual clock terminal candidate and the retained quartic origin channel

The previous goal turn made verified progress in2bb1d09869b91cae3ad08434f92b3e1660961ea2. Returned from deterministic spatial tests to the actual clock-averaged correction. This checkpoint constructs two required pieces of1059's proposed heat-kernel cancellation, without assuming that cancellation or declaring a (2,0) limit.

`IBMQuarticClockTerminal` uses the actual constructed continuous Brownian clock and1059's actual Gaussian-L2 primitive. The existing sixth-moment clock machinery gives an integrable common bound4(1+|Y_T|)^3 on norm(P_n(|Y_T|)). Joint-source density or an occupation field is not assumed. It proves genuine Bochner integrability of the terminal source fields and their unmollified limit. Dominated convergence then yields strong source-Gaussian-L2 convergence

E_Y[P_n(|Y_T|)] → E_Y[P_0(|Y_T|)],

and, since P_n(0)→P_0(0)=0,

E_Y[P_n(|Y_T|)]-P_n(0) → E_Y[P_0(|Y_T|)].

This is an actual clock expectation with values in the source L2 space, not a formal heat-semigroup coefficient. It proves convergence of the proposed terminal candidate only, until the drift-plus-origin identity is established.

`IBMQuarticOriginProjection` constructs the actual quartic origin source factor (1/6)U_n(0)^3 V_n(0), proves its literal constructed-field representative, and directly reuses1057's cube-product projection to prove

Pi_2[(1/6)U_n(0)^3 V_n(0)] = P_n'(0)
=(c_n(0)/2):U_n(0)V_n(0):,

where the last equality uses the verified variance slope at0. Thus the origin coefficient required in the candidate boundary cancellation is now identified from the actual source observable, not inserted to match the proposed formula.

Using the existing independent-product L2 tensor constructor and the actual continuous Tanaka mass coordinate, it constructs the joint source-projected origin term P_n'(0)L_T^0(Y). Its literal product representative is verified and Fubini gives its actual clock mean E[L_T^0(Y)]P_n'(0). The actual random mass factor is retained. No physical white-noise kernel identification, origin-term vanishing estimate or cancellation is inferred.

Scope clarification for the accumulated IBM audit: the general-Schwartz joint time/source domain and conditional projection constructed in1055–1056 concern the time-integrated curvature component, integral g_n''(|Y_s|)ds. The full manuscript Ito–Tanaka correction additionally has its separate origin term g_n'(0)L_T^0(Y), as well as the curvature prefactor1/2. The current quartic origin construction addresses that separate term; the earlier curvature results must not be advertised as already constructing the whole origin-plus-curvature correction or its singular limit.

Remaining central obligation: prove that the genuine clock average of the quartic origin-plus-one-half-curvature correction equals E_Y[P_n(|Y_T|)]-P_n(0). The next focused route is the Gaussian half-line heat/occupation-mean identity, its endpoint contribution and Bochner domains, reusing the actual clock law and mass normalization. The terminal convergence and identified origin coefficient do not themselves prove the identity. No new general reflected stochastic-calculus infrastructure has been introduced. Full general-Schwartz higher-source six-channel identification and clock-integrated limits, F1 cross-sector bounds/global dual topology and F3 remain open. Source hashes, concrete mollifier/fixed-parameter scope, pseudoprocess freeze and indefinite goal are preserved.


## Discovery1061: source-resolved IBM reuse review and genuine Gaussian heat-potential identities

At the user's request, refreshed `IBM_SOURCE_RESOLVED_REUSE_AUDIT.md` against the current F1–F3 campaign, without opening a separate chaos campaign. The source-resolved wrapper still has its previously inventoried hash897F68ED4BBF3445928FE0AEA0833442E73C475E230D6DBDD61E0D56908C0D45 at C:/Operator/ibm/main.tex; nine body sections and a manuscript-specific formalization remain unavailable in the searched locations. The archived main.tex remains the independently observed1049 energy-framework replacement; no source writes or restoration were performed. Available variance/atlas companions were selectively compared to actual Lean declarations, with retrieval limitations retained.

The review now distinguishes the genuine weighted F2 result1053 from the older1049 unweighted reuse. New `IBMSchwartzBoundaryChaosReuse` directly composes existing Gaussian number-sector contractions with `IBMOriginalBoundaryResidual.originalPathIntegral_tendsto`. Every fixed clock sector of the actual Schwartz residual converges strongly in clock L2 to f''(a)Pi_k L_T^0, including the correct one-half curvature coefficient. A verified contraction error estimate needs no new sector infrastructure. Parameters remain fixed and the mollifier sequence remains the concrete normalized shrinking bump. This does not identify a physical local-time multiple-Wiener kernel or exchange an infinite sector sum with a singular limit.

The complete source-resolved comparison records actual joint-L2 curvature input and conditional clock projection1055–1056, exact quartic second-source projection1057, its actual spatial primitive1058, deterministic spatial weak convergence1059, and the terminal convergence/separate origin projection1060. These are reusable specific theorems, not a claimed general Schwartz six-channel proof. The separate origin term is retained throughout.

Independent kernel scripts1049 and1057 were rerun with their source-hash assertions. Reflected first-clock cancellation and the exact candidate second-clock origin norm T/(6pi) remain useful normalization tests; actual identification of the second-clock kernel with Pi_2 of the constructed Tanaka mass remains open. The unreflected/reflected covariance discrepancy is an existing Lean theorem. The six-direction quadrature checks at order96 have errors below4.5e-15 with the full second-source candidate and large errors when its Q6 channel is removed. These are explicitly numerical diagnostics, not rigorous counterexamples or a general Lean formula. The exact quartic test has no Q6 term and cannot validate that channel.

At the existing heat-kernel proof break, completed `IBMClockGaussianTail`: actual continuous clock coordinate law, genuine vector-valued density integral identity, standard Gaussian density derivative and integrability, actual half-line tail integral, FTC derivative, nonnegativity, decay and tail(0)=1/2. Reuses existing Gaussian coordinate laws and GaussianCore rather than postulating a tail or occupation formula.

`IBMClockHeatPotential` defines p_T(r)=p_1(r/sqrt(T))/sqrt(T) and W_T(r)=4(sqrt(T)p_1(r/sqrt(T))-r tail(r/sqrt(T))). For T>0 it verifies p_T is the actual Gaussian density and rewrites actual clock expectations using it. Native derivative proofs establish W_r'=-4tail, W_r''=4p_T and W_T'=2p_T, plus W_T(0)=4sqrt(T)p_1(0) and W_r'(0)=-2. These are analytic identities of actual functions. They do not assume or yet prove W_T(r)=2 integral_0^T p_s(r)ds.

Next main IBM obligation remains the clock-averaged quartic origin-plus-one-half-curvature identity. Prove the potential's time-zero limit and time-integral domains, then the actual clock/time/source interchanges and half-line integration-by-parts endpoint terms. The existing terminal convergence is a candidate limit until this equality is established. General Schwartz higher-source six-channel identification, remaining-sector convergence, F1 common dual topology/uniform tails and F3 remain open. Spatial evaluation derivatives are not noise-coordinate H^-1 control. Full spatial local-time occupation-density factorization is still missing and is unnecessary for the direct heat route; do not build it merely to reproduce the manuscript's organization. The focused IBM campaign and indefinite Stardust goal remain active; pseudoprocess extension stays frozen.


## Discovery1062: genuine heat time integral and actual origin normalization in the quartic boundary identity

The previous turn made verified progress in4b862a44da0116a08bb2451b349894f785a46038. Continued the existing higher-source IBM proof after the bounded source-resolved review. This checkpoint discharges1061's initial-time/time-integrability obligation and identifies the stochastic origin coefficient; it does not assume the infinity boundary or a clock occupation factorization.

`IBMClockHeatOccupation` proves a global standard-density bound by p_1(0), measurability/nonnegativity of the actual heat density, and the near-zero bound p_t(r)<=p_1(0)t^(-1/2) for t>=0. The existing integrable-rpow theorem gives genuine time integrability on every finite interval. The square-root density product tends to zero; for r>0 the scaled tail tends to zero by the actual tail's atTop limit. Handling r=0 separately proves the right-hand initial limit W_t(r)->0 for every r>=0. It is essential to use this right limit: substituting t=0 into the original explicit formula is not a valid continuous extension for positive r.

The genuine FTC with endpoint limits now proves, for T>0 and r>=0,

W_T(r)=2 integral_0^T p_s(r)ds.

This is an actual Lebesgue time integral with its integrability verified, rather than an occupation-mean hypothesis. Nonnegativity of W follows. The result does not yet construct a spatial local-time field or establish the vector-valued source/time/clock interchange.

`IBMQuarticHeatBoundary` reuses the actual source primitive P_n, its derivatives and existing vector-valued interval integration by parts twice. For every real finite radius R and T>0 it proves

integral_0^R W_T(r)Pi_2 g_n''(r)dr
= E_n(T,R)-W_T(0)P_n'(0)-2P_n(0)+4 integral_0^R p_T(r)P_n(r)dr,

where E_n(T,R)=W_T(R)P_n'(R)-W_T'(R)P_n(R) is retained as an explicitly defined Gaussian-L2 vector. All finite-interval domains follow from actual continuity; no arbitrary endpoint-vanishing assumptions are inserted. Scalar multiplication/algebra then gives the exact finite-radius origin cancellation, still retaining one half of E_n(T,R).

`IBMClockOriginMean` proves the standard Gaussian density's atTop decay and actual first half-line moment using its native derivative and improper FTC. The actual standard absolute mean is2p_1(0), using the reflected scalar Lebesgue integral identity. Gaussian scaling and the constructed clock law give E|Y_T|=2sqrt(T)p_1(0), including T=0. Reusing the constructed Tanaka mass's existing expectation identity yields

E[L_T^0]=2sqrt(T)p_1(0)=W_T(0)/2.

Consequently `actual_origin_finite_cancellation` proves with the actual Tanaka-mass mean, for T>0,

E[L_T^0]P_n'(0)+(1/2)integral_0^R W_T Pi_2 g_n''
=2 integral_0^R p_T P_n-P_n(0)+(1/2)E_n(T,R).

Combined with1060's identified actual origin source projection, this fixes the stochastic coefficient and signs in the proposed cancellation. It remains a finite-radius spatial identity, not yet the entire clock-averaged stochastic correction.

Next central obligations: prove E_n(T,R)->0 in source L2 from actual polynomial growth and Gaussian density/tail decay; justify the half-line source-Bochner domains, reflected terminal density formula and actual time/source/clock Fubini connection to the curvature integral. Then1060's terminal convergence can be applied to an identified correction. General Schwartz six-channel projection, remaining higher-source singular limits, F1 common dual topology/uniform sector tails and F3 remain open. No physical white-noise-coordinate H^-1 theorem or full random local-time occupation formula is inferred. The focused IBM campaign and indefinite Stardust goal remain active; pseudoprocess extension remains frozen. No manuscript files or dependency/toolchain settings were changed.


## Discovery1063: vanishing actual heat endpoint and absolutely integrable quartic half-line reconstruction

The previous goal turn made verified progress in3d90cbac34062bec3c16a2604f0b83c7b34d285c. Continued the exact retained endpoint from1062, rather than assuming it vanishes or pivoting to unrelated chaos machinery. Four local IBM modules reuse actual source coefficients, existing Gaussian moments and native Bochner integration.

`IBMHeatTailDecay` proves integrability and the exact first standard-Gaussian tail moment integral_r^infinity x p_1(x)dx=p_1(r) for r>=0. Integral comparison gives the Mills estimate r tail(r)<=p_1(r), and hence tail(r)<=p_1(r) for r>=1. The explicit potential obeys W_T(r)<=4sqrt(T)p_1(r/sqrt(T)) for r>=0. Reusing Mathlib's Gaussian exponential asymptotics proves r^k p_1(r/a)->0 and (1+|r|)^k p_1(r/a)->0 for every natural k and a>0. These are actual function estimates, not asymptotic assumptions imported from a manuscript.

`IBMQuarticHeatEndpoint` uses the existing coefficient growth and verified bilinear cross norm bound to prove actual quadratic-source growth, then ||P_n'(r)||<=C_n(1+|r|)^3. The coefficient C_n is allowed to depend on the fixed mollifier; no uniform bound is claimed. The previous common primitive bound and the new Mills bound show both W_T(R)P_n'(R) and W_T'(R)P_n(R) tend to zero in source Gaussian L2 as R->infinity. Thus the actual endpoint E_n(T,R) retained in1062 vanishes for every fixed n,T>0.

`IBMQuarticHeatHalfLine` transfers the already proved actual clock-terminal Bochner domain through the constructed clock's Gaussian law and density. It proves absolute Bochner integrability on the half-line and the actual reflected terminal formula

E_Y[P_n(|Y_T|)]=2 integral_0^infinity p_T(r)P_n(r)dr.

The factor2 is proved by splitting the genuine vector-valued integral and reflecting its negative half-line; matching one-time laws alone is not asserted as a mixed-kernel equivalence. Combining this with endpoint decay proves that the genuine finite-radius origin-corrected heat integrals tend to E_Y[P_n(|Y_T|)]-P_n(0).

`IBMQuarticHeatDomain` closes the remaining absolute spatial-domain issue. The actual second-source curvature projection has polynomial growth ||Pi_2 g_n''(r)||<=D_n(1+|r|)^3, derived from the verified covariance-geometry formula, curvature bound and actual cross-source growth. Gaussian finite moments give integrability of p_T(r)(1+|r|)^k for every natural k. Consequently W_T(r)Pi_2 g_n''(r) is genuinely absolutely Bochner integrable on the positive half-line. Radius-limit uniqueness now proves the actual half-line source-L2 identity

E[L_T^0]P_n'(0)+(1/2)integral_0^infinity W_T(r)Pi_2 g_n''(r)dr
=E_Y[P_n(|Y_T|)]-P_n(0).

All terms are actual integrals or verified source objects; no endpoint assumption or unspecified test domain remains in this spatial identity. Direct reuse of1060's terminalDifference_tendsto gives strong source-L2 convergence of this origin-corrected half-line expression to E_Y[P_0(|Y_T|)] as the concrete mollifier sequence shrinks. This uses the exact identity at each n and does not exchange radius and mollifier limits or assert uniform-in-n endpoint estimates.

The next central IBM obligation is now specifically the stochastic integration bridge: identify the spatial heat-weighted Bochner correction with the actual time-integrated projected curvature averaged over the clock, with the time/clock/source measurability and Fubini domains proved. The half-line identity alone does not establish that bridge. Useful existing ingredients are BrownianClockWeightedEnergy.sigma_measurable, actual clock laws, Gaussian finite-moment bounds, the newly proved projected cubic growth and the existing finite-horizon integration machinery. After that identification the verified terminal convergence can yield an actual clock-averaged second-source correction limit.

This remains the quartic test f(z)=z^4/24, which is not Schwartz. General Schwartz six-channel identification, other higher-source limits, F1 cross-sector common dual topology/uniform tails and F3 remain open. No physical white-noise-coordinate H^-1 closure or full spatial local-time occupation-density field has been inferred. The focused IBM campaign and indefinite Stardust goal remain active; pseudoprocess extension remains frozen. All source and dependency settings are preserved.


## Discovery1064: actual clock/time Fubini bridge and projected whole quartic correction limit

The previous goal turn made verified progress in03f7dbf4b327246c2e407ee1a41bfeb9396e2553. Continued the remaining stochastic integration bridge from the absolutely integrable half-line identity. This checkpoint proves the clock/time/source-class identification for the actual second-source curvature process and commutes projection through the actual source-valued whole time correction.

`IBMQuarticHeatFubini` constructs the actual Gaussian-L2-valued heat integrand (2p_s(r))Pi_2 g_n''(r). Its joint strong measurability is derived from the explicit measurable heat kernel and the verified continuous source curvature. For each radius, its finite-time integral and norm integral are respectively W_T(r)Pi_2 g_n''(r) and the norm of that vector. Thus1063's actual absolute spatial Bochner domain supplies the full positive-space/time product domain by the existing product-integrability theorem. Genuine Fubini proves

integral_0^T integral_0^infinity 2p_s(r)Pi_2 g_n''(r)dr ds
=integral_0^infinity W_T(r)Pi_2 g_n''(r)dr.

No uniform moment estimate or spatial local-time field is substituted for this domain argument.

`IBMReflectedClockMean` packages direct actual Gaussian-law reuse for a strongly measurable observable on a proved reflected-clock Bochner domain. It transfers integrability through the actual clock law and density, then splits/refects the vector-valued Lebesgue integral. The resulting reflected expectation has the required factor2. This small reusable lemma is used for both the actual source vector and its norm, without identifying any unreflected mixed-source kernels.

`IBMQuarticClockMean` constructs the genuine source-Gaussian-L2-valued process H_n(t,omega_Y)=Pi_2 g_n''(|Y_t|), using the existing continuous Brownian clock and actual source curvature projection. Its fixed-time Bochner integrability follows from verified projected cubic growth and the existing clock cubic-moment domain. The actual-law lemma identifies both its clock mean and mean norm with the corresponding positive-space heat integrals. The already established heat product domain then transfers to a genuine finite-time/clock product domain for H_n. This proves Bochner integrability of the clock-dependent time integral and justifies clock/time Fubini. Consequently

E_Y[integral_0^T Pi_2 g_n''(|Y_s|)ds]
=integral_0^infinity W_T(r)Pi_2 g_n''(r)dr.

The previous half-line identity now gives the actual time-correction mean identity

E[L_T^0]P_n'(0)+(1/2)E_Y[integral_0^T Pi_2 g_n''(|Y_s|)ds]
=E_Y[P_n(|Y_T|)]-P_n(0),

and strong source-L2 convergence to E_Y[P_0(|Y_T|)] along the concrete shrinking-mollifier sequence. The stochastic integration bridge left open in1063 is therefore discharged at this explicitly projected source-class level, with the separate origin factor and the one-half coefficient retained.

`IBMQuarticTimeProjection` additionally proves continuity of the actual fourth-power Wick class, polarized square/cube products, and unprojected quartic source curvature. Every constructed continuous clock path therefore gives a genuine continuous source-L2 integrand and a justified finite-time Bochner integral. The existing Gaussian number-sector continuous linear map commutes with that integral. Constructing the whole source-valued correction

C_n(T,omega_Y)=L_T^0(omega_Y) originClass_n+(1/2)integral_0^T g_n''(|Y_s(omega_Y)|)ds,

it proves pointwise in the clock representative

Pi_2 C_n=L_T^0 P_n'(0)+(1/2)integral_0^T Pi_2 g_n''(|Y_s|)ds.

The projected whole correction is Bochner integrable over the clock, its actual clock mean is the identified correctedMean, and that mean converges strongly in source L2 to the actual terminal limit. The earlier actual field representatives and origin projection identify the source objects; no manuscript formula has been taken as an axiom.

Precise scope: this closes the quartic clock-averaged second-source model calculation for T>0, fixed horizon and the concrete mollifier sequence, in source Gaussian L2. The quartic test f(z)=z^4/24 is not Schwartz. This checkpoint does not assert a native joint-L2 orthogonal ((2,0)) projection of the entire unprojected correction: full unprojected clock/source L2 realization, scalar joint representative/time recovery and its norm domains remain to be identified if that native joint statement is required. It also does not prove the general Schwartz six-channel identity (in particular the Q6 channel), remaining higher-source limits, F1 common dual topology/uniform sector tails or F3. No physical white-noise-coordinate H^-1 closure is inferred. Next reuse the completed mean reconstruction to tackle those precise domains or the genuinely missing general-Schwartz source identities, rather than reopening the proved heat endpoint/Fubini obligations. The focused IBM campaign and indefinite Stardust goal remain active; pseudoprocess extension stays frozen. Manuscripts and dependency/toolchain settings are preserved.


## Discovery1065: native joint-L2 realization of the whole quartic correction and convergent source-two clock-zero block

The previous goal turn made verified progress inca3291a1d590bb71b50fc66dc58a96997cf18d27. Addressed the unprojected joint-L2 domain left open in1064, using the already verified onto product/Bochner equivalence and native conditional-expectation operator rather than inventing a different chaos space.

`IBMQuarticSourceGrowth` derives ||quartic(u)||^2=105||u||^8 directly from the verified actual eighth mixed Gaussian moment. It proves actual fourth-power norm bounds, bounds the existing polarized square/cube products and quartic correction, and obtains ||g_n''(r)||<=C_n(1+|r|)^4 for the unprojected source curvature. The bounds cover zero and linearly dependent coefficient directions. Constants are allowed to depend on the fixed mollifier; no uniform singular-limit bound is asserted.

`IBMClockEighthMoment` proves the actual clock identity E|Y_t|^8=105t^4 from the same source moment and the actual first-chaos clock law. It constructs the needed L2 domain for (1+|Y_t|)^4, proves the bound E(1+|Y_t|)^8<=256(1+105t^4), and proves genuine finite-horizon integrability of that time/clock majorant. The clock is the existing constructed continuous Brownian process, not a new assumed realization.

`IBMQuarticBochnerDomain` constructs the unprojected source-L2-valued time/clock field and proves its L2 domain on every finite horizon. The scalar finite-measure L2 integration theorem applied to its norm, together with the native Bochner norm-integral inequality, proves that the actual source-valued time integral belongs to clock-parametrized source L2. The independent actual Tanaka-mass origin term is in the same L2 space by the existing tensor constructor. Consequently the entire wholeCorrection, before source projection, has a genuine Lp(source GaussianL2,2,clock Gaussian measure) class, including its literal clock/source-class representative.

`IBMQuarticJointRealization` transports that whole class through the verified onto product/Bochner isometry to a native scalar joint L2 class. This module orders product coordinates (clock,source), explicitly; source/clock bidegrees continue to be named in the manuscript's source-first order. Almost every clock section of the joint representative equals the previously constructed actual whole source correction in source L2. This is a proved realization, not a hypothesized joint domain.

The existing source number-sector projection is transported through the same isometry. Its source-two component of the actual whole joint class has almost-every-clock sections equal to Pi_2 wholeCorrection. Using the existing source-class/representative Fubini theorem, the actual clock average of its scalar joint representative is identified almost everywhere with1064's correctedMean. Independence then identifies conditional expectation onto the full source sigma algebra. The native condExpL2 operator applied to this source-two joint input equals the product-space isometric lift of correctedMean.

Thus the actual reflected IBM quartic source-two/clock-zero block has the native joint L2 identity and limit

Pi_clock0(Pi_source2 C_n)=sourceLift(E_Y[P_n(|Y_T|)]-P_n(0))
 -> sourceLift(E_Y[P_0(|Y_T|)])

strongly in joint L2 for every fixed positive horizon along the concrete shrinking-mollifier sequence. The source projection here is the transported existing Gaussian number-sector operator; the clock-zero operation is the native conditional expectation onto the source sigma algebra. The separate origin term remains in the whole correction. No infinite sector-sum/limit exchange or uniform-in-n joint bound has been used.

Precise remaining obligations: the class-level joint realization and native block identification gap in1064 is now closed for this quartic model. A direct global scalar representative equating this inverse-curry joint class with the literal polynomial time integral of the chosen simultaneous scenery derivative representatives has not yet been proved; the established sections identify it with the native source-L2-valued Bochner time correction. If a pathwise scalar identity is needed, reuse BochnerL2RepresentativeFubini and the actual derivative-field joint measurability, rather than redefining the joint class. The quartic test f(z)=z^4/24 is not Schwartz, has no Q6 channel, and does not prove the general six-channel Schwartz projection or its singular limits. Other source sectors, F1 common dual topology and uniform summable tails, the physical white-noise-coordinate H^-1 closure and F3 remain open. The unreflected occupation manuscript's mixed kernels are not transferred across the clock convention. Next prioritize a necessary general-Schwartz source identity or the explicit scalar recovery if it supports the Itô–Tanaka claim; do not restart the already verified endpoint and mean-Fubini work. The focused IBM campaign and indefinite Stardust goal remain active; pseudoprocess extension stays frozen. Manuscripts and dependency/toolchain settings are preserved.


## Discovery1066: literal scalar quartic recovery and nonlinear single-observation source projection

The previous goal turn made verified progress in079c4ab6d432f9619e85c5215fef9fadfca076ba. Closed the explicit scalar representative gap in1065, then advanced a general-Schwartz supporting identity without opening an unrelated chaos campaign.

`IBMQuarticScalarRecovery` defines the literal polynomial curvature from the actual simultaneously constructed scenery fields U_n,V_n,W_n: (1/2)U_n^2 V_n^2+(1/6)U_n^3 W_n. Its spatial/source and time/source measurability follow from the existing jointly measurable fields and actual continuous clock paths. For every constructed clock path and finite horizon, source-class continuity gives a genuine source-L2-valued time integral. Direct reuse of BochnerL2RepresentativeFubini proves the actual scalar time/source product domain and identifies the native Bochner integral almost everywhere in the source with the literal scalar time integral. That scalar integral belongs to source L2 for every fixed clock path. A separate global time/clock/source measurability proof supplies a measurable scalar time integral on the full two-source space.

`IBMQuarticLiteralJoint` uses the actual continuous Tanaka mass path, rather than an unspecified mass representative, and the literal origin coefficient (1/6)U_n(0)^3 V_n(0). The resulting scalar whole correction is

C_n(T)=L_T^0(Y)(1/6)U_n(0)^3 V_n(0)
 +(1/2)integral_0^T [(1/2)U_n(|Y_s|)^2 V_n(|Y_s|)^2
                    +(1/6)U_n(|Y_s|)^3 W_n(|Y_s|)]ds.

It proves joint measurability and almost-every-clock equality of the source-L2 representatives with the native wholeCorrection. Combining those sections with1065's inverse-curry sections gives actual product-almost-everywhere equality of this literal scalar expression with the native jointClass. In particular the literal correction has genuine joint L2, and its toLp class equals the previous native joint class. The native source-two/clock-zero block limit is now a theorem of this literal scalar stochastic correction, not merely an unspecified inverse-curry representative. Product coordinates remain (clock,source) in these modules. This identifies the correction term; it does not by itself prove an entire mollified stochastic Itô–Tanaka identity including its martingale term.

`IBMScalarSecondProjection` then reuses verified single-observation Wick density and native number-sector projections. It removes the unit-variance restriction from the existing terminal projection theorem: for u!=0 and f measurable in the Gaussian observation W_u, the nth source projection is

Pi_n f = [<:W_u^n:,f>/(n! ||u||^(2n))] :W_u^n:.

The proof uses the existing closure of the one-observation Wick span, not an assumed Hermite expansion or a new chaos definition. Specializing to the actual bounded composition class and the existing second Stein identity proves

Pi_2[phi(W_u)]=(1/2)E[phi''(W_u)]:W_u^2:

for every bounded C2 phi with bounded first and second derivatives. The degenerate observation u=0 is separately verified; no division by zero or normalization hypothesis survives in this theorem. This is an actual Gaussian-L2 source projection of a nonlinear observable, not a polynomial-only test or scalar expectation identity.

Direct reuse of the verified shifted Schwartz jets gives, for every g in Schwartz, shift a, natural k and coefficient u,

Pi_2[g^(k)(a+W_u)]=(1/2)E[g^(k+2)(a+W_u)]:W_u^2:,

with the native jet domains and derivative bounds discharged. This supplies a genuine nonpolynomial coefficient projection needed in the general correction channels.

Remaining focused obligations: the full mixed product projection for g''(a+U)V^2+g'(a+U)W still needs its exact contractions and higher-order Stein identities. In particular a second-order single-observation formula does not establish the source-four coefficient of g'', hence does not prove or eliminate the Q6 channel. The quartic model cannot detect that channel. General-Schwartz higher-source singular limits, other source sectors, F1 common dual topology and uniform summable tails, physical white-noise-coordinate H^-1 closure and F3 remain open. The quartic model's literal/native realization, retained origin, half-line endpoints and clock/time mean bridge should now be reused as completed results rather than re-proved. Next investigate the necessary third/fourth single-observation pairings or a direct mixed Stein reconstruction using the existing conditional Gaussian and projection machinery. The focused IBM campaign and indefinite Stardust goal remain active; pseudoprocess extension stays frozen. Manuscripts and dependency/toolchain settings remain unchanged.


## Discovery1067: genuine polynomial-weighted Stein recurrence and source-three/source-four Schwartz coefficients

The previous goal turn made verified progress in833547fded6d8881a78aaa284956b08c6ae527ec. Continued the actual higher-order pairings needed for the general mixed correction, reusing the established weighted Gaussian IBP domain instead of treating polynomial multiples of bounded functions as bounded.

`IBMPolynomialWeightedStein` proves integrability of coordinate powers times bounded continuous scaled tests under the actual quarter Gaussian. Scaled polynomial tests, their actual product derivatives and coordinate multiples all have proved domains before invoking HelicalWeightedPressureIBP.stein_integrable. The resulting recurrence holds at every real scale, including zero. Transporting it through the verified actual first-chaos law gives, with W_u the existing first-chaos observation and v=||u||^2,

E[W_u^(k+1)phi(W_u)]=k v E[W_u^(k-1)phi(W_u)]+v E[W_u^k phi'(W_u)]

for every natural k and bounded C2 phi with bounded first derivative. At k=0 the first term is zero and the natural subtraction is harmless. All source polynomial-weighted moments in this formula are proved integrable, including degenerate u. No division by the scale is used.

`IBMShiftedJetMoments` specializes to the existing actual shifted Schwartz derivative jets. The recurrence gives the first four raw weighted moments and the third/fourth centered Hermite identities. In particular, for phi_j(z)=g^(j)(a+z),

E[(W_u^3-3vW_u)phi_j(W_u)]=v^3 E[phi_(j+3)(W_u)],
E[(W_u^4-6vW_u^2+3v^2)phi_j(W_u)]=v^4 E[phi_(j+4)(W_u)].

The domain proofs use actual Gaussian absolute moments and verified jet bounds; the identities are not restricted to polynomial observables. The generic weighted recurrence remains available for further finite-order pairings without rebuilding IBP foundations.

`IBMHigherScalarProjection` identifies these expressions with actual native Wick pairings and reuses1066's unnormalized terminal projection theorem. It proves

Pi_3[g^(j)(a+W_u)]=(E[g^(j+3)(a+W_u)]/6):W_u^3:,
Pi_4[g^(j)(a+W_u)]=(E[g^(j+4)(a+W_u)]/24):W_u^4:.

Zero observations are explicitly verified using the native Wick norm formula, so neither result has a nondegeneracy or unit-variance hypothesis. Together with1066's source-two formula, this supplies actual nonlinear single-observation source coefficients needed up to order4. In particular j=2 gives the source-four coefficient of g'', with the actual sixth-derivative expectation Q6 and factorial1/24. This verifies the scalar coefficient that the quartic test cannot detect; it does not yet prove its mixed-product contraction coefficient12 or the full correction projection.

Selectively reread the Stroock-kernel paragraph of the read-only `ResearchSources/ibm/BidegreeAtlas.tex`, lines818–845. SHA256 remains409FFE56EDB47DF23DAEEA788CEEC24E1C7ED9FF657BDCB6914708F8FA535D4E. The native source-three/four coefficients agree with its factorial normalizations for these orders. The paragraph's displayed variance-norm argument supplies compact-radius control; that argument alone does not justify a bound over all radii. A direct additional verified result gives ||Pi_m phi(W_u)||<=A whenever ||phi||<=A, uniformly over all source directions and all fixed sectors, by the actual bounded composition's L2 norm and the existing projection contraction. This is a native source-vector bound, not an identification with the manuscript's physical white-noise tensor kernels. It also does not provide uniform tails of an infinite sector expansion or bounds for multiplication by the singular V/W fields.

Remaining central obligation: prove the source-two projection of the actual mixed products g''(a+U)V^2 and g'(a+U)W, including the contractions from the now verified source-three/four scalar coefficients and the exact coefficient of Q6. Product domains, conditional Gaussian polynomial identities and the existing completed second-chaos machinery should be reused. No bounded multiplication operator on arbitrary Gaussian L2, unproved Hermite-series interchange, physical kernel identification or all-sector uniform bound has been assumed. General-Schwartz singular limits, other source sectors, F1 common dual topology/uniform summable tails, physical white-noise-coordinate H^-1 closure and F3 remain open. The focused IBM campaign and indefinite Stardust goal remain active; pseudoprocess extension remains frozen. All manuscript, dependency and toolchain files are preserved.


## Discovery1068: actual mixed fourth moments and the squared-factor source-two test

The previous goal turn made durable progress by recording the gated external-source audit in7098885; verified mathematical work resumes from1067. IBM remains the immediate campaign. The A(4) and A(2) successor mandates and October31 stopping date remain in force.

`IBMMixedFourthStein` reuses the existing actual singleton conditional Wick projection, zero-safe regression identity, shifted Schwartz moment identities and finite quartic polarization. It proves actual fourth mixed Wick pairing for every pair of source directions, including zero and collinear directions. No division by a possibly zero variance is left as a hypothesis, and no infinite Hermite-series interchange is used.

Let U=W_u, V=W_v, K=W_k be the existing Gaussian first-chaos observations, phi_j(z)=g^(j)(a+z), and Q_l=E[phi_l(U)] on the actual Gaussian source probability space. Write q=||v||^2, r=||k||^2, h=<v,k>, d=<u,v>, b=<u,k>. The new actual integral identity, with integrability proved independently from native L2 quartic representatives and bounded test composition, is

E[V^2 K^2 phi_j(U)]=(q r+2 h^2)Q_j+(q b^2+r d^2+4 h d b)Q_(j+2)+d^2 b^2 Q_(j+4).

The centered quadratic-test identity follows by subtracting the already verified genuine second mixed moment:

E[V^2 (K^2-r) phi_j(U)]=2 h^2 Q_j+(q b^2+4 h d b)Q_(j+2)+d^2 b^2 Q_(j+4).

At j=2 this retains the Q6 coefficient d^2 b^2 in the actual squared-derivative curvature term paired with the actual second-chaos Wick test. Thus the finite mixed contraction now goes beyond1067's single-observation scalar coefficient. It agrees with the square-factor portion of the six-channel candidate recorded from `ResearchSources/ibm/BidegreeAtlas.tex` lines848–923; the source hash is checked against the existing immutable baseline. No additional manuscript content was needed for this proof. The intermediate fourth-power formula E[V^4 phi_j(U)]=3q^2 Q_j+6q d^2 Q_(j+2)+d^4 Q_(j+4) is also verified as an actual integral on its proved domain.

Still open: the complementary W(K^2-r)phi_1(U) contraction, the full second-sector projection of the actual curvature using the existing joint L2 domains and verified density/separation, general-Schwartz singular limits, other sectors, F1 common topology and uniform tails, physical noise-coordinate H^-1 closure, and F3. The centered identity is a test-pairing theorem, not by itself the completed projection or a physical tensor-kernel identification. No arbitrary-L2 multiplication operator, generalized signed path probability, threshold conclusion or RH implication is claimed. Existing quartic native/literal reconstruction and limits remain available. All original manuscripts and dependencies are preserved.


## Discovery1069: full native second-source projection of shifted Schwartz IBM curvature

The previous goal turn made durable progress in6eacd02 by recording the final campaign and hard October31 research stop. Mathematical work continues from verified1068, commit797cef0357aab559960acf159dbd17b4c6e4654e. IBM remains immediate; no successor gate has been released. The latest explicit finite campaign sequence overrides historical indefinite-exploration wording.

`IBMMixedCubicStein` proves the complementary actual Gaussian contractions. For U=W_u, W=W_w, K=W_k and phi_j(z)=g^(j)(a+z), let Q_l=E[phi_l(U)], r=||k||^2, e=<u,w>, b=<u,k>, h=<w,k>. Actual singleton conditional Wick projection and the zero-safe regression identity give the third mixed Wick pairing. Finite cubic polarization then proves

E[W K^2 phi_j(U)]=(r e+2 h b)Q_(j+1)+e b^2 Q_(j+3),
E[W (K^2-r) phi_j(U)]=2 h b Q_(j+1)+e b^2 Q_(j+3).

The product is genuinely integrable, proved using the existing actual mixedCube L2 representative and bounded test composition. Zero directions and collinear directions are included. These identities complete the previously missing linear-factor test alongside1068's squared-factor test.

`IBMSecondChaosTesting` reuses the existing completed second-chaos matrix approximations, `GaussianQuadraticMatrixApproximation.boxCore_tendsto`, rather than assuming density. It identifies the existing mixedTarget with the existing Wick cross, proves quadratic Wick tests separate every native second-sector vector, and obtains a projection criterion for arbitrary ambient Gaussian L2 inputs. The criterion has a proved second-sector hypothesis and tests every Gaussian direction. No physical tensor-kernel isometry or new chaos space is postulated.

`IBMSchwartzSecondProjection` first proves actual L2 domains for multiplication by each bounded shifted Schwartz jet. This is bounded-observable multiplication; it asserts no multiplication bound for two arbitrary L2 variables. The independently realized correctionClass is a.e. the actual curvature

F=g''(a+U)V^2+g'(a+U)W.

For q=||v||^2, d=<u,v>, e=<u,w>, its completed native source-two projection is now verified:

Pi_2 F = ((q+e)Q4+d^2 Q6)/2 :U^2: + 2d Q4 cross(u,v) + Q2 (:V^2:+cross(u,w)).

Here cross(u,v) is the existing actual UV-<u,v> L2 representative, and :U^2: is the native Wick2 vector. The proof combines actual centered quadratic-test integrals with the proved separation criterion, so this is a completed projection equality, not only a finite polynomial test or numerical diagnostic. The Q6 term survives with coefficient d^2/2. The same machinery proves the general linear-factor projection

Pi_2[g^(j)(a+U)W]=Q_(j+1) cross(u,w)+(e Q_(j+3)/2):U^2:.

At j=1 it supplies the actual source-two origin term needed in the whole correction. Finally mollifiedClass substitutes the existing tripleCoefficient directions. Its representative is proved a.e. equal to the actual constructed IBMDyadicExtension.field curvature at every fixed n and real spatial r, and its native source-two projection is identified with the explicit formula. This supplies a genuine process-field connection, not a merely formal Gaussian triple.

Selectively reread `ResearchSources/ibm/BidegreeAtlas.tex` lines848–923 (channel enumeration and start of Theorem D). Its immutable SHA256 remains409FFE56EDB47DF23DAEEA788CEEC24E1C7ED9FF657BDCB6914708F8FA535D4E. The native formula agrees with the six finite channel contributions and their factorial normalizations1,1,4,12,1,3: in particular12 times Q6/24 gives the verified half coefficient. This is native Gaussian source agreement; the manuscript's physical white-noise tensor kernels still require an exact isometry/specialization if that representation is claimed. The manuscript's infinite Stroock-series substitution is not used. For the finite selector, the exact equation 2j=p+q-2 together with j<=q gives p<=q+2 directly; no convergence theorem follows merely from enumerating surviving indices. Theorem D's full source/clock block, time integration and singular limit are not certified by this pointwise-in-radius projection alone.

Next substantive route: construct and differentiate the actual general-Schwartz source-two spatial primitive P_n(r)=Q2(n,r)/2 times Wick2(u_n(r)), reusing existing Gaussian differentiation, coefficient geometry and Wick derivative machinery. The expected derivative identities Q2'=d Q4 and Q2''=(q+e)Q4+d^2 Q6 would connect the verified projection with P_n''. They remain proof obligations, not imported assumptions. This could extend the already verified quartic heat/occupation reconstruction to nonlinear Schwartz data. All fixed-mollifier domain, spatial endpoint, random-time Fubini and singular-limit hypotheses must be discharged. General-Schwartz singular reconstruction, other sectors, F1 common topology/uniform summable tails, physical noise-coordinate H^-1 closure, and F3 remain open. No IBM campaign freeze, A(4)/A(2) transition, RH implication or final multichannel completion is asserted. Manuscripts and pinned dependencies remain unchanged.


## Discovery1070: genuine nonlinear Schwartz spatial primitive and strong clock-averaged limits

The previous goal turn made verified progress inebb201b52e0efd0356fabb2e7d0c9e3e547bb977. IBM remains immediate, with successor gates and the October31 hard stop unchanged. This checkpoint follows the actual general-Schwartz primitive route recorded at1069, without imposing a nonzero Gaussian variance or introducing a new source realization.

`IBMGaussianMeanDerivative` proves a genuine global first-order Taylor remainder bound for bounded-second-derivative C2 real functions using Mathlib's actual Taylor theorem. Applied to the existing shifted Schwartz jets, actual first-chaos L2 representatives and already verified mixed Stein identity, it gives for every source directions u,v and every jet index j:

|Q_j(v)-Q_j(u)-<u,v-u>Q_(j+2)(u)| <= (C_(j+2)/2)||v-u||^2,

where Q_j(u)=E[g^(j)(a+W_u)] on the existing source probability space and C_j is the existing Schwartz seminorm bound for the jth jet. All subtracted terms and the remainder are genuinely integrable. The actual Gaussian second moment equals ||v-u||^2 by the native first-chaos isometry. The estimate implies Frechet differentiability on the entire source Hilbert space, with derivative Q_(j+2)(u) times innerSL(u). In particular u=0 is included. No pathwise continuous white-noise functional, common pointwise bound over all Hilbert directions, division by the variance or differentiation of a square root at zero is assumed. For every genuinely differentiable Hilbert source curve, this proves the scalar chain rule Q_j'= <u,u'>Q_(j+2).

`IBMSchwartzSpatialPrimitive` constructs the actual native primitive

P(u)=Q2(u)/2 :W_u^2:,

and proves it equals the existing source-two projection of the actual bounded observable g(a+W_u). For a source curve u with u'=v and v'=w at the point in question, the actual Gaussian-L2 derivative is

P'= <u,v>Q4(u)/2 :W_u^2: + Q2(u)cross(u,v).

A second actual derivative, using the existing bounded Wick cross calculus, equals exactly1069's full secondCandidate: the Q6 term, covariance term, squared derivative term and all cross terms are present. Specializing the existing proved coefficient derivatives gives for every fixed mollifier n and every real spatial r:

P_n''(r)=Pi_2[mollifiedClass(g,a,n,r)].

The class on the right has already been identified with the constructed scenery-field curvature. The actual slope also equals the source-two projection of g'(a+U_n(r))V_n(r), including r=0, so the origin term is independently identified. This is a literal native Gaussian-L2 second derivative identity for nonlinear Schwartz data; it is not only a formal kernel derivative or a distributional assertion in the physical noise coordinate.

`IBMSchwartzPrimitiveLimit` proves continuity in the source direction and in spatial r. Projection contraction gives the global bound ||P(u)||<=C0, uniform over all source directions, n and r. The actual mollifier coefficient convergence therefore gives strong source-L2 convergence P_n(r) -> P_infinity(r) at every real r. The limiting primitive is continuous and vanishes at r=0, using the actual zero source-scenery class. Composing with the existing Brownian clock |Y_T| gives actual Bochner-integrable source-L2 terminal fields. The same global bound proves by dominated convergence that their clock means converge strongly in source L2, for every horizon T>=0, and that the terminal-minus-origin primitives have the same limit. The proof supplies the limiting object as the actual clock integral of the limiting projected Schwartz observable, rather than defining it through a desired correction limit.

No new manuscript theorem was adopted or source content reread: this was a direct extension and reuse of verified source-law, Stein, coefficient geometry, quadratic Wick calculus, projection and Brownian-clock foundations. The three new modules use default resource settings. Existing source hashes and pinned dependencies are preserved.

Remaining central work: identify the whole projected Schwartz correction, with its actual origin and time integral, with this terminal-minus-origin primitive via justified heat/occupation Fubini and integration by parts. The finite-radius and infinite-endpoint estimates must be proved for the new nonlinear primitive, not inherited by analogy from quartic data. The global primitive bound is useful, while its slope and actual curvature need appropriate fixed-mollifier estimates. Native joint source/clock block identification, general singular reconstruction, other source sectors, F1 common topology/uniform summable tails, physical white-noise-coordinate H^-1 closure and F3 remain open. Strong convergence of the primitive clock means is not by itself convergence of the original whole correction. No campaign transition or final full multichannel reconstruction is declared.


## Discovery1071: absolutely integrable nonlinear Schwartz heat reconstruction and actual origin cancellation

The previous goal turn made verified progress inf4594d5a4e65722e4365c78bd84d5a5fa7fdb753. IBM continues under the queued-campaign gates and October31 stopping date. This checkpoint proves the heat-side reconstruction for the actual nonlinear source-two curvature, not yet its identification with the original random-time correction.

`IBMSchwartzHeatBounds` reuses the genuine weightedClass representative and the existing Lp domination theorem to prove ||jet_j(U)F||_2 <= C_j||F||_2 for the actual bounded jet multiplier. It does not assert unrestricted L2 multiplication. The existing square norm identity gives ||V^2||_2 <=2||v||^2, so the actual curvature class is bounded by2 C2||v||^2+C1||w||. Projection contraction and the existing compact-kernel source growth give quadratic spatial growth for the projected curvature at every fixed mollifier. More sharply, the already identified origin/slope projection has only linear spatial growth, because it is the projection of g'(a+U)V. These bounds avoid artificially estimating the fully expanded Q6 formula term by term. Actual projected-curvature continuity follows from1069's finite coefficient formula,1070's genuine mean differentiation, and existing coefficient/Wick continuity. The source-vector bounds are valid on the proved native L2 domain; constants can depend on the fixed mollifier and Schwartz seminorms.

`IBMSchwartzHeatBoundary` performs two actual vector integration-by-parts steps on the finite interval[0,R], using the already verified spatial primitive and slope derivatives. With P_n the nonlinear source-two primitive, H_n=Pi_2(actual curvature), W_T the existing heat occupation potential and W_T' its actual radius derivative, the exact remaining endpoint is

E_n(T,R)=W_T(R)P_n'(R)-W_T'(R)P_n(R).

The proof retains this endpoint in the finite-radius identity. It identifies the origin coefficient W_T(0)/2 with the actual expectation of the constructed Brownian Tanaka mass. The actual constant primitive bound and linear slope growth, together with verified Gaussian-tail decay, prove both endpoint pieces tend to zero in source L2 as R tends to infinity, for every fixed n and positive horizon. No uniform-in-mollifier endpoint convergence is asserted or used.

`IBMSchwartzHeatHalfLine` transfers the actual Brownian clock law through the existing generic reflected-clock theorem. It proves the primitive terminal heat integral and W_T H_n are absolutely Bochner-integrable on the positive half-line, the latter using the actual quadratic growth and the existing polynomial Gaussian heat moments. Passing the finite identity to the radius limit therefore proves, for every shifted Schwartz g, fixed mollifier n and T>0,

E[L_T]P_n'(0)+(1/2) integral_(0,infinity) W_T(r)H_n(r)dr
 = E_Y[P_n(|Y_T|)]-P_n(0).

Here L_T is the existing actual coordinate Tanaka-mass class, not a prescribed normalization, and the clock expectation is an actual source-L2 Bochner integral. The reflected density factor2 and the half coefficient are retained. Combining this equality with1070's terminal-minus-origin convergence proves strong source-L2 convergence of the entire displayed origin-plus-half-line correction to the actual clock integral of the limiting projected Schwartz observable. Radius limits are first discharged separately at each mollifier; the proof does not exchange radius and mollifier limits.

The heat-side theorems explicitly require a positive horizon. They do not extend the algebraic heat-potential expression by a false substitution at T=0; the zero-horizon random-time identity should be handled separately when that actual time-integral correction is identified. No manuscript contents were needed or adopted in this checkpoint. Source hashes and pinned dependencies remain preserved; the three new modules use default resource settings.

Next obligation: prove the time/space/clock Fubini identity for H_n using its actual polynomial growth, heat law and the verified W_T=2 integral_0^T p_s identity. Then identify this heat correction with the original native source-two projection of the actual origin-plus-time correction, reusing the existing joint L2 domain and representative/Fubini machinery. A heat-side limit alone is not that identification. The native joint source/clock block, other source sectors, F1 common topology/uniform tails, physical noise-coordinate H^-1 closure and F3 remain open. IBM is not frozen, and A(4), A(2) and final multichannel work remain gated.


## Discovery1072: actual nonlinear Schwartz time correction, source projection and clock-mean limit

The previous goal turn made verified progress in86df1d22df787ea5ab013c4f00328ef190ef8002. IBM remains the immediate campaign, and the October31 stopping date and successor gates are unchanged. This checkpoint connects1071's spatial heat reconstruction with actual Brownian-clock time integrals and the unprojected source-L2 curvature.

`IBMSchwartzHeatFubini` proves joint strong measurability and actual absolute Bochner integrability of2 p_s(r) H_n(r) on finite positive time times the positive radius half-line. It identifies the time integral at every nonnegative radius with W_T(r)H_n(r), and proves the matching norm integral. These facts discharge the product domain before swapping time and radius. This is a direct nonlinear extension using the existing heat-potential theorem and1071's absolute weighted curvature domain.

`IBMSchwartzClockMean` composes H_n with the actual reflected constructed clock |Y_s|. It proves fixed-time clock integrability, identifies both its mean and its norm mean through the actual clock law, and proves absolute time/clock Bochner integrability. Polynomial growth is controlled using existing genuine clock moments. Actual product Fubini then identifies

E_Y[integral_0^T H_n(|Y_s|)ds]=integral_(0,infinity) W_T(r)H_n(r)dr.

Including the actual Tanaka-mass expectation times the already identified slope gives a clock mean equal to E_Y[P_n(|Y_T|)]-P_n(0). Hence this actual source-L2 clock mean converges strongly to1070's terminalLimit for positive horizons. Measurability and integrability are proved before each interchange; no occupation formula is merely postulated.

`IBMSchwartzSourceContinuity` supplies the missing unprojected source-domain connection. It proves the bounded jet multiplier's observation-difference estimate using an actual Gaussian-L2 product witness. A precise weighted convergence theorem requires that witness and its proved zero limit, rather than presuming multiplication of arbitrary L2 inputs is continuous. Existing finite Gaussian cubic polarization supplies the witness W_(u-v) V^2; finite square polarization supplies W_(u-v) W. Their actual representative identities and continuity are proved using existing Wick continuity. This proves continuity of the actual unprojected mollifiedClass along the scenery coefficient curve. No new probability source, new integration space or unbounded ambient multiplication operator is introduced.

`IBMSchwartzTimeProjection` therefore constructs the whole unprojected correction as a genuine source-L2 Bochner time integral along every constructed clock path:

C_n(T,Y)=L_T(Y) G_n'(0)+(1/2) integral_0^T G_n''(|Y_s|)ds,

where G_n'(0) is the independently realized original shifted-Schwartz origin class and G_n'' is the actual curvature class. The first term uses the existing actual coordinate Tanaka-mass class. Source projection commutes with the actual time integral by its verified continuous linear map theorem and the actual continuous finite-interval domain. Thus the source-two projection is exactly L_T(Y)P_n'(0)+(1/2) integral_0^T H_n(|Y_s|)ds. This projected whole correction is genuinely integrable in the clock, its clock mean is the reconstructed correctedMean, and those clock means converge strongly in source L2 to terminalLimit for every T>0. This closes the previously missing whole-correction identification at the level of the actual source-two projection and its clock mean, not only the heat surrogate.

`IBMSchwartzScalarRecovery` independently identifies the Bochner construction with the literal scalar expression in the chosen simultaneous scenery fields. It proves joint measurability of the actual shifted-Schwartz curvature, fixed-clock time/source absolute integrability, and representative Fubini identifying the source-L2 integral with the literal scalar time integral. The actual origin representative is also identified. For every chosen clock representative, the native source-valued whole correction agrees a.e. in the source with the literal scalar origin plus curvature-time integral. Its time-integral section has a proved source-L2 domain. These statements do not silently change source/clock coordinate order: this module's scalar joint time representative uses(clock,source); earlier IBMSchwartzJointL2 uses(source,clock), so any native joint-block identification must explicitly transport between them.

All five modules reuse the existing source construction, projection, finite Gaussian products, heat estimates, reflected clock law and representative/Fubini machinery, with default resource settings. No new manuscript content was needed or adopted. Original sources and pinned dependencies remain preserved.

Remaining central obligations: package the actual nonlinear whole correction as a native product-source L2 class, identify its full source-two/clock-zero block with the source lift of this proved clock mean, and obtain that block's strong product-L2 limit. Reuse the existing general-Schwartz time/joint L2 domain and the independent Tanaka-mass/origin product domain, with the coordinate flip and literal representatives proved explicitly. The current result already proves the actual source-valued projected whole clock mean and its strong source-L2 limit; it does not assert convergence of the unprojected correction or of its remaining clock/source sectors. Other sectors, F1 common topology/uniform summable tails, physical white-noise-coordinate H^-1 closure and F3 remain open. The positive-horizon heat hypotheses remain explicit; zero-horizon statements can be discharged separately from the actual time integral. IBM has not reached a full freeze, and no successor campaign has begun.


## Discovery1073: native joint source-two/clock-zero convergence of the literal Schwartz correction

The previous goal turn made verified progress inc6d02403468f9b7dc6d6bd2b9dd384ee20843a55. IBM remains immediate; successor gates and the October31 stopping date remain in force. This checkpoint completes the native product-space and literal-representative obligations left at1072 for the source-two/clock-zero block of the constructed reflected model.

`IBMSchwartzBochnerDomain` proves a quadratic spatial growth bound for the actual unprojected mollified curvature. The proof uses the existing bounded-jet multiplier estimate and actual Gaussian square/linear norms, before any projection. Existing constructed-clock eighth moments dominate the required lower powers on a finite horizon; no new clock law or moment axiom is introduced. Finite-measure L2 integration then proves that the actual source-valued curvature time integral belongs to L2 in the clock. The origin uses the existing actual Tanaka-mass L2 class tensor the independently realized source origin class. Consequently the whole unprojected origin-plus-time correction is genuinely an L2(clock;L2(source)) object, for every fixed mollifier and every nonnegative horizon. No uniform-in-mollifier bound on the unprojected correction is asserted.

`IBMSchwartzJointRealization` transports this independently proved whole object through the existing onto product/Bochner isometry. The product coordinates are explicitly(clock,source). It reuses the already verified generic `IBMQuarticJointRealization.jointMeasure`, `jointSourceSector`, `sourceLift` and `sourceSigma_le`; it introduces no replacement source-chaos projection, probability space or conditional expectation. Actual joint sections agree with the1072 whole correction, and actual source-two sections agree with its source projection. Genuine representative Fubini identifies the clock mean in source L2. Independent-factor conditioning then proves the native conditional projection identity

condExp_(full source sigma)[jointSourceSector_2(C_n)]
 = sourceLift(correctedMean_n).

Here correctedMean is the actual origin-plus-time source-projected clock mean already reconstructed at1072. Its verified strong source-L2 limit transports isometrically to a strong native product-L2 limit of this block for every positive horizon. This proves the completed joint-block statement, beyond separate pointwise sections or a scalar expectation identity.

`IBMSchwartzLiteralJoint` identifies the joint class with the literal scalar correction built from the actual shifted Schwartz scenery fields, actual curvature time integral and actual continuous Tanaka-mass path. Global product measurability and a single product-a.e. equality are proved. The literal scalar correction therefore has a genuine joint L2 domain at every fixed mollifier, and its independently formed toLp class equals the native joint class. The native block limit applies to this literal class, including both stochastic terms.

The zero horizon is handled separately using the actual clock zero class, the a.e. zero initialization of the continuous mass limit and the actual integral over[0,0]. The literal joint class and the limiting terminal object both vanish there. `IBMSchwartzLiteralJoint.literal_native_block_tendsto_all` thus proves the strong product-L2 block limit for every T>=0. No heat-potential expression is substituted at zero time. All32 new public declarations were inspected in the checkpoint audit; the three modules use default resource settings, with only the same local Lp exponent fact needed by the existing product isometry.

Selective anchor review: reread the named open-problem statements in the existing extraction of `ResearchSources/ibm/EJP2605-044RA0.pdf`, SHA2565A91914A535AD19BDDF219D7A9AB9F8B5F20A52DD4EC6ED7333AA80B403182BE: Open problem5.4(F3), PDF page12; Open problem6.4(F2), page19; Open problem7.1(F1), page22. F1 explicitly concerns a global cross-sector dual summation and previously unresolved blocks with source degree at least2, or source degree0 and positive clock degree. The new theorem resolves one concrete sequence-based part of this frontier, the literal native(2,0) block for all shifted Schwartz tests along the repository's shrinking compact-bump sequence. It does not prove global summability, all source/clock blocks, arbitrary mollifier profiles or a full continuous-epsilon theorem. The PDF's F3 discussion itself uses scenery at the reflected clock; no equivalence with an unreflected two-sided IBM model or the source-resolved manuscript's different kernels is inferred. The requested Incoming PDF duplicate remains absent; this is the already identified available archive version, not a claimed match to that missing duplicate.

Next direct reuse opportunity: `IBMSchwartzJointL2.clockProjection_eq` already identifies the native source-zero projection of the integrated curvature in(source,clock) coordinates, and `IBMSceneryAveragedCorrectionLimit.averagedClass_tendsto` proves its strong clock-L2 limit. That existing class is curvature-only. To extend it to the current literal whole correction, prove the coordinate transport and actual origin contribution, including its exact scenery mean, rather than silently omitting the origin or reusing the incompatible coordinate order. This could consolidate the source-zero clock sectors without a separate chaos campaign. Remaining central work includes the other cross sectors, a common global dual topology and uniform summable tails(F1), full physical noise-coordinate H^-1 realization, and an independent audit/construction of the intrinsic F_Z core and its density question(F3). The prior concrete F2 shrinking-bump random limit stays verified. A block limit does not imply convergence of the whole unprojected correction or resolve its first-chaos obstruction. IBM is not frozen, and no successor campaign has begun. All manuscripts and pinned dependencies remain unchanged.


## Discovery1074: complete native source-zero clock family, uniform eventual tails and controlled partial sum

The previous goal turn made verified progress in2a64fb25a0429433eaf5c00592c21d3705945538. IBM remains immediate, with the finite successor sequence and October31 stopping date unchanged. This checkpoint directly reuses the existing full clock-L2 averaged-curvature limit while proving the missing actual origin and native whole-class connections.

`IBMSchwartzWholeSourceMean` proves the actual origin covariance is zero by the existing boundary symmetry identity at radius0, not by a bulk covariance substitution. The genuine mixed Stein identity and actual origin representative then prove that the origin class has zero scenery mean for every shift and Schwartz test. Applying the actual bounded source-mean functional to the continuous source-L2 time integral gives, for every chosen clock representative and every horizon,

E_X[C_n(T,Y)]=(1/2) averagedPath_n(T,Y).

The whole source-zero projection is this actual scalar mean times the native Gaussian vacuum. Both stochastic terms are included before the origin's zero mean is used; it is not silently omitted.

`IBMSchwartzSourceZeroJoint` explicitly transports the existing clock lift from(source,clock) to(clock,source) using the already verified product swap isometry. Its representative is proved to depend on the first coordinate. It identifies the actual source-zero projection, using the existing generic jointSourceSector0, of the independently realized literal whole correction with

clockLift((1/2) averagedClass_n).

No new conditional expectation or chaos definition is introduced. Reusing `IBMSceneryAveragedCorrectionLimit.averagedClass_tendsto` therefore gives strong native joint-L2 convergence of this entire component for every nonnegative horizon, retaining every clock sector at once. The explicit limiting clock class is

(1/2)g''(a) L_T + (1/8)bulkLimit(g,a,T),

where L_T and bulkLimit are the previously constructed actual classes. The half and eighth coefficients come from the whole correction and the existing averagedLimit definition. This resolves the native whole-class source-zero family along the repository's concrete compact-bump sequence, beyond the previous curvature-only or fixed-clock-sector statements.

`IBMSchwartzSourceZeroTails` uses the existing complete Gaussian decomposition and contractive truncations. The elementary verified bound

||f-trunc_N f|| <= 2||f-h||+||h-trunc_N h||

combines actual strong convergence with the existing truncation limit. For each tolerance eta>0 it proves the precise eventual uniform bound: there exist N0,n0 such that every clock cutoff N>=N0 and every mollifier index n>=n0 satisfy

||jointSourceSector0(literalClass_n)-clockLift(trunc_N((1/2)averagedClass_n))|| < eta.

Thus one finite clock-chaos cutoff controls all sufficiently refined mollifiers. This is not merely convergence at each fixed clock degree, and it does not assert uniformity over different mollifier profiles, shifts or horizons. The module also proves that the sum of this source-zero/full-clock component and1073's literal native(2,0) block converges in the same native joint-L2 norm. This is an explicit controlled partial sum of existing operators, not a theorem about the complete cross-sector sum. All16 public declarations are inspected; the three modules use default resource settings.

Selective F3 audit/reuse check: reread the operator-bridge and intrinsic-core discussion on PDF pages11–12 of the immutable `ResearchSources/ibm/EJP2605-044RA0.pdf` (SHA2565A91914A535AD19BDDF219D7A9AB9F8B5F20A52DD4EC6ED7333AA80B403182BE), then rechecked the existing `IBMUnmollifiedSourceDerivative.randomSource_domain`, `randomSource_graph`, `gradient_norm`, `graph_tendsto`, `actual_section_ae` and `actual_section_domain`. This confirms the earlier campaign audit: the actual unmollified coordinate has a genuine square-integrable partial scenery derivative and its actual sections lie in that scenery domain. The manuscript's suggestion that scenery-at-clock is outside D_X's domain cannot justify nondensity of the joint intrinsic core. The clock derivative, the intersection with its domain, and approximation by F_Z-measurable joint-domain elements remain separate. Nonmembership of an observable in a derivative domain would not, on its own, establish nondensity either. No F3 density or nondensity theorem is claimed from these facts.

A concrete candidate for the next F3 test is time smoothing of actual IBM observables, A_(rho,phi)=integral rho(s)phi(Z_s)ds. Unlike scenery-mollified surrogates, these candidate observables use Z itself. If joint derivative-domain membership can be proved for a suitable time-smoothed algebra, while time approximate identities recover bounded continuous cylinder observables, it could supply a density route. The crucial uniform joint-Malliavin graph estimates, clock derivative realization, observable-algebra closure and density steps have not been proved or assumed. Inspect existing occupation/local-time and operator machinery before constructing additional foundations; do not label this candidate a density proof.

Remaining F1 sectors are now source degree at least1, excluding the separately controlled(2,0) block, together with their common physical dual topology and uniform cross-sector summation. The entire source-zero clock family has the concrete native closure and eventual tail control above. Full physical noise-coordinate H^-1 identification and the precise F3 intrinsic-core question remain open. The prior concrete F2 random limit is preserved. Do not infer convergence of the whole unprojected correction, bypass the first-chaos obstruction or declare the IBM campaign frozen. Original sources, unrelated documents and pinned dependencies remain unchanged; no successor campaign has begun.


## Discovery1075: full nonlinear source-Hilbert derivative and all-source terminal candidate

The preceding goal turn made verified progress in e7e2ccfb0f4da6d341c024f60ac3f62300b72a83. IBM remains immediate. The queued IBM → A(4) → A(2) → final multichannel campaign and October31 hard stop are unchanged. No successor gate is released.

`IBMSchwartzSourceDerivative` constructs the full actual Gaussian-L2 observable O_j(u)=g^(j)(a+W(u)), without a chaos projection. It constructs the bounded multiplier by the actual bounded Schwartz jet on the existing GaussianL2, then composes it with the verified first-chaos embedding. The resulting continuous linear source derivative is

DO_j(u)[h]=g^(j+1)(a+W(u)) W(h).

The representative, source domain and bounded multiplier are proved, not postulated. Taylor's scalar remainder, the actual Gaussian square class and its existing L2 norm bound give the global estimate

||O_j(v)-O_j(u)-DO_j(u)[v-u]||_L2 <= seminorm(g^(j+2)) ||v-u||^2.

This proves Frechet differentiability on the entire existing coefficient Hilbert space, including zero and degenerate directions, and the corresponding derivative along differentiable spatial coefficient curves. No arbitrary L2 product, point evaluation on L2 classes, covariance inverse or formal chaos-series differentiation is used. The module uses default elaboration resources.

`IBMFullSchwartzTerminal` applies this full observable to the actual concrete mollified coefficients and their verified source-coefficient limit. Its spatial derivative is the actual weighted first-chaos slope, before projection. It proves continuity and strong source-L2 convergence of the whole nonlinear observable at every radius. The exact base-embedding identity and the independently constructed continuous Brownian scenery modification identify the limiting section with g(a+X(r)) almost everywhere, and, for every fixed clock path, identify its random-radius section with g(a+Z_T). This does not claim an exceptional set uniform over all radii; its pointwise-in-clock AE source assertion is explicit.

The module constructs genuine Bochner clock averages of these full source classes, proves their absolute integrability using the bounded Schwartz observable, and obtains strong source-L2 convergence by dominated convergence, for every nonnegative horizon. The origin limit is g(a) times the Gaussian vacuum. Consequently the full terminal-minus-origin candidate converges strongly to

E_Y[g(a+X(|Y_T|))]-g(a).

This convergence retains all source chaos degrees together, rather than only the earlier second-source projection. The existing contractive chaos truncation estimate gives precise eventual uniform source tails for this candidate: for each eta>0 there exist N0,n0 such that every cutoff N>=N0 and mollifier index n>=n0 has truncation remainder below eta. These thresholds are chosen before either index varies. This is a theorem about the actual terminal-minus-origin candidate, not yet about the correction.

Exact remaining connection: identify the entire clock-averaged correction with this full terminal-minus-origin class. The earlier projected heat proof establishes that equality after the second-source projection. Extending it requires the full weighted-slope derivative (second spatial derivative equal to actual unprojected curvature), its needed continuity/domain bounds, and the vector-valued heat boundary/Fubini argument. The new first derivative does not supply this second derivative automatically. In particular, positive-source clock sectors, global F1 cross-sector convergence in a physical test dual, and identification of source Hilbert coordinates with the manuscript's physical white-noise coordinate remain open. No claim of full correction convergence is made from terminal convergence alone.

The F3 reuse search found existing zero-occupation/Tanaka-mass and heat occupation-mean results, but did not establish a full spatial local-time field or the uniform joint derivative estimate needed for a time-smoothed intrinsic-core argument. The previously verified partial scenery derivative remains valid. Neither joint clock Sobolev membership nor intrinsic-core density/nondensity was proved in this checkpoint. No F3 conclusion follows from the bounded multiplier construction. The concrete F2 limit and all prior verifications remain preserved.

All27 new public declaration types are inspected in the checkpoint audit. Original manuscripts and the43-file/42-hash Incoming inventory are preserved. No source, dependency or toolchain changes; no unrelated campaign, resource increase, or added mathematical axiom.


## Discovery1076: full nonlinear IBM curvature and every scenery sector after clock averaging

The previous goal turn made verified progress in d729526d70b861ee97f822ab6476ee553df54dec. This checkpoint closes that turn's precise missing second-derivative and heat-identification connection. IBM remains the immediate campaign. The IBM → A(4) → A(2) → final full multichannel campaign gates and October31 hard stop remain in force; no successor has started.

`IBMSourceProductBounds` reuses the actual centered quadratic bilinear calculus and polarized Gaussian cubic classes. It identifies the independently realized raw product with the centered cross product plus its covariance vacuum term, constructs its bounded bilinear map, and proves ||W(u)W(v)||_L2 <= 3||u||||v||. Separate scalar homogeneity of the actual polarized mixed cube, including both zero directions, converts the existing bounded-ball cubic estimate into

||W(u)W(v)^2||_L2 <= 12||u||||v||^2.

This is a bound on products of actual Gaussian first-chaos variables. It does not assert a bounded product on arbitrary L2 classes. The separate factors, rather than one common ball bound, are what make the next operator-norm remainder tend to zero at the required rate.

`IBMSchwartzSourceSecondDerivative` constructs a bounded bilinear Hessian for the entire actual nonlinear observable O_j(u)=g^(j)(a+W(u)):

D^2 O_j(u)[h,k]=g^(j+2)(a+W(u)) W(h)W(k).

Taylor's scalar remainder is multiplied by the genuine first-chaos direction and compared in L2 with the already realized mixed cubic. The resulting source-operator remainder is bounded by

||DO_j(v)-DO_j(u)-D^2 O_j(u)[v-u]||_op <= 6 seminorm(g^(j+3)) ||v-u||^2.

Thus DO_j is Frechet differentiable in operator norm on the entire source coefficient Hilbert space, including zero variance. The proof is uniform in the differentiated direction. Applying the genuine bounded-operator chain and evaluation rules gives the full spatial derivative of the actual weighted slope. Along the constructed mollified coefficient curve, u'=v and v'=w, it yields

d^2/dr^2 g(a+X_n(r)) = g''(a+X_n(r)) (X_n'(r))^2 + g'(a+X_n(r)) X_n''(r)

as equality in native Gaussian source L2, before every source-chaos projection. `spatial_second_deriv` identifies this derivative with the existing actual `IBMSchwartzSecondProjection.mollifiedClass`, despite that module's historical name. No formal differentiation of an infinite chaos sum or pointwise differentiation of an unmollified Brownian path occurs.

`IBMFullSchwartzHeatBoundary`, `IBMFullSchwartzHeatHalfLine`, `IBMFullSchwartzHeatFubini` and `IBMFullSchwartzClockMean` reuse the earlier heat-potential, Gaussian-tail, reflected-clock-law, actual origin-mass and product-Fubini arguments on this full source-L2 primitive. Fixed-mollifier slope growth and unprojected curvature growth are justified using the existing verified bounds. Both spatial endpoint terms tend to zero. All time/space and time/clock integrals used in swapping are proved absolutely Bochner-integrable, including the singular initial-time heat endpoint. The reflection factor2 and the origin coefficient are inherited from their existing actual law and Tanaka-mass proofs, not assumed.

For every Schwartz g, real shift a, concrete mollifier index n and positive horizon T, the full actual clock-averaged correction satisfies

E_Y[L_T g'(a+X_n(0))X_n'(0) + (1/2) integral_0^T {g''(a+X_n(|Y_s|))(X_n'(|Y_s|))^2 + g'(a+X_n(|Y_s|))X_n''(|Y_s|)} ds]
= E_Y[g(a+X_n(|Y_T|))]-g(a+X_n(0)).

The equality is in actual Gaussian source L2. It includes the origin layer before cancellation. It retains all source chaos degrees simultaneously. The right-hand side is exactly1075's full terminal-minus-origin candidate, so its already verified strong source-L2 limit now applies to the actual clock-averaged correction, rather than merely to an unidentified candidate. The limit is E_Y[g(a+X(|Y_T|))]-g(a), with the actual constructed Brownian scenery and independent continuous clock sections already identified in1075.

`IBMFullSchwartzNativeMean` connects this full Bochner mean to the existing independently realized literal scalar correction using the actual joint sections, representative Fubini and independent-source conditional expectation. Coordinates remain(clock,source); no source or conditional-projection definitions are replaced. Its exact native identity, `literal_native_mean_eq_all`, is

condExp_source(literalClass_n) = sourceLift(terminal_n-spatial_n(0)).

It proves strong native joint-L2 convergence for every nonnegative horizon, retaining the entire source-chaos family with clock degree0. Actual zero-time clock and time-integral identities handle T=0 separately; no positive-time heat-potential identity is substituted there. The native eventual uniform source-tail bound chooses N0,n0 before either source cutoff N>=N0 or mollifier index n>=n0 varies. It is a tail estimate for this actual conditional correction, not just for a terminal observable or for one fixed source degree. In particular, the earlier isolated(2,0) result is now part of a whole-family theorem.

Precise limits of this advance: the complete source-zero/all-clock family was verified in1074, and the complete all-source/clock-zero family is verified here. The genuinely mixed sectors with positive source degree AND positive clock degree, their common physical test-dual topology, and their global summability remain open. Clock averaging is an actual bounded projection and may remove singular behavior; this result does not bypass the random first-chaos obstruction or prove convergence of the full unprojected random correction. Physical white-noise-coordinate H^-1 identification is still absent. F3 joint clock-domain membership and intrinsic-core density/nondensity remain open. The concrete F2 result and all earlier work are preserved. These unresolved central obligations keep IBM active.

All69 public declaration types from the seven new modules are inspected at the checkpoint. The modules use default elaboration resource settings; only the existing spectral-space second-countability and exponent facts are used where needed. No new mathematical axiom, dependency, toolchain change, manuscript write, extra research branch or resource increase. Incoming remains43 files/42 exact content hashes; the four IBM archive baselines and the Yang–Mills/Navier–Stokes dictionary hash remain unchanged.


## Discovery1077: actual physical white noise, dense indicator realization, and clock-dependent physical H^-1 kernels

The previous goal turn made verified progress in c67bbe7947f705db60e08cd08d98958fa8ad3c25. IBM remains immediate. This checkpoint addresses the missing physical noise-coordinate realization directly, rather than adding further isolated chaos projections. The IBM → A(4) → A(2) → final multichannel gates and October31 hard stop remain unchanged.

`IBMPhysicalNoiseVectors` reuses the actual Lebesgue-L2 interval indicators from `GaussianTimeHilbert`, defining the two-sided oriented kernel

v_r=1_(0,r]-1_(r,0].

For negative r this is minus the indicator of(r,0]; for positive r it is the indicator of(0,r]. Its actual representatives, interval increments, norm squared |r| and increment norm squared |r-s| are proved. Pairing v_r with any actual physical L2 function equals its oriented integral from0 to r.

Crucially, `span_dense` proves that these kernels span a dense subspace of the ENTIRE physical L2(R,dw), including both half-lines. The proof imposes no density assumption: a vector orthogonal to the span has identically zero indefinite integral; the existing Lebesgue differentiation theorem applies to its locally integrable L2 representative and forces the vector to be zero almost everywhere. The Hilbert orthogonal-complement criterion then supplies density. No arbitrary embedding of an abstract countable-dimensional Hilbert space is substituted for the physical kernels.

`IBMPhysicalNoiseRealization` uses the existing `baseCoefficient` and its exact embedding into the already constructed Brownian scenery. Their norm and increment energies match v_r. Polarization proves equality of their Gram kernels. Consequently every finite Finsupp linear combination has exactly the same physical and scenery-coefficient norms. The existing Mathlib dense linear-isometry extension theorem constructs

J:L2(R,dw) -> CoefficientSpace,  J(v_r)=baseCoefficient(r).

J is a linear isometry on every actual physical L2 kernel. It is fixed by the Brownian indicator coordinates. Its range need not equal the entire ambient coefficient space; no such surjectivity is asserted. The existing generic Hilbert-basis Gaussian embedding alone would not give these exact scenery-coordinate identities, which is why this Gram-preserving transfer is needed.

Composing J with the VERIFIED existing first-chaos embedding constructs the physical white noise W(f) on the original scenery Gaussian probability space. The module proves its exact centered Gaussian law with variance ||f||^2, joint Gaussianity for the family indexed by physical L2, zero mean, and covariance <f,h>_L2 = integral f(w)h(w)dw. It also proves actual equality of classes

W(v_r)=X(r),  W(1_(a,b])=X(b)-X(a), a<=b.

These are equalities with the existing scenery, not just equalities in law or an independent replacement process. White noise here is the genuine isonormal family indexed by physical L2; no pointwise random white-noise function w -> W(w) or evaluation at a Dirac kernel is claimed.

`IBMPhysicalNoiseCalculus` identifies J's adjoint on its image, proves continuity of the physical indicator curve, and connects W(f) to the repository's actual CLOSED Gaussian source derivative graph, with constant coefficient J(f). Its bounded gradient pullback J* acts on vector-valued Gaussian L2 fields; on these actual derivative graphs it returns the physical kernel f. This does not assert closedness of an unrestricted postcomposed derivative or solve an intrinsic-domain density problem.

For every continuous compactly supported rho, the module constructs the physical L2 Bochner kernel

Q_(rho,x)=integral rho(x-r) v_r dr,

proves its absolute Bochner integrability, and proves W(Q_(rho,x))=wholeLineScenery(rho,x). The actual closed Gaussian gradient pulls back to Q_(rho,x). For each of the three concrete mollifier jet kernels i=0,1,2, continuity and compact support are discharged, and `triple_coefficient_physical` proves

J(Q_(derivativeKernel(n,i),r))=tripleCoefficient(n,r,i).

Thus the actual zeroth, first and second spatial mollifier coefficients all have fixed physical white-noise kernels. The concrete zeroth physical mollifier kernel converges STRONGLY in L2(R,dw) to v_r at every real radius r. This is inherited through J* from the actual verified coefficient convergence; it is not an unverified formal convolution limit.

`IBMPhysicalNoiseClock` composes the genuine first-chaos coefficient adjoint with J*, giving a bounded kernel pullback on the existing source GaussianL2. Applying its Bochner-L2 lift to the already constructed random-time scenery classes constructs actual physical kernel fields Q_n(|Y_t|) and v_(|Y_t|). Their AE representatives use the independently constructed continuous Brownian clock, and they converge strongly in L2(clock;L2(R,dw)). The actual-section theorem recovers the independently constructed continuous IBM Z_t=X(|Y_t|) by applying W to the limiting random physical kernel, for almost every clock source and then almost every scenery source. No exceptional set uniform over all spatial points is assumed.

Finally, ordinary real-to-complex scalar inclusion and the ALREADY verified bounded spatial distributional derivative L2 -> H^-1 are composed on this ACTUAL physical variable w. The module constructs H^-1(R)-valued random variables from Q_n(|Y_t|), identifies their actual physical-kernel representatives and their distributional derivative meaning, and proves the precise topology

d_w Q_n(|Y_t|) -> d_w v_(|Y_t|) strongly in L2(clock;H^-1(R,dw))

for every nonnegative time t. The complexification preserves the physical variable and Lebesgue measure. These are actual Bochner-L2 random distributions associated with the constructed IBM clock, not a coefficient-space negative norm renamed as physical H^-1.

Exact remaining obligations: an explicit physical FUNCTION identity for Q_(rho',x), including signs, boundary constants and its relation to translated rho, has not yet been proved. No Dirac evaluation of W is asserted. The new H^-1 convergence is for the physical distributional derivatives of the zeroth Brownian mollifier kernels. It is NOT a theorem identifying the manuscript's entire first-source correction kernel with these derivatives, and it is NOT convergence of the full nonlinear correction. That coefficient/kernel identification, weighted random physical estimates, the genuinely mixed positive-source/positive-clock sectors and their common dual/global summation remain open. The coordinate isometry itself is now constructed, so it should no longer be listed as entirely missing; the remaining physical H^-1 identifications and estimates are narrower and explicit.

F3 joint clock-domain membership and intrinsic-core density/nondensity remain open. In particular, this physical scenery realization does not prove density of F_Z-measurable elements in the joint derivative domain. The complete source-zero/all-clock family from1074, complete all-source/clock-zero family from1076, and concrete F2 closure are preserved. IBM remains active; no successor gate is released.

All62 public declaration types from the four new modules are inspected at the checkpoint. No added mathematical axiom, dependency/toolchain change, elaboration resource increase, manuscript modification or unrelated research branch. Incoming remains43 files/42 exact hashes, with the four IBM archive baselines and dictionary hash preserved.

## Discovery1078: explicit physical derivative kernels and the whole Schwartz first-chaos correction

Resumed at terminal time2026-10-18T21:17:05-04:00 from verified d8d9b6662a37730b60b7ae4595e219ca337c9473. The previous goal turn made verified progress; this turn closes1077's explicitly missing derivative-kernel identity and identifies the whole first-source correction kernel. IBM remains immediate, with the successor gates and October31 hard stop unchanged.

`IBMPhysicalDerivativeColumn` proves the scalar column calculation with its sign and both compact-support endpoints. For every C1 compactly supported rho,

integral rho'(x-r) v_r(w)dr = rho(x-w).

Here v_r(w)=1_(w<=r)-1_(w<=0) is the already constructed two-sided oriented Brownian indicator. The derivative is with respect to rho's argument. A compactly supported primitive -rho(x-r) has derivative +rho'(x-r); its integral over[w,infinity) is +rho(x-w), while its whole-line derivative integral is zero. Thus the anchoring-at-zero term cancels. The proof establishes actual scalar integrability, joint measurability and an explicit bounded spatial-support estimate; no formal delta-function integration is used.

`IBMPhysicalDerivativeKernel` lifts that calculation to the ACTUAL physical Lebesgue-L2 class. It reuses `BochnerL2Fubini.integral_eq_of_slices` on a compact parameter interval, supplying an independently realized translated-rho L2 class. The uniform majorant is a constant times a bounded-interval indicator in the physical variable w and is proved to belong to L2(R,dw). Compact support and derivative bounds are discharged from C1 and compact support; callers supply no radius, majorant or density hypothesis. The resulting theorem is

Q_(rho',x) = [w -> rho(x-w)] in physical L2(R,dw).

Applying it again to rho' identifies Q_(rho'',x) with [w -> rho'(x-w)] for a C2 kernel. `physicalJet_one_coeFn` and `physicalJet_two_coeFn` instantiate the actual compact bump sequence. These are positive rho and positive rho' representatives in the physical coordinate; they must not be confused with taking d/dw, which reverses the sign of a translate. No physical distributional differentiation identity is silently substituted.

`IBMSchwartzFirstCoefficient` proves the full first-chaos coefficient of the ACTUAL nonlinear Schwartz curvature. It reuses the independently realized quadratic/cubic products and existing mixed Stein pairings, so all test products are on proved GaussianL2 domains. Let U=W(u), V=W(v), R=W(w), d=<u,v>, e=<u,w>, q=||v||^2 and Q_j=E[g^(j)(a+U)]. Then

firstChaosEmbedding* [g''(a+U)V^2+g'(a+U)R]
= ((q+e)Q_3+d^2 Q_5)u +2d Q_3 v+Q_1 w.

The fifth derivative term is retained. This holds for every actual source direction, including zero/dependent directions, and every real shift a and Schwartz g. There is no variance division, finite-chaos truncation assumption, or claim that a polynomial is itself a Schwartz test. The proof also supplies the separate weighted-linear and weighted-square adjoint formulas.

`IBMSchwartzPhysicalFirstKernel` transports that exact coefficient through1077's fixed physical noise isometry. For the ACTUAL concrete triple at radius r define u_n(r),v_n(r),w_n(r), q_n,d_n,e_n,Q_(j,n) accordingly, and

A_n(r)=(q_n(r)+e_n(r))Q_(3,n)(r)+d_n(r)^2 Q_(5,n)(r),
B_n(r)=2d_n(r)Q_(3,n)(r).

The actual physical curvature kernel is therefore

K_n(r;w)=A_n(r)Q_(rho_n,r)(w)+B_n(r)rho_n(r-w)+Q_(1,n)(r)rho_n'(r-w).

The zeroth term remains the genuine Bochner-L2 Brownian convolution kernel from1077; the other two terms have the explicit translated representatives proved above. The exact covariance d_n(0)=0 is reused at the origin, rather than replacing it by its interior value. Consequently the actual first-source origin kernel is Q_(1,n)(0)rho_n(-w).

The module constructs the whole kernel, including the genuine Tanaka mass L_T,

K_n^whole(T,Y;w)=L_T(Y) Q_(1,n)(0)rho_n(-w)
 + (1/2) integral_0^T K_n(|Y_s|;w)ds.

`wholeKernel_eq_pullback` proves that this is exactly the physical pullback of the first-chaos coefficient of the existing whole correction. `wholeKernel_embeds` proves the stronger image identity with the full actual first-chaos coefficient, so no unexamined orthogonal coefficient component is lost by the adjoint pullback. `wholeKernel_realizes_projection` applies the genuine physical noise to recover the ENTIRE `GaussianPastFirstChaos.projection` of the actual whole correction at each chosen clock representative. All finite-time Bochner interchanges have actual continuity/integrability proofs.

`wholeKernelClass` constructs a genuine L2(clock;L2(physical space)) class for every mollifier index and every nonnegative horizon. Its AE representative is the explicit whole kernel. The exact lifted reconstruction theorem recovers the first-chaos projection of the existing whole source-valued correction class, retaining all clock variability and performing no clock averaging. The previously verified joint/literal realization of that whole class is preserved; no new stochastic law is assumed for it.

An exact obstruction-preservation theorem is also proved: physical-L2 differences between two whole kernels equal Gaussian-source-L2 differences between the corresponding first-chaos projections. Therefore this coordinate identification provides no native L2 regularization. Any inherited native non-Cauchy obstruction survives; a singular limit still requires an independently justified weaker topology or cancellation.

Remaining F1 work is now more concrete. The full finite-mollifier FIRST-source kernel, including its origin term and all clock variability, is identified here; its convergence in L2(clock;H^-1(physical space)) has NOT been proved.1077's convergence of d_w Q_(rho_n,|Y_t|) is a different kernel limit and does not certify convergence of K_n^whole. In particular, the weighted translated derivative term, the localized covariance combination q_n+e_n, and the origin mass must be handled together with their precise signs and domains. No bulk replacement q_n+e_n=0 is made at the origin. Higher positive-source/positive-clock sectors and common dual/global summation remain open. F3 joint clock-domain and intrinsic-core density remain open. All prior edge-family limits and concrete F2 closure remain preserved; IBM stays active.

A candidate reuse route, not a theorem, is to apply the verified clock stochastic-integration machinery to the physical first-source primitive Q_(1,n)(r)Q_(rho_n,r). Its formal first spatial derivative contains an approximate physical Dirac kernel, while its second derivative is the exact K_n identified above. A genuine reflected-clock Ito/Tanaka argument in the completed physical H^-1 target could potentially avoid constructing an unrelated occupation-field infrastructure. The existing smooth Ito theorem is scalar with bounded-derivative C3 hypotheses; it does NOT automatically supply this Hilbert-valued reflected/singular theorem. The required target-valued adapted integral, boundary formula, and uniform limit estimates must first be supplied through actual theorem reuse or proved extensions. Do not treat this candidate as F1 closure.

All34 public declaration types from the four new modules are inspected at the checkpoint. The modules use default elaboration resource settings. Incoming remains43 files/42 hashes and all four IBM archive baselines plus the dictionary hash remain unchanged. No manuscript, dependency/toolchain, unrelated document or successor campaign is modified.

## Discovery1079: actual physical C2 primitive, nonlinear IBM endpoints, and strong clock-Hminus Dirac limits

Continued after committing1078 as3804e7c12696d016fb4eb32a3306d9cccbd6f5c6. Terminal clock readings include2026-10-18T21:34:00-04:00 and21:46:50-04:00. IBM remains immediate; A(4), A(2), and the final multichannel campaign retain their gates and October31 hard stop.

`IBMSchwartzPhysicalPrimitive` identifies the ACTUAL first-source physical primitive of the whole Schwartz spatial observable, without a formal Gaussian series. For a shifted Schwartz test g, actual source vector u_n(r), and Q_j=E[g^(j)(a+W(u_n(r)))], it proves

P_n(r)=Q_(1,n)(r) Q_(rho_n,r),
P_n'(r)=d_n(r) Q_(3,n)(r) Q_(rho_n,r)+Q_(1,n)(r)rho_n(r-w),
P_n''(r)=K_n(r),
P_n'(0)=originKernel_n.

Here d_n=<u_n,v_n>, Q_(rho_n,r) is the actual physical Lebesgue-L2 convolution kernel, and K_n is1078's FULL first-source curvature, including ((q_n+e_n)Q_3+d_n^2 Q_5)Q_0+2d_n Q_3 rho_n+Q_1 rho_n'. The origin identity uses the verified d_n(0)=0. All derivatives are genuine norm derivatives in physical L2, and `primitive_C2` proves ContDiff R2 on the entire real line. Both first and second spatial FTC identities hold for arbitrary endpoint ordering. `wholeKernel_derivatives` identifies the actual whole kernel as the Tanaka mass times P_n'(0) plus one-half the clock-time integral of P_n'' at the reflected clock. This last theorem is an exact rewriting of independently constructed objects, NOT a stochastic chain rule.

The general source formula firstChaosEmbedding* observable_j(u)=Q_(j+1)(u)u is independently justified from the existing mixed Gaussian Stein identity. It includes u=0 and uses no variance division. Applying the actual physical noise to P_n recovers the complete first-chaos projection of the actual spatial observable; the adjoint physical pullback does not lose an unexamined coefficient component. The primitive limit is Q_1(base(r))v_r in the actual physical L2 space and reconstructs the first-chaos projection of the actual unmollified observable.

`IBMSchwartzPhysicalPrimitiveClock` constructs actual Bochner L2(clock;GaussianL2(source)) endpoint classes of g(a+X_n(|Y_T|)) and g(a+X(|Y_T|)). Their source sections are the already constructed continuous IBM observable g(a+Z_T), almost everywhere in each independent factor. The entire endpoint classes converge strongly, retaining every source chaos degree; the proof reuses the Schwartz uniform bound, existing source convergence and verified Bochner dominated convergence. The physical primitive endpoint classes consequently converge strongly in L2(clock;physical L2), and applying the physical noise reconstructs exactly the entire first-source endpoint projection before clock averaging. This endpoint convergence does not imply convergence of the spatial derivatives or whole correction.

`IBMPhysicalDiracDifference` proves the physical sign identity from actual complexified Brownian indicator functions:

D_w v_r = delta_0-delta_r in tempered distributions.

The proof evaluates the actual Lp-to-distribution embedding on Schwartz tests, uses the oriented whole-line indicator pairing and the complex FTC, and keeps both endpoints. Thus delta_r-delta_s has the genuine H^-1 representative D_w(v_s-v_r), with norm at most ||D_w|| sqrt(|s-r|). This proves the physical Holder bound and continuity of anchored Dirac differences without interpreting arbitrary L2 values at a point.

`IBMPhysicalDirac` explicitly REUSES `IBMDeltaBoundary.deltaZeroHminusOne`, whose Fourier proof of delta_0 membership was already verified. No new Fourier normalization or alternate probability source is introduced. The new translated mass is

delta_r^H = deltaZeroHminusOne-D_w v_r,

and its distribution is exactly delta_r. The physical smooth translated bump is the Sobolev realization of its actual complexified Lebesgue-L2 class. For every n and every real r, the exact equality is

[rho_n(r-w)]_(H^-1) = deltaZeroHminusOne-D_w Q_(rho_n,r).

This is proved by bounded scalar testing of the existing Bochner kernel integral, the already established derivative-of-indicator identity, the actual normalized bump integral and cancellation of the two scalar integrals. It does not define the translated bump by the right side and then assume agreement. The Sobolev embedding of the actual translated L2 function is constructed first, and equality is proved by distributional extensionality. The fixed-n scalar integrability is supplied by actual compact support.

Consequently the actual translated bump converges strongly to the actual Dirac at each physical r. More significantly, `mollifiedDirac_ae`, `diracClass_ae`, and `mollifiedDirac_tendsto` give genuine L2(clock;H^-1(physical space)) classes with representatives rho_n(|Y_T|-w) and delta_(|Y_T|), and prove their strong convergence at every nonnegative fixed horizon T. They reuse1077's existing strong physical derivative limit by adding the SAME deterministic delta_0 in the clock L2 space. This now identifies what that derivative limit means for the actual approximate-Dirac channel, rather than confusing it with the whole correction.

Remaining F1 obligations: convergence of nonlinear weighted first spatial slopes in the correct time-clock norm; an actual adapted H^-1-valued clock integral with reflected boundary accounting and a justified stochastic chain-rule limit; then convergence of the entire K_n^whole, including the origin mass and weighted rho_n' channel. The new unweighted Dirac limit is not a limit for Q_1 rho_n', nor for the covariance-layer term. Higher positive-source/positive-clock sectors, common physical dual/global summation, and F3 joint clock-domain/intrinsic-core density remain open. No bulk origin substitution or native-L2 regularization is asserted.

The clock-Ito reuse audit is sharpened: `GaussianC2Ito.c2_ito` already improves the scalar smooth core to C2 with bounded first and second derivatives, and `GaussianFiniteRankTimeIto.finite_rank_ito` supplies a scalar finite-rank time-dependent formula. The earlier1078 candidate description mentioned the narrower scalar C3 theorem; the C2 theorem should be reused when its ACTUAL derivative bounds hold. Neither theorem by itself supplies a reflected-clock formula for this infinite-dimensional H^-1 target. `GaussianMixedStoppedIto` concerns deterministic stopped coordinates and must not be treated as random stopping/localization. No target-valued/reflected stochastic calculus theorem is silently assumed here.

All62 public declaration types from the four new modules are inspected at the checkpoint. Default elaboration settings are retained. Incoming remains43files/42hashes, with the dictionary and all four IBM archive baselines unchanged. Manuscripts, dependencies/toolchain, unrelated documents and successor campaigns are preserved.

## Discovery1080: full nonlinear first-slope convergence and actual predictable Hminus clock integrands

Continued from verified3ad926590528014bc0c6b60295ccf3450a87102d. The preceding turn made verified progress. Starting terminal time was2026-10-18T21:48:44-04:00; subsequent proof-break checks include21:53:56,21:58:35 and22:01:47. IBM remains immediate, with the three successor gates and October31 hard stop unchanged.

`IBMPhysicalNegativeEmbedding` bundles the actual physical Lebesgue-L2 function as an element of the SAME physical complex H^-1 used for the existing derivative. It reuses1079's actual Sobolev membership `IBMPhysicalDirac.l2Value`, not a replacement coefficient norm. Additivity and real homogeneity are proved by distributional extensionality. The sequential graph is proved closed by comparing the continuous L2 and H^-1 embeddings into tempered distributions, and the existing closed-graph theorem supplies the bounded real-linear embedding E. Its distribution is EXACTLY the complexification of the original physical L2 function. The operator norm is finite; no unproved norm-one estimate is asserted. Two local-use propositions verify the norm and joint continuity of the existing pointwise real scalar action on H^-1 by transporting through the verified Bessel-to-L2 isometry. They introduce no alternate Sobolev normalization or global type-class overrides.

`IBMSchwartzPhysicalSlope` proves convergence of the ENTIRE first spatial slope from1079, with both nonlinear terms. Write u_n(r)=the actual zeroth triple coefficient, d_n(r)=<u_n(r),v_n(r)>, M_j(u)=E[g^(j)(a+W(u))], and let v_r denote the physical oriented Brownian indicator. The fixed-n object is ACTUALLY E(P_n'(r)), where P_n is1079's physical C2 primitive. The exact identity is

S_n(r)=d_n(r) M_3(u_n(r)) E(Q_(rho_n,r))
       +M_1(u_n(r)) [rho_n(r-w)]_(H^-1).

The complete strong H^-1 limit at every real r is

S(r)=(signum(r)/2) M_3(base(r)) E(v_r)
       +M_1(base(r)) delta_r^H.

This includes negative radii and the degenerate origin. The covariance identity d_n=(variance_n)'/2, its uniform bound, and its pointwise limit signum(r)/2 are reused from `IBMQuarticSecondGeometry.coefficient_slope` and `IBMVarianceClockGeometry.slope_bound/slope_tendsto`. In particular d_n(0)=0 and the limiting coefficient at zero is zero. No interior value1/2 is substituted at zero. All shifted Schwartz Gaussian means are proved continuous on the full source Hilbert space, including zero, and bounded by their actual Schwartz seminorm. Their convergence uses the already verified actual source-vector mollifier limit.

The translated-Dirac term is1079's ACTUAL smooth L2-function embedding; its strong limit is the actual Dirac distribution, not a formal white-noise evaluation. The zeroth term uses the newly bounded zero-order embedding E. Consequently both terms converge in the SAME physical H^-1 space. `value_tendsto` is a theorem about convergence of actual fixed-n first spatial derivatives; it does NOT by itself assert that differentiating the unmollified primitive commutes with the singular limit. That deterministic derivative-identification step, if needed, must be proved by an appropriate FTC or closed derivative argument.

A single finite constant C_g, independent of n and r, is proved to satisfy

||S_n(r)||_(H^-1) <= C_g(1+|r|),
||S(r)||_(H^-1) <= C_g(1+|r|).

The proof transports the existing quantitative physical Brownian smoothing estimate, bounds Q_(rho_n,r) by3(1+|r|), and uses the exact anchored Dirac identity. It does not try to bound the native physical L2 norm of an approximate Dirac uniformly. The growth constant uses only actual Schwartz seminorms, ||E||, ||D_w|| and the already verified delta_0 H^-1 norm.

`IBMSchwartzPhysicalSlopeClock` constructs the actual signed candidate clock fields

U_n(s,omega)=1_(0<s<=T) signum(Y_s(omega)) S_n(|Y_s(omega)|),
U(s,omega)=1_(0<s<=T) signum(Y_s(omega)) S(|Y_s(omega)|).

They are actual Bochner L2 equivalence classes with values in physical H^-1, using the existing continuous clockPath and the existing timeProbability measure volume x gaussianProduct. Their AE representative identities are proved. The time support is exactly the existing horizon, including the zero horizon case. The global growth bound, verified clock moments, and original Bochner dominated convergence prove

U_n -> U strongly in L2(R_time x Omega_clock;H^-1(R_physical)).

This is a joint time-clock theorem on each finite horizon, not merely fixed-time convergence, clock averaging, or a sectorwise formal limit. It retains BOTH nonlinear source-mean weights. The first-chaos physical coefficient has been retained before all clock chaos degrees; no clock-sector truncation is used.

`field_predictable` and `limitField_predictable` prove AEStronglyMeasurable representatives for the repository's EXISTING predictable sigma-algebra of the actual Gaussian Brownian filtration. The proof reuses `GaussianHermiteRepresentation.hermiteIntegrand 1 T` and `BrownianSignIntegral.brownian_field_joint`, composes its predictable representative with the actual Borel H^-1-valued signed spatial function, and checks zero extension using signum(0)=0. This establishes genuine predictability rather than taking adaptedness as a supplied hypothesis. It does not define a target-valued Ito integral by naming a residual.

The first-source F1 frontier is therefore narrowed: the complete nonlinear candidate integrands now have actual predictable domains and strong time-clock H^-1 convergence. An actual bounded/isometric H^-1-target clock Ito operator and a justified reflected-clock finite-mollifier identity are still needed to turn these into convergence of the ENTIRE correction kernel. The whole correction includes the Tanaka boundary coefficient and second spatial curvature, and no such stochastic identity is assumed. The weighted rho_n' channel and covariance layer cannot be separately replaced by this first-derivative limit. Higher positive-source/positive-clock sectors, common physical dual/global summation, and F3 joint clock-domain/intrinsic-core density remain open. All earlier F2 and edge-family results are preserved.

A concrete reuse route for the next proof break is recorded, not claimed as a theorem: `ProductL2Curry.curryEquiv` in `ProductL2Equivalence` is already an onto isometry for SFinite parameter measures, so the physical Lebesgue variable need not be treated as a finite probability factor. Combined with the Bessel-to-physical-L2 isometry and the actual scalar predictable Ito isometry, it may supply a fiberwise target-valued integral after the predictable slice domain is rigorously identified. `BochnerLinearIsometry.lift` already lifts a genuine isometry to a Bochner parameter space. `GaussianBochnerDivergenceRecovery` is a source-divergence recovery theorem; it must not be confused with an adapted clock Ito integral for this H^-1 target. No new tensor-product foundation or unproved stochastic law is introduced at this checkpoint.

All48 new public declaration types are inspected at the checkpoint. All three modules use default elaboration resources, with only local instance selection for the existing complex Hilbert target. Source manuscripts, toolchain/dependencies, unrelated documents and queued campaigns are preserved. Incoming remains43files/42hashes, and the dictionary plus all four IBM archive hashes remain unchanged.

## Discovery1081: actual predictable physical H^-1 Itô integral and strong convergence of the nonlinear clock integrals

Continued from verified cd7d6ed02687ad4740bbe5aec92c9f2f0f89335d (1080). Terminal checks during the dependency rebuild include 2026-10-18T22:48:27-04:00 and22:49:25. IBM remains the immediate campaign; A(4), A(2), and the final multichannel pseudoprocess attempt retain their gates and October31 hard stop.

The previous first-source clock field is now integrated by an ACTUAL real-linear isometry, independently of any proposed reconstruction. `IBMPhysicalClockIto.Domain T` is the existing native complex `lpMeas` space of physical H^-1-valued, finite-horizon L2 fields measurable for `PredictableRealL2.predictable naturalFiltration`. Its ambient measure is the existing `horizonMeasure T gaussianProduct`. The integral is transported through Mathlib's exact `lpMeasToLpTrimLie`, the actual Bessel-potential-to-physical-complex-L2 isometry, the actual scalar Brownian Itô operator, and the inverse Bessel map. It is NOT defined as endpoint minus a correction. `integralIsometry`, `integral_norm`, `integral_isometry`, additivity, zero and real homogeneity are proved, including T=0.

The supporting construction reuses `ProductL2Curry.flip`, `curryEquiv`, and `BochnerLinearIsometry.lift`. The latter's four existing public declarations are generalized from real scalars to arbitrary nontrivially normed scalar fields; all previous uses are included in the full-build and transitive audit. `ComplexL2Isometry` complexifies a real L2 isometry by its real and imaginary parts, proving the genuine squared-norm sum identity. The resulting operator is bundled as real-linear; no unjustified complex linearity is assumed. `GaussianComplexHorizonIto.realIto_trim` identifies the transported scalar operator with the original native predictable Itô isometry. Second countability of the real and complex trimmed predictable L2 spaces is proved by isometric embedding into the actual ambient L2 spaces, without assuming countable generation of the predictable sigma-algebra.

`GaussianParameterizedIto.integral` constructs the actual parameter-target operator by flipping real L2 factors, lifting the existing scalar Itô isometry, complexifying on the flat product space, and currying back. Physical Lebesgue measure is allowed; it is not replaced by a probability measure. `GaussianParameterizedItoTensor.integral_tensor` proves agreement with the actual scalar integral times every complex physical L2 vector. `integral_scalarization` proves that EVERY bounded real scalar functional commutes with this parameter-target integral on its ENTIRE L2 domain, using finite-rank agreement and Mathlib's Lp simple-field density. This closes a genuine naturality obligation rather than adding it as a hypothesis.

`IBMPhysicalClockItoTensor` transports the finite-rank identities to the SAME physical H^-1 target used in1077–1080. Native input and output AE representatives are verified. In particular `integral_native_tensor` and `integral_native_tensor_ae` identify the result with the original native scalar Itô integral times the prescribed H^-1 vector. This is agreement with the existing stochastic increment-product construction, not just an operator satisfying an abstract norm estimate. General H^-1-functional naturality can subsequently be transported from the proved parameter-target theorem; no such additional theorem is silently asserted here.

`IBMSchwartzPhysicalClockIntegral` restricts1080's actual signed predictable nonlinear fields to this native horizon domain. Both finite and limiting integrands have their required measurability proved from the existing representative theorems. `integrand_tendsto` and `integralValue_tendsto` give strong convergence in the actual domain and in L2(Omega_clock;H^-1(R_physical)), respectively. `integralValue_difference_norm` gives the exact Itô-isometry distance identity. These results preserve all clock variability and both nonlinear source-mean slope terms. They are not merely convergence of clock expectations or a clock-sector truncation. No unproved martingale/time-consistency property is appended to the newly constructed terminal values.

`ReflectedC2Primitive` supplies a deterministic ingredient for the remaining identity. For every real C2 function f, the corrected reflected primitive f(|x|)-|x| f'(0) is proved globally C2, including at zero. Its derivative is f'(x)-f'(0) on the positive side and f'(0)-f'(-x) on the negative side; its second derivative is f''(|x|). Global first- and second-derivative bounds transfer explicitly (first derivative at most twice the original bound, second derivative with the same bound). The proof glues actual within-half-line derivatives at zero; differentiability of absolute value is not assumed.

The ENTIRE first-source IBM correction limit is STILL OPEN. It requires the finite-mollifier reflected Itô/Tanaka identity identifying endpoint minus this actual integral with1078's boundary-plus-curvature physical kernel. The new integral convergence alone does not identify that residual with the manuscript correction. A concrete next route is fixed-mollifier global derivative bounds via first-chaos contraction, followed by the EXISTING scalar C2 Itô theorem applied to the proved reflected correction, scalar testing, and the existing Tanaka normalization. Neither those bounds nor that stochastic chain identity are claimed here. Higher mixed source/clock sectors, common physical dual/global summation, and F3 joint clock-domain/intrinsic-core density remain unresolved. The previous F2 and edge-family results are preserved. IBM is not frozen and no successor campaign is opened.

All87 public declaration types, including the four generalized old declarations, are inspected at the checkpoint. Manuscripts remain read-only. Incoming retains43files/42hashes and the dictionary SHA256 8EC222C21FDB2D81D652E3CF553BE59EEA987F01AD3B1C54EEC91216111BC22E. The four archived IBM source hashes retain their recorded baselines. No toolchain/dependency changes, resource-flag increases, extra axioms or unrelated document edits are introduced.

Verification recovery: an interrupted build session left ten generated .olean files with invalid headers. Those exact cache artifacts were quarantined inside .lake, and the complete5666-job build was repeated successfully with the already installed Lean4.34.1 toolchain (commit5045d00). No Lean source contains null bytes; comparison with1080's entire source manifest found only the intended generalized-isometry and root-import changes among pre-existing files. The interrupted and failed recovery logs are preserved separately.

Exploration during verification also produced separately kernel-checked DRAFTS of the fixed-mollifier global physical first-slope/curvature bounds, native H^-1-functional integral commutation, and the scalar reflected C2 Itô/Tanaka formula with its actual signed predictable-field and time-drift representatives. These drafts are not part of this87-declaration public checkpoint and have not yet received a root build/axiom audit as production modules. Exact source fragments, successful draft logs, hashes and a recoverable source snapshot are listed in `.lake/stardust-1081-pending-research.md` and `.lake/stardust-1082-draft-hashes.json`. They support the next IBM proof step; they do not establish the physical whole-kernel identity or settle F1–F3.

Verification1081: target4409 jobs, full5666 jobs, exit0. All87 public types inspected. Root audit30249 safe Foundation declarations with only propext, Classical.choice, Quot.sound. Forbidden-token and direct/Git whitespace checks passed. All43 sources retain42 hashes, staged/unstaged source/dependency diffs empty. Evidence: `.lake/stardust-1081-module.log`, `.lake/stardust-1081-full-build.log`, `.lake/stardust-1081-audit.log`, `.lake/stardust-1081-public-types.json`, `.lake/stardust-1081-inventory-check.json`. The focused IBM F1–F3 campaign remains active; successor gates and the October31 hard stop remain in force. The final multichannel campaign is queued, not active.

## Discovery1082: actual reflected physical Itô–Tanaka identity and the whole first-source H^-1 correction limit

Continued from audited commit fa7ebb7d65279a409a5591519b96a1be4d6ab985 (1081). System-clock proof breaks on 2026-10-19 included 00:11:53, 00:15:30, 00:19:25 and 00:21:40 America/New_York. The focused IBM F1–F3 campaign remains active; A(4), A(2), the final multichannel campaign and the October31 stop retain their existing gates. No manuscript was changed or adopted as an axiom.

`IBMSchwartzPhysicalGlobalBounds` closes the previously missing FIXED-mollifier global derivative bounds. The verified Gaussian first-chaos adjoint is contractive, so |M_(j+1)(u)| ||u|| is bounded by the j-th Schwartz-jet seminorm, including u=0 without variance division. Translation invariance gives the exact physical L2 norms of translated kernel jets. The actual bracket ||v||²+<u,w>=rho_n(r), together with the verified covariance bound, yields global bounds for the physical first slope and curvature. These constants may grow with n; no uniform approximate-Dirac L2 bound is asserted. They are used only for the finite-n chain rule. The already verified H^-1 integrand estimates, rather than these n-dependent constants, control the singular limit.

`IBMPhysicalClockItoScalar.native_scalarization` transports the previously proved parameter-target naturality to EVERY bounded real functional on the actual native physical H^-1 integral domain. Its `pullback`, `decode_test` and `encode_test` use the existing Bessel representation and its inverse. `IBMSchwartzPhysicalReflectedIto.scalarization_full` further identifies scalarized native integrals with the OLD full predictable Brownian Itô integral whenever their actual horizon-supported representatives agree. This is proved through the exact trimmed-domain equivalence, zero extension and equality of the independently constructed integral domains; it is not an extra naturality assumption.

`GaussianReflectedC2Ito` proves the actual scalar reflected C2 formula for every real C2 f with globally bounded first two derivatives and every nonnegative horizon T. It applies the existing C2 Itô theorem to f(|x|)-|x|f'(0), then the actual Brownian Tanaka identity. The predictable running field is proved AE equal to 1_(0,T] sign(Y_s) f'(|Y_s|). The drift is identified AE with the ordinary pathwise interval integral of f''(|Y_s|), using the existing Bochner representative/Fubini theorem. Thus `reflected_ito_pathwise` is a stochastic identity with the existing integral and continuous clock mass, not an expectation-level heat equation. The normalization is f'(0)L_T+(1/2) integral f''(|Y_s|)ds, where L is the previously verified Tanaka residual. No differentiability of absolute value at zero is assumed.

`IBMSchwartzPhysicalReflectedIto` applies this formula to all real scalar tests of the actual embedded physical primitive. `scalarPrimitive_C2`, its two derivative identities and `scalarPrimitive_bounds` discharge its functional hypotheses. `native_integrand_ae` identifies the existing native predictable field with sign(Y) times the embedded full nonlinear slope, retaining both nonlinear coefficient terms. `integral_test` identifies the resulting stochastic term with the actual native H^-1 integral constructed at1081. `tested_reflected_identity` then matches both the boundary and curvature terms with the ORIGINAL `IBMSchwartzPhysicalFirstKernel.wholeKernel`. Countable dual separation in the actual separable H^-1 space proves `reflected_identity_ae`, an H^-1-valued equality rather than a collection of incompatible scalar null-set claims.

Writing E for the existing physical L2-to-H^-1 embedding, P_n for the previously verified first-source primitive and K_n for the ORIGINAL whole physical correction kernel, the exact finite-mollifier identity is

    E(P_n(|Y_T|)-P_n(0)) = I_n(T) + E(K_n(T))  almost surely.

The value P_n(0) is retained at finite n. `endpointClass_ae` and `wholeClass_ae` identify the actual random representatives. `finite_mollifier_identity` establishes equality in L2(Omega_clock;H^-1(R_physical)); the stochastic integral I_n is NOT defined as a reconstruction residual. `wholeClass` is defined by applying E to the already constructed wholeKernelClass, so the new theorem genuinely identifies the old manuscript correction. It includes the origin layer, bulk curvature, every clock chaos degree, all shifts a, all Schwartz tests g, all mollifiers n and T=0.

`endpointClass_tendsto` combines the existing strong endpoint convergence with the actual deterministic origin convergence. `wholeClass_tendsto` then proves strong convergence of the ENTIRE first-source physical correction in the PRECISE topology L2(Omega_clock;H^-1(R_physical)). `primitiveLimit_zero` follows from the already verified physical vector at zero, so the origin subtraction disappears only after taking the limit. `endpointLimitClass_ae` identifies the limiting representative as E(P(|Y_T|)); `wholeClass_tendsto_uncentered` identifies the limit as this actual endpoint class minus the actual limiting native stochastic integral. The primitive endpoint already realizes the first-source projection of the constructed nonlinear IBM observable by `IBMSchwartzPhysicalPrimitiveClock.primitiveLimitClass_realizes_projection`; the source/clock factorization and earlier source-resolved interpretation are reused directly.

This closes the previously open finite-mollifier physical identity AND the full first-source/all-clock physical H^-1 correction limit. It does NOT establish convergence in native joint Gaussian L2, extend physical white noise continuously to arbitrary H^-1 distributions, control higher source chaos m>=2, supply a common topology with global source-sector summation, or resolve F3's intrinsic IBM core density. Source sector m=1 with unrestricted clock degree n is covered; arbitrary (m,n) is not. The previously proved native first-chaos obstruction remains valid. No completion of IBM F1–F3, full unprojected Itô–Tanaka calculus or successor transition is declared.

At the user's separate request, private GitHub backup and an independent 30-minute Windows synchronization task were configured. `AGENTS.md` and `STARDUST_SYNC.md` record the exact-commit audit-receipt step. Only completed audited checkpoints may advance remote main; the task commits nothing, builds nothing, never force-pushes or deletes refs, verifies private visibility and compares remote commit IDs. This supersedes historical no-push/no-automation backup restrictions, without authorizing unfinished mathematical commits or manuscript edits. The original archival backup remains on its separate backup branch.

Verification1082: target4414 jobs and full5670 jobs completed successfully; all41 public types inspected; transitive root audit30334 safe Foundation declarations, with only propext, Classical.choice, Quot.sound. All107 archive file hashes and the43-file/42-hash Incoming inventory remain unchanged, including the dictionary hash. The prior1612-source manifest differs only at the intended root imports; four new modules bring the source manifest to1616. No dependency/toolchain changes, resource-flag increases or unsafe proof devices were introduced. The exact9-path checkpoint includes the four new modules, root imports, both research ledgers, and the two explicitly requested backup-governance documents. Evidence: `.lake/stardust-1082-module.log`, `.lake/stardust-1082-full-build.log`, `.lake/stardust-1082-audit.log`, `.lake/stardust-1082-public-types.json`, `.lake/stardust-1082-source-integrity.json`, `.lake/stardust-1082-inventory-check.json` and `.lake/stardust-1082-working-checkpoint.json`. The first failed target log preserves only the corrected name of the constant-Lp zero lemma; the central prototype and final production proof both pass. IBM remains active.

## Discovery1083: actual full-source finite-mollifier Itô–Tanaka identity and exact native convergence criterion

Continued from verified c4895627783be666515c6ab2632eeb3c1a8b68e6 (1082). System-clock proof breaks included 2026-10-19T00:27:25, 00:31:53, 00:38:49 and 00:42:56 America/New_York. The preceding goal turn made verified mathematical progress; the focused IBM F1–F3 campaign remains active and no successor gate is released. Manuscripts remain read-only and untrusted as theorem sources.

`GaussianRealParameterizedItoScalar` extends the already constructed REAL parameter-target integral by two actual naturality theorems. `realIntegral_scalarization` proves agreement with every bounded real scalar functional. `realIntegral_naturality` proves commutation with every bounded endomorphism of the real parameter L2 target. Both use the existing scalar Itô isometry, the verified `realIntegral_tensor` stochastic step/tensor agreement and Mathlib's actual Lp simple-field density. No density, naturality or stochastic law is assumed. This reuses1081's parameter integral rather than constructing a new Hilbert stochastic integration foundation.

`GaussianSourceClockIto` instantiates that operator with the independent scenery's actual gaussianProduct measure. Its target is GaussianL2 of scenery, its input is the existing real lpMeas GaussianL2 predictable domain on the actual clock horizon, and `trimEquiv` is the exact Mathlib trimmed-measure equivalence. `integral` is a genuine real-linear isometry. `integral_tensor`, `native_scalarization` and `scalarization_full` connect it respectively to actual scalar tensors, bounded source functionals and the OLD full predictable clock Itô integral. `mapField_ae` identifies bounded source-operator actions on the actual native input representative, and `integral_mapField` proves that these actions commute with integration. No intrinsic IBM filtration or intrinsic adjoint is claimed from this clock-filtration construction.

`IBMSchwartzFullGlobalBounds` supplies fixed-mollifier GLOBAL bounds for the UNPROJECTED nonlinear source curve. Exact `jet_one_norm` and `jet_two_norm` transport the existing physical translation identities to the actual source-coefficient jets. With B0=||rho_n||_2 and B1=||rho'_n||_2, the full slope is bounded by seminorm1(g)*B0, and the curvature by 2*seminorm2(g)*B0²+seminorm1(g)*B1. Bounded Gaussian jet multiplication and the actual Gaussian-square L2 bound discharge these estimates independently of the radius; no arbitrary L2 multiplication is used. The already verified actual first/second spatial derivatives and their continuity give `spatial_C2`. These are fixed-n estimates, not uniform shrinking-mollifier estimates.

`IBMSchwartzFullReflectedIto` constructs the actual signed field sign(Y_s) g'(a+W(u_n(|Y_s|))) W(v_n(|Y_s|)) as a genuine scenery-GaussianL2-valued clock integrand. Its finite-horizon L2 membership, measurable representative and raw clock-predictability are all proved. The predictable representative is obtained by composing the EXISTING first Hermite integrand representative, not by assuming a target stochastic domain. `integralValue` applies the already constructed stochastic operator to this field; it is not a residual definition.

The scalar-tested primitive is the whole nonlinear scenery observable, not its first-source projection. Its actual C2 derivatives and global bounds meet1082's scalar reflected Itô theorem for every bounded real source functional. `integral_test` identifies its stochastic term with the actual new native integral. `tested_reflected_identity` matches the ORIGINAL `IBMSchwartzTimeProjection.wholeCorrection`, including its original originClass and its original full mollifiedClass time integral. Dual separation in actual separable scenery GaussianL2 proves `reflected_identity_ae`. The resulting `finite_mollifier_identity` is equality of actual L2(Omega_clock;L2(Omega_scenery)) classes:

    endpoint_n(T) - constant(sourceObservable_n(0))
       = actual_clock_Ito_n(T) + ORIGINAL_wholeCorrectionClass_n(T).

These are fixed-horizon AE identities, not an asserted common exceptional set over all horizons or an additional path-continuity/martingale theorem for the native terminal family. This closes the full finite-mollifier stochastic reconstruction with every source and clock sector retained together, for all Schwartz g, all shifts a, all n and all nonnegative horizons including zero. The finite-n origin is the mollified random source observable at zero, not an assumed deterministic g(a). `spatialLimit_zero` proves that its LIMIT is g(a) times the source vacuum. `endpointClass_tendsto` gives strong native joint-L2 convergence of the centered endpoints, and `endpointLimitClass_actual_sections` identifies their limiting sections with the genuinely constructed IBM observable g(a+Z_T)-g(a).

`source_projection_identity` passes the actual finite-n identity through EVERY existing completed source-chaos projection, commuting the source projection through the genuine stochastic integral via the proved bounded-operator theorem. `source_integrand_ae` gives its exact signed projected representative. The concrete `source_two_integrand_ae` reuses `IBMSchwartzSpatialPrimitive.spatialSlope_eq_origin_projection` and hence the existing explicit second-source slope kernel, rather than launching a separate chaos construction. The old completed `correction_projection_two`/`secondCandidate` curvature formulas and source-resolved interpretation remain compatible with the original correction on the right. Clock-chaos projections are not asserted to commute with Itô integration; no fixed-bidegree limit or cross-sector summation follows from source naturality alone.

The exact singular-limit test `whole_cauchy_iff_integrand` proves that the ORIGINAL full corrections are Cauchy in native joint Gaussian L2 IF AND ONLY IF these genuine native predictable integrands are Cauchy. This follows from the actual finite-n reconstruction, the proved endpoint convergence, completeness of the target L2 and the exact Itô isometry. It does not assume either Cauchy property. Thus finite-scale representation is not mistaken for a full correction limit; previously established native obstructions are not removed. The verified1082 first-source/all-clock physical H^-1 closure remains valid, but a common physical topology for higher sources and global F1 summation are still missing.

Selective source/reuse audit reread the cached text of the immutable primary manuscript PDF at pages12,22–23, especially Open problem5.4/F3 and7.1/F1. The source still expects intrinsic-core nondensity based partly on pointwise scenery-domain failure. The already verified partial scenery derivative contradicts that proposed rationale; it does not prove joint-clock membership or intrinsic-core density. The earlier1074/1075 time-smoothed IBM cylinder route is preserved. A possible next concrete estimate is a TWO-TIME folded-clock density bound controlling mollified source-gradient covariance in time-averaged observables. No such uniform joint graph estimate, intrinsic algebra closure or density theorem is claimed at1083. F2's genuine boundary-layer random limit and the controlled source-zero/full-clock family remain preserved. IBM remains active; October31 remains the hard stop.

Verification1083: target4413 and full5674 jobs passed, all46 public types inspected, transitive root audit30424 safe Foundation declarations with only propext, Classical.choice, Quot.sound. All107 archive hashes and the43-file/42-hash Incoming inventory remain unchanged, including the dictionary SHA2568EC222C21FDB2D81D652E3CF553BE59EEA987F01AD3B1C54EEC91216111BC22E. The old1616-source manifest differs only at root imports; four new modules bring it to1620. Code hygiene and whitespace checks pass; exact7-path checkpoint excludes ResearchSources, dependencies and unrelated notes. No toolchain/dependency changes, resource increases, new axioms or unsafe proof devices. Evidence: `.lake/stardust-1083-module.log`, `.lake/stardust-1083-full-build.log`, `.lake/stardust-1083-audit.log`, `.lake/stardust-1083-public-types.json`, `.lake/stardust-1083-source-integrity.json`, `.lake/stardust-1083-inventory-check.json` and `.lake/stardust-1083-working-checkpoint.json`. The independent backup scheduler completed its regular00:40 run during this research turn without touching the drafts. IBM remains active.


## Verified discovery1084 — uniform actual two-time clock bound for physical mollifier overlaps

Continued from audited79f76dbe45745724516a0ad2f0b7ab751ff0364b (1083). Terminal proof breaks on2026-10-19 include00:55:16,00:57:48,01:00:29,01:02:24 and01:04:49 America/New_York. The preceding queue-confirmation turn was a read-only status response, not mathematical progress. Revalidation found no live proof/build handle; this turn resumes the concrete F3 time-average route rather than repeating the status. IBM remains immediate. The IBM → A(4) → A(2) → final full multichannel campaign gates and October31 stopping date remain unchanged.

New root-imported module: `Foundation/IBMFoldedTransitionBound.lean`. Write rho_n for the existing actual normalized nonnegative compactly supported smooth mollifier, and

`K_nm(r,q) = integral_x rho_n(r-x) rho_m(q-x) dx`.

The module identifies K_nm exactly with BOTH the physical Lebesgue-L2 inner product of `convolutionKernel (deriv (kernel n)) r` and its m,q counterpart, and the coefficient-space inner product of the verified first-spatial-derivative columns `tripleCoefficient n r 1`, `tripleCoefficient m q 1`. It proves nonnegativity, continuity, and a fixed-n,m bound (the latter is not claimed uniform). This reuses the actual physical white-noise realization and derivative-column Fubini identification; no abstract substitute covariance is introduced.

The substantive new estimate is `clockPath_overlap_le`: for all n,m and actual continuous constructed Brownian clock Y, whenever0<=s<t,

`E[K_nm(|Y_s|,|Y_t|)] <= 2 / sqrt(2*pi*|t-s|)`.

The Lean statement uses `2 * peak (nndist (t:Real) (s:Real))`, with `peak v = (sqrt(2*pi*v))^-1`; s,t have type NNReal. Thus the estimate is uniform in BOTH mollifier widths. It permits s=0 and requires s<t. No assertion is made on the diagonal, and no diagonal-null or product-time integrability theorem is inferred without proof.

Proof route: establish the L1-to-L-infinity estimate for integration of any continuous nonnegative Lebesgue-integrable k against the ACTUAL folded Gaussian law of arbitrary mean a and nonzero variance v. The density is bounded by its peak, folding costs a factor2, and positive-halfline mass is bounded by total mass. Apply this to each translated mollifier; prove product-kernel integrability and actual Gaussian/Lebesgue Fubini; integrate the other normalized positive mollifier to obtain a bound uniform in n,m,r,a. Transfer to two actual clock times via `process_disjoint_increments_independent`, the actual time/increment Gaussian laws, their independent product law, translated Gaussian laws, and the fixed-time AE equalities for the continuous clock modification. No conditional-density, Markov-kernel, covariance-bound, or Sobolev-domain hypothesis is supplied by the caller. The elementary observation that a translated folded Gaussian has at most twice the Gaussian peak is thereby proved for the process used in IBM, rather than adopted from a formal analogy.

Relevance and exact remaining gap: this proves the previously proposed two-time kernel estimate needed for time-averaged IBM cylinders. It does NOT establish that their actual clock derivatives exist, that a uniform derivative-energy bound holds after double time integration, that the derivatives converge strongly, or that their intrinsic algebra is dense in L2(F_Z). Next discharge the product-time diagonal and the integrable inverse-square-root bound with the actual clock representer factor min(s,t); construct the fixed-n time-average CLOCK derivative graph and connect the strong observable limit to a verified closed/weak gradient criterion. The partial scenery graph is already available from1046. Bounded smooth functions of several genuine time averages and arbitrary-law observable density remain separate obligations; Gaussian observation polynomial-density theorems cannot simply be applied to IBM. F1 higher-source common physical topology/global summation remains open. F2 and all1082/1083 results are preserved. No IBM freeze or successor transition is asserted.

Verification: the module checked with no errors; full `lake build` passed5675 jobs. Root-wide transitive axiom audit passed30445 safe Foundation declarations, with only `propext`, `Classical.choice`, `Quot.sound`. All19 new public declaration types were inspected, including variance, sign, time-order, measure, and realization hypotheses. No sorry/admit/new axiom was introduced. All107 original archive manuscript hashes and43 Incoming files (42 distinct hashes) match their saved baselines; the Yang-Mills/Navier-Stokes dictionary hash remains8EC222C21FDB2D81D652E3CF553BE59EEA987F01AD3B1C54EEC91216111BC22E. No manuscript, pinned dependency, unrelated draft, goal, or campaign instruction was changed. Source reference remains the immutable IBM Itô–Tanaka anchor's F3 discussion (cached pages12,22–23), interpreted with the earlier1046 correction to its asserted scenery-domain obstruction. This checkpoint resolves a supporting estimate, not the manuscript's joint core-density claim.


## Verified discovery1085 — uniform signed clock-covariance energy on the full time square

Continued from audited9a9a709030f4807675c75e3adac224b85c242833 (1084). The previous goal turn made substantive mathematical progress. Terminal proof/research checks on2026-10-19 include01:07:16,01:10:28,01:14:17,01:18:47,01:22:32,01:26:38,01:27:36 and01:29:09 America/New_York. IBM F1–F3 remains immediate. The queued A(4), A(2), final multichannel campaign and October31 hard stop retain their gates.

New root-imported module: `Foundation/IBMClockOverlapEnergy.lean`. All time integrals use the actual Lebesgue restriction `window T = volume.restrict (Ioc 0 T)` with0<=T; no abstract reference measure or inferred pathwise convergence is substituted. Reuse of `DiagonalAmbientNullity.ae_off_diagonal` proves the product-window diagonal is null. The finite-mollifier covariance on that diagonal is retained unchanged; it is not assigned zero to manufacture a bound.

With K_nm from1084 and the actual continuous IBM clock Y, define

`C_nm(s,t) = E_Y[K_nm(|Y_s|,|Y_t|)]`,

`S_nm(s,t) = E_Y[sign(Y_s) sign(Y_t) K_nm(|Y_s|,|Y_t|)]`,

`J_nm(s,t) = min(s,t) S_nm(s,t)`.

The new exact uniform result is `signedEnergyKernel_integral_norm_bound`:

`integral_(0,T]^2 |J_nm(s,t)| ds dt <= 8 / sqrt(2*pi) * T^2 * sqrt(T)`.

It holds for every n,m, including different mollifier widths, and T=0. Actual joint measurability, fixed-width integrability, reflection-sign norm domination, product-window nullity and the required two-time/time-square integration are proved. `signedCovariance_coefficient_formula` identifies the signed integrand with the existing `tripleCoefficient ... 1` inner product, and `signedEnergyKernel_time_pairing` identifies min(s,t) with the verified Brownian time-vector Hilbert pairing. Consequently these are the actual signed source-column/clock-representer covariance expressions for the proposed derivative, rather than a generic positive surrogate. The definition does NOT assert that any observable belongs to the closed derivative graph.

The positive bounds established along the way are `integral C_nm <= 8*peak(1)*T*sqrt(T)` and `integral min(s,t) C_nm <= 8*peak(1)*T^2*sqrt(T)`, where peak(1)=1/sqrt(2*pi). The singular time kernel is treated by an integrable one-sided cutoff of x^(-1/2), translation/reflection invariance of actual Lebesgue measure and a two-sided row bound4*sqrt(T). This is a non-sharp bound with the correct T^(5/2) scaling for the weighted energy. Existing `BrownianClockWeightedEnergy.sigma_measurable`, the actual sign field and the old diagonal-nullity theorem are reused. A local elaborator irreducibility annotation on the already constructed clock prevents expensive unfolding; it changes no mathematical definition, hypothesis or axiom.

Source recheck: selectively reread cached primary PDF pages12,22–23 in `tmp/pdfs/stardust-ibm-1046/pages.json`. Open problem5.4 defines the MAXIMAL pullback core C_Z={F in L2(F_Z): iF in Dom(D_X) intersection Dom(D_Y)}, not merely a finite point-cylinder class. Thus genuine time-averaged IBM observables, if shown to have BOTH derivative domains, are a legitimate route. The manuscript's proposed scenery-domain rationale for nondensity remains contradicted by1046, while joint clock-domain membership and L2(F_Z) density remain open. Reuse-audit clarification:1074 formally verifies the source-zero clock family (`IBMSchwartzSourceZeroJoint/Tails`), and1075 the nonlinear source derivative/terminal candidate (`IBMSchwartzSourceDerivative`, `IBMFullSchwartzTerminal`); references in earlier notes to a1074/1075 time-average route are not citations of a verified time-average clock graph theorem.

Related kernel investigation, NOT a Lean theorem: folding the two-time Gaussian density with reflection signs suggests a Dirichlet half-line heat kernel difference, rather than the unsigned reflected-kernel sum. For0<s<t, a candidate off-diagonal unmollified limit for S_nm is

`g_(t-s)(0) - g_(t+3*s)(0)`, with g_v the centered Gaussian density of variance v.

Three one-dimensional diagonal-density quadratures agree with this candidate to floating-point roundoff, and Gaussian spatial-mollifier tests at overlap variances0.1,0.01,0.001 approach it. An independent direct two-dimensional integral in the original independent clock normals at(s,t)=(1,2), overlap variance0.01 gives0.21915350,0.21889687,0.21883269 on400,800,1600-panel grids, approaching the folded-reduction value0.21881130. These are diagnostics with truncated integration and no rigorous error bound. They use GAUSSIAN mollifiers, not the repository's compact bumps, and do not prove a limit, a Dirichlet semigroup identification, or Cauchy convergence for the actual family. Evidence is retained in `.lake/stardust-1085-dirichlet-kernel-tests.json`.

Exact remaining obligations: construct the actual fixed-n time-average clock derivative graph and identify its Hilbert energy with this covariance expression; prove strong convergence of the actual observables; then use a verified bounded-gradient/closed-adjoint criterion or prove convergence of the cross energies. A uniform bound alone is not strong gradient convergence or derivative-domain membership. The Dirichlet candidate may help the latter route, but its reflection identity and off-diagonal approximate-identity limit for the actual compact mollifiers must be proved first. Bounded smooth functions of genuine averages and L2(F_Z) density remain separate; IBM averages are not Gaussian observation vectors. `InfiniteGaussianProjectionConvergence.cylindricalDivergence_adjoint_eq_closedDerivative` is an existing exact weak-gradient graph bridge. No new joint-domain or F3 density conclusion, global F1 summation, or IBM campaign freeze is asserted. F2 and all earlier verified constructions are preserved.

Verification: full `lake build` passed5676 jobs. The root-wide transitive axiom audit passed30495 safe Foundation declarations, allowing only `propext`, `Classical.choice`, `Quot.sound`. All42 new public declarations/instance types were inspected. No sorry, admit, new axiom or hidden domain assumption was introduced. All107 archive manuscript hashes and43 Incoming files/42 distinct hashes match saved baselines. ResearchSources, pinned dependencies, unrelated drafts, goal state and campaign order are unchanged. This is a verified supporting F3 energy checkpoint, with the central graph and density claims still explicitly open.


## Verified discovery1086 — genuine Bochner-L2 clock-gradient candidates and exact mixed-energy identities

Continued from auditedec6758adb96bbe687ef7410da8c57f4e54412c17 (1085). The previous goal turn made substantive progress. Terminal proof/research checks on2026-10-19 include01:31:43,01:33:54,01:36:02,01:38:36,01:40:30,01:43:27,01:45:14 and01:46:21 America/New_York. IBM remains immediate. A(4), A(2), the final full multichannel campaign and October31 stop retain their existing gates.

New root-imported module: `Foundation/IBMClockAverageCandidate.lean`. The signed covariance bounds from1085 are now connected to independently constructed Hilbert-space objects. The target is the genuine nested space `Lp GaussianVectorL2 2 gaussianProduct`: outer probability is the actual clock factor, inner GaussianVectorL2 is source-Gaussian L2 valued in the clock coefficient Hilbert space. The source and clock factors are separate copies of the existing Gaussian product law. No signed pseudoprocess pseudo-L2 or supplied covariance space is substituted.

At time t, the actual source-Gaussian vector section is

`sign(Y_t) * X'_n(|Y_t|) * h_t`,

where h_t is the existing embedded Brownian time vector, X'_n is the first spatial-derivative scenery column, and multiplication by h_t is the existing scalarTensor map. `sourceColumn_actual_ae`, `sectionField_actual_ae` and `field_actual_ae` identify the sections with `IBMDyadicExtension.field n 1` and the actual constructed `mollifiedValue n 1`, first at each clock sample and then in nested AE form. This is equality of the actual L2 source sections; no new pathwise differentiation theorem for separately chosen modifications is asserted.

The construction proves joint strong measurability and fixed-time Bochner-L2 membership without caller-supplied domain, measurability or integrability assumptions. Existing `ProductL2Sections.sectionL2_stronglyMeasurable`, actual physical-column covariance, scalarTensor pairing and the Brownian time-vector geometry are reused. The required fixed-width source-column bound is derived from the existing overlap bound, not imposed as a new process hypothesis. A continuous bilinear lift is proved equal to scalarTensor using the existing Mathlib compLpL2 machinery; the genuine tensor norm factors into the scalar and direction norms.

`field_inner` proves the exact Hilbert inner product of two time sections equals1085's signedEnergyKernel J_nm(s,t). The time-averaged object `average n T = integral_(0,T] field n t dt` is an actual integrable Target-valued Bochner integral for every T>=0. `average_ae` is a justified OUTER-CLOCK representative formula for an integral valued in SOURCE vector-L2; its Fubini hypotheses and uniform square-integrable clock majorant are discharged using `BochnerL2Fubini.integral_eq_of_slices`. This formula is not silently strengthened to a pointwise-in-both-factors integral identity.

The substantive new exact identities are

`inner(average n T, average m T) = integral_(0,T]^2 J_nm(s,t) ds dt`,

`norm(average n T)^2 = integral J_nn`,

`norm(average n T - average m T)^2 = integral (J_nn + J_mm - 2 J_nm)`.

Thus1085's bound now controls the norm of a genuine constructed object:

`norm(average n T)^2 <= 8/sqrt(2*pi) * T^2*sqrt(T)`, uniformly in n.

The mixed-width distance formula is an exact potential route to a strong Cauchy proof once actual cross-energy convergence is established. It does not assume or establish that convergence. Integrability is proved before the two nested Hilbert inner-product/time interchanges; none is a formal expectation-level replacement for the Hilbert norm identity.

Exact remaining gap: these are still CANDIDATE clock derivatives. No pair consisting of a scalar IBM time average and this field has yet been placed in the actual closed D_Y graph. The scalar time averages' strong L2 convergence and intrinsic F_Z realization, the fixed-n reflected Gaussian composition/weak IBP theorem, the factor-order transport to the fibre-lifted clock derivative, and a valid limiting closed-domain argument remain. The current nested target orders clock probability outside source probability; the canonical source/clock L2 interchange must be proved or reused when matching `BochnerClosedOperator.lift gaussianProduct closedCylindricalDerivative`. Abstract equality of underlying coefficient spaces cannot replace that factor identification.

A precise existing alternative to demanding strong derivative convergence was located: Mathlib `LinearPMap.mem_adjoint_domain_iff` characterizes the actual adjoint domain by continuity of its inner-product functional on the original domain. Once FIXED-N graph membership and strong scalar convergence are established, the uniform bound could yield continuity of the limiting divergence-test functional, followed by the verified `InfiniteGaussianProjectionConvergence.cylindricalDivergence_adjoint_eq_closedDerivative` or the Hilbert bidual identification. The bound on a candidate alone does not supply the necessary IBP. No new generic adjoint theory was built. The Dirichlet signed folded-kernel/compact-mollifier convergence idea from1085 remains an unproved alternative; its numerical Gaussian-mollifier diagnostic is not a theorem.

F3 maximal pullback-core density remains open, as do F1 higher-source common physical topology/global summation. Bounded smooth intrinsic functions and arbitrary-law L2(F_Z) density remain separate from the Gaussian observation polynomial-density theorems. F2 and all earlier verified results remain preserved. No IBM freeze, successor transition or new research campaign is asserted. No manuscript was read wholesale or modified during this proof checkpoint.

Verification: full `lake build` passed5677 jobs. The root-wide transitive axiom audit passed30556 safe Foundation declarations with only `propext`, `Classical.choice`, `Quot.sound`. All38 new public declaration/abbreviation types were inspected, including the nested probability factors, time sign restrictions, representative quantifiers and Bochner-integral domains. No sorry, admit or new axiom was introduced. All107 archived manuscript hashes and43 Incoming files/42 distinct hashes match the saved baselines. Pinned dependencies, ResearchSources, unrelated drafts, goal state and campaign order are unchanged.


## Verified discovery1087 — actual IBM-observable time averages, strong scalar limits and partial source graphs

Continued from audited178c919a1c8a16f59b17668b1cbbb972fafc187b (1086). The intervening queue-confirmation turn was a read-only status response, not mathematical progress. Current worktree and the previous Lean log were revalidated before continuing; the unfinished draft had one representative-identification error, now repaired. Terminal checks on2026-10-19 include02:05:54,02:06:54,02:07:53 and02:08:40 America/New_York. IBM remains immediate; IBM -> A(4) -> A(2) -> final full multichannel pseudoprocess attempt and the October31 stopping date are unchanged. No successor gate is released.

New root-imported module: `Foundation/IBMTimeAveragedObservable.lean`. This constructs the scalar side missing from1086. The existing random mollified scenery classes are continuous in physical time in the genuine outer-clock/inner-source Bochner L2 space. The proof derives a global Hilbert-valued spatial Lipschitz bound from the actual mollified spatial derivative, then uses the existing Brownian L2 curve and Mathlib Lipschitz composition. The existing uniform square-root mollifier error proves uniform convergence to the unmollified random source classes, hence their time continuity. Thus both curves are integrable on every finite window (0,T]; negative windows are empty. No new stochastic process or assumed integrability is introduced.

The actual Bochner integrals `mollifiedAverage n T` and `sourceAverage T` satisfy, for T>=0,

`norm(mollifiedAverage n T - sourceAverage T) <= T * sqrt((bump n).rOut)`.

`average_tendsto` proves strong L2 convergence. The native joint realization is built using the existing product-L2 curry equivalence followed by the actual source/clock swap, giving the original (source,clock) order. `joint_point_actual_ae` identifies every fixed-time realized class with the actual constructed continuous IBM coordinate under the actual joint law. `jointRealization_ae_of_sections` explicitly proves the necessary AE product-section identification and measure-preserving swap; equal underlying Gaussian factor types are not treated as a substitute for factor order.

`IntrinsicSpace` is the existing L2 space measurable for the sigma algebra generated by ALL actual IBM coordinates, using `IBMConditionalObservable.observableSigma` and its existing closedness theorem. Each realized point lies in it by coordinate measurability. Its own continuous curve and Bochner average are constructed. `nativeAverage_eq_intrinsicAverage` proves that this intrinsic average equals the native realization of `sourceAverage`, by justified continuous-linear-map interchange with the integrals. Consequently `nativeAverage_intrinsic` proves genuine F_Z measurability. This neither substitutes Gaussian polynomial-density results for the non-Gaussian observation law nor claims full F3 core density. `nativeAverage_tendsto` and `nativeAverage_error` transfer the strong scalar limit and rate to the actual native joint space.

The existing scenery first-chaos projection fixes the random point classes, including the actual mollified classes. Its bounded first-chaos gradient and the verified projected closed-derivative graph, lifted fibrewise, show that both scalar averages belong to the actual PARTIAL SOURCE derivative graph. `source_graph_tendsto` proves convergence of both coordinates of these source-derivative graphs in the genuine product norm. Here the outside clock variable is held as a parameter and differentiation is in the inside scenery factor. The target type is not evidence of a clock derivative: the separate clock candidate from1086 remains unidentified with D_Y.

`sourceAverage_hasDerivAt` and `nativeAverage_hasDerivAt` prove ordinary real-time L2 differentiation of the averages at every T>0 recovers the corresponding point class. This supplies a concrete coordinate-recovery mechanism for a future density argument. It is ordinary Bochner fundamental calculus, not Malliavin differentiation or a stochastic Ito formula. No full algebra/cylinder density is inferred from this identity alone.

Exact remaining obligations: the literal AE sample-path formula nativeAverage(T)(omega)=integral_0^T ibmValue(t,omega)dt has not been proved here (the class-valued average and its fixed-time representatives have been proved). The fixed-n reflected Gaussian weak chain rule/IBP identifying the clock derivative of the scalar average, the correct vector-valued factor interchange, and the limiting closed-adjoint domain argument remain open. Uniform1086 candidate bounds alone supply no IBP. A promising direct reuse for the missing representative formula is the existing finite-measure L2-to-L1 inclusion and Bochner/Fubini machinery, avoiding an unnecessary path-supremum infrastructure. For the clock graph, reuse existing closed Gaussian cylindrical derivative, divergence adjoint and smooth absolute approximations; source Sobolev membership and ordinary time differentiability do not discharge this obligation. Full F3 intrinsic smooth-function/core density and F1 higher-source common physical topology/global summation remain open; F2 and all prior verified results are preserved. No IBM freeze or campaign transition is asserted.

Verification: the direct module check and full `lake build` passed (5678 jobs). Root-wide transitive axiom audit passed30618 safe Foundation declarations using only `propext`, `Classical.choice`, `Quot.sound`. All39 new public theorem/definition/abbreviation types were printed and inspected, including probability-factor order, intrinsic sigma algebra, source-graph identification and time restrictions. No sorry/admit or new axiom was introduced. All107 archived manuscript hashes and43 Incoming files/42 distinct hashes match the saved baselines. ResearchSources, pinned dependencies, unrelated drafts and goal state are unchanged. This checkpoint adds no claims about RH, A(4), A(2) or completion of the IBM objectives.


## Verified discovery1088 — reflected Gaussian Sobolev graph and actual mollified-scenery scalar tests

Continued from auditedf5ced567e8a9779702712bb4d1467b285c0016aa (1087); the previous goal turn made substantive verified progress. Terminal proof breaks on2026-10-19 include02:10:48,02:11:59,02:14:00,02:14:51,02:16:02,02:17:06,02:17:57,02:19:09,02:19:56 and02:20:18 America/New_York. IBM F1-F3 remains the immediate campaign. The IBM -> A(4) -> A(2) -> final full multichannel gates and October31 stopping date are preserved. No manuscript is modified or introduced as an axiom.

New root-imported module: `Foundation/IBMReflectedGaussianSobolev.lean`. This addresses the reflected Gaussian weak-chain-rule gap directly. The derivative throughout this module is the existing ONE-DIMENSIONAL `GaussianCore.closedDerivative`, namely the graph closure of the actual Gaussian polynomial derivative, not an assigned classical differential expression.

`stein_of_integrable` proves standard Gaussian Stein IBP for an everywhere genuine classical derivative with three actual integrability premises (f, f', x*f). Weighted Lebesgue integrability is discharged from the existing Gaussian density bridge; whole-line improper IBP supplies boundary decay from integrability. `polynomial_test_ibp` then proves, for f,h in Gaussian L2 and h the everywhere derivative of f,

`integral h(x)*q(x) dgamma = integral f(x)*(x*q(x)-q'(x)) dgamma`

for EVERY polynomial q. All weighted products are genuinely integrable by L2 Holder and existing Gaussian polynomial moments, including x*q. There is no unproved assertion that multiplication by x is bounded on L2. `classical_closed_graph` uses this test identity and the previously verified Hermite adjoint identification to put (f,h) in the actual closed derivative graph. This is an analytic-to-operator bridge with precise functional domains, rather than a second definition of a derivative.

`reflected_closed_graph` proves that, when f'=g is continuous and globally bounded, the actual reflected function f(|x|) belongs to that closed graph with derivative g(|x|)*signum(x). Both L2 memberships are conclusions. The value need not be bounded: its Gaussian L2 membership follows from the derived global Lipschitz bound and existing Gaussian coordinate moments. The proof reuses `SmoothAbsoluteApproximation.radius`, its actual derivative `slope`, the existing `RealSteklovApprox.width`, `BrownianTanakaApproximation.slope_tendsto_sign`, and `FiniteMeasureL2Dominated.toLp_tendsto_of_constant_bound`. For the smooth approximants f(radius(width_n,x)), both graph coordinates converge STRONGLY in Gaussian L2: the value error is bounded by K*width_n and the derivative converges by the existing finite-measure dominated theorem with uniform bound K. The already verified graph closedness passes this actual pair to the limit. No differentiability of |x| at zero is assumed. This is a FIRST Sobolev derivative theorem; it asserts neither a second derivative without a boundary term nor removal of the Tanaka/local-time correction.

The concrete application `mollified_pair_reflected_graph n V a` takes ANY actual source-Gaussian L2 test V and ANY real scale a. Its value is

`x -> inner(V, wholeLineScenery(kernel_n, a*|x|))`

and its actual one-dimensional closed derivative is

`x -> a * inner(V, sourceColumn(n,a*|x|)) * signum(x)`.

The scale factor a and sign factor are derived from actual classical differentiation, not postulated. Continuity and boundedness of the derivative are discharged using1086's actual source-column continuity/bound and1087's actual mollified spatial derivative. Thus this is a verified scalar test of the genuine Hilbert-valued scenery curve at a reflected Gaussian argument, not a polynomial-only replacement for that curve. Positive a=sqrt(t) is the normalized Gaussian-clock scale of interest; zero and negative scales are also covered by the analytic statement. The theorem does not itself transport this graph to the actual countable Gaussian clock probability space or assert an AE full joint-process formula.

Exact next connection: lift the one-dimensional polynomial-closure graph along a normalized genuine first-chaos observation. Existing `InfiniteGaussian.firstChaos_law` proves its actual measure map; `InfiniteGaussian.isonormalCylinderL2_mem_core` and `polynomialDerivative_on_cylinder` in `Foundation/InfiniteGaussianDerivative.lean` supply the arbitrary Hilbert-direction polynomial graph. The existing one-dimensional Hermite graph approximations should allow continuous pullback of both coordinates, with rank-one tensor direction, followed by the existing closed-graph limit. This is more direct than constructing a new general Malliavin calculus or assuming the law of one coordinate determines the ambient derivative. The zero clock direction/time must be handled separately or by a valid degenerate statement. The actual source/clock vector factor swap and Hilbert-valued/Bochner lifting still require proof.

Remaining central obligations: the full fixed-n clock graph for scalar IBM time averages and identification with1086's candidate, their limiting closed-adjoint domain argument, and full F3 intrinsic core density are not yet proved. The previous scalar and source graph limits remain intact. Native sample-path integral representative equality remains open. F1 higher-source common physical topology and uniform global summation remain open; F2 is preserved. Scalar reflected graph tests do not release any of those gates and do not complete IBM. No successor transition or new campaign is asserted.

Verification: direct module check passed; full `lake build` passed5679 jobs. Root-wide transitive axiom audit passed30628 safe Foundation declarations with only `propext`, `Classical.choice`, `Quot.sound`. All9 public theorem types were printed and inspected, including the standard Gaussian domain, existential MemLp witnesses, exact source/clock distinction and the scale/sign factors. No sorry, admit or new axiom was introduced. All107 archived manuscript hashes and43 Incoming files/42 distinct hashes match saved baselines. Pinned dependencies, ResearchSources, unrelated drafts, goal state and campaign order are unchanged.


## Verified discovery1089 — actual clock-observation derivative graphs for reflected mollified scenery tests

Continued from audited1a0304d8c8b0400d5951a069bb61ffe9f6b21c81 (1088). The previous goal turn made substantive verified progress. Worktree, saved checkpoint and clock were revalidated. Terminal proof breaks on2026-10-19 include02:23:03,02:25:03,02:25:39,02:26:28,02:27:35,02:28:28,02:29:29,02:30:19,02:30:36,02:31:21,02:31:41 and02:32:14 America/New_York. IBM remains immediate; the IBM -> A(4) -> A(2) -> final full multichannel gates and October31 stopping date remain unchanged.

New root-imported module: `Foundation/IBMClockObservationGraph.lean`. This closes the specific one-dimensional-to-countable-Gaussian transport gap left in1088. For a genuine coefficient direction h of norm1, `observation_measurePreserving` proves that the ACTUAL random variable `firstChaosEmbedding h` maps the constructed Gaussian product to the standard one-dimensional Gaussian law. `pullback` is the existing Mathlib measure-preserving composition linear isometry, with a proved AE representative formula. This is a constructed map of the actual L2 spaces, not a declaration that identically distributed variables have the same derivative.

`pderiv_univariate` proves the exact polynomial embedding derivative identity in one-variable MvPolynomial form. `pullback_polynomial` identifies actual pulled-back polynomial classes with the existing isonormal cylinders. `pullback_polynomial_graph` then proves the actual derivative intertwining using the existing arbitrary Hilbert-direction polynomial derivative theorem. The direction is scalarTensor h of the pulled-back scalar derivative. No finite-coordinate assumption on h is made.

The substantive operator result `pullback_closed_graph` transports the ENTIRE existing one-dimensional Gaussian closed derivative graph to `InfiniteGaussian.closedCylindricalDerivative`:

`(f,g) in D_1.graph => (pullback_h f, scalarTensor(h,pullback_h g)) in D_clock.graph`.

It reuses the already verified one-dimensional Hermite graph approximation of both coordinates. Polynomial graph intertwining applies to every approximant; continuous pullback and1086's continuous tensor map pass both coordinates to their limits; existing closedness of the actual countable-Gaussian derivative closes the graph. Thus the conclusion is stronger than a core-only identity and does not assume a new chain rule, graph density or abstract operator equivalence.

`reflected_observation_graph` combines this transport with1088's reflected Gaussian theorem. For every actual source-Gaussian L2 test V, every mollifier n and every real scale a, it constructs actual ambient CLOCK Gaussian classes F,G with their genuine closed graph and explicit AE formulas. `reflected_direction_graph` removes normalization for any nonzero original direction h. The proof uses actual first-chaos linearity and AE representatives to derive norm(h)*abs(W(h/norm(h)))=abs(W(h)) and equality of signs; the scale from the scalar derivative cancels against the normalized direction. The resulting derivative direction is h itself.

`reflected_clock_graph` specializes to the embedded Brownian time vector for every t>0, deriving nondegeneracy from its verified norm square and explicitly identifying the first-chaos coordinate with the existing `GaussianTimeProcess.process t`. Finally `reflected_actual_clock_graph` transfers the representative formulas to the ACTUAL constructed continuous Brownian clock `IBMConstructedSources.clockPath`, using the verified fixed-time AE coordinate identity. Its value and derivative are

`F(omega_Y) = inner(V, X_n(abs(Y_t)))`,

`G(omega_Y) = [inner(V, X'_n(abs(Y_t))) * signum(Y_t)] * h_t`.

Here X_n is the actual Hilbert-valued mollified scenery curve, X'_n is1086's actual derivative source column, and h_t is the original embedded Brownian time vector. The equality is in actual clock L2 and the ACTUAL closed clock derivative graph. All domain memberships are constructed. V remains a source-Hilbert test, while omega_Y is the clock sample. The public clock theorems require positive time; no degenerate-time normalization is used. Time0 can be handled separately by the existing constant-graph theorem when needed, or excluded only with a justified null-time argument during integration.

Exact remaining step: these scalar-test clock graphs must still be assembled into the full joint source/clock Bochner graph. Having the graph for every source-Hilbert V is not silently promoted to an AE source-sample fibre graph. A direct next route is finite orthonormal source projections: each scalar coordinate result gives a separated-variable lifted graph via existing `BochnerClosedOperator.tensor_graph`; finite sums stay in that graph; actual product-L2 curry/swap identities and strong convergence of BOTH projected coordinates must identify the limiting scalar field and1086 candidate. Existing `ProductL2Curry`, `ProductL2Flip`, `BochnerClosedOperator.lift_isClosed` and `BochnerL2Approximation.tendsto_of_dominated` should supply this without a new stochastic calculus. Factor order matters:1087 scalar averages and1086 candidates have the clock factor outside, while the fibrewise clock derivative expects the source factor outside.

The full fixed-n time-average clock graph and candidate identification, justified time integration, limiting closed-adjoint domain argument, literal sample-path time-integral representative equality, and full F3 intrinsic core density remain open. The existing uniform candidate energy bound and strong scalar limit do not by themselves supply the missing joint IBP. F1 higher-source common physical topology/global summation remains open; F2 and all prior verified work are preserved. This first Sobolev graph theorem makes no claim about removing Tanaka/local-time boundary corrections. No IBM freeze or successor transition is asserted.

Verification: direct module check passed; full `lake build` passed5680 jobs. Root-wide transitive axiom audit passed30649 safe Foundation declarations using only `propext`, `Classical.choice`, `Quot.sound`. All11 new public types were printed and inspected, including norm1/nonzero/positive-time domains, actual measure maps, pre-existing operator graphs, probability-factor roles and AE representative quantifiers. No sorry, admit or new axiom was introduced. All107 archive manuscript hashes and43 Incoming files/42 distinct hashes match saved baselines. ResearchSources, pinned dependencies, unrelated drafts, goal state and campaign order are unchanged.


## Verified discovery1090 — full joint mollified-point clock graph and exact candidate-energy identification

Continued from audited67fdb058a64445f82a35abb2d7ba19700207f7bd (1089); the previous goal turn made substantive verified progress. Worktree and saved checkpoint were revalidated. Terminal checks on2026-10-19 include02:34:51,02:36:38,02:38:38,02:39:26,02:40:14,02:41:07,02:42:04,02:44:13,02:45:27,02:46:08,02:47:03,02:47:43,02:48:07,02:48:20,02:48:37 and02:49:01 America/New_York. IBM remains immediate; IBM -> A(4) -> A(2) -> final full multichannel and the October31 stopping date retain their existing gates.

New root-imported module: `Foundation/IBMFirstSourceClockGraph.lean`. The main advance closes the scalar-test-to-joint-clock-graph gap for every fixed mollifier at every positive observation time. Both the actual Hilbert-valued mollified scenery and its spatial derivative are in the FIRST SOURCE chaos. This permits direct reuse of the existing Gaussian coordinate series rather than construction of a new arbitrary Hilbert basis or a new general Malliavin calculus.

`projection N` is the actual finite-rank continuous linear source map sum_(i<N) inner(coordinateL2_i,f)*coordinateL2_i. Bessel proves it is a contraction on ALL source Gaussian L2. `coordinate_embedding_inner` identifies its coefficients on the genuine first-chaos embedding, and `projection_embedding_tendsto` follows from the existing unconditional first-chaos series. The lifted `projected_tendsto` proves strong Bochner-L2 convergence on actual fields with AE first-source-chaos sections, using the existing dominated-convergence theorem and the derived contraction. `projected_sum` identifies these projections with actual separated source/clock tensors.

The assembly theorem `assembled_graph` proves a precise domain statement. For actual outer-CLOCK/inner-SOURCE fields u,w with first-source-chaos sections, if every genuine source coordinate pairing has the verified CLOCK graph (coordinate_i(u), scalarTensor(h,coordinate_i(w))), then

`(flip(u), gradientMap(h,flip(w))) in (BochnerClosedOperator.lift gaussianProduct closedCylindricalDerivative).graph`.

After `flip`, probability order is SOURCE OUTSIDE, CLOCK INSIDE, exactly the order of that fibrewise CLOCK derivative. The existing scalar product-L2 flip is an actual isometry and swaps separated tensors. Existing `tensor_graph` puts each finite source-coordinate sum into the actual lifted graph. Both coordinates converge strongly by the contraction/series proof, flip continuity and the existing continuous tensor map. Existing closedness of the lifted operator then closes the actual graph. The scalar-test premise is not merely reinterpreted as an AE fibre assertion; this limiting argument proves it.

The concrete `signedSourceClass n t` is signum(actual clock Y_t) times1086's sourceColumn n(abs(Y_t)), as an actual source-Gaussian L2 vector at every clock sample. Its strong measurability and Gaussian L2 membership follow from actual clock measurability, source-column continuity and its derived uniform bound. `signedSource` is the actual Bochner class. `signedSource_firstChaos` and `mollified_firstChaos` discharge both first-source-chaos premises from existing coefficient/scenery identities. `coordinate_clock_graph` identifies the actual coordinate classes with1089's existing clock-graph witnesses, using actual toLp, clock-coordinate and tensor AE representatives.

Define `clockGradient n t = gradientMap(h_t, flip(signedSource n t))`. Then `mollified_clock_graph` proves for every n and t>0:

`(flip(randomMollifiedL2 n t), clockGradient n t) in lifted CLOCK graph`.

This is a genuine joint partial clock derivative of the actual defined mollified observable class, with every domain membership proved. It is distinct from the previously verified partial SOURCE graph and from a supplied candidate derivative. No equality of the underlying Gaussian-space types substitutes for the factor interchange. The public point-graph theorem excludes time0; a later time-integral proof must either handle that case with the existing constant graph or explicitly use the null/excluded endpoint of (0,T].

The candidate connection is exact at the level needed for energy estimates. `gradientMap_inner` proves inner(gradientMap(h,u),gradientMap(k,v))=inner(u,v)*inner(h,k). `candidate_eq_gradientMap` identifies1086's outer-clock field with gradientMap(h_t,signedSource n t), without the scalar factor flip. Because the genuine scalar flip preserves inner products, `clockGradient_inner` proves

`inner(clockGradient n t,clockGradient m s) = inner(field n t,field m s)`

for ALL n,m and nonnegative times s,t. `clockGradient_norm` gives the identical point norm. Thus the actual joint clock derivatives have exactly the candidate mixed energies despite their different probability-factor order. No general arbitrary vector-field flip infrastructure was needed. This Gram identity is not silently promoted to an unproved pointwise-in-both-factors vector representative formula.

Exact next obligation: prove time strong measurability and integrability of the actual clockGradient curve, integrate the positive-time pairs in the ACTUAL CLOSED GRAPH, and identify the scalar average with the flipped1087 mollifiedAverage. Joint measurability of signedSourceClass and existing ProductL2Sections.sectionL2 should supply time measurability of signedSource; the existing continuous bilinear compLpL2 lift and direction continuity should supply it for clockGradient. The proved point-norm identity transfers1086's finite-window bound; two justified time-inner-product interchanges should transfer the averaged mixed energies and the existing uniform estimate. Those average graph/domain and uniform actual-gradient statements are NOT yet proved here. Once obtained, the strong1087 scalar limit and the uniform actual-gradient bound can support the existing closed-adjoint-domain route without assuming strong derivative Cauchy convergence.

The unmollified clock domain, literal sample-path time-integral representative equality, full F3 intrinsic smooth-cylinder/core density and F1 higher-source common physical topology/global summation remain open. F2 and all previous verified results are preserved. This first clock-Sobolev result asserts neither removal of Tanaka/local-time corrections nor completion of IBM. No campaign freeze or successor release is asserted.

Verification: direct module check passed; full `lake build` passed5681 jobs. Root-wide transitive axiom audit passed30717 safe Foundation declarations with only `propext`, `Classical.choice`, `Quot.sound`. All29 public declarations/abbreviations were printed and inspected, including factor order, first-source-chaos premises and their actual discharge, positive-time restriction, genuine lifted graph, representative quantifiers and strong L2 topology. No sorry, admit or new axiom was introduced. All107 archived manuscript hashes and43 Incoming files/42 distinct hashes match saved baselines. ResearchSources, pinned dependencies, unrelated drafts, goal state and campaign order are unchanged.


## Verified discovery1091 — genuine unmollified IBM time-integral clock domain, energy bound and sample-path realization

Continued from auditedba63382742b976c34e0503cf2ec9c6acf8db4ba7 (1090); the previous goal turn made substantive verified progress. Saved checkpoint, tracked state and terminal clock were revalidated. Checks on2026-10-19 include02:51:46,02:52:27,02:54:14,02:54:26,02:55:14,02:56:44,02:58:12,02:59:01,03:00:11,03:00:36,03:01:11,03:01:22,03:01:57,03:02:22,03:03:27,03:04:23,03:05:24,03:06:59 and03:07:44 America/New_York. IBM remains immediate; IBM -> A(4) -> A(2) -> final full multichannel and the October31 stop retain their gates.

New root-imported module: `Foundation/IBMClockAverageGraph.lean`. This resolves the previously recorded actual time-integration and unmollified closed-clock-domain obligations for the IBM time averages. The derivative is the existing `BochnerClosedOperator.lift gaussianProduct closedCylindricalDerivative` with SOURCE probability outside and CLOCK probability inside. No assigned candidate is substituted for this operator.

First, `signedSourceClass_jointly_stronglyMeasurable` uses the actual continuous-clock joint measurability, sign measurability and actual spatial derivative-column continuity. `signedSource_time_stronglyMeasurable` identifies the independently chosen per-time toLp classes with the existing sectionL2 construction before concluding time measurability. The existing continuous bilinear compLpL2 lift and the actual Brownian direction continuity give `clockGradient_time_stronglyMeasurable`. Its finite-window integrability is then derived from1090's point-norm equality with1086's field and the already verified C_n*sqrt(T) bound. The real-time toNNReal behavior is explicitly checked; negative times are not silently treated as positive.

Define `averageGradient n T` as the genuine Bochner time integral of1090's actual joint clock derivative. `mollified_average_clock_graph` proves for every n and T>=0:

`(flip(mollifiedAverage n T), averageGradient n T) in actual joint CLOCK graph`.

Both coordinates are proved Bochner integrable before this assertion. The positive-time point graph applies AE on (0,T], so no normalization of a zero Brownian direction or artificial endpoint value is needed. To integrate inside the existing closed graph S, the proof reuses the existing continuous quotient S.mkQL: it kills every AE point pair, its integral commutes with the Bochner integral, and its verified kernel is exactly S. Scalarflip's actual continuous-linear-map integral identity identifies the scalar coordinate with1087's average. No new graph-integration or stochastic-process infrastructure was built.

`averageGradient_inner` proves that ALL mixed inner products of these actual averaged derivatives equal those of1086's averaged candidates. It uses two justified Hilbert-inner/time interchanges and1090's exact point mixed-energy identity. Consequently `averageGradient_norm` and `averageGradient_uniform_energy` give

`norm(averageGradient n T)^2 <= 8*peak(1)*T^2*sqrt(T)`, uniformly in n.

The old candidate estimate now controls ACTUAL closed-clock derivatives. It does not merely bound an independently chosen field whose graph membership is open.

The limiting argument is also now verified. `clock_domain_of_bounded_graph_limit` proves for this actual lifted clock operator that strong convergence of scalar inputs and a uniform norm bound on their ACTUAL derivative values force the limit into its domain, with the same derivative norm bound. For each actual adjoint-domain test y, formal adjointness gives inner(u_n,D_Y* y)=inner(v_n,y); strong scalar convergence passes the bounded functional to the limit. The existing bounded-linear-map construction establishes actual bidual-domain membership, and the already verified `HilbertAdjointDomainDensity.closed_adjoint_dense` and `closed_bidual` identify that bidual with the original closed operator. Density of the actual adjoint domain then proves the canonical derivative norm bound. No weak subsequence, strong derivative Cauchy assumption, or new Riesz/adjoint theory is postulated.

Applying this to the actual mollified averages,1087's strong scalar limit, and the uniform actual-gradient estimate proves `source_average_clock_domain` and `source_average_clock_graph`: the UNMOLLIFIED scalar time average genuinely belongs to the joint partial CLOCK domain, and its canonical derivative obeys the same energy estimate. `nativeAverage_clock_representation` explicitly identifies currying1087's native(source,clock) IBM-observable class with the factor-flipped scalar average. `nativeAverage_clock_domain` transfers the domain and norm theorem to that actual native object. Combined with1087's separately verified partial SOURCE graph, these are genuine nontrivial intrinsically IBM-observable time averages having both partial regularities in their correct probability-factor representations. This does not assert density of their nonlinear algebra or membership of every point observation.

The remaining sample-path realization gap is closed by direct theorem reuse. The already verified `BochnerL2RepresentativeFubini.integral_coeFn_ae` supplies scalar representative Fubini from integrable L2 sections under finite measures, without a uniform pointwise majorant. Using1087's actual native fixed-time coordinate equality and the constructed IBM joint measurability, `nativeAverage_path_integral_ae` proves

`nativeAverage(T)(omega_X,omega_Y) = integral_(0,T] actualIBMvalue(t,omega_X,omega_Y) dt`,

AE under the ACTUAL joint source/clock probability law. This identity holds for every real T (negative windows are empty). The native object was already proved measurable for the sigma algebra generated by the actual IBM process; it is not a Gaussian observation surrogate. No new path-supremum theory or independently supplied column L2 class is needed. The full build was rerun after this final representative theorem was added.

Exact remaining obligations: F3 density of the maximal intrinsic IBM pullback/intersection core is still open. Having these intrinsic averages in both partial domains, and ordinary-time coordinate recovery from1087, does not by itself prove closure under bounded smooth functions of finite average families or arbitrary-law observable L2 density. Gaussian-generated polynomial-density results cannot be applied to the non-Gaussian IBM observation law. The sufficient observable-projection invariance criterion and the exact annihilator criterion already in the library also require actual hypotheses not yet discharged. Strong convergence or a complete explicit stochastic limit formula for the averaged derivative sequence is not proved here; the canonical limiting derivative and its norm bound are proved without needing that stronger claim. F1 higher-source common physical topology/global summation remains open; F2 and all earlier results are preserved. No complete IBM Ito-Tanaka theorem, intrinsic adjoint, campaign freeze or successor release is asserted, and no Tanaka/local-time boundary correction is removed.

Verification: final direct module check passed; final full `lake build` passed5682 jobs. Root-wide transitive axiom audit passed30742 safe Foundation declarations with only `propext`, `Classical.choice`, `Quot.sound`. All18 public declarations/abbreviations were printed and inspected, including actual operator identity, time-domain restrictions, strong scalar/uniform actual-derivative premises, native factor order, canonical derivative bounds and AE sample-path identity. No sorry, admit or new axiom was introduced. All107 archived manuscript hashes and43 Incoming files/42 distinct hashes match saved baselines. ResearchSources, pinned dependencies, unrelated drafts, goal state and campaign order are unchanged.


## Verified discovery1092 — analytic finite Gaussian weak gradients and bounded nonlinear cylinder chain rule for the F3 route

Continued from audited55254da75bd1e5905880b687f7997c7589e6e5f4 (1091); the previous goal turn made substantive verified progress, closing actual unmollified time-integral clock-domain and sample-path realization obligations. Those results remain preserved. Saved checkpoint and tracked state were revalidated. Terminal checks on2026-10-19 include03:10:06,03:10:39,03:11:02,03:11:25,03:11:37,03:12:26,03:13:05,03:13:27,03:15:06,03:15:16,03:16:25,03:16:41,03:17:34,03:18:31,03:18:43,03:19:21,03:20:31,03:22:29,03:23:56 and03:24:01 America/New_York. IBM remains immediate; the IBM -> A(4) -> A(2) -> final full multichannel gates and October31 stop are unchanged.

The theorem-level reuse audit confirmed that existing polynomial and spatial/time chain rules do not yet prove bounded nonlinear closure of the actual Gaussian closed Sobolev domain. The next F3 route therefore needs an analytic bridge into the existing operator graphs, followed by a genuine closed-domain limit. New root-imported module: `Foundation/GaussianAnalyticCoordinateIBP.lean`. It constructs the finite-dimensional analytic bridge without a new derivative definition or unrelated stochastic foundation.

`coordinate_insert_hasDerivAt` and `polynomial_insert_hasDerivAt` prove actual coordinate-fibre differentiation, including the exact multivariate polynomial partial derivative. For the independent Gaussian product in positive dimension Fin(n+1), `coordinate_stein_integrable` proves Gaussian Stein IBP for an arbitrary actual coordinate derivative when f, its derivative h, and f*x_i are genuinely integrable. It uses the existing measure-preserving piFinSuccAbove coordinate split, existing product Fubini and AE slice integrability, and1088's verified one-dimensional `stein_of_integrable`. Neither a Stein identity nor a conditional-law hypothesis is supplied by the caller.

`coordinate_test_ibp` derives for every polynomial q:

`integral h(z)*q(z) dgamma_product = integral f(z)*(z_i*q(z)-partial_i q(z)) dgamma_product`.

Its functional domain is f,h in actual finite Gaussian L2, with h the everywhere genuine i-th coordinate-fibre derivative. ALL products are proved integrable from Holder and existing multivariate Gaussian polynomial moments, including the z_i*q term. Multiplication by a coordinate is not assumed bounded on L2. Scalar polynomial Hilbert pairings are explicitly identified with these actual integrals.

`classical_closed_gradient` then proves that a Gaussian-L2 function and Euclidean-valued Gaussian-L2 field of its actual coordinate derivatives belong to the EXISTING `FiniteGaussian.closedGradient` graph. The proof tests against every genuine polynomial divergence field and reuses the already verified finite Hermite adjoint identification `closedGradient_eq_divergence_adjoint`. It does not stipulate a weak derivative graph, impose the conclusion as a domain premise, or replace vector L2 by coordinatewise expectations.

The concrete nonlinear result `bounded_polynomial_chain_graph` proves: for any finite Gaussian polynomial P and a bounded function phi with actual continuous bounded derivative phi', the classes of

`phi(P(z))` and `phi'(P(z))*gradient(P)(z)`

belong to the actual finite Gaussian closed-gradient graph. Both Gaussian-L2 memberships are CONCLUSIONS. Value membership follows from the actual bound; the actual derivative field is an L-infinity scalar multiplier of the existing polynomial Euclidean gradient, so its L2 domain is derived. The coordinate chain derivative is verified analytically before applying the preceding weak-gradient bridge. This provides a genuine bounded nonlinear cylinder calculus, rather than a polynomial-only chain identity or a formal gradient expression.

Scope and next exact connections: the public analytic theorems are for Fin(n+1), so positive finite dimension is explicit; the zero-dimensional constant case has not been silently normalized. Extension from polynomial inputs to arbitrary closed Sobolev inputs, transport to the countable Gaussian product, fibrewise application to the actual IBM averages, bounded finite-family nonlinear closure/algebra, and intrinsic non-Gaussian observable L2 density remain unproved. This checkpoint is a supporting F3 construction and does not declare F3 solved.

The reuse audit found a stronger existing transport route than rebuilding finite-coordinate laws: `InfiniteGaussianRepresentation.finiteGaussianPoint`, `finiteGaussianPoint_coordinate`, `finiteGaussianPoint_law`, `isonormalCylinder_finiteGaussianPoint`, and `isonormalCylinderGradient_finiteGaussianPoint` already construct finite Hilbert Gaussian realizations and actual coordinate/gradient AE transport for isometric inclusions. The representation-independence proof already forms the finite span of arbitrary, possibly dependent, coefficient directions. `GaussianOrthonormalPolynomialLaw.orthonormal_firstChaosFamily_law` and `basis_firstChaosFamily_law` already prove the actual independent product law for finite orthonormal observations, with source embeddings. These are precise candidates for transporting the new analytic closed graph, with existing finite Hermite graph approximations and1089's one-dimensional pullback as a prototype. Their mere availability is not counted as a proved nonlinear infinite-dimensional chain rule.

A direct next limit route is to approximate in BOTH coordinates of the actual Gaussian derivative graph, compose scalar inputs using the existing Lipschitz compLp machinery, and prove strong convergence of phi'(F_n)*D(F_n) by a bounded-multiplier estimate plus dominated convergence on an AE-convergent scalar subsequence. The actual finite-to-infinite graph intertwining and multiplier convergence still require verification. Equal laws alone do not identify derivatives, and a linear span of differentiable averages alone does not establish full observable L2 density. Existing observable-projection invariance is only a sufficient criterion and remains unproved for IBM; Gaussian observation polynomial-density theorems cannot replace density under the actual non-Gaussian IBM observation law.

F1 common physical topology/global higher-source summation and full F3 maximal intrinsic pullback/intersection-core density remain open. F2 and1091's genuine time-integral domains, energy bounds and actual sample-path identity remain preserved. No intrinsic adjoint, complete IBM Ito-Tanaka theorem, campaign freeze or successor transition is asserted. No new manuscript was read wholesale or changed during this proof checkpoint.

Verification: direct module check passed; full `lake build` passed5683 jobs. Root-wide transitive axiom audit passed30750 safe Foundation declarations with only `propext`, `Classical.choice`, `Quot.sound`. All7 public theorem types were printed and inspected, including positive dimension, actual coordinate derivatives, exact global integrability/L2 domains, Euclidean gradient, existing closed operator and bounded nonlinear hypotheses. No sorry, admit or new axiom was introduced. All107 archive manuscript hashes and43 Incoming files/42 distinct hashes match saved baselines. ResearchSources, pinned dependencies, unrelated drafts, goal state and campaign order are unchanged.


## Verified discovery1093 — finite Gaussian closed-gradient transport and analytic chain calculus on the full cylindrical core

Continued from audited commit78d251367f043172b39f71848dbb9678da86a8dc (1092). The intervening queue-confirmation turn was read-only and made no mathematical progress. On resumption the previous proof session handle was missing; its saved log contained only warnings. The current source was therefore revalidated by a fresh full root build, not assumed verified from a stale handle. Terminal proof/checkpoint readings on2026-10-19 include03:37:32,03:38:35 and03:39:06 America/New_York. IBM remains immediate. IBM -> A(4) -> A(2) -> final full multichannel pseudoprocess attempt and the October31 stopping date retain their gates.

New root-imported module `Foundation/GaussianFiniteGradientTransport.lean` directly reuses1092's actual finite Gaussian analytic chain rule, the existing actual orthonormal first-chaos joint law, Bochner linear-isometry lifting, finite Hermite graph approximation and the existing infinite Gaussian closed cylindrical derivative. It does not introduce a new stochastic source or derivative definition.

`directionIsometry` identifies a finite Euclidean space with its actual orthonormal Hilbert directions. `observations_measurePreserving` proves that their constructed first-chaos observations have the actual finite independent Gaussian product law. The scalar and vector pullbacks are genuine L2 linear isometries, with AE representatives. Their polynomial value and gradient identities intertwine the existing finite and infinite operators.

`closed_gradient_transport` transports the ENTIRE existing finite closed-gradient graph along any finite orthonormal observation family. The proof uses the already verified finite Hermite graph truncations and strong convergence of BOTH graph coordinates under the pullback isometries. Infinite derivative graph closedness supplies the limit. Empty families are included. A caller need not supply a new core-density assumption or covariance inverse.

`bounded_orthonormal_chain_graph` realizes phi(P) and phi'(P) DP in the actual infinite Gaussian closed derivative graph for a finite orthonormal cylinder, with phi bounded and an actual continuous bounded classical derivative. The dimension-zero constant case is proved explicitly. `bounded_cylinder_chain_graph` removes orthonormality entirely: arbitrary dependent, zero or infinite-coordinate-support finite Hilbert directions are realized in their actual finite Hilbert span, its standard orthonormal basis, and the existing `basisPolynomialMap`. Existing finiteGaussianPoint value and gradient identities prove agreement of BOTH actual random fields with the original dependent cylinder. No independence of the original directions is asserted.

`bounded_core_chain_graph` proves the resulting analytic chain rule for EVERY element of the original `polynomialCylindricalDomain`, using its actual polynomial representation and verified representation-independent derivative. Its conclusions supply actual Gaussian L2 function/gradient classes, membership in the original closed derivative graph, and AE identities phi(u) and phi'(u)D0u. Thus this is a genuine nonlinear closed-graph identification on the full polynomial operator core, including dependent observations, not merely a finite-coordinate or expectation-level formula.

Scope: arbitrary CLOSED Sobolev-domain inputs are not yet covered. Extending from the full cylindrical core requires a strong derivative-product limit. A productive next proof is graph approximation u_N -> f, D0u_N -> g, bounded-derivative Lipschitz convergence for phi(u_N), and an AE scalar subsequence plus dominated L2 convergence for phi'(u_N)g. Split phi'(u_N)D0u_N - phi'(f)g into the uniformly bounded multiplier applied to D0u_N-g and the fixed-g multiplier difference. Existing `BochnerL2Approximation.tendsto_of_dominated` and `tendstoInMeasure_of_tendsto_Lp.exists_seq_tendsto_ae` supply the needed analytic tools; avoid creating a separate probability framework. `InfiniteGaussianProjectionConvergence.hilbertDivergence_polynomial_graph_core_sequence` supplies the precise existing sequential graph-closure proof pattern (mem_closure_iff_seq_limit, mem_domain_of_mem_graph, image_iff), reusable for the derivative.

F3 still needs full closed-domain nonlinear chain closure, its correctly ordered source/clock fibre lifts on the actual IBM averages, a genuine nonGaussian intrinsic observable-density argument and intrinsic adjoint identification. The1091 actual unmollified time-average source/clock domains and AE sample-path integral remain proved and must not be reopened as missing. Gaussian-generated linear observation density cannot be substituted for actual IBM observable density. F1 global higher-source physical dual topology and uniform cross-sector summation remain open. F2 retains its fixed concrete normalized bump-family scope. No IBM freeze or successor transition is justified by this milestone. No new manuscript ingestion was needed for this direct supporting proof.

Verification1093: full root `lake build` passed5684 jobs, exit0. Root-wide transitive axiom audit passed30780 safe Foundation constants using only `propext`, `Classical.choice`, `Quot.sound`. All17 new public definition/theorem types were printed and inspected, including orthonormal transport hypotheses, arbitrary dependent-family scope, empty-family coverage, actual L2 representatives and the distinction between polynomial core and full closed domain. No sorry/admit or new axiom. All107 archived manuscript hashes and43 Incoming files/42 distinct hashes match their saved baselines. ResearchSources and dependency pins are unchanged. Evidence: `.lake/stardust-1093-full-build.log`, `.lake/stardust-1093-audit.log`, `.lake/stardust-1093-public-types.json`, `.lake/stardust-1093-archive-check.json`, `.lake/stardust-1093-inventory-check.json`.


## Verified discovery1094 — full closed Gaussian C1 chain rule and nonlinear intrinsic IBM averages in both partial domains

Continued from audited6ce5bdfa776331e567c200664dd5bcf69181febe (1093); the preceding turn made substantive verified progress. Current tracked state, saved checkpoint and system clock were revalidated. Terminal proof checks on2026-10-19 include03:41:21,03:42:39,03:43:50,03:44:44,03:46:05,03:46:24,03:47:11,03:48:33,03:49:04 and03:49:42 America/New_York. IBM remains immediate; IBM -> A(4) -> A(2) -> final full multichannel and the October31 hard stop retain their gates. No manuscript was edited or treated as an axiom.

New root-imported modules: `Foundation/GaussianClosedChainRule.lean` and `Foundation/IBMNonlinearAverageGraph.lean`. The first extends1093's full polynomial cylindrical-core chain rule to EVERY pair(f,g) in the ORIGINAL closed Gaussian derivative graph. The second applies this actual calculus to the constructed intrinsically IBM-observable time averages, respecting both probability-factor orders.

The multiplier construction is an actual coefficient-Hilbert-valued L2 class for a genuinely AE measurable uniformly bounded scalar field times a GaussianVectorL2 input. `multiplier_ae` proves its literal representative and `multiplier_sub_bound` proves the L2 Lipschitz estimate in the vector input. `multiplier_tendsto_fixed` uses the existing dominated-L2 theorem with the actual scalar L2 majorant B*norm(g). `multiplier_tendsto` then proves strong L2 convergence when scalar multipliers converge AE and vector inputs converge strongly. Its split into fixed-g dominated convergence and the uniform estimate B*norm(g_n-g) requires no common pointwise bound on the approximating vector gradients. B>=0 is explicit in these convergence theorems.

`core_graph_sequence` derives actual simultaneous polynomial-core approximations of BOTH graph coordinates from the existing closedCylindricalDerivative_graph closure identity. It does not assume a new core. `bounded_closed_chain_graph` proves: if(f,g) belongs to the existing closed Gaussian derivative graph, phi is globally bounded and has an actual everywhere classical derivative dphi which is continuous and globally bounded, there are actual L2 classes F,G in that SAME graph satisfying F=phi(f) and G=dphi(f)g AE. B>=0 follows from the derivative bound. Bounded derivative gives the Lipschitz scalar-value limit. A scalar AE subsequence, continuous dphi and the verified strong multiplier limit identify the strong gradient limit. Closedness passes the pair to the existing operator graph. This closes the previously recorded arbitrary closed-domain nonlinear chain obligation; it is no longer limited to polynomial inputs, finite observations or supplied weak derivative identities. The theorem retains global boundedness of phi and dphi; no unbounded chain rule or nonsmooth Lipschitz extension is claimed.

`bounded_product_chain_graph` applies this full-domain theorem inside actual Gaussian product sections. BOTH the nonlinear function and its derivative are first constructed globally in product L2 using actual MemLp proofs. Their genuine curry representatives and product AE Fubini identify each section with the scalar theorem's witnesses. Thus no measurable choice of fiberwise derivative values is assumed. Its graph conclusion is the existing BochnerClosedOperator.lift of the original closed Gaussian derivative, with the actual derivative field dphi(f)g. This is actual stochastic derivative identification, not an expectation identity.

`IBMNonlinearAverageGraph.swap_swap` and `nativeAverage_source_representation` establish the exact native (source,clock) / clock-outside-source-inside conversion via the existing swap and curry isometries. `nativeAverage_bounded_chain` proves, for every T>=0 and every bounded C1 phi with continuous bounded derivative, that the SAME actual random variable F=phi(nativeAverage T) is in the intrinsic IBM observable L2 subspace and has BOTH genuine partial derivative graphs. Clock sections are source-outside/clock-inside; source sections are clock-outside/source-inside, using swap F. The clock input domain and actual derivative come directly from1091's nativeAverage_clock_domain; the source input graph is1091/1087's sourceAverage_source_graph. The two nonlinear scalar outputs are proved equal under the actual probability swap, rather than treated as unrelated representatives. Intrinsic measurability follows from actual IBM-generated-sigma measurability of the original average and continuous composition. Product-chain derivative formulas are proved in the generic theorem; the IBM specialization records actual jointly measurable L2 graph witnesses rather than introducing a new derivative definition.

Reusable next direction: finite linear combinations of actual time averages inherit both partial domains by existing operator linearity, so the new bounded chain rule gives smooth bounded functions of these linear combinations. This is the productive route toward a sufficiently rich intrinsic observable core. The remaining F3 obligations are genuine NON-Gaussian intrinsic observation-L2 density and the appropriate intrinsic restriction/adjoint identification. The linear span of averages or separate one-variable functions alone is not a density proof. Investigate finite families and a concrete measure-determining argument, reusing `ObservableDensityCriterion.derivative_dense_iff_annihilator_zero`; `ObservableCoreDensity.derivative_dense_of_projection_invariant` is only a sufficient conditional theorem and its invariance hypothesis has not been proved for IBM. Ordinary-time recovery/path continuity of the actual averages can help prove observation-sigma generation, but does not itself yield the L2 core theorem. Do not substitute GaussianGeneratedDensity for the actual nonGaussian IBM law.

F1 global higher-source physical dual topology and uniform cross-sector summation remain open. F2 retains its fixed concrete normalized bump-family scope.1091's actual unmollified time-average source/clock domains and AE sample-path integral remain proved. Full closed Gaussian chain closure and its actual bounded nonlinear IBM time-average application are now established; full F3, F1 and the whole IBM manuscript are not declared complete. No successor gate is released. No new manuscript ingestion was necessary for this direct supporting calculus.

Further direct reuse audit: `GaussianGeneratedDensity.familyPolynomial_orthogonal_measurable_zero` already contains a pi-lambda proof on the OBSERVATION sigma-algebra, using `generateFrom_measurableCylinders`, `isPiSystem_measurableCylinders` and `MeasurableSpace.induction_on_inter`. Its Gaussian polynomial finite-observation density hypothesis does not apply to IBM, but that sigma-algebra argument is a precise reusable proof pattern once actual finite IBM observation tests are established. Mathlib `Measure.ext_of_charFun` in `MeasureTheory/Measure/CharacteristicFunction/Basic.lean` proves uniqueness of finite positive measures on complete second-countable inner-product spaces from their actual characteristic functions. A candidate nonGaussian finite-family route is to use bounded smooth sine/cosine tests of all real linear combinations, compare the pushforwards of the positive and negative parts of an integrable annihilator, then use the observation pi-lambda argument. Weighted-measure domains, exact Fourier identifications, finite-family domain closure and generation by actual time averages are NOT yet proved here. This is a focused next strategy, not a claim of F3 density or a new research branch.

Verification1094: direct generic and IBM module checks passed; final full `lake build` passed5686 jobs, exit0. Root-wide transitive axiom audit passed30802 safe Foundation declarations using only `propext`, `Classical.choice`, `Quot.sound`. All13 new public definition/abbreviation/theorem types were printed and inspected, including AE versus strong convergence, original graph identification, bounded C1 hypotheses, native/swap factor orders and intrinsic-sigma measurability. No sorry/admit or new axiom. All107 archived manuscript hashes and43 Incoming files/42 distinct hashes match their saved baselines. ResearchSources and dependency pins are unchanged. Evidence: `.lake/stardust-1094-draft3.log`, `.lake/stardust-1094-draft5.log`, `.lake/stardust-1094-ibm-draft2.log`, `.lake/stardust-1094-full-build.log`, `.lake/stardust-1094-audit.log`, `.lake/stardust-1094-public-types.json`, `.lake/stardust-1094-archive-check.json`, `.lake/stardust-1094-inventory-check.json`.


## Verified discovery1095 — actual IBM finite Fourier core, point recovery in L2 closure and annihilator moment identities

Continued from auditede77507b622586a54f3510170a3ecffcfa58b1623 (1094); the preceding turn made substantive verified progress. Current tracked state and saved checkpoint were revalidated. Terminal proof breaks on2026-10-19 include03:53:51,03:55:33,03:56:34,03:57:36,03:58:33,03:58:53,03:59:41,04:00:29,04:01:20,04:01:58 and04:02:14 America/New_York. IBM remains immediate. IBM -> A(4) -> A(2) -> final full multichannel and the October31 stopping date retain their gates. No manuscript was modified or adopted as an axiom.

New root-imported module `Foundation/IBMFiniteAverageCore.lean`. Its `intrinsicCore` is the actual intersection of the existing intrinsic IBM observable L2 subspace with BOTH existing partial Gaussian derivative domains, pulled back through the genuine curry and probability-swap isometries. This is a concrete submodule of native(source,clock) joint L2, not a separately assumed dense core. `mem_intrinsicCore_iff` exposes the exact native/swap factor order and both actual domain conditions. `nativeAverage_mem` directly reuses1091's clock-domain theorem and1087's source graph, proving membership for every nonnegative terminal time.

`bounded_chain` strengthens1094's single-average application to EVERY element of this actual intersection. Bounded C1 composition with continuous bounded derivative preserves the actual common intrinsic domain, using the already verified product chain graph, actual globally constructed gradient classes and intrinsic-sigma continuous composition. The source/clock scalar outputs are identified through the probability swap, so both domains concern the same random variable. This theorem does not assume domain invariance under the IBM conditional expectation or introduce a new derivative operator.

`averageCombination` is the actual L2 finite weighted sum of unmollified IBM averages; its AE finite-sum representative and intrinsic common-domain membership are proved for arbitrary finite index types, all real weights and all nonnegative times, including empty families. `cosine_average_cylinder` and `sine_average_cylinder` prove that BOTH Fourier channels of every such finite weighted average family lie in that actual common domain. They are obtained using actual sine/cosine derivatives and global norm bounds, not a Gaussian law for the observations. `annihilator_average_fourier_moments` proves that an actual joint-L2 vector orthogonal to this domain has zero weighted cosine and sine integrals for all those families.

A distinct ordinary-time connection resolves an important density issue. `point_mem_core_closure` uses1087's actual nativeAverage_hasDerivAt and positive-increment difference quotients of the genuine averages to put the actual IBM point L2 class at EVERY positive time in the L2 closure of intrinsicCore. Each difference quotient belongs to the common domain by its proved linearity, since both terminal times are positive. This is strong scalar L2 closure, not graph convergence and NOT membership of the point observation in either partial derivative domain. No uniform derivative bound for those quotients is claimed.

`bounded_chain_closure` proves bounded C1 composition stability of the L2 closure of this common intrinsic domain. It uses actual domain approximants, the verified bounded_chain theorem, global bounded-derivative Lipschitz control and strong scalar L2 convergence. Derivative norms of approximants need not be bounded because the conclusion is L2 closure alone. This avoids the invalid inference from scalar convergence to derivative-domain membership.

`point_cylinder_closure` combines those two facts to realize bounded C1 functions of arbitrary finite real weighted sums of ACTUAL IBM POINT VALUES at positive times in intrinsicCore's L2 closure. It explicitly identifies the original constructed process ibmValue using the already verified joint_point_actual_ae theorem and finite AE sums. The original observations need not be Gaussian, independent or nondegenerate.

`annihilator_point_fourier_moments` is the resulting concrete finite-dimensional test: if H in native joint L2 is orthogonal to intrinsicCore, then for EVERY finite family of positive times and EVERY real weight vector,

    integral H*cos(sum_i w_i ibmValue(t_i)) = 0,
    integral H*sin(sum_i w_i ibmValue(t_i)) = 0.

The proof reuses orthogonal_closure and the actual point-cylinder representatives, not a formal characteristic-function assumption. These are actual weighted stochastic moment identities. H is not required to be intrinsic in this theorem; unobservable latent vectors may indeed survive these tests. Intrinsic measurability is essential in the remaining final annihilator-zero argument.

The remaining F3 density step is now sharply isolated: use the proved actual finite point-observation Fourier moments to show the corresponding signed finite-dimensional weighted laws vanish, then use the existing observation-sigma pi-lambda argument and intrinsic measurability to force an intrinsic annihilator H to zero. Mathlib `Measure.ext_of_charFun` applies to FINITE POSITIVE measures; it cannot be applied directly to H times probability as if that were positive. A rigorous route is the finite positive pushforwards of weights ENNReal.ofReal(H) and ENNReal.ofReal(-H). L2 implies actual integrability of H, and `isFiniteMeasure_withDensity_ofReal` is available in MeasureTheory/Function/L1Space/HasFiniteIntegral. `integral_withDensity_eq_integral_toReal_smul` and its AE version, in Integral/Bochner/ContinuousLinearMap, give the exact weighting identity; `integral_map` supplies the observation pushforward formula. Correct integrability, real/complex Fourier conversion and positive-part subtraction must be proved, not assumed. This weighted-law identification remains UNPROVED at1095.

Existing GaussianGeneratedDensity.familyPolynomial_orthogonal_measurable_zero has the needed observation pi-lambda proof pattern after finite-event integrals are established; its Gaussian polynomial-density theorem still does not apply to IBM. The new point tests restrict to positive times. To include the time-zero coordinate in the generated observation sigma, reuse the actual EVERY-SAMPLE continuity `IBMConstructedSources.ibmValue_continuous` (line147) and a positive sequence decreasing tozero; do not silently drop that sigma-algebra issue or assume an unproved raw zero-time identity. Full density, exact intrinsic adjoint and all of F3 are not yet asserted.

Reuse audit: Mathlib BoundedContinuousFunction.toLp_denseRange requires finite weakly regular measure and is valid for arbitrary finite-dimensional laws under its actual hypotheses, but bounded continuous approximation alone supplies no derivative-domain membership. It was not used to shortcut the needed stochastic chain calculus. No separate chaos or unrelated campaign was opened. F1 global higher-source physical dual topology/uniform summation remains open; F2 keeps its fixed concrete normalized bump-family scope. Previously verified unmollified time-average domains, sample-path realization and full closed Gaussian bounded C1 calculus are preserved. No IBM freeze or successor transition is justified yet.

Verification1095: direct module checks passed; final full root `lake build` passed5687 jobs, exit0. Root-wide transitive axiom audit passed30837 safe Foundation declarations using only `propext`, `Classical.choice`, `Quot.sound`. All17 new public definition/abbreviation/theorem types were printed and inspected, including native/swap domain orders, actual process representatives, arbitrary finite/empty family scope, nonnegative average versus positive point times, ordinary-time recovery into L2 closure rather than derivative domain, bounded C1 hypotheses, and annihilator moment conclusions without an unproved density claim. No sorry/admit or new axiom. All107 archived manuscript hashes and43 Incoming files/42 distinct hashes match saved baselines. ResearchSources and dependency pins are unchanged. Evidence: `.lake/stardust-1095-draft3.log`, `.lake/stardust-1095-draft5.log`, `.lake/stardust-1095-draft6.log`, `.lake/stardust-1095-draft7.log`, `.lake/stardust-1095-full-build.log`, `.lake/stardust-1095-audit.log`, `.lake/stardust-1095-public-types.json`, `.lake/stardust-1095-archive-check.json`, `.lake/stardust-1095-inventory-check.json`.


## Verified discovery1096 — nonGaussian density of the actual intrinsic IBM common partial-derivative domain

Continued from audited3f8e632d354ba84f3f9ba595b7430a88447dfda5 (1095); the preceding turn made substantive verified progress. Current tracked state and saved checkpoint were revalidated. Terminal proof breaks on2026-10-19 include04:05:51,04:07:51,04:08:00,04:09:02,04:10:07,04:10:14,04:11:04,04:13:05,04:13:15,04:14:08,04:14:52,04:15:00 and04:15:38 America/New_York. IBM remains immediate; IBM -> A(4) -> A(2) -> final full multichannel and the October31 stop retain their gates. No manuscript was edited or introduced as an axiom.

New root-imported modules `Foundation/IBMFiniteWeightedLaws.lean` and `Foundation/IBMIntrinsicCoreDensity.lean` close1095's concrete nonGaussian intrinsic-density obligation. The main theorem `IBMIntrinsicCoreDensity.core_closure_eq_intrinsic` states an equality of ACTUAL submodules of native joint L2:

    IBMFiniteAverageCore.intrinsicCore.topologicalClosure = IBMTimeAveragedObservable.IntrinsicSpace.

Here intrinsicCore is EXACTLY the intersection of actual IBM-observable L2 and the two existing source/clock partial Gaussian derivative domains, with their genuine curry/swap identifications. IntrinsicSpace is the original sigma-algebra generated by the constructed continuous IBM process. Thus the true common domain is dense in the full intrinsic observable L2 space. No Gaussian observation-law hypothesis, supplied projection-invariance condition, alternative noise, finite-observation-only conclusion or new definition of derivative is substituted.

The proof uses1095's actual sine/cosine annihilator moments against all finite positive-time IBM point observations. `weighted_integral_difference` proves for an actual measurable integrable real H and bounded AE measurable test v that the integral against the positive measure dP*ofReal(H), minus that against dP*ofReal(-H), equals integral H*v dP. This derives actual weighting and integrability using the verified positive/negative L1 parts and the existing withDensity Bochner formula. `weighted_integral_balance` gives equality of the two positive integrals when the H-weighted moment vanishes. The proof does NOT treat H*dP as positive.

`finite_measure_eq_of_cos_sin` derives equality of arbitrary finite positive measures on a finite Euclidean space from equality of all cosine and sine inner-product integrals. Actual bounded continuous complex characters are integrable, real/imaginary integral identities recover the characteristic functions, and Mathlib Measure.ext_of_charFun supplies measure uniqueness. This permits nonGaussian and singular observation laws, including empty index types.

`pointObservation` is the actual finite Euclidean random vector of the constructed ibmValue at supplied times, with measurability proved. `annihilator_finite_weighted_laws` proves equality of its two finite positive pushforward laws with weights ofReal(H) and ofReal(-H), for any actual H orthogonal to intrinsicCore and arbitrary finite positive-time observations. H in joint L2 implies genuine L1 integrability and finiteness of both weighted laws. The actual Euclidean inner product agrees with the weighted finite point sum in1095's moment theorem. `annihilator_finite_event` then proves the set integral of H over EVERY measurable finite point-observation event is zero, using an actual indicator test, pushforward integration and the exact weighting difference identity. This is stronger than an expectation or a formal characteristic identity.

The density proof defines the sigma-algebra of all strictly positive-time actual observations. Its finite cylinders are identified with those Euclidean finite events. `annihilator_positive_measurable_zero` performs the existing observation-sigma pi-lambda proof pattern on this NON-Gaussian family: finite cylinders, complements and disjoint countable unions give all observation-event integrals zero. Lp.ae_eq_zero_of_forall_setIntegral_eq_zero' then forces any positive-observation-measurable annihilator to vanish. Only the pi-lambda proof pattern is reused from GaussianGeneratedDensity; its Gaussian polynomial-density theorem is not applied to IBM.

`all_coordinates_positive_measurable` resolves the time-zero issue without an assumed zero-time normalization. Positive coordinates are coordinate projections of the observation map. The zero coordinate is the EVERY-SAMPLE limit along the already verified positive widths 1/(n+1), using the actual ibmValue_continuous theorem, continuous real-to-nonnegative conversion and measurability of sequential pointwise limits. Consequently `intrinsicSigma_le_positive` proves that the full original IBM-generated sigma-algebra is contained in this positive-time observation sigma-algebra. No AE common-null-set or countability assumption on all times is smuggled in.

`intrinsic_annihilator_zero` combines this sigma inclusion with the actual intrinsic AE measurability of H. The intrinsic common domain is a subspace of IntrinsicSpace; closedness of that original observable subspace keeps its L2 closure inside it. Its orthogonal complement intersects IntrinsicSpace trivially by the annihilator theorem. The existing Hilbert orthogonal-projection decomposition gives the exact submodule equality core_closure_eq_intrinsic.

Scope correction superseding1095's open-density statements: density of this ACTUAL maximal common intrinsic partial-derivative domain is now proved. Point observations themselves are still only asserted to lie in its L2 closure; this result does not prove pointwise clock Sobolev regularity, graph-norm density of a smaller specified cylinder family, conditional-expectation invariance of either domain, or convergence of singular Ito-Tanaka correction sectors. The main theorem concerns scalar intrinsic L2 density, not an unproved stronger graph-core statement. It gives a rigorous positive answer to the intrinsic-density component of F3 for these identified source/clock operators. Exact packaging/comparison with any manuscript joint-noise pullback operator and an intrinsic adjoint/divergence identification remain separate theorem-level obligations. Do not turn this milestone into completion of all F1-F3 or the whole manuscript.

Next focused action: audit the existing `ObservableRestriction`, `ObservableProjectedDivergence`, `ObservableCoreDensity`, `ObservableDensityCriterion`, actual native source/clock operator transports and their adjoints to expose the precise already verified intrinsic operator now having a dense domain. Prefer direct reuse of closed pullback/intersection operator and projection-of-adjoint theorems. Check exact joint-noise domain/range identifications before equating formulations. Do not reopen Gaussian chain closure, actual common intrinsic density, time-average source/clock domains or sample-path realization as missing. F1 global higher-source physical dual topology/uniform summation remains open and is an independent campaign gate. F2 preserves its fixed concrete normalized bump-family scope. No IBM freeze or A(4) transition is justified by density alone.

Additional theorem-level reuse audit: `IBMSceneryObservableRestriction` explicitly concerns the positive-time Gaussian SCENERY observable subspace, not the intrinsic IBM sigma-algebra. Its derivative_dense result must not be presented as the new IBM density proof. `ObservableProjectedDivergence` already proves projected_pairing, source_divergence_mem and divergence_source_value for a genuinely densely defined observable restriction, with equality only on the embedded source-adjoint domain. These are precise candidates for the next actual IBM operator instantiation; they do not identify full adjoint domains automatically. Preserve that one-sided scope when reusing them.

Verification1096: direct weighted-law and density proof checks passed after the final composition simplification; final full root `lake build` passed5689 jobs, exit0. Root-wide transitive axiom audit passed30858 safe Foundation declarations using only `propext`, `Classical.choice`, `Quot.sound`. All17 new public definition/abbreviation/theorem types were printed and inspected, including the attributed positiveSigma definition. An additional explicit-instance type check verified that annihilator_positive_measurable_zero requires AE measurability in positiveSigma, that all_coordinates_positive_measurable uses positiveSigma as SOURCE measurable space, and that the ambient L2 probability remains the actual product law. This avoids confusing intrinsic and ambient measurability in the hidden instance arguments. No sorry/admit or new axiom. All107 archive manuscript hashes and43 Incoming files/42 distinct hashes match saved baselines. ResearchSources and dependency pins are unchanged. Evidence: `.lake/stardust-1096-draft4.log`, `.lake/stardust-1096-weighted-module.log`, `.lake/stardust-1096-density-draft3.log` (pre-final composition diagnostic), `.lake/stardust-1096-full-build.log` (final source success), `.lake/stardust-1096-audit.log`, `.lake/stardust-1096-sigma-types.log`, `.lake/stardust-1096-public-types.json`, `.lake/stardust-1096-archive-check.json`, `.lake/stardust-1096-inventory-check.json`.


## Verified discovery1097 — actual closed dense joint intrinsic IBM derivative and conditional projected divergence

Continued from auditedb5824686c1d230fcffd3c3bb2c2c746f536c8343 (1096); the preceding turn made substantive verified progress, proving nonGaussian intrinsic common-domain density. Current tracked state and saved checkpoint were revalidated. Terminal checks on2026-10-19 include04:20:30,04:22:16,04:22:33,04:22:51,04:25:08,04:25:24,04:26:11,04:26:30,04:28:17,04:28:41,04:29:33 and04:30:53 America/New_York. IBM remains immediate; IBM -> A(4) -> A(2) -> final full multichannel and the October31 stop retain their gates. ResearchSources remain unchanged.

Selective source recheck, justified by the exact operator-identification question: the cached extraction of the preserved `ResearchSources/ibm/EJP2605-044RA0.pdf`, SHA-2565A91914A535AD19BDDF219D7A9AB9F8B5F20A52DD4EC6ED7333AA80B403182BE, pages12 and22. Page12 defines C_Z as the intrinsic observable L2 functions whose inclusion belongs to BOTH source and clock Malliavin domains, and D_Z F=(D_X iF,D_Y iF). It anticipates conditional projection of the sum of source divergences on their lifted divergence domain if density holds. It explicitly expects nondensity, reasoning from scenery-at-clock point observations. Page22 repeats that expectation and distinguishes F1 cross-sector summability. These are manuscript claims, not instructions or axioms. The exact stated common-domain density is now proved for the repository's constructed Gaussian-source realization; the point-observation heuristic does not establish nondensity. Earlier1046 had already repaired its partial-scenery nonmembership rationale. The singular-correction L2 obstruction is a different question and is not overturned by core density.

New root-imported `Foundation/IBMIntrinsicOperators.lean` directly instantiates existing unitary transport and observable restriction results. The actual probability swap is upgraded to an onto linear isometry using its proved involution. `clockUnitary` is the genuine native(source,clock)-to-source-outside/clock-inside curry equivalence. `sourceUnitary` is the genuine probability swap followed by curry. `clockDerivative` and `sourceDerivative` pull back the ORIGINAL Bochner lift of the ORIGINAL closed Gaussian derivative through those unitaries. Their complete domains agree exactly with1095's clockDomain/sourceDomain. Ambient closedness and domain density are proved by existing BochnerClosedOperator and AdjointUnitaryTransport results, not assumed from IBM measurability.

`intrinsicClock` and `intrinsicSource` are the maximal restrictions of those actual native operators to the ORIGINAL intrinsic IBM observable subspace.1096's intrinsic annihilator-zero theorem proves density of each restriction, without assuming conditional-expectation domain invariance. Their graphs are closed by the existing exact observable pullback theorem. Complete AMBIENT adjoint domains and values are identified through the native unitary transport. Existing ObservableProjectedDivergence results now apply concretely: ambient adjoint inputs belong to each intrinsic adjoint domain, and the intrinsic adjoint value is the intrinsic orthogonal projection of the actual native ambient divergence. Equality of full intrinsic and ambient adjoint domains is NOT asserted.

New root-imported `Foundation/IBMJointIntrinsicDerivative.lean` constructs the actual joint intrinsic derivative. Its domain is the exact intersection of intrinsicSource.domain and intrinsicClock.domain. `joint_domain_iff` identifies it with the inclusion pullback of1095's ACTUAL intrinsicCore, so this is precisely the stated maximal common domain, not a smaller selected cylinder core. Its codomain is the genuine two-channel Hilbert space PiLp2(FieldSpace,FieldSpace); channel0 is scenery/source, channel1 is clock. The gradient is the actual pair of existing derivative values. The Hilbert norm and inner product come from the two-channel L2 product, not the max norm on a plain product.

`joint_graph_iff` identifies the two graph components exactly. `jointDerivative_closed` derives closedness from the two continuous graph projections. `jointDerivative_dense` uses the ACTUAL common intrinsic density, rather than the invalid general inference that an intersection of dense domains must be dense. `jointDivergence` is the genuine Hilbert adjoint of this closed densely defined derivative with its naturally determined domain; no divergence values are assigned by fiat.

`joint_adjoint_pair` proves that a pair of integrands from the individual intrinsic adjoint domains belongs to the joint adjoint domain and that its joint divergence is the sum of their actual intrinsic adjoint values. `ambient_pair_divergence` specializes this to the LIFTED AMBIENT source and clock adjoint domains, yielding

    delta_Z(u_X,u_Y) = P_Intrinsic(delta_X u_X + delta_Y u_Y).

`ambient_pair_conditional_divergence` identifies that exact orthogonal projection with the repository's actual IBMConditionalObservable.observableProjection, defined by condExpL2 on the original IBM-generated sigma-algebra. Thus the anticipated manuscript formula is a verified conditional-expectation identity on its stated lifted ambient divergence domain. `ambient_pair_duality` gives the actual joint derivative–divergence pairing for every input in the maximal joint intrinsic derivative domain. Full equality of the joint adjoint domain with the pair of individual ambient adjoint domains is not claimed or needed for this formula.

F3 scope resolution:1096 proves the stated common intrinsic domain dense in the actual intrinsic IBM L2, and1097 now constructs its closed joint derivative, genuine Hilbert adjoint and projected conditional divergence on the specified lifted domain. This supplies a positive result in the repository's constructed canonical Gaussian-source realization, correcting the manuscript's expected nondensity. There is no claim of graph-norm density of a smaller chosen class, pointwise clock derivative regularity, identification of physical white-noise distributions with spectral coordinates without a theorem, or convergence of the singular full Ito-Tanaka correction. Non-semimartingale/Markov issues are not inferred from this Sobolev calculus. F1 remains the main cross-sector analytic gate. F2 retains its verified fixed concrete normalized bump-family scope. No IBM freeze or successor transition occurs until the remaining campaign audit/central F1 obligations are resolved or reach a rigorously documented stopping point under the user's gate.

Next promising F1 question, explicitly UNPROVED: can a common CLOCK Gaussian negative-order norm control the full source/clock correction through the distributional second clock derivative of the actual bounded reflected field? At s>0 let v_s be the normalized clock Hilbert direction, norm1, so the formal classical second derivative is s^{-1} D_{v_s}^2 of f(X_n(|Y_s|)). Its distributional reflected derivative also contains the origin delta term, whose time integral must be identified with the ACTUAL local-time boundary correction. That identity, including both origin and curvature terms, is essential; dropping the delta would invalidate the approach.

Direct reuse candidate: GaussianInverseNumberPotential.potentialOperator is an ALREADY constructed bounded Gaussian inverse-number operator with potential_hasSum=sum_n n^{-1} projection_n. Adding projection0 gives an injective smoothing K with degree0 coefficient1 and positive degreej coefficient1/j. On a normalized one-coordinate Hermite mode of input degree n, the formal K D_v^2 multiplier is zero for n<2, sqrt2 at n=2, and sqrt(n(n-1))/(n-2) for n>=3, bounded by sqrt6. This elementary mode normalization is a candidate estimate, not yet a Lean theorem for the full operator. It suggests a common clock-sector weight preserving all sectors, including the pure-clock-mean channel, without creating a new stochastic source or treating fixed-sector limits as summable automatically. Investigate whether existing Gaussian sector derivatives/creation operators and this inverse-number potential prove the actual bounded regularized derivative.

For time integration, subtract the clock-constant source field f(X_n(0)), which the clock derivative should annihilate. Uniform Brownian scenery increment estimates would give an L2 bound of order s^{1/4} for the remaining reflected field and hence an integrable candidate bound s^{-3/4} after the s^{-1} derivative scaling. Both the uniform increment bound, global clock-sector estimate, strong limit and exact finite-mollifier identification of K C_n with the integrated regularized second derivative remain proof obligations. A genuine topology must be specified and related to the actual correction; this is not a claimed F1 solution or an assumed equivalence to the manuscript's spatial H^-1 topology. Reject or repair the route if an explicit counterexample or missing boundary identity appears. This is a focused F1 investigation using verified operator machinery, not an unrelated research campaign.

Verification1097: individual native/intrinsic operator direct check passed; joint direct check passed after the final explicit observable-space unfolding. Final full root `lake build` passed5691 jobs, exit0. Root-wide transitive axiom audit passed30944 safe Foundation declarations using only `propext`, `Classical.choice`, `Quot.sound`. All41 new public definition/abbreviation/theorem types were printed and inspected, including the full native domains, ambient density, actual intrinsic sigma-space, exact joint-domain intersection, source/clock channel order, genuine PiLp2 Hilbert codomain, natural joint adjoint domain, restricted ambient-domain formula and actual condExpL2 projection. The generic restriction-density helper is discharged for both concrete operators; no unproved stability or density assumption remains in the concrete theorems. No sorry/admit or new axiom. All107 archive manuscript hashes and43 Incoming files/42 distinct hashes match saved baselines. ResearchSources and dependency pins are unchanged. Evidence: `.lake/stardust-1097-draft1.log`, `.lake/stardust-1097-operators-module.log`, `.lake/stardust-1097-joint-draft3.log`, `.lake/stardust-1097-full-build.log`, `.lake/stardust-1097-audit.log`, `.lake/stardust-1097-public-types.json`, `.lake/stardust-1097-archive-check.json`, `.lake/stardust-1097-inventory-check.json`.


## Verified discovery1098 — a common injective clock-number regularization, sharp second-derivative bound and an explicit reflected-boundary test

Continued from audited7f8495578953842a290f70e9347c2bae51983120 (1097); the previous turn made substantive verified progress, constructing the actual closed dense joint intrinsic IBM derivative and conditional divergence formula. Those F3 results remain proved. Current state and system clock were revalidated. Terminal checks on2026-10-19 include04:35:09,04:35:49,04:37:56,04:39:19,04:40:30,04:41:32,04:42:59,04:43:40,04:44:31,04:44:58,04:46:11,04:46:49,04:48:03,04:48:48,04:49:01,04:49:17,04:50:53,04:52:03,04:52:14 and04:53:15 America/New_York. F1 is the immediate analytic target. The queued A(4), A(2), final multichannel campaign and October31 stop retain their gates. No manuscript changes or new stochastic-source assumptions.

New root-imported modules: `GaussianRegularizedSecondDerivative`, `GaussianObservedSecondRegularization`, `GaussianReflectedSecondBoundary`. These establish the proposed regularization and a necessary boundary counterexample/test. They do NOT yet identify or prove convergence of the full IBM correction.

`GaussianRegularizedSecondDerivative` works in the ORIGINAL actual one-dimensional standard Gaussian L2 and reuses its complete normalized Hermite basis, exact Parseval coefficients and original closed derivative graph. A bounded weighted shift is realized by the existing square-summable-coefficient realization theorem. Linearity follows from actual coefficient uniqueness and completeness; its norm bound follows from Parseval and the injective index shift. No new probability, independent prescribed coefficient space or assumed derivative graph is introduced.

Define kappa_0=1 and kappa_j=1/j for j>=1. The actual bounded smoothing operator S has Hermite coefficients kappa_j times the input coefficient. It is injective, has dense range, and norm<=1. The mean channel is explicitly retained. Define gain_j=kappa_j*sqrt(j+1)*sqrt(j+2). The actual bounded operator A has output coefficient gain_j times input coefficient(j+2). Its norm is EXACTLY sqrt6, not merely a conjectured mode estimate: gain_j^2<=6 for allj gives the upper bound, and the actual normalized cubic Hermite vector attains it. `regularizedSecond_hermite` verifies all shifted Hermite modes; the quadratic maps to sqrt2 times the constant, and the cubic maps to sqrt6 times the linear mode. Constants in the TARGET are not silently removed.

`regularizedSecond_actual_graph` proves agreement with two successive ORIGINAL closed derivatives: if(f,g) and(g,h) belong to GaussianCore.closedDerivative.graph, then A f=S h. The coefficient construction is therefore identified with the actual smoothed second derivative on its genuine domain. The extension is bounded on all Gaussian L2, including nonsmooth functions; no classical second derivative for every such input is claimed.

`GaussianObservedSecondRegularization.commonSmoothing` is ONE already available full infinite-Gaussian operator K=projection0+GaussianInverseNumberPotential.potentialOperator. Its exact sector action is kappa_n times the n-th actual Gaussian sector, and commonSmoothing_hasSum identifies its unconditional chaos expansion. A positivity/recovery argument proves its kernel is zero: the zero-sector squared mean and actual divergence-recovery energy cannot both vanish except at zero. Thus the candidate norm f -> norm(K f) does not identify nonzero vectors or delete any chaos sector. This is a common smoothing on the entire clock sample space, independent of which direction is observed.

The proof directly bridges the two existing Hermite constructions (the one-dimensional probabilists' polynomial and the time-space Wick polynomial atvariance1). Along EVERY actual unit first-chaos observation h, the existing measure-preserving pullback J_h carries normalizedHermite_n to the actual normalizedWick(h,n). Sector action and complete-basis density prove the exact intertwining

    K J_h f = J_h S f  for ALL actual one-dimensional Gaussian L2 f.

This is the common-norm connection needed when the normalized clock direction varies with time. Separate coordinate norms are not substituted for a common target topology.

`observedSecond=J_h A` has norm<=sqrt6, uniformly over all actual unit directions. Its actual-graph theorem gives J_h A f=K J_h h2 when h2 is the genuine second closed derivative of f. `fullObservedSecond=J_h A J_h*` is a bounded operator on full Gaussian L2, also uniformly bounded bysqrt6. It agrees with J_h A on the actual observation range J_h(L2). IMPORTANT SCOPE: on arbitrary full-space functions it first projects through the one-observation adjoint J_h*. It is not asserted to be the unrestricted directional second derivative on functions also depending on orthogonal Gaussian directions. Actual IBM point fields must be proved to be one-observation functions in the clock variable before using this identification; that range proof remains an application obligation.

The operators lift through the ORIGINAL Bochner L2 functor to genuine source-random clock fields: outer factor is scenery/source, inner factor is clock. sourceSecond retains the uniform sqrt6 bound. sourceSmoothing is the SAME K acting in the clock sections and is proved injective on the actual whole source/clock Bochner space. Its AE section formula is verified. This preserves all source randomness rather than replacing the scenery with a scalar expectation. No mollifier limit is concluded from this lift alone.

The concrete reflected-boundary test uses the existing actual weak first derivative of abs. `absoluteClass` is the actual standard-Gaussian L2 class of abs(x), and `signClass` is its already rigorously approximated closed derivative, obtained by reusing IBMReflectedGaussianSobolev.reflected_closed_graph for the identity function. The first Hermite coefficient of sign equals the actual integral of abs(x). The exact lowering identity then gives

    coefficient_0(A absoluteClass)=integral abs(x) dgamma !=0.

Nonvanishing is independently proved using genuine Gaussian integrability, the nonnegative-integral-zero criterion and continuous representative uniqueness; no numerical moment value is assumed. At the same time the ordinary second derivative of the underlying linear function r->r is exactly zero. Thus reflecting a linear function and retaining only its positive-radius bulk second derivative would incorrectly give zero, while the actual regularized extension has a nonzero constant Gaussian channel. This is an explicit rigorous obstruction to discarding the reflection boundary channel. It is not advertised as the full local-time identity for IBM, nor as existence of an ordinary L2 second derivative of abs.

What remains for F1: construct/identify the actual source-random normalized one-Gaussian profiles for the mollified f(X_n(abs(Y_s))) fields, using the already constructed process and actual clock law. At s>0 the normalized clock direction is h_s/sqrt(s), and the physical coordinate second derivative formally introduces a factor1/s. Prove the correct actual range/pullback identity before applying the uniform operator. For reflection, retain the distributional origin term 2g_n'(0)delta0 as well as the bulk curvature. Its time integral must be matched with the ACTUAL Tanaka/local-time boundary correction, on an exact dense test class or in a specified common topology. This finite-mollifier identification is still a central UNPROVED obligation.

For the time-zero singularity, subtract the clock-constant source field f(X_n(0)); clock differentiation should annihilate it. Establish a genuine uniform-in-n Brownian scenery increment estimate of order s^(1/4) in actual joint L2. Combined with1/s and the uniform sqrt6 bound this would yield an integrable s^(-3/4) majorant. Prove the source-random field's time measurability and convergence, then the Bochner integral limit. Do not assume those domains or drop the boundary test because the operator estimate passed. The norm induced by the common sourceSmoothing gives a precise candidate all-clock-sector weaker topology, but no equality with the manuscript's physical spatial H^-1 norm, no completed all-sector correction and no F1 solution are claimed yet.

No new manuscript ingestion was necessary: this checkpoint independently proves and tests1097's focused F1 operator question. F3's actual joint calculus remains established; F2 keeps its concrete normalized bump-family scope. IBM is not frozen and no successor gate is released.

Verification1098: direct scalar regularization, observation transport and reflected-boundary checks passed after repairing the final coercion/adjoint-norm detail. Full root `lake build` passed5694 jobs, exit0. Root-wide transitive axiom audit passed31046 safe Foundation declarations with only `propext`, `Classical.choice`, `Quot.sound`. All63 new public definition/abbreviation/theorem types were printed and inspected: actual one-dimensional versus infinite-product Gaussian measures, genuine closed two-derivative hypotheses, sharp cubic and retained quadratic/constant channels, observation-range scope of J A J*, injective COMMON smoothing, outer-source/inner-clock Bochner order and the actual nonsmooth abs counterexample. No sorry/admit or new axiom. All107 archived manuscript hashes and43 Incoming files/42 distinct hashes match saved baselines. ResearchSources and dependency pins are unchanged. Evidence: `.lake/stardust-1098-regularized-module2.log`, `.lake/stardust-1098-boundary-draft2.log`, `.lake/stardust-1098-full-build.log`, `.lake/stardust-1098-audit.log`, `.lake/stardust-1098-public-types.json`, `.lake/stardust-1098-archive-check.json`, `.lake/stardust-1098-inventory-check.json`. Pre-final observed-draft logs are diagnostic only; the final full build and audit certify the final observation/source-field source bytes.


## Verified discovery1099 — uniform actual IBM clock profiles and full predictable Itô chaos intertwining

Continued from audited7582d85b266da4a2017e4c6c87c2d41cf31034eb (1098). The intervening queue-confirmation response was read-only and made no mathematical progress. On resumption, the worktree, final profile draft log and process state were inspected: no live Lean/lake process remained, and the final profile draft log was empty. The actual source was revalidated by a successful module build before use. Terminal proof/checkpoint readings on2026-10-19 include05:13:08,05:14:58,05:17:54,05:19:51 and05:20:40 America/New_York. IBM/F1 remains immediate. IBM -> A(4) -> A(2) -> final full multichannel and the October31 stopping date retain their gates. No successor starts here.

New root-imported modules: `IBMUniformMollifiedIncrements`, `IBMNormalizedClockProfiles`, `GaussianItoChaosIntertwining`. All constructions use the already verified Brownian scenery, canonical Gaussian clock, actual Gaussian L2 spaces, original derivative/divergence graphs and genuine predictable Itô integral.

`IBMUniformMollifiedIncrements.mollified_increment_norm` proves

    norm(X_n(r)-X_n(s)) <= sqrt(abs(r-s))

for every index of the concrete normalized nonnegative bump family and ALL real spatial points. The bound has no mollifier-dependent derivative constant. The proof uses the actual common-offset convolution representation, positivity and unit mass of the existing kernel, the exact Brownian scenery increment norm and Bochner integral estimates. The original finite-mollifier scenery embedding is explicitly identified with the existing coefficient0 embedding. The actual nonlinear Schwartz observable satisfies a Gaussian-L2 Lipschitz estimate in the isonormal coefficient vector; hence the full nonlinear spatial classes satisfy the same spatial half-Hölder bound with the Schwartz first-derivative seminorm. The bound also passes to the already constructed strong spatial limit. No finite-source-chaos truncation or expectation replaces these classes.

`IBMNormalizedClockProfiles` constructs, for T>0, the ACTUAL unit clock direction v_T=h_T/sqrt(T), proves its norm is1 and proves the AE identity Y_T=sqrt(T)*W(v_T). Define the source-Hilbert-valued standard-Gaussian profile

    F_n,T(x)=spatial_n(sqrt(T)*abs(x))-spatial_n(0).

Its continuity, measurable realization, boundedness and Gaussian L2 membership are verified. `sampledProfile_eq_endpoint` identifies its measure-preserving pullback along W(v_T) with the EXISTING full nonlinear `IBMSchwartzFullReflectedIto.endpointClass`. This retains every scenery/source chaos. Probability-factor order is explicit: the profile is standard-real-clock Gaussian L2 with values in source Gaussian L2; the sampled class has canonical-clock outer factor and source-Hilbert inner values. This does not yet prove every desired flip/naturality identity for a source-outer clock differential operator.

The uniform increment estimate yields the genuine time-zero energy control

    norm(F_n,T)^2 <= L_g^2*sqrt(T)*integral abs(x) dgamma(x),

where L_g is the recorded Schwartz first-derivative bound. This is uniform in n. By the actual measure-preserving isometry it is also the full joint endpoint energy bound. `endpointLimit_uniform_energy` passes it to the actual unmollified endpoint using the PREVIOUSLY proved strong endpoint convergence. The absolute Gaussian moment is an actual finite integral, reusing existing Gaussian abs L2 membership. No numerical moment value is assumed. In particular, the estimate is at the right scale for a future squared regularized first-derivative bound of order T^(-1/2), rather than a nonintegrable fixed-mollifier derivative estimate. The future bound itself is not claimed here.

The main operator connection is `GaussianItoChaosIntertwining.integral_projection`. For EVERY actual full predictable L2 field u and every n>=0,

    Ito(P_n^field u) = P_(n+1)(Ito(u)).

Here P_n^field is the original probability-chaos projection applied sectionwise through the already verified time/probability curry; it is proved genuinely predictable. This is an equality for the actual isometric Brownian stochastic integral, not an assigned formal coefficient map. No Malliavin differentiability assumption on u, finite chaos cutoff, finite observation set or grid is present in the final theorem.

The proof first establishes `rank_projection_divergence_graph`: on every genuine rank-one full-adjoint divergence graph pair, projecting the scalar coefficient to chaos n projects the divergence output to chaos n+1. It uses the existing all-Hilbert-direction closed derivative lowering theorem, rank-one Hilbert pairing, projection self-adjointness and actual adjoint-graph duality. Past polynomial steps are then handled by the PREVIOUSLY verified genuine increment-product divergence identity. Closure and density of the original predictable polynomial step space extend both predictability and the graph identity to all full predictable L2 fields. Uniqueness in the original Hilbert divergence graph gives the actual Itô equality.

This identifies the existing `GaussianItoAlternatingProjection.alternatingOperator` A=I* N^(-1) I concretely at every integrand chaos:

    P_n^field(Au) = (n+1)^(-1)*P_n^field(u).

More strongly, `alternating_hasSum` proves the UNCONDITIONAL full predictable-L2 sum of these weighted projected fields is Au. It directly transports the existing unconditional inverse-number-potential expansion through the actual bounded predictable adjoint. Combined with the already verified `integral_alternating`, this gives the shifted inverse-number regularization of the actual Itô integral, with the essential +1 shift. It reuses existing operator machinery rather than constructing a separate spectral probability space or a new stochastic integral.

New focused F1 route, not yet a completed proof: reuse the ALREADY verified full reflected identity

    endpoint_n = Ito(B_n) + wholeCorrection_n,

whose wholeCorrection includes the actual Tanaka boundary mass AND the full curvature. The common injective clock smoothing K=P0+N^(-1) acts as N^(-1) on the centered Itô output. The new actual chaos identity identifies its integrand-side regularization as A with weights1/(n+1). For a one-clock-observation profile at time s, the normalized derivative of F_n,s should equal sqrt(s)*B_n(s). Combining shifted first-derivative smoothing with the bounded actual one-observation divergence recovery should bound the regularized field by s^(-1/2)*norm(F_n,s), whose squared norm is controlled by the newly proved integrable s^(-1/2) scale. If rigorously identified, strong endpoint-profile convergence and time-L2 dominated convergence would give a genuine regularized stochastic limit, then the correction limit by the full reflected identity. This route automatically retains the origin channel because it starts from the existing actual reflected identity; it does not discard the explicit1098 abs boundary counterexample.

EXACT remaining obligations: prove the normalized reflected first closed derivative identity with the actual signed slope field; identify the one-observation recovery with the shifted chaos regularization and lift this equality through the actual source-valued/time field spaces; prove the necessary factor-order/naturality and measurable time realization; establish strong time-L2 convergence of the regularized mollified fields; apply the actual isometric Itô limit and the same common K to the full correction. Do not infer these from a mode test or merely define a new field by an operator and presume it equals the signed slope regularization. The scalar full-predictable intertwining is proved; its required source-parameterized identification is still an application obligation. No equality with the manuscript's physical spatial H^(-1) norm or completed F1 common-topology correction theorem is asserted.

F3's actual intrinsic joint calculus and common-domain density remain proved. F2 retains the concrete normalized bump-family scope. IBM is not frozen; no A(4), A(2), RH or final multichannel conclusion is made. No manuscript ingestion was needed for this direct F1 proof question.

Verification1099: profile module build passed4428 jobs; the direct Itô intertwining module check passed before extending its final weighted-sum theorems. The FINAL full root build passed5697 jobs, exit0, including all final sources and weighted-sum statements. Root-wide transitive axiom audit passed31097 safe Foundation declarations, allowing only `propext`, `Classical.choice`, `Quot.sound`. ALL31 new public definitions/theorems were printed and reviewed: actual Gaussian measures and factor order, positive-time restrictions, uniform-in-n constants, the original full-adjoint graph hypothesis, full predictable domain, chaos degree shift, and unconditional full predictable-L2 topology. No sorry/admit or new axiom. The working manifest covers1643 Foundation/root Lean sources. All107 archived manuscript hashes and43 Incoming files/42 distinct hashes match saved baselines; the dictionary hash remains8EC222C21FDB2D81D652E3CF553BE59EEA987F01AD3B1C54EEC91216111BC22E. No ResearchSources or dependency-pin modification. Evidence: `.lake/stardust-1099-profile-build.log`, `.lake/stardust-1099-full-build.log`, `.lake/stardust-1099-audit.log`, `.lake/stardust-1099-archive-check.json`, `.lake/stardust-1099-inventory-check.json`, `.lake/stardust-1099-working-checkpoint.json`. Earlier draft logs are diagnostic only; the final full build and audit certify the checkpoint source bytes.


## Verified discovery1100 — actual full-source signed-slope recovery, strong clock-chaos reconstruction and uniform integrable time-zero energy

Continued from audited917017b7dcb82b87d1446f2ba63ca311613000d3 (1099); the preceding goal turn made substantive verified progress. Current worktree and saved checkpoint were revalidated. Terminal proof/checkpoint checks on2026-10-19 include05:24:13,05:26:51,05:28:26,05:29:34,05:30:01,05:32:15,05:33:25,05:34:29,05:36:31,05:37:12,05:38:11,05:39:13,05:39:59,05:40:33,05:41:04 and05:41:27 America/New_York. IBM/F1 remains immediate. IBM -> A(4) -> A(2) -> final full multichannel and the October31 hard stop retain their gates. ResearchSources remain read-only and uncommitted.

Four new root modules: `GaussianDirectionalRecovery`, `IBMNormalizedSlopeGraph`, `GaussianClockValueOperators`, `IBMClockRegularizedSlope`. These close1099's normalized first-derivative, bounded-recovery, source-factor-order and positive-time strong-reconstruction obligations. They do not yet close the predictable time-field / stochastic-integral limit obligation.

`GaussianDirectionalRecovery` reuses the ORIGINAL infinite-Gaussian bounded divergence recovery R and its actual component map. Define R_v f=component(v)(R f). The component norm bound and existing recovery bound give norm(R_v f)<=norm(v)*norm(f). No new spectral operator or assigned derivative is needed. For EVERY genuine closed derivative graph pair

    (f, scalarTensor(v,g)) in closedCylindricalDerivative.graph, norm(v)=1,

`shifted_derivative_hasSum` proves the unconditional Gaussian-L2 sum

    R_v f = sum_(k>=0) (k+1)^(-1) P_k g.

It maps the existing unconditional inverse-gradient series through the actual component operator, uses the already verified all-direction derivative lowering identity, and retains the essential +1 shift. `shifted_derivative_projection` gives its exact projection identity at EVERY k. The real closed-graph hypothesis is explicit; it is not inferred from a formal derivative expression.

`IBMNormalizedSlopeGraph` builds the actual source-Hilbert-valued standard-Gaussian slope profile

    H_n,t(x)=sign(x)*sqrt(t)*spatialSlope_n(sqrt(t)*abs(x)).

Its strong measurability and Gaussian L2 membership follow from the already constructed full source spatial slope and its fixed-mollifier global bound. The bound here may depend on n and is used ONLY to establish the genuine finite-mollifier graph/domain. It is not substituted for the later uniform energy estimate.

For EVERY continuous source functional L, `tested_closed_graph` proves that L applied to the1099 actual endpoint profile F_n,t has L(H_n,t) as its derivative in the ORIGINAL standard-Gaussian polynomial-closure graph. The proof scales the already proved actual source-Hilbert spatial derivative, then invokes the existing reflected Gaussian Sobolev theorem. This retains the reflection cusp. No classical derivative of abs at0 or missing boundary convention is assumed.

The exact measure-preserving pullback/test naturality is proved on actual L2 classes. The already verified complete closed-graph transport then gives `tested_sampled_closed_graph`: after every continuous source test, the ACTUAL full `endpointClass` has canonical-clock derivative v_t times the sampled normalized slope. `sampledSlope_actual_ae` independently identifies that sampled source-valued class with sqrt(t) times the actual signedSlope_n(Y_t). The proof uses the actual clock-coordinate identity, positive-scaling invariance of signum and the actual normalized source slope; it does not define the process slope through recovery. `actual_slope_recovery_hasSum` now applies the genuine bounded recovery identity to this actual graph.

`GaussianClockValueOperators` carries scalar clock operators through the EXISTING product-L2 flip. Its Field has outer CLOCK probability and inner SOURCE Gaussian L2. For a bounded scalar-clock operator A, define

    C_A = flip o (A.compLpL on source parameter) o flip.

`clockLift_tensor` verifies C_A(a_clock tensor v_source)=(A a_clock) tensor v_source, so the factor on which A acts is unambiguous. `clockLift_test` proves on the WHOLE source-valued Bochner L2 space that every continuous source test commutes with C_A. This is established by the existing actual tensor-density/Lp induction machinery, not by assuming raw nested-Lp representatives form a jointly measurable function. Full source tests separate classes, all lifted clock projections separate classes, and norm(C_A f)<=norm(A)*norm(f). In particular the lifted R_v has norm bound norm(v), so unit-direction recovery is uniformly bounded across all source chaos.

The flip involution is proved on the actual whole Bochner space. `clock_truncation_tendsto` proves strong joint-L2 convergence of the original clock chaos truncations, using existing scalar truncation convergence/norm bounds and Bochner L2 dominated convergence on the source parameter. Finite operator sums commute with the lift and identify the actual finite clock-chaos sums. No finite-dimensional scenery assumption is imposed.

`IBMClockRegularizedSlope.pointSlope_actual_ae` identifies its finite-mollifier pointSlope class with signedSlope_n(Y_t), for every t>0, as a SOURCE-valued canonical-clock L2 class. Define

    Q_n(t)=t^(-1/2) C_(R_vt)(endpointClass_n(t)).

This is the actual bounded source-valued recovery of the full endpoint. `recoveredSlope_projection` proves

    P_k^clock Q_n(t) = (k+1)^(-1) P_k^clock pointSlope_n(t)

as an equality in FULL joint source/clock L2 for EVERY k. It is derived from the genuine reflected graph through all continuous source tests and the proved naturality/separation results. `recoveredSlope_unique` proves the recovered class is the UNIQUE source-valued class with these clock projections. It is not an arbitrary operator-defined substitute for the actual slope regularization.

More strongly, `recoveredSlope_chaos_tendsto` proves the finite sums over k=0,...,N of those actual shifted signed-slope projections converge STRONGLY in full joint L2 to Q_n(t). This final source-valued theorem is a natural-cutoff sequence convergence assertion; the generic scalar graph result separately has an unconditional HasSum. We do not relabel the source-valued theorem as an unproved unconditional arbitrary-finite-set sum or a time-L2 convergence theorem.

The whole source-valued bound is now

    norm(Q_n(t))^2 <= L_g^2 * (integral abs(x) dgamma(x)) / sqrt(t),  t>0,

UNIFORMLY in the concrete normalized mollifier family. It follows from the unit recovery bound and1099's actual full endpoint energy, not an n-dependent slope bound or separate estimates on finitely many sectors. The exponent t^(-1/2) is the required integrable squared-energy scale near0. The RHS contains the actual finite Gaussian absolute moment; no numerical value is postulated.

`recoveredSlope_tendsto` proves STRONG full joint source/clock L2 mollifier convergence at each fixed t, using the PREVIOUSLY proved full endpoint convergence and the actual bounded clock recovery operator. The limit is precisely the same recovery applied to the actual unmollified endpoint, preserving all scenery randomness. The uniform positive-time energy estimate passes to that limit. At0 the definition is harmless through inverse0, but no positive-time derivative graph or point-process derivative at0 is asserted.

Exact remaining F1 obligations: assemble these positive-time Q_n(t) classes into actual measurable predictable fields, identifying their time slices with the original horizon signed-slope field through actual product/curry/Fubini results. Prove strong TIME-L2 convergence in the source-valued predictable domain using the uniform t^(-1/2) squared-energy majorant and fixed-time strong limits. Extend/identify1099's actual scalar Itô-number intertwining on this genuine source-valued horizon domain. Then use the EXISTING full finite-mollifier reflected identity endpoint_n=Ito(B_n)+wholeCorrection_n to obtain the common-clock-number-smoothed stochastic and correction limits. The wholeCorrection already includes actual boundary mass plus full curvature; the1098 abs boundary counterexample remains relevant and unchanged. No origin term may be dropped.

A direct next implementation route is to lift finite clock-chaos projections sectionwise on the existing source-valued time/clock product space. Each finite projection preserves the original predictable domain by1099's scalar result plus actual source tensor density. Finite shifted sums should converge at fixed n in time-L2, dominated by the ORIGINAL finite-n integrand norm, and their positive-time slices are the now-proved Q_n(t) by strong clock-chaos reconstruction. This would give measurability/predictability without assuming operator-norm continuity of a varying v_t or jointly measurable arbitrary nested-Lp representatives. The subsequent mollifier limit uses the new uniform energy and a genuinely integrable time bound. This remains a proposed rigorous route, not a proved domain-identification or convergence statement.

No equivalence with the manuscript's physical spatial H^(-1) topology is claimed. A common injective clock-number topology is a separate precisely specified candidate; its completed full correction identity is still open. F3's actual joint intrinsic calculus remains proved, F2 keeps the concrete bump-family scope, and IBM is not frozen. No new source ingestion or unrelated campaign was necessary.

Verification1100: final supporting modules and full root build passed5701 jobs, exit0. Root-wide transitive axiom audit passed31210 safe Foundation declarations with only `propext`, `Classical.choice`, `Quot.sound`. ALL45 new public definitions/abbreviations/theorems were printed and inspected, including original closed-graph hypotheses, positive-time/unit-direction restrictions, standard versus canonical Gaussian laws, clock/source factor order, finite-mollifier domain versus uniform energy estimates, full source-valued equalities, uniqueness and exact strong-convergence topologies. No sorry/admit or new axiom. Working manifest covers1647 Foundation/root Lean files. All107 archive hashes and43 Incoming files/42 distinct hashes match the saved baselines; ym_ns_dictionary.tex remains8EC222C21FDB2D81D652E3CF553BE59EEA987F01AD3B1C54EEC91216111BC22E. No ResearchSources or dependency-pin changes. Evidence: `.lake/stardust-1100-full-build.log`, `.lake/stardust-1100-audit.log`, `.lake/stardust-1100-working-checkpoint.json`, `.lake/stardust-1100-archive-check.json`, `.lake/stardust-1100-inventory-check.json`. Draft errors were corrected before this final full build/audit; final certification refers to the final sources, not stale support logs.


## Verified discovery1101 — genuine source-valued predictable clock regularization and the full finite-mollifier stochastic IBM identity

Continued from audited876a9518876592f6a1aa5f52f153b72402dcb07a (1100); the preceding goal turn made substantive verified progress. Worktree, checkpoint and source evidence were revalidated. Terminal checks on2026-10-19 include05:44:43,05:47:26,05:49:16,05:50:16,05:51:07,05:52:09,05:53:32,05:54:21,05:55:52,05:56:14,05:56:34 and05:57:23 America/New_York. IBM/F1 remains immediate. IBM -> A(4) -> A(2) -> final full multichannel and the October31 stop retain their gates. No manuscript or goal state is changed.

New root modules: `GaussianHorizonChaosIntertwining`, `GaussianSourceHorizonRegularization`, `IBMRegularizedStochasticIdentity`. These construct the actual source-valued predictable regularization, prove its real stochastic-integral intertwining, and apply it to the full mollified IBM identity. They do not yet prove the mollifier limit of the predictable fields or identify their almost-every-time slices with1100's bounded recovery.

`GaussianHorizonChaosIntertwining.scalarLift_cut` proves that a bounded probability operator applied sectionwise commutes with the actual finite-time cutoff on every full predictable field. The proof uses existing actual polynomial step generators, the existing cutoff/tensor identities and closed step-space density. Therefore the actual chaos projections preserve finite-horizon support; no support or predictability is assumed for a proposed projected field.

`horizonProjection_eq` identifies the finite-horizon adjoint construction I_T* P_(n+1) I_T with the restriction of the ACTUAL probability-chaos projection P_n of the zero-extended predictable field. `integral_horizonProjection` and its trimmed `integral_realProjection` prove the original stochastic integral raises the clock-chaos degree by1 on the entire finite-horizon predictable domain. `realProjection_norm_le` proves contraction. Here the sector index is CLOCK probability chaos, not the scenery/source chaos index.

The existing full-space alternating operator A=I* N^(-1) I is proved to preserve the original finite-horizon support by mapping its ALREADY verified unconditional shifted-chaos sum through the actual predictable cutoff. The resulting finite-horizon regularization is identified with the restriction of A acting on the actual zero extension. The actual finite-horizon Itô identity is

    I_T(A_T u)=N^(-1) I_T(u).

This holds for every scalar predictable horizon integrand. It is not a replacement integral, a formal multiplication of coefficients or a finite-grid construction. `realRegularization_hasSum` proves the unconditional shifted-chaos sum with weights1/(k+1) converges to the actual trimmed predictable regularization, using the existing inverse-number expansion and bounded finite-horizon adjoint.

`GaussianSourceHorizonRegularization` lifts these CLOCK operators through the ORIGINAL source parameter using the existing product-L2 flip and the existing trimmed/native predictable isometry. `mapPredictable` is an actual bounded linear operator on `GaussianSourceClockIto.Domain T`, the independently specified source-Gaussian-L2-valued predictable horizon domain. Thus its outputs are genuinely predictable with the original native time/probability L2 domain, rather than merely individually defined positive-time classes.

The tensor formula proves this operator transforms the predictable CLOCK tensor coefficient and retains its full source value. `trimmedMap_test` and `mapPredictable_test` prove compatibility with EVERY continuous SOURCE functional on the whole source-valued predictable space, by actual tensor/Lp density. Native and trimmed predictable measures are kept explicit; arbitrary nested-Lp representatives are never presumed jointly measurable.

`integral_intertwining` lifts an actual scalar intertwining to the existing source-valued Itô integral on its WHOLE native predictable horizon domain. Its proof starts with genuine predictable/source tensors, uses the previously verified actual parameterized integral tensor formula and the actual clock-value operator tensor action, then extends by the existing Lp density and continuity. It does not invoke an assumed conditional expectation identity or assume source stochastic laws are Gaussian after a nonlinear test.

In this module `sourceProjection k T` denotes the SOURCE-VALUED lift of CLOCK probability projection k. It must not be confused with the older scenery/source-sector projection k used elsewhere in the IBM audit. Its precise stochastic identity is

    I_T(sourceProjection_k u)=C_(P_(k+1)) I_T(u),

where C_B is1100's actual clock operator on the full source-valued endpoint L2 space. `sourceRegularization T` is the corresponding source-valued CLOCK inverse-number regularization. For every original predictable source-valued u,

    I_T(sourceRegularization_T u)=C_(N^(-1)) I_T(u).

This is an actual signed/source-valued stochastic identity retaining ALL source and clock sectors; no expectation, scenery averaging or source truncation occurs.

`sourceRegularization_chaos_tendsto` proves the finite sums over k=0,...,N of1/(k+1) times these actual source-valued clock projections converge STRONGLY in the ORIGINAL native predictable horizon norm to sourceRegularization_T u. This norm is genuine time-clock-source L2. The proof identifies the corresponding terminal finite sums with actual clock-chaos truncations of C_(N^(-1)) I_T(u), uses1100's strong full source-valued truncation theorem, and pulls the convergence back through the original Itô ISOMETRY. It is a natural-cutoff strong sequence theorem; the scalar trimmed theorem separately has an unconditional HasSum. Neither assertion is mislabeled as convergence in the mollifier index.

The actual Itô output has zero constant CLOCK sector even as a full random source value: `integral_clock_centered` is proved using arbitrary continuous source tests, the existing source-valued scalarization and the original scalar finite-horizon centeredness theorem. Thus the SAME common K=P0+N^(-1) from1098 agrees with N^(-1) on the actual Itô output while retaining the constant channel on general endpoints and corrections.

`IBMRegularizedStochasticIdentity.smoothing` is C_K on the full source-valued endpoint L2 space. `smoothing_injective` proves it is injective by the existing scalar K injectivity and whole-source continuous-test separation. The resulting weaker common norm therefore loses no nonzero source/clock class. This is independent of T and of the mollifier; it is not a separately chosen one-observation norm or a projection deleting a difficult channel.

For each actual mollifier, define V_n,T=sourceRegularization_T of the ORIGINAL verified full signed-slope predictable integrand, and C_n,T=C_K applied to the ORIGINAL whole correction class. V_n,T belongs to the actual native predictable domain by construction; its time-L2 finite clock-chaos reconstruction follows from the universal theorem above. `finite_mollifier_stochastic_identity` proves

    C_K(endpoint_n,T)=I_T(V_n,T)+C_n,T

in FULL joint source/clock L2. The correction is exactly the common smoothing of the already verified actual boundary/local-time mass PLUS full curvature. Both are retained. This is a genuine stochastic identity, not an expectation-level heat formula. It does not claim an ordinary stochastic derivative of the unmollified IBM point observation or remove the reflection boundary obstruction.

The common-smoothed actual endpoint converges strongly by the PREVIOUSLY verified full endpoint limit. `correction_cauchy_iff_field` proves the exact remaining equivalence

    (C_n,T) Cauchy in full joint L2 <=> (V_n,T) Cauchy in ORIGINAL predictable time-L2.

`correction_tendsto_of_field` gives the precise correction limit C_K(endpointLimit_T)-I_T(V_T) IF the actual predictable V_n,T converge to V_T in that domain. This hypothesis is explicitly present. It is not asserted or hidden in a definition. The Cauchy equivalence shows why finite-mollifier construction or pointwise-time convergence alone cannot certify the singular reconstruction.

EXACT next F1 obligation: identify the almost-every-time SOURCE-valued clock slices of these NOW-CONSTRUCTED predictable V_n,T with1100's Q_n(t)=t^(-1/2) bounded directional recovery of the ACTUAL endpoint. Then transfer1100's uniform squared-energy bound C/sqrt(t) and strong fixed-time mollifier limit to obtain strong predictable time-L2 convergence. This slice identification is still UNPROVED. The predictable fields, their genuine stochastic intertwining and fixed-mollifier time-L2 chaos reconstruction are NOW proved and should not be rebuilt or treated as missing foundations.

A direct next route is the source-valued zero extension followed by the EXISTING ProductL2Curry on volume-time times canonical-clock probability, retaining source Gaussian L2 as the value space. Prove continuous source tests commute with this actual curry using its existing AE section theorem and product Fubini. Combine the new mapPredictable_test and horizonProjection_eq with1099's scalarLift probability-section action to identify each finite source-valued clock projection's slices. The new strong predictable finite-sum convergence gives an AE-time convergent subsequence of slices;1100's strong positive-time chaos reconstruction then identifies those slices with Q_n(t). This can establish time measurability of the desired recovery realization from the actual predictable field rather than assuming continuity of the varying unit clock direction. For the original IBM field use the existing actual signedSlope representation, Brownian joint field identity and actual pointSlope AE identity. All countably many cutoffs/mollifier indices need simultaneous AE sets, not an uncountable uniform sample-path assertion.

After that, use a genuinely integrable time majorant to prove the mollifier limit. The existing BochnerL2Dominated.tendsto_of_ae_norm_bound assumes the bound is the LIMIT norm and cannot be blindly used for C/sqrt(t). Reuse Mathlib Lp dominated convergence/completeness or correctly prove the necessary norm-square dominated argument; do not silently assume the candidate limit has a Bochner L2 realization. Preserve the exact time measure, positive-time restrictions and native predictable closedness. No equality with the manuscript's physical spatial H^(-1) topology is proved. F1's singular full correction remains open; F3 remains proved; F2 keeps its concrete normalized bump-family scope. IBM is not frozen and no successor campaign starts.

Verification1101: final full root build passed5704 jobs, exit0. Root-wide transitive axiom audit passed31312 safe Foundation declarations using only `propext`, `Classical.choice`, `Quot.sound`. ALL44 new public definitions/theorems were printed and reviewed, including finite-horizon support, original/native predictable domains, trimmed-measure instance scope, CLOCK versus SOURCE sector distinction, actual Itô intertwinings, strong finite-sum versus mollifier convergence, injective common smoothing, and explicit remaining convergence hypotheses. No sorry/admit or new axiom. Working manifest covers1650 Foundation/root Lean sources. All107 archived manuscript hashes and43 Incoming files/42 distinct hashes match the saved baselines; dictionary hash remains8EC222C21FDB2D81D652E3CF553BE59EEA987F01AD3B1C54EEC91216111BC22E. ResearchSources and dependency pins unchanged. Evidence: `.lake/stardust-1101-full-build.log`, `.lake/stardust-1101-audit.log`, `.lake/stardust-1101-working-checkpoint.json`, `.lake/stardust-1101-archive-check.json`, `.lake/stardust-1101-inventory-check.json`. Earlier diagnostic draft failures were repaired before the final full build and audit.


## Verified discovery1102 — actual predictable time slices, singular time-L2 convergence and full common-clock stochastic reconstruction

Continued from auditedb432ad8fabe0440b77011f92ce1775d7703bbc5c (1101); the preceding goal turn made substantive verified progress. Worktree and saved checkpoint were revalidated. Terminal checks on2026-10-19 include06:00:58,06:03:39,06:05:44,06:05:59,06:07:05,06:07:14,06:08:04,06:10:19,06:10:54,06:11:37,06:12:02,06:13:16,06:15:09,06:15:17,06:16:18,06:16:47,06:17:09,06:18:10,06:18:17 and06:18:58 America/New_York. IBM remains immediate. IBM -> A(4) -> A(2) -> final full multichannel and the October31 stopping date retain their gates.

Three new root modules: `GaussianPredictableSourceSlices`, `IBMRegularizedPredictableSlices`, `IBMRegularizedTimeLimit`. They close1101's precise time-slice identification and strong predictable mollifier-limit obligations and obtain a genuine full-source stochastic reconstruction in the SAME injective common clock-number topology. No source expectation, scenery truncation or finite clock-chaos cutoff remains in the final theorem.

The original zero-extension helper was specifically real-valued, rather than generic over the source value Hilbert space. `GaussianPredictableSourceSlices.zeroExtend` supplies exactly the required native source-valued zero extension as an ACTUAL linear L2 isometry, using the existing measurable indicator, Lp realization and exact norm identities. It proves the original horizon field's actual indicator representative. The old scalar zero-extension module and its verified consumers are unchanged. No new probability space or replacement predictable domain is introduced.

The original actual product-L2 equivalence gives sourceCurry: joint(time,clock)-L2 with source Gaussian-L2 values is isometric onto time-L2 with values in full clock/source L2. `testedNative_ae`, `zeroExtend_test` and `sourceCurry_test` prove the native/trimmed/source functional and actual time-section compatibilities. The proof uses the ORIGINAL product-L2 AE section theorem and product Fubini; it does not assume that arbitrary nested-Lp representatives form a jointly measurable function.

`zeroExtend_sourceProjection` and `sourceProjection_slices` identify the already constructed source-valued predictable projector with the ACTUAL CLOCK Gaussian probability projection on almost-every-time clock/source sections. They reuse1101's horizonProjection_eq, support/cutoff facts and compatibility with EVERY continuous SOURCE functional. The projector index remains a CLOCK chaos index; no scenery/source-sector projection is substituted.

`finite_regularization_slices` identifies every finite shifted predictable chaos sum's actual time slices. `regularization_slices_of_clock_limit` joins1101's STRONG native predictable finite-sum convergence with any verified strong positive-time clock-slice limit. The argument maps the actual native fields through the source-valued zero-extension/time-section isometry, extracts an almost-every-time convergent subsequence from the strong time-L2 convergence, and uses uniqueness of limits. It does not presume measurability of the proposed slice limit. All indices used to make simultaneous AE sets are countable; no uncountable uniform sample-path exceptional-set assertion is made.

`IBMRegularizedPredictableSlices.integrand_slices` identifies the ORIGINAL full signed-slope predictable integrand's slices with the independently verified actual signedSlope_n(Y_t) classes on(0,T]. The existing joint coefficient sigma(t,omega) is already the constructed clockPath at t.toNNReal, so no additional Brownian-law identification is assumed. `stochasticField_slices` then proves that the ACTUAL predictable regularized field V_n,T from1101 has almost-every-time slices equal to1100's Q_n(t), the bounded directional recovery of the actual full endpoint. This closes the previously central identification; the recovered field is not merely an operator assigned to fit a desired terminal formula.

Measurability and actual time-L2 realization of the horizon-restricted Q_n(t) follow from that equality with the original predictable field. `predictable_slice_uniform_energy` transfers the whole-source uniform estimate

    norm(slice(V_n,T)(t))^2 <= 1_(0,T](t) * C_g/sqrt(t),

where C_g=L_g^2 times the ACTUAL finite Gaussian absolute moment. The bound is uniform in the concrete normalized mollifier index. `predictable_slices_tendsto` proves almost-every-time strong full clock/source L2 convergence of these actual slices to the bounded recovery of the unmollified endpoint. No finite-source-chaos restriction is present.

`IBMRegularizedTimeLimit.majorant_integrable` rigorously proves the singular majorant is integrable at0, including the T=0 case, by reusing the existing Mathlib interval-integrability theorem for t^(-1/2), the actual nonnegative time interval and the exact sqrt/rpow identity. Time0 is excluded by the horizon indicator; it is not silently assigned an invalid inverse bound there.

`limitValue_measurable` obtains the actual limit's AE strong measurability from the verified AE strong pointwise limit of the ORIGINAL measurable slice sequence. The energy estimate passes to that limit, and its norm-square integrability establishes MemLp. Thus the limit is an actual Bochner L2 class, not a merely postulated family of pointwise classes.

`slices_tendsto` proves STRONG time-clock-source L2 convergence. It applies scalar integral dominated convergence to the squared norm difference with integrable majorant4C_g/sqrt(t), uses the exact Bochner L2 norm-square integral identity, and passes through sqrt to the norm limit. The proof does NOT misuse the earlier helper whose majorant was required to equal the limit norm. Both the approximating and limit fields' energy bounds and the limit class realization are explicitly proved.

The original native source-valued predictable horizon domain is complete because it is the original closed AE-predictable L2 subspace. The composition of the actual source zero extension and product-L2 time-section equivalence is an isometry with closed range. `exists_predictable_limit` proves the strong slice limit lies in that range and pulls the convergence back to an actual u in `GaussianSourceClockIto.Domain T`. Its slices are exactly the constructed limitClass, hence are identified with the bounded recovery of the ACTUAL unmollified endpoint. Predictability of u is therefore proved through the original closed domain, not inferred from individual-time measurability.

The main result is `IBMRegularizedTimeLimit.exists_stochastic_reconstruction`. For EVERY Schwartz g, real shift a and finite nonnegative horizon T, there exist an ACTUAL source-Gaussian-L2-valued predictable horizon integrand u and a full source/clock L2 class c such that

    V_n,T -> u  STRONGLY in the ORIGINAL predictable time-L2 norm,
    C_K(wholeCorrection_n,T) -> c  STRONGLY in full joint L2,
    sourceCurry(zeroExtend(u)) = limitClass(actual unmollified endpoint recovery),
    C_K(endpointLimit_T) = actualSourceClockIto_T(u) + c.

Here K=P0+N_clock^(-1) is the SAME common injective clock-number smoothing from1098/1101. The wholeCorrection_n,T is the ORIGINAL independently verified boundary/local-time mass PLUS full curvature. The actual correction sequence's strong convergence is part of the theorem; c is not merely an unverified residual definition. The source-valued Itô integral is the previously constructed isometry on its original predictable domain. The endpointLimit has the previously verified actual source sections g(a+IBM_T)-g(a). Thus this is a genuine signed/source-valued stochastic reconstruction in a specified common weaker clock topology, with all source and clock sectors retained. It is not an expectation-level heat identity, finite-scale complex-noise representation, ordinary unregularized IBM Itô formula, or assertion that raw point observations have a classical clock Malliavin derivative.

Selective primary-source audit at this natural proof break: re-read the F1/F2/F3 statements on cached PDF page22, and the F2 statement on page19, of `ResearchSources/ibm/EJP2605-044RA0.pdf`, preserved SHA2565A91914A535AD19BDDF219D7A9AB9F8B5F20A52DD4EC6ED7333AA80B403182BE (read-only extraction cache `tmp/pdfs/stardust-ibm-1046/pages.json`). Open problem7.1 asks for a global cross-sector DUAL NORM with full correction convergence; it does not require the new global norm to equal the physical spatial H^(-1) topology used for its first-scenery-chaos theorem5.13. Its open claim includes higher source sectors and source0/positive clock sectors in ANY such topology. This exact wording changes the next audit target.

Correction to earlier continuation notes: comparison with physical spatial H^(-1) remains a useful separate question, but it must NOT be imposed as an extra F1 gate if the paper explicitly permits a different global dual norm. The current verified theorem supplies the analytic full-field convergence core for a concrete injective clock-number candidate. Before declaring F1 resolved or freezing IBM, explicitly audit/formalize its joint source/clock sector summability and rigorous dual-test-space interpretation, and state the concrete normalized mollifier-family scope. Do not substitute an unnecessarily stronger spatial-equivalence claim for the actual open problem, and do not claim the dual interpretation merely because K is bounded and injective.

Focused next mathematical audit: show the whole-field norm norm(C_K F) has the intended dual pairing on the clock-regular test image K(test), using actual self-adjointness and injectivity of K. Existing scalar projection self-adjointness and potential_inner, the actual product flip isometry and integral L2 pairing should suffice; avoid inventing a new Gaussian probability space or elaborate completion machinery unless necessary. Establish the actual joint source/clock chaos truncations, their commutation with K and their strong convergence. Whole smoothed-correction convergence plus uniformly bounded truncation operators should then give a genuine uniform eventual joint-sector tail bound. This would connect the proved actual stochastic limit directly to the manuscript's sum over(m,n), rather than inferring cross-sector summability from finitely many block tests. No such joint-tail/dual-pairing theorem is claimed in this checkpoint.

F3's actual closed dense intrinsic calculus remains proved. F2 keeps its concrete normalized bump-family scope. No IBM campaign freeze or successor transition is declared by this checkpoint. No claim about A(4), A(2), RH, or equivalence of Millennium problems is made.

Verification1102: direct slice, actual IBM slice and time-limit checks passed after repairing typed Lp/indicator and curry naturality elaboration. FINAL full root build passed5707 jobs, exit0. Root-wide transitive axiom audit passed31398 safe Foundation declarations allowing only `propext`, `Classical.choice`, `Quot.sound`. ALL37 new public definitions/abbreviations/theorems were printed and reviewed: actual source zero-extension isometry, original predictable domains, full source/clock factor order, AE-time rather than uniform pathwise identities, explicit singular majorant integrability, actual MemLp limit realization, strong N-cutoff versus n-mollifier convergence, closed isometry-range argument and the complete actual stochastic reconstruction statement. No sorry/admit or new axiom. Working manifest covers1653 Foundation/root Lean files. All107 archive hashes and43 Incoming files/42 distinct hashes match saved baselines; ym_ns_dictionary.tex remains8EC222C21FDB2D81D652E3CF553BE59EEA987F01AD3B1C54EEC91216111BC22E. ResearchSources and dependency pins unchanged. Evidence: `.lake/stardust-1102-full-build.log`, `.lake/stardust-1102-audit.log`, `.lake/stardust-1102-working-checkpoint.json`, `.lake/stardust-1102-archive-check.json`, `.lake/stardust-1102-inventory-check.json`. Draft logs are diagnostic only; final verification certifies the final root-imported source bytes.


## Verified discovery1103 — genuine common-clock dual norm, uniform joint chaos tails and raw fixed-sector limits

Continued from audited2d4d885279ecbf3ee31d79bcabc44af73aac06a5 (1102). The intervening queue-confirmation turn was read-only and made no mathematical progress. On resumption the previous build handle was missing and its saved log conclusively recorded a failed simplification in the new raw-clock-sector limit. The composition simplification was corrected, then the entire root was rebuilt successfully; no stale build was treated as evidence. Terminal checks on2026-10-19 include06:22:25,06:36:40,06:39:37,06:40:16,06:40:58 and06:41:20 America/New_York. IBM remains immediate. IBM -> A(4) -> A(2) -> final full multichannel and the October31 stopping date retain their gates.

Four new root modules: `GaussianClockSourceSpectral`, `IBMCommonClockDual`, `IBMCrossSectorDualClosure`, `IBMMollifierProfileAudit`. They resolve1102's exact dual-test interpretation and source/clock summability obligations for the verified concrete mollifier sequence. No new stochastic process or substitute probability space is introduced.

`GaussianClockSourceSpectral.sourceLift` acts on actual SOURCE values in the full outer-CLOCK/source-valued Gaussian L2 space; `source_clock_commute` proves that this action commutes with every lifted CLOCK operator by all continuous source-functional tests. Actual source truncations are contractions and converge strongly by Bochner dominated convergence. `jointTruncation_eq_sum` identifies actual rectangular partial sums with the explicit double sum of source/clock blocks. Joint truncations are contractions; `joint_tail_compare` bounds their error on f by twice norm(f-g) plus the separate source and clock tails of g. The actual common smoothing K=P0+N_clock^-1 commutes with these truncations. The two chaos labels are not interchangeable.

`IBMCommonClockDual` proves actual whole-field self-adjointness of K, reusing scalar projection/potential pairing and the actual product-L2 flip isometry. `smoothing_denseRange` proves its test image is dense in the original full joint L2 space using self-adjointness, verified injectivity and the closed orthogonal-complement theorem. Define the norm of a raw field F by norm(K F). Nonnegativity, definiteness, triangle inequality and absolute homogeneity are verified. Crucially `dual_bound`, `dual_attainment` and `dualNorm_le_iff` identify this norm with the genuine operator norm of

    K psi |-> inner(F,K psi),     test norm(K psi)=norm(psi).

Injectivity gives a unique test preimage; the test norm here is the pulled-back norm, not the ambient L2 norm of K psi. The exact extremizer is K F/norm(K F), with the zero case handled separately. `correction_dual_uniform` obtains uniform convergence over the entire unit test ball from1102's actual strong K-correction limit. The resulting limiting functional is inner(c,psi); it does not require c to lie in range(K), nor assert a raw L2 correction limit or equivalence with spatial white-noise-coordinate H^-1.

`IBMCrossSectorDualClosure.correction_uniform_rectangular_tail` proves, for the ORIGINAL full correction (including its separate origin/local-time term and full curvature), uniformly for late mollifiers and independently large source and clock cutoffs M,N,

    norm(K(C_n - sum_(m<=M,k<=N) block_(m,k) C_n)) -> 0.

This is genuine full cross-sector tail control in one common dual topology, not a finite-block computation or a first-source conditional expectation. `exists_cross_sector_dual_reconstruction` combines it with the ACTUAL original predictable-domain convergence V_n->u, actual full K C_n->c, and K endpointLimit=actualSourceClockIto(u)+c, retaining every source and clock sector. The stochastic identity reuses1102 rather than postulating an integral for a desired residual.

The additional `smoothed_clock_projection` proves clockP_k(K F)=weight(k) clockP_k(F), with weight(0)=1 and weight(k)=1/k for k>0. Consequently `raw_clock_projection_tendsto` proves ordinary full joint L2 convergence of every fixed clock projection of C_n, retaining ALL source sectors, to weight(k)^-1 clockP_k(c). `raw_block_tendsto` gives ordinary joint L2 convergence of each original (m,k) block to weight(k)^-1 block_(m,k)(c). This does not imply an unregularized sum over all clock sectors converges in L2, and does not contradict the paper's first-source aggregate L2 obstruction.

Selective primary-source audit read cached PDF pages3-4 and9, following1102's pages19/22 audit: `ResearchSources/ibm/EJP2605-044RA0.pdf`, SHA256 `5A91914A535AD19BDDF219D7A9AB9F8B5F20A52DD4EC6ED7333AA80B403182BE`. The paper fixes an arbitrary even nonnegative compact smooth mass-one profile rho and dilates it for all positive epsilon. Its condition(4.2) is a first-chaos nondegeneracy condition, not a prerequisite to our stronger all-Schwartz common-dual construction. F1 asks for a global cross-sector dual norm; it does not mandate equality with the first-sector physical H^-1 norm. No stronger artificial gate is imposed.

`IBMMollifierProfileAudit` proves that the actual previously used bump sequence has exactly one fixed profile: kernel_n(x)=epsilon_n^-1 kernel_0(x/epsilon_n), epsilon_n=1/(n+1)>0 tending to zero, with actual evenness and normalization inherited from the verified mollifier. Its proof uses exact ContDiffBump dilation and the actual integral change of variables. This identifies our sequence with a legitimate subsequence of the paper's continuum family, but DOES NOT establish an all-positive-epsilon limit or all-profile independence.

Precise next obligation: extend the actual kernel/curve and finite reflected-Ito bridge to continuum dilations, then reuse the established derivative, common-dual, native stochastic time-limit and joint-sector machinery. Generic whole-line convolution error estimates and C2/closed-source derivative theorems already exist for arbitrary compact kernels. Do not rebuild the solved stochastic limit or chaos framework, infer a continuum limit from one sequence, or substitute a stepwise sequence for the actual rho_epsilon family. F3's actual closed dense intrinsic calculus remains proved; F2 retains its verified concrete normalized bump scope. IBM is not frozen and no successor starts here.

Verification: pinned Lean4.34.1 full root build passed5711 jobs. Root axiom audit passed31479 safe Foundation declarations, with only propext, Classical.choice and Quot.sound transitively. ALL46 new public theorem/definition types were printed and reviewed, including native source/clock factor order, original correction versus K correction, independent tail quantifiers, and exact limit topology. No sorry/admit/new axiom was introduced. The working manifest covers1657 Foundation/root Lean files. All107 archived manuscript hashes and43 Incoming files/42 distinct hashes remain unchanged, including dictionary SHA256 `8EC222C21FDB2D81D652E3CF553BE59EEA987F01AD3B1C54EEC91216111BC22E`. ResearchSources, pinned dependencies, unrelated drafts and goal state remain unchanged. Exact-path Git checkpoint and private synchronization follow this verified ledger entry.
