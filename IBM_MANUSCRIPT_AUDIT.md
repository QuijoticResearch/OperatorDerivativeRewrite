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
