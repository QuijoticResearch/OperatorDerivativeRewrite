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
