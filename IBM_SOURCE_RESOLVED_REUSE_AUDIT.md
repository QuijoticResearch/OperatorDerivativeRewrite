# Source-resolved IBM chaos: reuse within F1–F2

2026-10-18, discovery1049. This is a bounded manuscript/library comparison within the current Itô–Tanaka campaign. It does not open a separate chaos campaign. Manuscript assertions remain unverified unless a precise Lean theorem below covers them.

## Source availability and integrity

At initial inspection, the requested title matched `ResearchSources/ibm/main.tex`, title57–58, abstract65–85. The same wrapper remains available at `C:/Operator/ibm/main.tex`, with the matching original hash below. It includes nine section files at90–98: introduction, setup, product_chaos, operator_derivatives, occupation_functional, first_order_split, mixed_chaos, pde_connection, conclusion. All nine are absent from the preserved archive and original IBM directory. No complete manuscript-specific Lean formalization was located in the searched workspace or that original IBM directory. This is a retrieval limitation, not an assertion that such a formalization exists nowhere. A path clarification was requested while the available-source audit continued.

**Observed concurrent source change:** the final integrity check at terminal2026-10-18T16:07:45-04:00 detected that `ResearchSources/ibm/main.tex` had changed from wrapper hash897F68ED… to SHA256 `314D3B33B211ADE564F918C6E2EC363CCEE0C8C9F8D7209B8ECAD8105623283F`, title *An Energy-First Reorganization of Stochastic Calculus*. No command in this work writes to ResearchSources. The replacement was not restored, edited or treated as the missing chaos manuscript. The source-resolved review is tied to the inspected wrapper version still present at C:/Operator/ibm/main.tex. The companion hashes remained unchanged. Source integrity is therefore reported as an observed external version transition, not falsely reported as an unchanged whole archive.

| Read-only source | SHA-256 | Selected relevance |
|---|---|---|
| `C:/Operator/ibm/main.tex` (also the initially inspected archive version) | `897F68ED4BBF3445928FE0AEA0833442E73C475E230D6DBDD61E0D56908C0D45` | Title, abstract, occupation factorization and claimed source projection; missing body sections. Current archive main.tex has the different framework hash documented above. |
| `ResearchSources/ibm/variance.tex` | `B9FDC0B78B8B2E75C812728A1088CD72C8B96E5B138B58DCC01DDC71B1E63459` | Setup155–195, explicit clock kernels199–308, parity310–337, numerical mixed-kernel cross-check470 onward. This is the available numerical companion, not a substitute for missing proofs in main.tex. |
| `ResearchSources/ibm/BidegreeAtlas.tex` | `409FFE56EDB47DF23DAEEA788CEEC24E1C7ED9FF657BDCB6914708F8FA535D4E` | Definitions345–370 and fixed-scale decomposition375–406; correction observable differs from occupation functional. |

These are outside Incoming. Its separate43-file/42-hash inventory remains unchanged. No source was modified, renamed, deleted or staged. No empirical variance percentage is treated as a proved estimate.

## Direct theorem reuse and precise gaps

| Requested component | Reusable verified results | Missing identification |
|---|---|---|
| Source-resolved projections ((m,n)) | `GaussianNumberSectors.projection`, `projection_norm_le`, `projection_idempotent`, `sectors_orthogonal`; `GaussianChaosDecomposition.projection_hasSum`, `projection_hasSum_norm_sq`; actual product/Bochner isometry `ProductL2Curry.curryIsometry`. | The verified one-factor sectors are not themselves a manuscript-specific two-factor projection theorem. Assemble/identify the two actions on the actual joint product, prove commutation and match the manuscript normalization before calling them its ((m,n)) projections. This comparison does not construct that general infrastructure. |
| Actual low scenery chaos kernels of the correction | `IBMCubicFirstChaos.projection_correction`, `IBMSceneryCubicProjection.spatialCorrection_projection` and `variance_geometry_projection`; `IBMClockCubicTimeProjection.time_integrated_projection`. | These identify actual polynomial correction source vectors, including the origin layer, rather than arbitrary occupation-test kernels. Map spectral Hilbert vectors to the physical oriented-indicator white-noise kernels before importing explicit spatial kernel formulas. |
| Joint random/time domains and recovery | `IBMClockCubicJointTimeL2`, `IBMClockCubicBochnerRecovery.clockTarget_energy`, `clockPrimitive_graph`, `clockPrimitive_minimal_norm`; `BochnerClosedOperator` and `GaussianBochnerDivergenceRecovery`. | These are genuine fixed-mollifier cubic results. They give neither uniform shrinking-mollifier estimates nor all Schwartz correction sectors. |
| Occupation-time factorization | `BoundedPathOccupation.schwartzOccupation`, its norm bound and `occupation_fubini`; constructed scenery/clock paths and their actual IBM composition. | Existing generic bounded path occupation does not supply a spatial clock local-time field L_T^x with joint measurability, a Bochner-L² spatial integral and the occupation density identity. The constructed continuous origin Tanaka mass is not already that full spatial field. A pushforward occupation measure can express factorization without a density, but does not give the explicit local-time chaos kernels. |
| Projection through an integral | Existing bounded CLM Bochner integral commutation; actual `IBMClockCubicTimeProjection` time projection. | A spatial source-projection formula needs actual integrability, e.g. integral over x of the product of the two source L² norms finite, plus equality with the actual occupation functional. Formal multiplication of arbitrary L² variables on the same source is insufficient. Independence makes separated products legitimate, but the spatial integral still needs its own bound. |
| F2 boundary functional | `IBMVarianceClockGeometry.variance_second`, `IBMBoundaryClockLimit.clockMass_identity`, `clockMass_coeFn`, `path_integral_tendsto`. | The original mollifier clock integral already converges in actual random L² to the origin Tanaka mass. Identify the manuscript's general Schwartz residual with its weighted version and a vanishing shrinking-layer remainder. The occupation manuscript alone does not discharge this coefficient calculation. |
| F1 cross-sector limit | Fixed-observable Parseval and actual first-chaos/polynomial source vectors; concrete necessary kernel bounds in `IBMSourcePrimitiveObstruction`. | Finite-mollifier decomposition is not uniform tail control as the mollifier vanishes. Need a specified common dual norm, genuine sector kernel identifications, each required sector limit, and a uniform summable tail bound. The source primitive obstruction module explicitly does not prove the missing actual blow-up estimate. |

## Convention test: unreflected and reflected clocks

The source-resolved manuscript defines Z_t=X_(Y_t); the current Itô–Tanaka construction uses Z_t=X_(|Y_t|). Matching one-time laws does not identify their two-time or mixed kernels. The new Lean test `IBMBoundaryChaosReuse.scenery_reflection_covariance_test` uses actual verified source covariances:

Cov_X(X_1,X_(-1))=0, whereas Cov_X(X_|1|,X_|-1|)=1.

Thus a substitution of the reflected clock into an unreflected mixed kernel without rederivation fails even at the covariance level. For r>0 the reflected occupation density would be L_T^r(Y)+L_T^(-r)(Y). Its positive-side trace at0 is2L_T^0(Y); the value assigned at the single spatial point0 does not change a Lebesgue occupation integral, but this trace matters in boundary distribution identities.

The companion's candidate first-clock kernel is

k_T(x,s)=erf(x/sqrt(2s))-erf(x/sqrt(2T)), 0<s<T.

It is odd in x. The reflected candidate is consequently k_T(r,s)+k_T(-r,s)=0. For example k_1(1,1/4)≈0.27181024397, while the reflected sum is zero. Tests at three positive points agree with this cancellation. This is a necessary analytic kernel convention check, not a newly verified general operator parity theorem. In particular, the unreflected manuscript's nonzero mixed((1,1)) occupation sector cannot be copied into the reflected problem. A full reflected-chaos parity statement is not asserted as a new Lean result here.

## Concrete second-clock boundary kernel test

The available companion199–308 proposes the symmetric second-clock local-time kernel

K_T(s1,s2;x)=psi_T(x)-psi_max(s1,s2)(x), psi_s(x)=(2pi s)^(-1/2)exp(-x²/(2s)).

At x=0 the max-time reduction gives norm²=2 integral_0^T s(psi_T(0)-psi_s(0))² ds. Substituting s=T u² reduces the dimensionless part to integral_0^1(2u³-4u²+2u)du=1/6. Thus the candidate has norm²=T/(6pi), and its candidate I₂ variance under the factorial isometry is T/(3pi), not zero. The apparent s^(-1/2) singularity does not exclude this kernel from L²: the triangular area density cancels it. This is an explicit nontrivial clock-sector target for the verified F2 boundary limit.

The rational arithmetic and first-clock numeric checks are independently reproducible in ignored `.lake/stardust-1049-kernel-tests.py`/`.json`. They are diagnostics, not Lean identification of this K_T with projection2 of the actual Tanaka mass. That exact stochastic-integral/kernel identification remains open and is a productive narrow test if needed by F2; it does not require starting a separate all-chaos program.

## New verified reuse: the actual F2 limit in every clock sector

`Foundation/IBMBoundaryChaosReuse.lean` directly applies the existing continuous Gaussian number-sector projections to1048's actual clock mass B_j(T)=integral_0^T rho_j(|Y_s|)ds. For every fixed clock sector n and horizon T it proves

Pi_n B_j(T) → Pi_n L_T^0(Y) in L²,

and the quantitative contraction error bound by ‖B_j(T)-L_T^0(Y)‖. It proves projection commutation with the actual Bochner curvature time integral, retaining its proved integrability. It reuses the existing complete decomposition and Parseval for B_j(T) and for its actual limit. No new Gaussian chaos definition, abstract joint product theory or spatial local-time field is introduced.

This supplies actual fixed-clock-sector convergence for the unweighted F2 boundary part and shows that it is available beyond its mean. It is not a proof of F1's full correction limit, the general weighted F2 residual, a physical mixed-kernel identification, or an exchange of an infinite sector sum with the mollifier limit.

## Immediate campaign consequence

Keep the next main proof on F2: derive and bound the actual averaged Schwartz coefficients using the now verified boundary bracket and unweighted clock mass. Use existing bounded projection commutation whenever a fixed clock sector is needed. Reserve the explicit second-clock origin kernel as a concrete normalization test. Defer general joint sector infrastructure and cross-sector summability until an actual estimate requires them. Review the missing section files or manuscript-specific Lean files if their path becomes available; do not claim their proofs were audited from the wrapper.
