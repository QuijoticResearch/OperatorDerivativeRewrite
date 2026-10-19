# Paper 1: manuscript–Lean crosswalk

Audit date: 2026-10-12. Verified rewrite HEAD: `582ee395185c1a2a4d42654d9a3b6ac6f67853a9`.

This crosswalk inspects actual statements and proof bodies. A proved implication with an unsuitable or conclusion-equivalent hypothesis is not counted as a formalization of the manuscript's intended mathematical claim. No Lean sources, manuscripts, dependency pins, or pre-existing untracked documents were modified for this audit.

## Sources, notation, and verification scope

| Key | Exact file path |
|---|---|
| Paper | `C:\Operator\OperatorDerivative.tex` |
| Original | `C:\Operator\OperatorDerivative.lean` |
| Prefix | `C:\OperatorDerivativeRewrite\Legacy\GaussianLogSobolevSection.lean` |
| Integrated | `C:\OperatorDerivativeRewrite\Legacy\OperatorDerivativeIntegrated.lean` |
| Root | `C:\OperatorDerivativeRewrite\OperatorDerivativeRewrite.lean` |
| F/name | `C:\OperatorDerivativeRewrite\Foundation\name` |

Line references below are one-based in the audited files. Original-line references refer to the original, not the offset integration copy. For each Foundation row, the `F/` path key expands to the exact absolute directory above. Namespace-qualified declaration names are given explicitly.

The original and integration copies are different verification targets:

1. The default project imports Foundation modules, not either Legacy copy. The complete Lake build passed, **4,030 jobs**.
2. `lake env lean Foundation/AxiomAudit.lean` passed. Its **1,213 declarations** have transitive axiom union exactly `propext`, `Classical.choice`, and `Quot.sound`. There was no `sorryAx`.
3. `lake env lean Legacy/GaussianLogSobolevSection.lean` passed. This file contains the original prefix through `log_sobolev_1d`, with the proved Gaussian LSI adapter. Thus early algebraic legacy declarations really do compile under their stated interface assumptions. They are not thereby concrete stochastic-calculus theorems.
4. Directly checking `C:\Operator\OperatorDerivative.lean` failed at **3156, 3272, 3300, 3609, 3630, 3696, and 4456**. The error at 3272 is the false general L² multiplication claim; other failures include API/proof elaboration problems. No successful whole-file verification is claimed.
5. The full integration copy is deliberately outside default imports. Its creation at commit `1972449856bc31ceadf00e22b0a308cf5e87be92` replaced only the Gaussian axiom and added the import; it did not repair the unrelated legacy development. This audit reran the original and compiling prefix, not a fresh full-integrated-file check.

Commands used the installed pinned executable `C:\Users\ramir\.elan\toolchains\leanprover--lean4---v4.34.1\bin\lake.exe`; Mathlib lock revision remains `d13f23b723b8a846827a245b89c10fc7d3f11612`.

Temporary logs: `%TEMP%\paper1-audit-axioms.log`, `paper1-legacy-prefix.log`, `paper1-original-compile.log`, and `paper1-legacy-types.log`. The last log records actual `#check @...` elaboration and `#print axioms` for 18 key legacy-prefix declarations. All 18 use only the standard axioms listed above. Explicit structure fields and theorem arguments are hypotheses, not custom axioms, and therefore do not appear as nonstandard dependencies in `#print axioms`.

Status terms:

- **Exact**: same mathematics and appropriate hypotheses, modulo notation.
- **Restricted/related**: a valid narrower result, or a different related result; not evidence for the larger claim.
- **Conditional legacy**: genuinely checked implication through legacy structures whose assumptions must be examined separately.
- **Absent**: no matching proved declaration found in the audited project.
- **Invalid claimed match**: theorem name or commentary materially overstates its elaborated type, or its proposed concrete hypotheses fail.

## Main theorems A–F

| Paper claim | Exact Lean candidates and locations | Comparison and missing obligations |
|---|---|---|
| A, `thmA` (Paper:91), `thm:CO` (327) | `UnboundedEnergySpace.clark_ocone_unbounded`, Original:226; compiling Prefix counterpart | **Conditional legacy, domain-restricted.** Requires `F ∈ U.D.domain`, projected derivative in `dom δ`, predictable isometry, and PRP. The overview's all-L² use of `D=δ*` lacks its required domain. The structure also carries irrelevant false all-L² multiplication assumptions. No clean Foundation representation theorem or Brownian predictable realization currently matches it. |
| A without PRP; `prop:GKW` (379), `prop:var` (409) | `UnboundedEnergySpace.gkw_orthogonality_unbounded`, Original:289; `UnboundedEnergySpace.variance_identity_unbounded`, Original:314 | Orthogonality is verified for domain elements under isometry. It is not an explicit construction of the closed stable-subspace projection. Variance additionally takes the Clark–Ocone equality as `hCO`; it does not derive that equality inside this theorem. |
| B, `thmB` (99), `thm:cylred` (710) | `UnboundedEnergySpace.ibp_rep_unbounded`:378; `UnboundedEnergySpace.cylindrical_leibniz_unbounded`:392; `UnboundedEnergySpace.cylindrical_implies_leibniz_unbounded`:407; bounded analogues `EnergySpace.ibp_rep`:1455, `EnergySpace.cylindrical_leibniz_on_class`:1468, `EnergySpace.cylindrical_implies_leibniz`:1482 | Core algebraic implications are checked given IBP and coordinate Leibniz. The full extension is supplied by `leibniz_closure`, not proved. `cyl_dense` does not even assert convergence. The rewrite supplies genuine polynomial Gaussian core results, detailed below, but no general C∞ cylindrical chain/closure theorem. |
| C, `thmC` (107), `thm:ito` (850), `thm:multi_ito` (903) | `UnboundedEnergySpace.operator_ito_decomposition_unbounded`, Original:520; `ito_formula_bounded`:2021; `ito_formula_with_clark_ocone`:2046; `ito_formula_time_indexed`:2118; `ito_formula_integrated`:2141 | **Invalid claimed match to a path/time Itô theorem.** These are static divergence product identities and their ordinary Bochner integrals. They do not prove time-increment limits, the actual quadratic-variation coefficient 1/2, or the displayed formula for `φ(Y_t)−φ(Y_0)`. The multivariate stochastic Itô statement is absent. |
| D, `thmD` (132), `thm:leib_sv` (1006), `prop:DM` (983) | `UnboundedEnergySpace.UnboundedStochVolAssumption`, Original:546; `UnboundedEnergySpace.leibniz_stochastic_volatility_unbounded`:560 | **Conditional algebraic transfer.** The structure assumes Brownian Leibniz and the transfer `D_M F=(1/σ)D_W F`. No Brownian motion, σ-process, weighted random energy space, stochastic-integral domain, or analytic transfer theorem is constructed. |
| E, `thmE` (140), `thm:obstr` (1116) | `EnergySpace.RepresentersDeterministic`:1496; `EnergySpace.representer_rigidity`:1515; `EnergySpace.stoch_vol_obstruction`:1590 | **Invalid claimed match.** `RepresentersDeterministic` factors a pairing with every random field, which is not ordinary deterministic representers. The obstruction assumes false multiplicative cancellation. It does not prove deterministic volatility. The intended central theorem needs a separate valid stochastic argument; no rewrite theorem replaces it. |
| F, `thmF` (144), `thm:gub` (570) | `UnboundedEnergySpace.gubinelli_base_invariance`, Original:595; `EnergySpace.controlled_pythagoras`:1751 | Only an algebraic cross-multiplication identity under supplied transfer formulas, plus an orthogonality/Pythagorean calculation. No time-indexed controlled expansion or `min(4H,2H+1)` remainder estimate is formalized. No concrete fBM construction is imported. |

## Supporting manuscript claims, including duplicate labels

| Paper labels and source lines | Crosswalk |
|---|---|
| `def:energy` 208; `rem:bounded` 216; `def:pred_proj` 231; `rem:filtration` 237 | Legacy `UnboundedEnergySpace` (Original:101), `EnergySpace` (735). These are abstract records, not stochastic-integral constructions. `δ_dense` and orthogonal-projection fields are explicit; full-L² multiplication fields are unsuitable for the intended non-atomic models. `dom_D_dense` is assumed in the unbounded record. |
| `lem:adjoint` 244; `def:opderiv` 254; `eq:adj` 256; `rem:nature` 262; `rem:choices` 266 | **Exact domain-aware support:** `OperatorDerivativeRewrite.Foundation.operatorDerivative` (F/Adjoint.lean:20), `OperatorDerivativeRewrite.Foundation.operatorDerivative_isClosed` (24), and `OperatorDerivativeRewrite.Foundation.operatorDerivative_adjoint_identity` (30). They take a densely defined real Hilbert partial operator, not a process. Adjointness is asserted only on both actual domains. |
| `prop:intrinsic` 279 | Linearity is built into `LinearPMap`; closedness and limit-domain membership are verified by `OperatorDerivativeRewrite.Foundation.closed_graph_limit` (F/OperatorDomains.lean:40). Bounded legacy constants/uniqueness are `EnergySpace.D_const` (Original:817), `EnergySpace.D_unique` (825). `OperatorDerivativeRewrite.Foundation.one_mem_adjoint_domain` (F/MultiplierCore.lean:242) proves constant-domain membership from actual centering; no manuscript all-domain algebra is needed. |
| `rem:vs_malliavin` 270; `cond:iso` 315; `eq:isometry` 317; `rem:CO_content` 368; `rem:Pi_trivial` 372; `rem:GKW_interp` 402 | The distinction between the adjoint of the predictable Itô isometry and the full Malliavin derivative is essential. The latter is unbounded. A successful abstract adjoint proof does not identify them. Theorem A rows above give the available conditional representation results. |
| `ex:mart_energy` 220; `ex:brownian` 427; `ex:gen_mart` 468 | No concrete Brownian/predictable construction in Foundation. `brownianEnergySpace` (Original:3466) accepts the divergence and incompatible universal pointwise L² operations as arguments. `IsonormalProcess` (2921) is a deterministic-direction Gaussian map interface, not a predictable Itô integral. |
| `ex:poiss_energy` 224; `ex:poisson` 435; `prop:poisson_explicit` 446; `eq:poisson_CO` 437; `eq:add_a_point` 442 | Rewrite gives a genuine **one-site** Poisson law, difference/divergence, graph cores, mutual adjoints, multiplier and jump-defect identities. It does not supply a Poisson random measure on time, predictable representation, or the paper's time-indexed Clark–Ocone formula. Exact one-site declarations are listed below. |
| `def:volterra` 486; `def:CM` 490; `def:isonormal` 494; `eq:malliavin_deriv` 501 | Genuine countable Gaussian/ℓ² isonormal construction and finite-family polynomial derivatives exist in Foundation; see Gaussian table below. No Volterra kernel transfer, path process, or abstract Cameron–Martin completion identification is proved. Legacy `EnergySpace.GaussianVolterra` (Original:1649) supplies a cylindrical interface rather than deriving it from a kernel. |
| `lem:meas_pres` 506; `cor:adapted_mall` 514 | **Absent** as Brownian filtration results. Finite Gaussian coordinate projections are not the stated time-adaptedness theorem. Pointwise-in-time manuscript formulations also need representatives/joint-measurability and a.e. qualification. |
| `def:adapted` 524; `def:gauss_pred` 528; `lem:rkhs_cond` 532 | Abstract finite-sector isometries/projections are proved in Foundation, but no equality with the paper's Gaussian time-predictable projection or conditional expectation on the process filtration is established. |
| `thm:fact_fbm` 546; `eq:fact_fbm` 548; `rem:honest_gauss` 564 | **Absent** as an fBM theorem. It cannot be inferred from the countable Gaussian Hilbert adjoints without the process/filtration/integral transfer and correct projection. |
| `rem:gub_scalar` 586; `def:DU` 597; `prop:volterra_verif` 606; `cor:DX_process` 623 | No kernel estimates, Volterra integral construction, or verification of these process assumptions found in Foundation. `EnergySpace.leibniz_gaussian` (Original:1659) invokes a supplied cylindrical structure. |
| `def:normalized_CM` 636; `eq:normalization` 638; `rem:normalization` 644; `lem:bracket_fbm` 648 | **Absent.** No time-dependent normalization/covariance bracket calculation is proved by the static adjoint modules. |
| `cond:leibniz` 669; `thm:equiv` 673 | `EnergySpace.leibniz_iff_product_rule` (Original:1133) is checked under its whole-space algebra; `EnergySpace.chain_rule_sq` (1218), `EnergySpace.chain_rule_pow` (1229) prove algebraic polynomial consequences. `EnergySpace.chain_rule_from_density` (1357) assumes continuity and density of a supplied defect. This does not prove smooth functional calculus under the manuscript's exact hypotheses. The proof's globally uniform polynomial C¹ approximation claim is invalid, and `xy` is not in `C_b^∞`. |
| `def:cyl` 702; `eq:IBP_abstract` 704; `rem:cyl_meaning` 730 | Genuine polynomial Gaussian cylinders are verified, including actual differentiation and representation independence. The general legacy structures instead supply coordinate derivative data, IBP, and closure. Their same-name match is only conditional, not a discharge of the definition for a process. |
| `thm:leib_gauss` 738; `prop:indep` 751 | `EnergySpace.leibniz_fBM` (Original:1830) ignores its `isFBM` premise and extracts the supplied cylindrical closure. Rewrite Poisson defects supply one concrete non-Leibniz example, but do not establish the paper's two time-process examples or its asserted fBM isometry failure under the precise projection. |
| `def:bracket` 770; `def:ito_proc` 776 | Legacy `EnergySpace.intrinsic_bracket` (Original:1996) is `pip(DY,ΠDY)`, not the asserted time integral of an instantaneous coefficient. `ItoProcess` (2081) stores a decomposition but its theorem does not use that decomposition. |
| `lem:prod_rule` 782; `prop:domain` 793; `rem:domain` 809 | `UnboundedEnergySpace.leibniz_implies_product_rule_unbounded` (Original:433) assumes the product is already in `dom δ`. The rewrite's multiplier commutator theorem proves a real restricted domain-preservation implication, not the full manuscript criterion for every proposed F,u. |
| `lem:orth` 813 | `orthogonal_projection_identity` (Original:2668) is the correct elementary Hilbert statement. It is outside the compiling Prefix and the complete Original fails elsewhere; the identity also follows directly from Mathlib projection theory. It cannot turn a static bracket into quadratic variation. |
| `lem:skor_iso` 826; `eq:skor_iso` 828; `rem:skor_scope` 843 | **Absent.** None of the Foundation full adjoint/core results proves the manuscript's short-time isometry remainder or its claimed Hilbert–Schmidt correction. Actual domain/derivative assumptions and the covariance time scaling must be established separately. |
| `rem:ito_status` 895; `rem:prod_role` 899; `ex:fbm_bracket_ex` 935; `ssec:ex_fbm` 1259; `eq:fbm_ito` 1268; `eq:fbm_final` 1278 | No corresponding genuine stochastic-time Itô derivation in Foundation. Static Stein/IBP does not by itself prove these formulas. |
| `ass:sv` 947; `def:HM_pred` 964; `def:HM_ext` 968; `rem:compat` 976; `eq:DM` 985; `eq:leib_sv` 1008 | No formal weighted random-volatility transport theorem. Legacy `UnboundedEnergySpace.transfer_preserves_pip` (Original:581) uses the supplied transfer formula algebraically. |
| `prop:rand_cyl` 1032; `eq:kappa` 1034; `rem:density_cyl` 1053; `rem:mechanism` 1057; `rem:two_ops` 1061 | No actual stochastic derivative of `M_t`, random representers, or M-cylinder graph-density theorem in Foundation. Genuine Gaussian polynomial density does not imply these random-coordinate assertions. |
| `lem:mall_ito` 1079; `eq:mall_ito` 1083; obstruction equations 1124–1156; `rem:obstr_strength` 1168; `rem:obstr_extended` 1172; `rem:obstr_interp` 1176; `eq:DMT` 1296 | No concrete formal stochastic-integral differentiation/isometry argument for volatility rigidity. The checked legacy obstruction instead assumes false `hcancel`; see below. These are central outstanding obligations, not replaced by Banach C6. |
| `conj:wild` 1233; `sec:open` 1312 | Open questions, not theorems. The one-site Poisson quadratic defect is related, but provides no example of a continuous-process wild Leibniz defect. |
| `rem:concrete_ito` 115; `eq:ito_covariance` 123; `sec:lean` 1335; `tab:lean_map` 1434 | Legacy static `ito_adjoint_level1/2` and `ito_correction_concrete` assume the unsuitable `SteinLemma` interface. Rewrite genuine polynomial Gaussian Stein and bounded-C¹ real Stein are valid replacements within their scopes. The paper's formalization summary, one-axiom count, chain-discharge and Brownian-instance claims are not accurate descriptions of current verification. |

## Strongest verified Foundation declarations available for repairs

### Domains, products, and adjoints

| Exact declaration | Location | Actual assumptions and conclusion |
|---|---|---|
| `OperatorDerivativeRewrite.Foundation.operatorDerivative_isClosed` | F/Adjoint.lean:24 | Real Hilbert spaces with the file's completeness instances; δ densely defined; actual δ* is closed. |
| `OperatorDerivativeRewrite.Foundation.operatorDerivative_adjoint_identity` | F/Adjoint.lean:30 | δ densely defined; F in actual δ* domain and u in actual δ domain; actual Hilbert pairing identity. |
| `OperatorDerivativeRewrite.Foundation.mem_adjoint_domain_iff_representable` | F/OperatorDomains.lean:23 | Dense δ domain, complete vector Hilbert space; F belongs to δ* iff a vector represents pairing against every u in dom δ. |
| `OperatorDerivativeRewrite.Foundation.bounded_adjoint_domain` | F/OperatorDomains.lean:33 | Actual bounded everywhere continuous linear δ; partial adjoint domain is top. |
| `OperatorDerivativeRewrite.Foundation.closed_graph_limit` | F/OperatorDomains.lean:40 | Closed actual partial D; inputs in dom D converge to f and their actual outputs converge to v; concludes f in dom D and Df=v. |
| `OperatorDerivativeRewrite.Foundation.fourthMomentDomain` / `OperatorDerivativeRewrite.Foundation.fourthMomentDomain_product_terms` | F/OperatorDomains.lean:58,63 | Actual D-domain elements whose values and derivatives are L⁴; product and proposed Leibniz terms are L². **No product-domain membership or Leibniz identity is asserted.** |
| `OperatorDerivativeRewrite.Foundation.mul_L2_integrable` / `OperatorDerivativeRewrite.Foundation.inner_L2_integrable` | F/LpProducts.lean:103,106 | L²×L²→L¹ for scalar products/Hilbert inner products. |
| `OperatorDerivativeRewrite.Foundation.mul_L4_memLp_two` / `OperatorDerivativeRewrite.Foundation.smul_L4_memLp_two` / `OperatorDerivativeRewrite.Foundation.inner_L4_memLp_two` | F/LpProducts.lean:111,114,118 | Actual scalar/vector L⁴×L⁴→L². |
| `OperatorDerivativeRewrite.Foundation.mul_Linfty_L2_memLp_two` / `OperatorDerivativeRewrite.Foundation.smul_Linfty_L2_memLp_two` / `OperatorDerivativeRewrite.Foundation.inner_Linfty_L2_memLp_two` | F/LpProducts.lean:121,125,129 | Actual L∞×L²→L² estimates. |
| `OperatorDerivativeRewrite.Foundation.IsDivergenceMultiplier` | F/MultiplierCore.lean:92 | A definition requiring bounded f, preservation of the given divergence domain, and an actual bounded commutator R. Those are hypotheses to establish for a concrete multiplier, not automatic consequences of boundedness. |
| `OperatorDerivativeRewrite.Foundation.IsDivergenceMultiplier.mul` / `OperatorDerivativeRewrite.Foundation.boundedMultiplierAlgebra` | F/MultiplierCore.lean:135,158 | Actual closure of admissible multipliers under products, with explicitly composed commutator. No density assumption. |
| `OperatorDerivativeRewrite.Foundation.IsDivergenceMultiplier.preserves_adjoint_domain` | F/MultiplierCore.lean:204 | Dense δ, complete H, admissible bounded multiplier; multiplication preserves actual δ* domain by constructing the representer `M_f δ*F+R*F`. |
| `OperatorDerivativeRewrite.Foundation.closedOperator_adjoint_adjoint_eq` / `OperatorDerivativeRewrite.Foundation.closableOperator_adjoint_adjoint_eq_closure` | F/AdjointBidual.lean:15,47 | Complete real Hilbert spaces; closed/closable T, dense T domain, **explicitly dense T* domain**; T**=T or closure T. No graph-core equality is assumed. |

### Genuine Gaussian model and calculus

The model is `SampleSpace = ℕ → ℝ`, product of standard real Gaussian laws, and `CoefficientSpace = ℓ²(ℕ)`. It supports arbitrary finite families of coefficient vectors. It is not a constructed Brownian path/filtration realization.

| Exact declaration | Location | Proved scope |
|---|---|---|
| `OperatorDerivativeRewrite.Foundation.InfiniteGaussian.gaussianProduct` | F/InfiniteGaussianProduct.lean:17 | Actual countable Gaussian product probability measure. |
| `OperatorDerivativeRewrite.Foundation.InfiniteGaussian.firstChaos_law` | F/InfiniteGaussianLaw.lean:119 | Actual W(h) has centered Gaussian law of variance ‖h‖². |
| `OperatorDerivativeRewrite.Foundation.InfiniteGaussian.isonormalCylinder` / `OperatorDerivativeRewrite.Foundation.InfiniteGaussian.isonormalCylinderGradient` | F/InfiniteGaussianCylinders.lean:14,19 | Polynomial evaluations and gradients using **actual polynomial partial derivatives**, arbitrary finite possibly dependent directions. |
| `OperatorDerivativeRewrite.Foundation.InfiniteGaussian.isonormalCylinder_memLp` / `OperatorDerivativeRewrite.Foundation.InfiniteGaussian.isonormalCylinderGradient_memLp` | F/InfiniteGaussianCylinders.lean:49,61 | All finite moments, proved from Gaussian laws and Hölder. |
| `OperatorDerivativeRewrite.Foundation.InfiniteGaussian.isonormalCylinderShift_hasFDerivAt` | F/InfiniteGaussianCylinders.lean:127 | Actual Fréchet derivative at zero of the affine-coordinate polynomial along Hilbert perturbations equals inner product with the constructed gradient. No sample-space translation theorem is asserted. |
| `OperatorDerivativeRewrite.Foundation.InfiniteGaussian.isonormalCylinderGradientL2_representation_independent` | F/InfiniteGaussianRepresentation.lean:83 | Equal scalar L² cylinders imply equal gradient L² classes for arbitrary finite representations, including dependent directions; proof uses their common finite Hilbert span. |
| `OperatorDerivativeRewrite.Foundation.InfiniteGaussian.polynomialDerivative` / `OperatorDerivativeRewrite.Foundation.InfiniteGaussian.polynomialCylindricalDomain_dense` / `OperatorDerivativeRewrite.Foundation.InfiniteGaussian.polynomialDerivative_on_cylinder` | F/InfiniteGaussianDerivative.lean:167,175,180 | Actual linear derivative on a dense scalar L² subspace, agreeing with every genuine polynomial representation. |
| `OperatorDerivativeRewrite.Foundation.InfiniteGaussian.polynomialProductL2_mem_domain` / `OperatorDerivativeRewrite.Foundation.InfiniteGaussian.polynomialDerivative_product` | F/InfiniteGaussianPolynomialProducts.lean:70,100 | Product closure and Leibniz for the genuine polynomial core. Product integrability is proved; neither theorem claims the full closed domain is an algebra. |
| `OperatorDerivativeRewrite.Foundation.InfiniteGaussian.isonormalCylinder_stein` / `OperatorDerivativeRewrite.Foundation.InfiniteGaussian.polynomialDerivative_stein` | F/InfiniteGaussianIBP.lean:12,58 | Genuine directional Gaussian Stein identity for arbitrary finite polynomial cylinders and for actual polynomial-domain classes. |
| `OperatorDerivativeRewrite.Foundation.InfiniteGaussian.rankDivergence` / `OperatorDerivativeRewrite.Foundation.InfiniteGaussian.polynomialDerivative_rank_integration_by_parts` | F/InfiniteGaussianIBP.lean:99,109 | δ₀(Gh)=G W(h)−⟨DG,h⟩ and genuine integrable rank-one IBP. |
| `OperatorDerivativeRewrite.Foundation.InfiniteGaussian.cylindricalVectorDomain_dense` | F/InfiniteGaussianVectorCore.lean:65 | Actual finite-rank polynomial fields are ambient L²-dense. This theorem alone is not graph density. |
| `OperatorDerivativeRewrite.Foundation.InfiniteGaussian.cylindricalDerivative` / `OperatorDerivativeRewrite.Foundation.InfiniteGaussian.cylindricalDivergence` | F/InfiniteGaussianOperators.lean:12,49 | Actual partial linear operators D₀ and δ₀. The divergence's graph is proved single-valued using IBP and scalar density. |
| `OperatorDerivativeRewrite.Foundation.InfiniteGaussian.cylindricalDerivative_formalAdjoint` / `OperatorDerivativeRewrite.Foundation.InfiniteGaussian.cylindricalDerivative_isClosable` / `OperatorDerivativeRewrite.Foundation.InfiniteGaussian.cylindricalDivergence_isClosable` | F/InfiniteGaussianOperators.lean:85,103,109 | Actual IBP, dense domains, and closability; no assumed essential adjointness. |
| `OperatorDerivativeRewrite.Foundation.InfiniteGaussian.closedCylindricalDerivative` / `OperatorDerivativeRewrite.Foundation.InfiniteGaussian.hilbertDivergence` | F/InfiniteGaussianOperators.lean:115,118 | D=closure D₀ and δ=D*, as partial operators. |
| `OperatorDerivativeRewrite.Foundation.InfiniteGaussian.hilbertDivergence_mem_iff` | F/InfiniteGaussianOperators.lean:156 | Exact weak-divergence domain, via an actual scalar L² representer against every element of dom D. |
| `OperatorDerivativeRewrite.Foundation.InfiniteGaussian.cylindricalDivergence_representation_independent` / `OperatorDerivativeRewrite.Foundation.InfiniteGaussian.cylindricalDivergence_field_apply` | F/InfiniteGaussianOperators.lean:193,207 | Equality of vector fields forces equality of finite-rank divergence expressions; actual values on the exact finite-rank domain. |
| `OperatorDerivativeRewrite.Foundation.InfiniteGaussian.cylindricalField_integration_by_parts` / `OperatorDerivativeRewrite.Foundation.InfiniteGaussian.cylindricalField_ibp_integrable` | F/InfiniteGaussianOperators.lean:215,226 | Genuine expectation identity and integrability of both integrands. |
| `OperatorDerivativeRewrite.Foundation.InfiniteGaussian.closedCylindricalDerivative_core_apply` | F/InfiniteGaussianOperators.lean:246 | Closed D retains the actual polynomial gradient values. |
| `OperatorDerivativeRewrite.Foundation.InfiniteGaussian.cylindricalDivergence_adjoint_eq_closedDerivative` / `OperatorDerivativeRewrite.Foundation.InfiniteGaussian.closedPolynomialDivergence_eq_hilbertDivergence` | F/InfiniteGaussianProjectionConvergence.lean:313,320 | Full operator equalities δ₀*=D and closure δ₀=δ. Finite-sector simultaneous scalar/vector convergence supplies the missing reverse inclusion. |
| `OperatorDerivativeRewrite.Foundation.InfiniteGaussian.hilbertDivergence_polynomial_graph_core_sequence` | F/InfiniteGaussianProjectionConvergence.lean:327 | For every (u,g) in graph δ, actual finite-rank polynomial fields converge to u and their divergences converge to g along the same sequence. |
| `OperatorDerivativeRewrite.Foundation.FiniteGaussian.closedGradient_domain_iff` | F/FiniteGaussianDomains.lean:147 | Scalar gradient domain is exactly square-summability of Hermite coefficients weighted by total degree. |
| `OperatorDerivativeRewrite.Foundation.FiniteGaussian.gradient_adjoint_domain_iff` | F/FiniteGaussianSpectral.lean:146 | Divergence domain is square-summability of the **combined** raising coefficients, preserving vector-component cancellations. |
| `OperatorDerivativeRewrite.Foundation.FiniteGaussian.closedGradient_eq_closedVectorDivergence_adjoint` / `OperatorDerivativeRewrite.Foundation.FiniteGaussian.closedVectorDivergence_eq_closedGradient_adjoint` | F/FiniteGaussianAdjoints.lean:110,117 | Genuine finite Gaussian full adjoint equalities. The dimension-zero case has explicit supporting declarations. |

### Gaussian entropy and exact legacy axiom repair

`OperatorDerivativeRewrite.Foundation.GaussianSteinBounded.stein_identity` (F/GaussianSteinBounded.lean:81) proves `∫ deriv h dγ = ∫ x*h(x) dγ` for bounded C¹ h with bounded actual derivative. Integrability and both Gaussian-density boundary limits are proved, not supplied as an identity.

The complete type of the main LSI result is:

```lean
OperatorDerivativeRewrite.Foundation.GaussianLogSobolevFull.gaussian_logSobolev_of_hasDerivAt
  {f h : ℝ → ℝ}
  (hd : ∀ x, HasDerivAt f (h x) x)
  (hf_sq : Integrable (fun x => f x ^ 2) GaussianCore.γ)
  (hh_sq : Integrable (fun x => h x ^ 2) GaussianCore.γ) :
  Integrable (fun x => f x ^ 2 * Real.log (f x ^ 2)) GaussianCore.γ ∧
    entropySq GaussianCore.γ f ≤ 2 * ∫ x, h x ^ 2 ∂GaussianCore.γ
```

Location: F/GaussianLogSobolevFull.lean:231. Here `GaussianCore.γ` and `entropySq` refer to the definitions in the enclosing Foundation namespaces, not a new entropy or measure. Its proof constructs smooth graph approximants, passes square-mass/energy limits, applies a nonnegative relative-entropy/Fatou argument, proves entropy integrability, then obtains the real inequality. No positivity, boundedness, or C¹ continuity of h is assumed.

`OperatorDerivativeRewrite.Foundation.GaussianLogSobolevFull.gaussian_logSobolev_of_hasDerivAt_pos` (same file:267) adds the unused legacy strict-positivity hypothesis and concludes the inequality. In the compiling Prefix, global `bakry_emery_log_sobolev` has the exact original signature and a proof by this adapter; global `log_sobolev_1d` is unchanged. Both print only standard axioms.

This establishes the **one-dimensional standard Gaussian inequality**. The original `log_sobolev_tensorization` (Original:2381) and `sobolev_embedding_from_hypercontractivity` (2429) conclude `True`; neither is repaired by the LSI adapter. No abstract Γ₂ curvature criterion or general Gaussian Sobolev L⁴ embedding is established.

### One-site Poisson results: related, not time-process instantiations

- `OperatorDerivativeRewrite.Foundation.PoissonGraphApprox.closure_coreDifference_eq_maximal` (F/PoissonGraphApprox.lean:175) and `OperatorDerivativeRewrite.Foundation.PoissonGraphApprox.closure_coreDivergence_eq_maximal` (193) prove actual graph-core equalities for rate λ>0.
- `OperatorDerivativeRewrite.Foundation.PoissonAdjoints.maximalDifference_adjoint_eq_maximalDivergence` (F/PoissonAdjoints.lean:181) and `OperatorDerivativeRewrite.Foundation.PoissonAdjoints.maximalDivergence_adjoint_eq_maximalDifference` (188) prove mutual full adjoints. The field Hilbert norm uses λ times the actual Poisson measure, giving `Df(n)=f(n+1)−f(n)` and `δu(n)=n u(n−1)−λu(n)` with the correct zero boundary.
- `OperatorDerivativeRewrite.Foundation.PoissonMultipliers.scalarMul_mem_domain` (F/PoissonMultipliers.lean:150), `OperatorDerivativeRewrite.Foundation.PoissonMultipliers.scalarMul_difference_shifted` (158), and `OperatorDerivativeRewrite.Foundation.PoissonMultipliers.scalarMul_difference_expanded` (182) prove bounded multiplier domain preservation and the jump product formula, with genuine integrability. Bounded g suffices in the one-site setting; arbitrary maximal-domain multiplication is not claimed.
- `OperatorDerivativeRewrite.Foundation.PoissonLipschitzChain.composition_mem_domain` (F/PoissonLipschitzChain.lean:48) and `OperatorDerivativeRewrite.Foundation.PoissonLipschitzChain.composition_difference_apply` (56) give genuine finite-difference composition statements, not a differential chain rule.
- `OperatorDerivativeRewrite.Foundation.PoissonQuadraticDefect.bounded_square_difference` (F/PoissonQuadraticDefect.lean:13) makes the nonzero quadratic jump correction explicit under its bounded-function hypotheses.

No one-site theorem constructs time-indexed predictable Poisson integration or proves the manuscript's compensated-Poisson Clark–Ocone formula. This lack of formal support does **not** by itself refute `prop:poisson_explicit`: on a finite horizon the conditional add-one representation for arbitrary L² terminal F may be obtained through a Mecke/L¹ argument, bounded predictable tests, and identification with the L² PRP integrand. Such a proof must not assume that the unconditioned add-one derivative is L² or that its product with an arbitrary L² test field is integrable.

## Selected actual elaborated legacy signatures

The following transcriptions use the notation printed by Lean, with coercion notation simplified where it does not change arguments. All structure hypotheses are additional to the arguments displayed; the descriptions following each block expose the important fields. These are checked implications in the compiling Prefix, not newly proved Foundation theorems.

### Clark–Ocone and GKW

```lean
UnboundedEnergySpace.clark_ocone_unbounded :
  ∀ U : UnboundedEnergySpace,
    U.IsometryCondition_unbounded → U.PRP_unbounded →
    ∀ (F : U.L2Ω) (hF_dom : F ∈ U.D.domain)
      (hProj_dom : U.Proj (U.D ⟨F, hF_dom⟩) ∈ U.δ.domain),
    F = U.constEmb (U.expect F) +
      U.δ ⟨U.Proj (U.D ⟨F, hF_dom⟩), hProj_dom⟩

UnboundedEnergySpace.gkw_orthogonality_unbounded :
  ∀ U : UnboundedEnergySpace,
    U.IsometryCondition_unbounded →
    ∀ (F : U.L2Ω) (hF_dom : F ∈ U.D.domain)
      (hProj_dom : U.Proj (U.D ⟨F, hF_dom⟩) ∈ U.δ.domain)
      (u : U.δ.domain),
    U.Proj (u : U.L2ΩH) = u →
    inner ℝ
      (F - U.constEmb (U.expect F) -
        U.δ ⟨U.Proj (U.D ⟨F, hF_dom⟩), hProj_dom⟩)
      (U.δ u) = 0
```

U contains actual dense δ and adjoint D, but also global multiplication and `mul_dom`, which are irrelevant to these proofs and wrong for the intended generic L² interpretation. It does not contain a process or a filtration. `UnboundedEnergySpace.variance_identity_unbounded` has the same domain/isometry/PRP arguments and **also requires the displayed Clark–Ocone equality as `hCO`** before concluding equality of centered and projected-gradient squared norms.

### PRP reduction

```lean
EnergySpace.PRP_from_full_isometry :
  ∀ E : EnergySpace,
    E.FullIsometryCondition →
    (∀ F : E.L2Ω, E.D F = 0 → ∃ c, F = E.constEmb c) →
    IsClosed (E.δ.range : Set E.L2Ω) → E.PRP
```

`EnergySpace.PRP_from_ker_D_subset_constants` additionally supplies a direct predictable-representation hypothesis `hClosed` for centered vectors orthogonal to ker D. That theorem's proof uses `hClosed` and the kernel condition; its isometry and range arguments are unused. Thus the bare manuscript slogan “PRP iff ker D consists of constants” omits a needed relation between the full divergence range and its predictable range. The stronger `FullIsometryCondition` forces δ=δΠ and is not the full Skorokhod isometry.

### Cylindrical extension and stochastic-volatility transfer

```lean
UnboundedEnergySpace.cylindrical_implies_leibniz_unbounded :
  ∀ (U : UnboundedEnergySpace) (cyl : U.UnboundedCylindricalStructure),
    U.LeibnizCondition_unbounded

UnboundedEnergySpace.leibniz_stochastic_volatility_unbounded :
  ∀ (U : UnboundedEnergySpace) (sv : U.UnboundedStochVolAssumption),
    U.LeibnizCondition_unbounded
```

The first body invokes `cyl.leibniz_closure`; its `cyl_dense` field has no convergence clause. The second body rewrites by `sv.transfer_formula`, applies `sv.brown_leibniz`, and distributes multiplication. Neither constructs the analytic assumptions. The manuscript's restricted L⁴ graph-limit proof is a sensible separate repair once core L⁴ membership and the correct common approximations are specified; it does not require the false general dom D algebra field.

### Rigidity and false cancellation

```lean
EnergySpace.representer_rigidity :
  ∀ (E : EnergySpace) (cyl : E.CylindricalStructure),
    E.RepresentersDeterministic cyl →
    ∀ F : E.L2Ω, cyl.is_cylindrical F → ∀ u : E.L2ΩH,
    E.expect (E.pip (E.D F) u) =
      ∑ i, E.expect (cyl.coord_deriv i F) * E.expect (E.pip (cyl.κ i) u)
```

`EnergySpace.stoch_vol_obstruction` also assumes:

```lean
∀ F G : E.L2Ω,
  (∃ c, E.mul F G = E.constEmb c) →
  (∀ d : ℝ, F ≠ E.constEmb d) → G = 0
```

This is false on two equiprobable atoms: F=(1,2), G=(1,1/2). Moreover `RepresentersDeterministic` assumes independence-style factorization against all random u; even a nonzero deterministic κ does not satisfy that property for arbitrary u. The checked theorem is not mathematical evidence for deterministic-volatility rigidity.

### Itô and the advertised chain-rule discharge

```lean
ito_formula_bounded :
  ∀ E : EnergySpace, E.LeibnizCondition →
    ∀ Y φ'Y φ''Y : E.L2Ω,
      E.D φ'Y = E.smul φ''Y (E.D Y) →
      E.δ (E.smul φ'Y (E.Proj (E.D Y))) =
        E.mul φ'Y (E.δ (E.Proj (E.D Y))) - E.ito_correction φ''Y Y

ito_from_leibniz_alone :
  ∀ E : EnergySpace, E.LeibnizCondition →
    ∀ Y φ'Y φ''Y : E.L2Ω,
      E.D φ'Y = E.smul φ''Y (E.D Y) →
      E.δ (E.smul φ'Y (E.Proj (E.D Y))) =
        E.mul φ'Y (E.δ (E.Proj (E.D Y))) - E.ito_correction φ''Y Y
```

These types are the same. Renaming the chain hypothesis `hChain_derived` does not derive it. `ito_formula_with_clark_ocone` additionally assumes both chain identities, Clark–Ocone, and `Π(φ'Y·DY)=φ'Y·ΠDY`. `ito_formula_time_indexed` applies the static identity at each t; `ItoProcess.decomp` is unused. `ito_formula_integrated` applies bounded-linear-map Bochner interchange and integrates the same identity. None is a time-increment Itô theorem.

### Original concrete Gaussian interface

`CylindricalFunctional` (Original:2939) contains `f_eval` and independent `df_eval`, with no relation by `HasFDerivAt`, `ContDiff`, or actual partial derivatives. `cylindrical_compose` (4892) prescribes derivative data by multiplication; `cylindrical_chain_rule` (4920) unfolds it and finishes by `rfl`. Its actual analytic meaning is therefore weaker than its name.

`SteinLemma` (Original:3903) quantifies over every such object. On a nonzero Gaussian direction, the allowed object `f_eval=0`, `df_eval=1` contradicts that identity. `steinFromGaussian` (Original:4155) uses supplied `IsonormalIsGaussian.per_coord_stein` and `IsonormalIsGaussian.cyl_orthog` fields from the class at Original:3827. It does not discharge this inconsistency from Mathlib's Gaussian law infrastructure. The rewrite's polynomial cylinders repair exactly this defect for their genuine polynomial core.

## Minimal paper-critical next step

Create a clean `Foundation/HilbertRepresentation.lean` only after accepting the audited scope:

1. Take actual real Hilbert spaces, a closed predictable subspace P, and a centered isometry `J : P →ₗᵢ L²`.
2. Prove the bounded adjoint `J*` exists on **all** L² and `JJ*` is the orthogonal projection onto its closed range.
3. Given a densely defined full divergence δ extending J, prove `J*F=Π(δ*F)` **for F in the actual adjoint domain**.
4. Derive GKW, and under a genuine range/PRP hypothesis, representation and variance identities. Do not carry multiplication fields into this module.

This is a reusable architecture repair for Theorem A, not a construction of Brownian integration and not a replacement for central Theorem E. The paper's stochastic-volatility rigidity claim remains a required independent mathematical obligation. The Foundation Gaussian graph-core theorem gives a defensible concrete adjoint-calculus model; attaching stochastic-process or filtration interpretations requires additional proved identifications. Banach C6 and unrelated extensions do not discharge those obligations.

## Subsequent verified implementations — HEAD `30d3140`

The original audit mapping above is retained. The following are new, precise partial repairs; all paths are relative to `C:/OperatorDerivativeRewrite/Foundation/`.

| Manuscript obligation | File and principal exact declaration | Proved scope |
|---|---|---|
| A, operator domains | `HilbertRepresentation.lean`: `adjoint_domain_iff_pairing_bound`, `predictableAdjoint_eq_projected_adjoint` | Ambient-norm domain criterion; projection agreement only on full-adjoint domain; no stochastic realization |
| E, transport | `AdjointUnitaryTransport.lean`: `pullback_adjoint_eq`; `WeightedAdjointTransport.lean`: `weightedOperator_adjoint_eq` | Equality of actual partial operators including full domains |
| E, weights | `WeightedL2Transport.lean`: `unitary`; `WeightedMeasurableTransport.lean`: `measurableUnitary` | Genuine square-density multiplication/division equivalence, also on actual sub-sigma-algebra L2 spaces |
| E, determinism ingredient | `FiniteGaussianKernel.lean`: `closedGradient_zero_iff_const`; `InfiniteGaussianKernel.lean`: `closedDerivative_zero_iff_ae_const` | Constants are exactly the kernel of the actual closed canonical Gaussian derivative |
| E, elementary integration | `GaussianElementaryIntegral.lean`: `elementaryIntegral_norm_sq`, `elementaryIntegral_hilbertDivergence_graph` | Past-polynomial random coefficients; genuine finite/infinite-model divergence and isometry |
| E, finite analogue | `GaussianElementaryRigidity.lean`: `elementaryIntegral_hasFDerivAt`, `elementaryIntegral_gradient_eq_coefficients_iff` | Actual sensitivity; gradient equals coefficient field iff all past polynomial coefficients are constant |

Theorem E in continuous time, Brownian PRP/Itô calculus and the defective bracket/Gubinelli claims remain unproved or require revision. No declaration above is a replacement of those claims by name alone. All 110 new public names appear in `Foundation/AxiomAudit.lean`; full build and 1323 transitive checks pass with standard axioms only.
