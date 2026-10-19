# Independent graph-core audit

Audit date: 2026-10-11. Repository: `C:\OperatorDerivativeRewrite`.
Target and inspected HEAD: `d9021ec16bef728e8e8c26f5018c54a08df3e793` (2026-10-11 09:58:08 -04:00).

This is an independent inspection of source definitions, proof bodies, elaborated theorem types, transitive axiom reports, and build results. `MATHEMATICAL_AUDIT.md` was not used as evidence. No Lean source or manuscript was edited; no commit was created. References below are to this commit unless an external repository is explicitly named.

## A. Executive verdict

**PASS — the advertised divergence graph-core theorem is established for the countable standard real Gaussian product. No blocking mathematical or formalization defect was found.**

The substantive identities are
\[
\delta_0^*=D,\qquad \overline{\delta_0}=\delta=D^*,
\]
with equality of partial linear operators, hence equality of domains **and** values. Here \(D\) is independently constructed as the closure of the genuine polynomial cylindrical derivative, and \(\delta_0\) is independently constructed from finite sums of the actual formula \(GW(h)-\langle DG,h\rangle\). Neither core equality is built into those definitions. See [operator definitions](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianOperators.lean:12), [the first equality](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianProjectionConvergence.lean:313), and [the second equality](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianProjectionConvergence.lean:320).

Every actual pair in the full divergence graph admits a sequence of actual \(\delta_0\)-graph pairs converging in both L² coordinates. The sequence theorem is existential, not an explicit global coordinate/chaos cutoff algorithm. This distinction does not weaken its advertised graph-core conclusion. See [hilbertDivergence_polynomial_graph_core_sequence](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianProjectionConvergence.lean:327).

The full build passed; direct re-elaboration of the principal proof module passed. A fresh complete audit produced 714 axiom reports covering 713 distinct declarations, including all seven requested targets. The only axioms reported were `propext`, `Classical.choice`, and `Quot.sound`. Details and scope qualifications follow.

## B. Exact mathematical formulation

### Ambient spaces and original operators

Write
\[
\Omega=\mathbb R^{\mathbb N},\quad
\mu=\bigotimes_{n\in\mathbb N}N(0,1),\quad
H=\ell^2(\mathbb N;\mathbb R),\quad
X=L^2(\mu;\mathbb R),\quad Y=L^2(\mu;H).
\]
These are the actual fixed Lean types, not abstract spaces equipped with assumed density or Gaussian properties:

- `SampleSpace`, `gaussianProduct`, `GaussianL2`: [InfiniteGaussianProduct:14](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianProduct.lean:14); the factor measure is `GaussianCore.γ = gaussianReal 0 1`: [GaussianCore:18](C:/OperatorDerivativeRewrite/Foundation/GaussianCore.lean:18).
- `CoefficientSpace` is Mathlib's real sequence `lp` at exponent 2: [InfiniteGaussianFirstChaos:60](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianFirstChaos.lean:60). `GaussianVectorL2` is genuine Bochner L² with that fiber: [InfiniteGaussianVectorCore:10](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianVectorCore.lean:10).
- \(W:H\to X\) is `firstChaosEmbedding`, the linear isometric extension of the independent coordinate family. Its actual coordinate series and Gaussian law are proved: [firstChaos_hasSum](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianFirstChaos.lean:68), [firstChaos_law](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianLaw.lean:119).

The scalar algebraic domain \(\mathcal P\) consists exactly of the classes
\[
F=p(W(h_1),\ldots,W(h_n)),\quad n<\infty,\ h_i\in H,
\]
for actual multivariate real polynomials \(p\). The directions may be correlated or linearly dependent. The set is defined at [isonormalPolynomialCore](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianCylinders.lean:204), then proved to be a submodule at [polynomialCylindricalDomain](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianDerivative.lean:106).

On this domain,
\[
D_0F=\sum_i (\partial_i p)(W(h_1),\ldots,W(h_n))h_i.
\]
The L² gradient is derived from actual polynomial partial derivatives and proved independent of representation **before** the intrinsic operator is defined. Sources: [isonormalCylinderGradient](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianCylinders.lean:19), [representation independence](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianRepresentation.lean:83), [polynomialGradient_agrees](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianDerivative.lean:130), [cylindricalDerivative](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianOperators.lean:12).

The vector algebraic domain \(\mathcal V\) is exactly the finite sums \(\sum_{j=1}^mG_jh_j\), \(G_j\in\mathcal P,\ h_j\in H\). On it,
\[
\delta_0\left(\sum_jG_jh_j\right)
=\sum_j\left(G_jW(h_j)-\langle D_0G_j,h_j\rangle_H\right).
\]
The graph is initially an algebraic span of these pairs. IBP and scalar density prove it single-valued; this is not an assumption in the graph definition. Its domain is proved exactly \(\mathcal V\), and each element has an actual finite-sum representation. Sources: [cylindricalDivergenceGraph](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianOperators.lean:17), [vertical_zero](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianOperators.lean:36), [cylindricalDivergence_domain](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianOperators.lean:61), [cylindricalVectorDomain_mem_iff](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianOperators.lean:260), [rankDivergence](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianIBP.lean:99).

Finally,
\[
D=\overline{D_0},\qquad
\delta=D^*,\qquad
\texttt{closedPolynomialDivergence}=\overline{\delta_0}.
\]
These definitions are independent of the target equalities: [InfiniteGaussianOperators:115](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianOperators.lean:115), [InfiniteGaussianFiniteSectors:112](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianFiniteSectors.lean:112). In particular, defining \(\delta=D^*\) is the intended definition of maximal divergence; the nontrivial result is identifying it with \(\overline{\delta_0}\).

The maximal divergence domain is genuinely
\[
u\in\operatorname{Dom}(\delta)
\iff \exists g\in X\ \forall F\in\operatorname{Dom}(D):
\langle DF,u\rangle_Y=\langle F,g\rangle_X.
\]
No componentwise Sobolev condition appears. This is the proved [hilbertDivergence_mem_iff](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianOperators.lean:156).

### Finite sectors and the seven requested statements

For a finite set \(s\subset\mathbb N\), let
\[
X_s=L^2(\gamma_s;\mathbb R),\quad Y_s=L^2(\gamma_s;\mathbb R^s),
\quad \gamma_s=\bigotimes_{i\in s}N(0,1).
\]
\(I_s:X_s\to X\) is actual sample-coordinate pullback. \(J_s:Y_s\to Y\) pulls back the field and zero-extends its Euclidean fiber into \(H\):
\[
I_sf(\omega)=f(\omega|_s),\qquad
J_su(\omega)=\sum_{i\in s}u_i(\omega|_s)e_i.
\]
These are equalities of a.e. representatives, established in [finitePullback_coeFn](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianProduct.lean:71) and [finiteVectorPullback_coeFn](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianProjectionConvergence.lean:92).

Set \(P_s=I_sI_s^*\), \(Q_s=J_sJ_s^*\), and \(s_N=\{0,\ldots,N-1\}\). Their definitions are [finiteScalarProjection](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianCoordinateFields.lean:181) and [finiteVectorProjection](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianProjectionConvergence.lean:124).

All seven targets are in namespace `OperatorDerivativeRewrite.Foundation.InfiniteGaussian`. Inspection using `#check @...` confirmed the following complete list of theorem parameters. The fixed ambient instances above introduce **no further theorem hypotheses**.

| Lean declaration and location | Quantifiers and hypotheses | Actual conclusion |
|---|---|---|
| [cylindricalDivergence_adjoint_eq_closedDerivative:313](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianProjectionConvergence.lean:313) | None | \(\delta_0^*=D\), as partial linear maps \(X\to Y\). |
| [closedPolynomialDivergence_eq_hilbertDivergence:320](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianProjectionConvergence.lean:320) | None | \(\overline{\delta_0}=\delta\), as partial linear maps \(Y\to X\). |
| [hilbertDivergence_polynomial_graph_core_sequence:327](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianProjectionConvergence.lean:327) | Every \(u:Y,\ g:X\); sole hypothesis \((u,g)\in\operatorname{graph}(\delta)\) | There exists \(v:\mathbb N\to\operatorname{Dom}(\delta_0)\) with \((v_N,\delta_0v_N)\to(u,g)\) in \(Y\times X\). |
| [finiteVectorPullback_eq_isometry:118](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianProjectionConvergence.lean:118) | Every `s : Finset ℕ`; no hypothesis | Existing \(J_s\) equals the continuous linear map underlying the separately proved `finiteVectorIsometry s`. |
| [finiteVectorProjection_range_tendsto:239](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianProjectionConvergence.lean:239) | Every \(u:Y\); no domain hypothesis | \(Q_{s_N}u\to u\) in the full vector L² norm topology. |
| [finiteScalarProjection_range_tendsto:260](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianProjectionConvergence.lean:260) | Every \(F:X\); no domain hypothesis | \(P_{s_N}F\to F\) in scalar L² norm topology. |
| [finiteSector_weak_gradient_range_graph:284](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianProjectionConvergence.lean:284) | Every \(F:X,\ G:Y,\ N:\mathbb N\); sole hypothesis \((F,G)\in\operatorname{graph}(\delta_0^*)\) | \((P_{s_N}F,Q_{s_N}G)\in\operatorname{graph}(D)\). |

Here `Tendsto ... atTop (𝓝 ...)` uses the ordinary norm topology of the indicated L² or product space. It is not weak convergence. The sequence's explicit Lean witness type is `ℕ → cylindricalDivergence.domain`; domain membership is part of each witness, not an omitted side condition.

## C. Statement fidelity and Gaussian foundations

**Actual differentiation, not prescribed values.** The gradient formula is independently verified to represent the Fréchet derivative of the polynomial under Hilbert coordinate perturbations \(W(h_i)(\omega)+\langle h_i,v\rangle\). The proof uses analytic differentiation and polynomial induction: [isonormalCylinderShift_hasFDerivAt](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianCylinders.lean:127). The polynomial product rule uses Mathlib's actual `MvPolynomial.pderiv_mul`, then descends to the intrinsic domain: [isonormalCylinderGradient_mul](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianCylinders.lean:102), [polynomialDerivative_product](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianPolynomialProducts.lean:100). This does not assert a simultaneous sample-space translation identity for every \(h,\omega\); that stronger statement is unnecessary here.

**Dependent coordinates are handled correctly.** [isonormalCylinderGradientL2_representation_independent](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianRepresentation.lean:83) takes two arbitrary finite families and only equality of their scalar L² classes. It puts both families in their common finite Hilbert span, constructs a standard Gaussian vector there, and transports both scalar and gradient expressions. The finite law is proved by characteristic functions: [finiteGaussianPoint_law](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianRepresentation.lean:41). Finite representation independence follows from full Gaussian support, continuity and equality of actual derivatives: [FiniteGaussian.cylinderGradient_representation_independent](C:/OperatorDerivativeRewrite/Foundation/FiniteGaussianCylinders.lean:146). No injectivity of evaluation on a dependent coordinate family is used.

**Gaussian properties are proved about the actual random variables.** Coordinate law and independence are [coordinate_law](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianProduct.lean:36) and [coordinates_independent](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianProduct.lean:47). The law of \(W(h)\) is obtained by L²/distributional convergence of finite coordinate sums and characteristic-function uniqueness: [firstChaos_charFun](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianLaw.lean:101), [firstChaos_law](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianLaw.lean:119). General finite families have their actual Gaussian law and Gram covariance, including degeneracy: [firstChaosFamily_hasGaussianLaw](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianIsonormal.lean:109), [firstChaosFamily_covariance](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianIsonormal.lean:122).

**Integrability is established, not inserted as an analytic premise.** Polynomial cylinders and their gradients have every finite moment, using Gaussian moments and doubled-exponent Hölder: [isonormalCylinder_memLp](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianCylinders.lean:49), [isonormalCylinderGradient_memLp](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianCylinders.lean:61). Products with \(W(h)\) and rank divergences are treated explicitly: [polynomial_times_firstChaos_memLp](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianIBP.lean:77), [rankDivergence_memLp](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianIBP.lean:92). IBP term integrability is also proved in [cylindricalField_ibp_integrable](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianOperators.lean:226). There is no assumption \(L^2L^2\subset L^2\).

**Density is independent of the desired graph result.** Scalar coordinate polynomial density uses finite polynomial density and uniqueness from integrals on measurable cylinders generating the product sigma algebra: [ae_zero_of_cylinder_integrals](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianDensity.lean:14), [coordinatePolynomialEmbedding_dense](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianDensity.lean:73). Vector core density tests scalar components against these polynomials and uses the countable coordinate basis of \(\ell^2\): [eq_zero_of_coordinatePolynomialVector_orthogonal](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianCoordinateFields.lean:29), [coordinatePolynomialVectorDomain_dense](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianCoordinateFields.lean:63). Ambient density is not mistaken for graph density.

**Finite Hermite completeness has noncircular analytic input.** [productPolynomialEmbedding_dense](C:/OperatorDerivativeRewrite/Foundation/FiniteGaussianDensity.lean:192) follows from the preceding orthogonality/weighted-measure moment-uniqueness proof. Algebraic Hermite spanning and orthogonality then produce an actual complete Hilbert basis: [tensorHermitePolynomial_span](C:/OperatorDerivativeRewrite/Foundation/FiniteGaussianCompleteness.lean:54), [tensorHermite_orthonormal](C:/OperatorDerivativeRewrite/Foundation/FiniteGaussianTensor.lean:94), [tensorHermiteBasis](C:/OperatorDerivativeRewrite/Foundation/FiniteGaussianCompleteness.lean:115). Completeness is not assumed in a structure field without a proof.

All ambient L² spaces are Mathlib Lp spaces with actual probability measures and complete real Hilbert fibers. A.e. transport uses measure-preserving finite projections. Countable simultaneous a.e. coordinate statements use the actual countability of \(\mathbb N\); no uncountable intersection is substituted. The finite-space construction supplies its Borel and finite-dimensional instances explicitly. Sources: [finiteProjection_measurePreserving](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianProduct.lean:60), [finiteVectorPullback_coeFn](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianProjectionConvergence.lean:92), [representation-independence proof](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianRepresentation.lean:83), [vector-density proof](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianVectorCore.lean:39).

## D. Reconstructed projection and operator argument

### 1. Start from genuine densely defined operators

IBP proves \(D_0\subset\delta_0^*\) and \(\delta_0\subset D_0^*\); both domains are proved dense. Closed adjoints then give closability of both original operators. Closing the first inclusion gives \(D\subset\delta_0^*\). These precede, and do not use, the graph-core theorem: [cylindricalDerivative_formalAdjoint](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianOperators.lean:85), [dense domains and closability](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianOperators.lean:76), [closedCylindricalDerivative_le_cylindricalDivergence_adjoint](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianOperators.lean:279).

The orientations are correct: \(D_0:X\to Y\), \(\delta_0:Y\to X\), \(\delta_0^*:X\to Y\). Mathlib's adjoint graph characterization requires density; every relevant application supplies it. This matters because Mathlib's general `LinearPMap.adjoint` has a fallback branch for nondense domains, which is not the branch used here: [Mathlib LinearPMap.adjoint](C:/OperatorDerivativeRewrite/.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/LinearPMap.lean:152).

### 2. The vector lift really is isometric

The proof constructs the actual zero-extension \(\mathbb R^s\hookrightarrow\ell^2\), proves its coordinate images orthonormal, lifts this norm equality to Bochner L², and composes with measure-preserving pullback. It then proves equality with the previously defined \(J_s\) by comparing their a.e. representatives. Thus isometry is not obtained by redefining the old lift. Sources: [finiteFiberMap_orthonormal](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianProjectionConvergence.lean:27), [finiteFiberIsometry](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianProjectionConvergence.lean:38), [finiteFiberIsometry_compLp_norm](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianProjectionConvergence.lean:54), [finiteVectorPullback_eq_isometry](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianProjectionConvergence.lean:118).

Consequently \(J_s^*J_s=1\), and \(Q_s=J_sJ_s^*\) is the orthogonal range projection. The exact properties needed are independently proved: it fixes the range and has norm at most one. The same holds for \(P_s\). The code need not identify these maps with Mathlib's conditional-expectation API. Sources: [finiteVectorProjection_fix](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianProjectionConvergence.lean:128), [finiteVectorProjection_norm_le](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianProjectionConvergence.lean:145), [finiteScalarProjection_fix](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianCoordinateFields.lean:185), [finiteScalarProjection_norm_le](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianCoordinateFields.lean:199).

### 3. Strong convergence handles both sample and fiber indices

A generator \(p(\omega|_s)e_n\) is fixed by \(Q_t\) whenever \(s\cup\{n\}\subset t\). The output index is explicitly included: [finiteVectorProjection_fix_coordinate_of_subset](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianProjectionConvergence.lean:190). Span induction therefore proves eventual fixation of every coordinate polynomial vector along \(s_N\): [finiteVectorProjection_eventually_fix_core](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianProjectionConvergence.lean:214).

For arbitrary \(u\in Y\), choose a dense-core vector \(v\) with \(\|u-v\|<\varepsilon/2\). For all sufficiently large \(N\),
\[
\|Q_{s_N}u-u\|
=\|Q_{s_N}(u-v)-(u-v)\|
\le 2\|u-v\|<\varepsilon.
\]
This is precisely the proof of [finiteVectorProjection_range_tendsto](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianProjectionConvergence.lean:239). The scalar argument uses the same exhaustion and scalar polynomial density: [finiteScalarProjection_range_tendsto](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianProjectionConvergence.lean:260). No incompatible subnet or weak topology enters.

### 4. Restrict a maximal weak-gradient graph pair

If \((F,G)\in\operatorname{graph}(\delta_0^*)\), then
\[
(I_s^*F,J_s^*G)\in\operatorname{graph}(\delta_{0,s}^*).
\]
To prove this, the code tests against every actual finite polynomial vector field \(a\), whose divergence is \(b\). Its lift \((J_sa,I_sb)\) is proved to lie in the global \(\delta_0\) graph. Global adjointness gives
\[
\langle I_sb,F\rangle_X-\langle J_sa,G\rangle_Y=0.
\]
Moving the bounded lift adjoints yields the finite weak-gradient relation. Sources: [finitePolynomialDivergence_lift_graph](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianFiniteSectors.lean:92), [finiteSector_weak_gradient_graph](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianCoordinateFields.lean:141). This uses the full finite polynomial test domain, not a weakened relation.

### 5. Finite weak gradients lift into the actual closed graph

Finite Hermite theory supplies genuine polynomial gradient pairs
\[
(S_{M+1}f,T_Mg)\in\operatorname{graph}(\nabla_{0,s})
\quad\text{if }(f,g)\in\operatorname{graph}(\delta_{0,s}^*),
\]
converging strongly to \((f,g)\). Here \(S,T\) are total-degree scalar and vector Hermite cutoffs, with the necessary degree shift. These facts are [divergence_adjoint_truncation_graph](C:/OperatorDerivativeRewrite/Foundation/FiniteGaussianAdjoints.lean:60) and [divergence_adjoint_truncation_tendsto](C:/OperatorDerivativeRewrite/Foundation/FiniteGaussianAdjoints.lean:77).

Every polynomial approximant lifts to the original \(D_0\) graph, and continuous lifts transport both limits. Therefore the lifted limit lies in \(\operatorname{graph}(D)\): [finitePolynomialGradient_lift_graph](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianFiniteSectors.lean:244), [finiteGradient_lift_closed_graph](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianFiniteSectors.lean:253). Applied to step 4, this proves
\[
(P_sF,Q_sG)\in\operatorname{graph}(D).
\]
See [finiteSector_weak_gradient_lift_graph](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianCoordinateFields.lean:172).

### 6. Close the global graph

Along the same \(s_N\), both coordinates converge strongly. The graph of \(D\) is closed. Therefore \((F,G)\in\operatorname{graph}(D)\), proving \(\delta_0^*\subset D\); antisymmetry with step 1 gives equality. Sources: [finiteSector_projections_range_tendsto](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianProjectionConvergence.lean:294), [cylindricalDivergence_adjoint_le_closedDerivative](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianProjectionConvergence.lean:303), [cylindricalDivergence_adjoint_eq_closedDerivative](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianProjectionConvergence.lean:313).

The graph limits use the ordinary product topology, equivalent to convergence for the usual graph norm \((\|x\|^2+\|Tx\|^2)^{1/2}\). Where an actual product Hilbert inner product is needed in the bidual proof, the code explicitly uses `WithLp 2 (E × F)`, not the default product norm: [closedOperator_adjoint_adjoint_eq](C:/OperatorDerivativeRewrite/Foundation/AdjointBidual.lean:15).

### 7. Bidual and actual polynomial graph sequence

The abstract bidual theorem assumes closedness, ambient dense domain, and dense adjoint domain; the closable version then identifies \(T^{**}\) with the actual graph closure. These hypotheses are all separately established for \(\delta_0\). Its adjoint domain is dense because it contains the already densely defined \(D\), not because graph-core equality is assumed. Sources: [closableOperator_adjoint_adjoint_eq_closure](C:/OperatorDerivativeRewrite/Foundation/AdjointBidual.lean:47), [cylindricalDivergence_adjoint_dense_domain](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianFiniteSectors.lean:289), [cylindricalDivergence_adjoint_adjoint_eq_closedPolynomialDivergence](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianFiniteSectors.lean:295).

Taking adjoints of \(\delta_0^*=D\) now yields \(\overline{\delta_0}=D^*=\delta\). The earlier equivalence theorem merely packages these proved bidual facts; it did not assume either core equality: [polynomialDivergence_core_iff_adjoint_identification](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianFiniteSectors.lean:302).

Finally, the proof uses sequential characterization of closure in the metrizable product L² space. Each selected point belongs to the original \(\delta_0\) graph. `mem_domain_of_mem_graph` constructs its domain witness and `image_iff` identifies its second coordinate with the actual \(\delta_0\) value. Thus the sequence consists of genuine polynomial divergence pairs, not merely weak finite-sector pairs: [hilbertDivergence_polynomial_graph_core_sequence](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianProjectionConvergence.lean:327), together with the exact finite-sum domain description at [InfiniteGaussianOperators:260](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianOperators.lean:260).

### 8. Cancellation and dimension zero

The finite maximal divergence coefficients are
\[
b_\beta=\sum_{i:\beta_i>0}\sqrt{\beta_i}\,u_{i,\beta-e_i}.
\]
The domain condition is \(\sum_\beta |b_\beta|^2<\infty\), **after summing over components**: [divergenceCoefficient](C:/OperatorDerivativeRewrite/Foundation/FiniteGaussianSpectral.lean:21), [gradient_adjoint_domain_iff](C:/OperatorDerivativeRewrite/Foundation/FiniteGaussianSpectral.lean:146). Total-degree truncation preserves this combined coefficient with a single degree shift: [divergenceCoefficient_truncation](C:/OperatorDerivativeRewrite/Foundation/FiniteGaussianTruncation.lean:159). It is not replaced by separate square-summability conditions.

The global proof works on arbitrary \(\delta_0^*\)-graph pairs and then takes adjoints; it never requires an arbitrary \(u\in\operatorname{Dom}(\delta)\) to have separately integrable component divergences. The final sequence theorem quantifies over the full maximal graph. Hence cancellations are preserved at the level required by the claim.

No positivity of the finite dimension is assumed. Empty fibers and the zero cutoff are included. Relevant checks are [tensorHermite_empty_expansion](C:/OperatorDerivativeRewrite/Foundation/FiniteGaussianCompleteness.lean:136), [gradient_adjoint_graph_empty](C:/OperatorDerivativeRewrite/Foundation/FiniteGaussianSpectral.lean:203), and [finiteVectorPullback_empty](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianFiniteSectors.lean:213).

## E. Build, axioms, and proof integrity

The audited configuration is Lean 4.34.1, release commit `5045d0056413266e57c625dcd7c365b10e377c52`, with Mathlib locked to `d13f23b723b8a846827a245b89c10fc7d3f11612` (2026-09-24). The Mathlib checkout matched the lockfile and had no local modifications. Configuration sources: [lean-toolchain](C:/OperatorDerivativeRewrite/lean-toolchain), [lakefile.toml](C:/OperatorDerivativeRewrite/lakefile.toml), [lake-manifest.json](C:/OperatorDerivativeRewrite/lake-manifest.json).

Commands were run from the repository using the direct toolchain Lake executable:

~~~powershell
& 'C:/Users/ramir/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake.exe' build
& 'C:/Users/ramir/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake.exe' env lean Foundation/InfiniteGaussianProjectionConvergence.lean
& 'C:/Users/ramir/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lake.exe' env lean Foundation/AxiomAudit.lean
~~~

| Check | Independent result |
|---|---|
| Full Lake build | Exit 0, “Build completed successfully (3359 jobs).” Existing valid artifacts were reused; this was not a clean rebuild of Lean/Mathlib. |
| Principal proof source re-elaboration | Exit 0, no diagnostic output. |
| Complete `AxiomAudit.lean` execution | Exit 0; 714 axiom reports, 713 distinct declaration names. One repeated query does not represent an additional theorem. |
| Axiom sets | Union exactly `{propext, Classical.choice, Quot.sound}`. Each of the seven requested targets reports this trio. No `sorryAx` or custom axiom appears transitively. |
| Source scan | No executable `sorry`, `admit`, `axiom`, `unsafe`, `native_decide`, `implemented_by`, or `extern` in project Lean sources. Occurrences of the English word “admits” were comments, not proof holes. |
| Local import dependency scan | 44 Foundation modules, no cycles and no missing local imports. |
| Source preservation | No tracked Lean/configuration/manuscript file changed during the audit. |

The build emitted two existing unused-section-variable lints in [Foundation/Adjoint.lean:24](C:/OperatorDerivativeRewrite/Foundation/Adjoint.lean:24) and [Foundation/Adjoint.lean:30](C:/OperatorDerivativeRewrite/Foundation/Adjoint.lean:30). They concern unused `CompleteSpace L2Ω` hypotheses of older general lemmas, not extra assumptions on the seven principal targets.

The principal audit commands are already present at [AxiomAudit:585](C:/OperatorDerivativeRewrite/Foundation/AxiomAudit.lean:585). Counts above refer to reports actually executed and parsed without truncation, not to a claimed count in prior documentation. Transitive axiom checking of the targets also covers private helper proofs on their dependency paths. The source scan and acyclic import graph supplement, rather than replace, Lean checking and statement inspection.

## F. Adversarial findings, risks, and limits

**Confirmed blocking defects: none.** The specific challenges were resolved as follows:

| Suspected failure | Finding |
|---|---|
| The maximal domain secretly equals a chosen core by definition | Rejected: \(\delta=D^*\) and \(\delta_0\) is independently built from the algebraic formula. Equality is proved only after projection convergence. See [Operators:17](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianOperators.lean:17), [Operators:118](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianOperators.lean:118), [ProjectionConvergence:320](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianProjectionConvergence.lean:320). |
| Ambient L² density substituted for graph density | Rejected: density is used to prove strong projection convergence; finite Hermite **graph** approximants and closedness supply graph membership. See [FiniteSectors:253](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianFiniteSectors.lean:253), [ProjectionConvergence:303](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianProjectionConvergence.lean:303). |
| Vector projection truncates only the random coordinates | Rejected: the proof requires and supplies inclusion of the output coordinate too. See [ProjectionConvergence:190](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianProjectionConvergence.lean:190). |
| Different scalar/vector limits or weak convergence | Rejected: both use `Finset.range N` and norm topology. See [ProjectionConvergence:294](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianProjectionConvergence.lean:294). |
| Adjoint orientation or nondense-domain fallback | Rejected: spaces and dense-domain arguments are explicit in [CoordinateFields:141](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianCoordinateFields.lean:141) and [FiniteSectors:295](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianFiniteSectors.lean:295). |
| Final sequence is only in a weak or enlarged domain | Rejected: its terms are in `cylindricalDivergence.domain`, with exact original operator values. See [ProjectionConvergence:327](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianProjectionConvergence.lean:327). |
| Componentwise regularity excludes cancellation | Rejected: combined coefficients are used in finite theory; no such global premise is present. See [Spectral:146](C:/OperatorDerivativeRewrite/Foundation/FiniteGaussianSpectral.lean:146). |
| Degenerate coordinate representations break differentiation | Rejected: common finite Hilbert span and Gaussian full support prove independence, without arbitrary-coordinate polynomial injectivity. See [Representation:83](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianRepresentation.lean:83). |

Scope limitations, not defects:

1. **Fixed real countable Gaussian product.** The principal results are not yet parameterized over an arbitrary isonormal process, an abstract Wiener space, a nonseparable Hilbert space, or a probability space carrying additional randomness. Scalar density depends on the coordinates generating this entire product sigma algebra. See [SampleSpace](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianProduct.lean:14) and [ae_zero_of_cylinder_integrals](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianDensity.lean:14).
2. **Existence rather than an explicit global divergence truncation formula.** Finite-sector Hermite approximants are explicit, but the final arbitrary-divergence sequence is obtained from graph closure. No global formula \(u_N=\text{specified cutoff}(u)\), or associated convergence rate, is established by [the sequence theorem](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianProjectionConvergence.lean:327).
3. **No full infinite-chaos domain formula in this milestone.** The combined spectral domain formula inspected here is finite-dimensional. The global result gives an exact adjoint domain and its polynomial graph core, not a newly stated infinite coefficient characterization. Compare [FiniteGaussianSpectral:146](C:/OperatorDerivativeRewrite/Foundation/FiniteGaussianSpectral.lean:146) with [InfiniteGaussianOperators:156](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianOperators.lean:156).
4. **No Itô identification, adapted-process theorem, non-Gaussian calculus, or validation of the whole original manuscript follows automatically.** The target operators and proved graph identities have precisely the scope in section B. Further interpretations need their own Lean bridges.
5. **External comparison is not external certification.** Public source inspection below was performed at pinned commits; those separate projects were not built or axiom-audited in this audit. Absence findings are bounded to the inspected source trees and searches, not a proof that no equivalent result exists anywhere.

## G. Classical mathematics and public Lean comparison

### Classical status

The mathematics is classical Gaussian Malliavin calculus. Hairer's *Introduction to Malliavin Calculus*, sections 5.1–5.3, gives the polynomial derivative, its closability (Proposition 5.17), the divergence as adjoint, and the finite-rank divergence formula (5.17). See [Hairer's notes](https://www.hairer.org/notes/Malliavin.pdf). The graph-core conclusion is a classical consequence of Gaussian finite-dimensional/chaos approximation and adjoint duality; the argument reconstructed in section D proves that consequence here. This audit does not identify a new mathematical theorem. Its contribution is formalizing the domain-sensitive conclusion and its dependencies.

### Mathlib already supplies much of the infrastructure

At locked commit [d13f23b](https://github.com/leanprover-community/mathlib4/commit/d13f23b723b8a846827a245b89c10fc7d3f11612), dated 2026-09-24:

- [Mathlib/Analysis/InnerProductSpace/LinearPMap.lean](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/Analysis/InnerProductSpace/LinearPMap.lean#L152) provides `LinearPMap.adjoint`, `Submodule.mem_adjoint_iff`, and `LinearPMap.adjoint_graph_eq_graph_adjoint` (lines 152, 273, 293).
- [Mathlib/Topology/Algebra/Module/LinearPMap.lean](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/Topology/Algebra/Module/LinearPMap.lean#L104) provides `LinearPMap.IsClosable.graph_closure_eq_closure_graph`.
- [Mathlib/Analysis/InnerProductSpace/Adjoint.lean:1068](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/Analysis/InnerProductSpace/Adjoint.lean#L1068) provides `LinearIsometry.adjoint_comp_self`, used for the finite projections.
- [Mathlib/Probability/ProductMeasure.lean:374](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/Probability/ProductMeasure.lean#L374) provides `Measure.infinitePi_map_restrict`.
- [Mathlib/RingTheory/Polynomial/Hermite/Basic.lean:48](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/RingTheory/Polynomial/Hermite/Basic.lean#L48) already defines probabilists' Hermite polynomials and proves their recurrence and degree facts.

These are already formalized mathematics, not contributions originating in this repository. A search of the pinned Mathlib tree found no named Malliavin/Skorokhod development or the present Gaussian polynomial divergence-core theorem.

### gaussian-hilbert: genuine finite-dimensional overlap

Pinned repository: [mrdouglasny/gaussian-hilbert](https://github.com/mrdouglasny/gaussian-hilbert), commit [4d055b0](https://github.com/mrdouglasny/gaussian-hilbert/commit/4d055b0bf3722c73bd6c327eeabd8a8a72ab4c7e), 2026-06-05 23:17:26 UTC, confirmed as its current main HEAD during this audit.

| Existing declaration | Comparison |
|---|---|
| [GaussianHilbert/HermitePolynomials.lean:99, hermiteMulti_orthogonality](https://github.com/mrdouglasny/gaussian-hilbert/blob/4d055b0bf3722c73bd6c327eeabd8a8a72ab4c7e/GaussianHilbert/HermitePolynomials.lean#L99) | Already formalizes finite Gaussian Hermite orthogonality; normalization differences do not constitute novelty. |
| [Same file:437, hermiteMulti_dense](https://github.com/mrdouglasny/gaussian-hilbert/blob/4d055b0bf3722c73bd6c327eeabd8a8a72ab4c7e/GaussianHilbert/HermitePolynomials.lean#L437) | Already gives L² approximation by finite Hermite sums. |
| [GaussianHilbert/WienerChaos.lean:362, wienerChaos_isHilbertSum](https://github.com/mrdouglasny/gaussian-hilbert/blob/4d055b0bf3722c73bd6c327eeabd8a8a72ab4c7e/GaussianHilbert/WienerChaos.lean#L362) | Finite-dimensional Gaussian chaos decomposition, with actual L² projections. |
| [GaussianHilbert/PolynomialDensity.lean:605, polynomial_dense_L2_of_subGaussian](https://github.com/mrdouglasny/gaussian-hilbert/blob/4d055b0bf3722c73bd6c327eeabd8a8a72ab4c7e/GaussianHilbert/PolynomialDensity.lean#L605) | A more general finite-dimensional measure hypothesis than this repository's standard Gaussian density theorem. |

All seven Lean files in that pinned tree were searched for adjoint/divergence/core constructions; no infinite-dimensional Malliavin polynomial divergence graph-core identity was found. This is a bounded comparison, not an audit of every theorem in that project.

### lean-malliavin: already a closed infinite-dimensional derivative

Pinned repository: [savarin/lean-malliavin](https://github.com/savarin/lean-malliavin), commit [a1a6ccc](https://github.com/savarin/lean-malliavin/commit/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272), 2026-08-31 20:53:26 UTC, likewise confirmed as current main HEAD.

[**Malliavin/MalliavinDerivative.lean**](https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/MalliavinDerivative.lean) contains:

- `integral_inner_mderiv` (843), `integral_inner_mderiv_mul` (864): Gaussian IBP.
- `IsSmoothBounded.divergenceLp` (660), `simpleDiv` (931): the actual rank-one divergence expression.
- `mderiv_closable` (1080), `InGraphClosure` (1092), `domD12` (1098): closability and Sobolev graph closure.
- `mderivPMap` (1308), `dense_mderivPMap_domain` (1338), `isClosed_mderivPMap_graph` (1344): a genuine closed densely defined partial derivative operator.

Its ambient model is a Gaussian measure on a complete second-countable real normed space, with the Cameron–Martin space; its initial test functions are bounded C¹ functions with bounded derivative. Thus this repository cannot claim the first Lean construction of a closed infinite-dimensional Malliavin derivative, nor greater generality in the ambient probability model.

[**Malliavin/CylindricalGrowth.lean:406**](https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/CylindricalGrowth.lean#L406), `cylinder_growth_mem_domD12`, also treats genuine cylindrical functions with polynomial growth inside the closed derivative domain. Merely using polynomial cylinders therefore is not by itself a novelty claim.

All 58 Lean files in the pinned tree were searched for bundled adjoints, divergence/core statements, and `HasCore`/graph-core terminology, with the relevant derivative source inspected directly. I found the rank-one formal divergence and closed derivative above, but no theorem identifying the closure of a polynomial finite-rank divergence with the full derivative adjoint. The derivative's adjoint can of course be formed using Mathlib; doing so alone does not prove this core equality. No claim is made that the two repositories' different derivative constructions have already been connected by a Lean equivalence.

### What this milestone adds

Relative to the inspected libraries, the useful additional formalized result is the exact maximal divergence core identification for the explicit countable Gaussian product, together with its actual polynomial graph approximants and the finite-sector proof supporting it. The strongest evidence is the three principal declarations at [ProjectionConvergence:313](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianProjectionConvergence.lean:313), [320](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianProjectionConvergence.lean:320), and [327](C:/OperatorDerivativeRewrite/Foundation/InfiniteGaussianProjectionConvergence.lean:327), not different names or proof style.

Classification:

- **Already established mathematics:** all the Gaussian operator identities audited here.
- **Already formalized mathematics:** substantial adjoint, Lp, Gaussian, Hermite, density, IBP, and closed-derivative infrastructure, as mapped above.
- **Apparently additional formalization of known mathematics:** this particular full polynomial divergence graph-core theorem and its integration with these explicit operators, relative to the inspected pinned libraries.
- **Potentially new mathematical results established by this milestone:** none identified.

The operator-first presentation makes domains, closure, inclusions, and maximal adjoints explicit. That is a useful formalization architecture; it does not strengthen classical Malliavin calculus or remove its analytic obligations. General helper lemmas such as [operatorClosure_adjoint_eq](C:/OperatorDerivativeRewrite/Foundation/AdjointClosure.lean:41) and [closedOperator_adjoint_adjoint_eq](C:/OperatorDerivativeRewrite/Foundation/AdjointBidual.lean:15) are candidates for reuse, subject to a separate upstream API and duplication review.

## H. Recommendation

**Accept this milestone as a verified foundation for subsequent development within its stated Gaussian model.** There is no remaining analytic obligation blocking the two graph-core identities or the existence theorem for simultaneous polynomial divergence graph approximation.

The exact next action is to review and explicitly accept this audit before any manuscript revision. For subsequent Lean development, preserve the three principal theorems as the public operator-domain interface and choose a separately scoped extension; compare and reuse existing libraries before rebuilding broader Malliavin or stochastic-integration machinery. Any claim about a different Gaussian model, an explicit global spectral domain, Itô integration, or a non-Gaussian manuscript theorem must be proved separately.

This report authorizes no source repair and records no commit. Only this requested report was added.
