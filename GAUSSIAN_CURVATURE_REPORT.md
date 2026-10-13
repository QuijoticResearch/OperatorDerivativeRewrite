# Gaussian curvature tower: verified checkpoint

Started at 4c11a891ce31fe7661be577d3bfe71a4ac8dba26, after the fractional campaign report. Final mathematics HEAD: f61a34e14dbc6baafc183cd18feaf14e9ba41704. This is a qualified checkpoint, not completion of all closed-domain curvature theory.

## Verified milestones

- ea83d7750afac997d45628792ef16b1e59cb999e: actual one-dimensional polynomial OU recursion, Gamma=p'q', Gamma2=p'q'+p''q'', curvature one, genuine Gaussian IBP/symmetry/energy. 15 declarations; full build 4194 jobs; axiom audit 3072.
- c48344a77e2723144b6bd2d6fadd45a286d05726: actual fractional covariance positivity, natural Hadamard-power positivity, Brownian innovation factorization and actual generalized eigenpairs; H=2 negative quadratic form. 24 declarations; full build 4196; audit 3096.
- f61a34e14dbc6baafc183cd18feaf14e9ba41704: actual Wick-cylinder Gram formula and closed derivative graph, with exact finite-sum norm. 6 declarations; full build 4197; audit 3102.

Three successful full builds and three transitive audits. All 45 new public declarations have explicit-type checks. Only propext, Classical.choice, Quot.sound occur. Logs: `.lake/campaign-curvature/01-*` through `03-*`. No existing theorem body, pin, manuscript, or unrelated document was changed; no push.

## Source audit and qualifications

No `iterated_gamma_curvature_tower.tex` exists in the recursive C:/Operator inventory. The available relevant source is `C:/Operator/fbm/hurst_curvature.tex` (graded spectrum lines 285ff, Wiener-chaos interpretation 330ff, innovation factorization 359ff, signed H=2 discussion 556ff). `C:/Operator/fbm/bakry_emery_revised_v8.tex` contains the fractional-Laplacian Gamma definitions (387ff, Gamma2 429ff).

1. The first-level generalized spectrum uses D_k/D_1=D_k. The source's comparison against the FIRST form is not an adjacent-level error. An adjacent-level comparison must use D_k/D_(k-1). The verified example is 7/3, not 7.
2. The Wick Gram identity is now independently proved in Lean. It does not establish the source's stronger assertion that its curvature tower IS a Wiener-chaos decomposition, nor identify the spatial innovation index with chaos degree or identify closed operator domains.
3. For complex sesquilinear Gamma, the source's `L Gamma(f,f)-2 Gamma(f,Lf)` can be complex. It needs `L Gamma(f,f)-Gamma(Lf,f)-Gamma(f,Lf)` (equivalently the real part). For L e_n=-|n|e_n and f=e_1+i e_2 at x=0, Gamma(f,Lf) has a nonzero imaginary part. This diagnosis is mathematical source review, not yet a Lean theorem about that Fourier generator.
4. H=2 is not a probability covariance: Lean proves the quadratic form at times (1,2), coefficients (2,-1), equals -12. Signed algebraic kernels must not be labeled Gaussian probability realizations.
5. No H-dependent Gaussian OU curvature or hypercontractivity constant follows just from a covariance-matrix comparison. The Gaussian OU core proved here has curvature one.

## Remaining operator-domain obligations

- Identify a closed OU generator with minus the actual divergence-gradient composition on an exact common domain, using graph/spectral arguments.
- Extend Gamma and Gamma2 beyond the one-dimensional polynomial core with the required product integrability and second derivative domains.
- Prove any multivariate/infinite-dimensional higher recursion, rather than extrapolating the core formulas.
- Complete the matrix eigenbasis/full spectrum, trace and determinant assertions if needed; current results prove actual eigenpairs and factorization, not that entire spectral package.
- Define and justify a fractional-time generator separately from Gaussian OU. Indefinite Hurst kernels do not supply probability measures.

These obligations are not assumed. The verified checkpoint is sufficient to proceed to the separately queued stochastic-convolution investigation; it does not close the entire manuscript's curvature program.

## Exact new declarations

### Foundation/GaussianOUCore.lean

- OperatorDerivativeRewrite.Foundation.GaussianOUCore.generator — line 12
- OperatorDerivativeRewrite.Foundation.GaussianOUCore.gamma — line 14
- OperatorDerivativeRewrite.Foundation.GaussianOUCore.gammaTwo — line 17
- OperatorDerivativeRewrite.Foundation.GaussianOUCore.generator_actual_derivatives — line 20
- OperatorDerivativeRewrite.Foundation.GaussianOUCore.gamma_formula — line 26
- OperatorDerivativeRewrite.Foundation.GaussianOUCore.gammaTwo_formula — line 33
- OperatorDerivativeRewrite.Foundation.GaussianOUCore.gamma_actual_derivatives — line 42
- OperatorDerivativeRewrite.Foundation.GaussianOUCore.gamma_nonneg — line 46
- OperatorDerivativeRewrite.Foundation.GaussianOUCore.gaussian_curvature_one — line 50
- OperatorDerivativeRewrite.Foundation.GaussianOUCore.generator_integrable — line 55
- OperatorDerivativeRewrite.Foundation.GaussianOUCore.gamma_integrable — line 58
- OperatorDerivativeRewrite.Foundation.GaussianOUCore.gammaTwo_integrable — line 61
- OperatorDerivativeRewrite.Foundation.GaussianOUCore.gaussian_generator_pairing — line 64
- OperatorDerivativeRewrite.Foundation.GaussianOUCore.gaussian_generator_symmetric — line 73
- OperatorDerivativeRewrite.Foundation.GaussianOUCore.gaussian_generator_energy — line 82

### Foundation/FractionalCovarianceMatrices.lean

- OperatorDerivativeRewrite.Foundation.FractionalCovarianceMatrices.covarianceMatrix — line 13
- OperatorDerivativeRewrite.Foundation.FractionalCovarianceMatrices.covariancePower — line 15
- OperatorDerivativeRewrite.Foundation.FractionalCovarianceMatrices.covarianceMatrix_posSemidef — line 18
- OperatorDerivativeRewrite.Foundation.FractionalCovarianceMatrices.covariancePower_posSemidef — line 27
- OperatorDerivativeRewrite.Foundation.FractionalCovarianceMatrices.covariancePower_energy_nonneg — line 42
- OperatorDerivativeRewrite.Foundation.FractionalCovarianceMatrices.brownian_covariance — line 49
- OperatorDerivativeRewrite.Foundation.FractionalCovarianceMatrices.hurst_two_negative_energy — line 60

### Foundation/BrownianCovariancePowers.lean

- OperatorDerivativeRewrite.Foundation.BrownianCovariancePowers.innovation — line 11
- OperatorDerivativeRewrite.Foundation.BrownianCovariancePowers.covariance — line 13
- OperatorDerivativeRewrite.Foundation.BrownianCovariancePowers.summation — line 16
- OperatorDerivativeRewrite.Foundation.BrownianCovariancePowers.innovation_pos — line 18
- OperatorDerivativeRewrite.Foundation.BrownianCovariancePowers.innovation_sum — line 23
- OperatorDerivativeRewrite.Foundation.BrownianCovariancePowers.prefix_sum — line 29
- OperatorDerivativeRewrite.Foundation.BrownianCovariancePowers.covariance_factorization — line 37
- OperatorDerivativeRewrite.Foundation.BrownianCovariancePowers.covariance_power_brownian — line 53
- OperatorDerivativeRewrite.Foundation.BrownianCovariancePowers.comparisonRatio — line 61
- OperatorDerivativeRewrite.Foundation.BrownianCovariancePowers.comparisonRatio_identity — line 63
- OperatorDerivativeRewrite.Foundation.BrownianCovariancePowers.adjacent_ratio_two — line 67
- OperatorDerivativeRewrite.Foundation.BrownianCovariancePowers.adjacent_ratio_ne_innovation — line 70
- OperatorDerivativeRewrite.Foundation.BrownianCovariancePowers.predecessor — line 74
- OperatorDerivativeRewrite.Foundation.BrownianCovariancePowers.differenceVector — line 76
- OperatorDerivativeRewrite.Foundation.BrownianCovariancePowers.differenceVector_ne_zero — line 79
- OperatorDerivativeRewrite.Foundation.BrownianCovariancePowers.covariance_difference_action — line 91
- OperatorDerivativeRewrite.Foundation.BrownianCovariancePowers.generalized_eigenpair — line 110

### Foundation/FractionalWickCovariance.lean

- OperatorDerivativeRewrite.Foundation.FractionalWickCovariance.cylinder — line 17
- OperatorDerivativeRewrite.Foundation.FractionalWickCovariance.direction_inner — line 20
- OperatorDerivativeRewrite.Foundation.FractionalWickCovariance.cylinder_inner — line 25
- OperatorDerivativeRewrite.Foundation.FractionalWickCovariance.cylinder_centered — line 30
- OperatorDerivativeRewrite.Foundation.FractionalWickCovariance.cylinder_derivative_graph — line 34
- OperatorDerivativeRewrite.Foundation.FractionalWickCovariance.finite_sum_norm_sq — line 43
