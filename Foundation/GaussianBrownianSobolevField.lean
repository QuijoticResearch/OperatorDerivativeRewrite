import Foundation.GaussianQuadraticIto

/-! Genuine adapted graph approximation of the running Brownian field.
A bounded first-chaos map is used only on fields where agreement with the
actual derivative has been proved; it does not redefine the full derivative. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianBrownianSobolevField
open InfiniteGaussian GaussianTimeHilbert GaussianTimeProcess GaussianTimeDivergence
open GaussianTimeProductL2 GaussianProductDerivative GaussianPredictableFull
open GaussianQuadraticRepresentation GaussianAdaptedGraphCore GaussianContinuousRigidity
open GaussianSensitivityCore SeparableHilbertEmbedding GaussianTimePolynomialPairing
attribute [local instance] timeHilbert_secondCountable coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
set_option backward.isDefEq.respectTransparency false

def firstChaosGradient : GaussianL2 →L[ℝ] GaussianVectorL2 :=
  (Lp.constL 2 gaussianProduct ℝ).comp firstChaosEmbedding.toContinuousLinearMap.adjoint

theorem firstChaosGradient_apply (h : CoefficientSpace) :
    firstChaosGradient (firstChaosEmbedding h) = Lp.const 2 gaussianProduct h := by
  have he := congrArg (fun L : CoefficientSpace →L[ℝ] CoefficientSpace => L h)
    firstChaosEmbedding.adjoint_comp_self
  change firstChaosEmbedding.toContinuousLinearMap.adjoint (firstChaosEmbedding h) = h at he
  change Lp.const 2 gaussianProduct (firstChaosEmbedding.toContinuousLinearMap.adjoint _) = _
  rw [he]

def fieldFirstChaosGradient : TimeProbabilityL2 →L[ℝ] ProductDerivativeL2 :=
  vectorCurry.symm.toLinearIsometry.toContinuousLinearMap.comp
    ((firstChaosGradient.compLpL 2 volume).comp scalarCurry.toLinearIsometry.toContinuousLinearMap)

theorem fieldFirstChaosGradient_tensor (a : TimeHilbert) (f : GaussianL2) :
    fieldFirstChaosGradient (productTensor a f) =
      ProductL2Curry.productTensor volume gaussianProduct a (firstChaosGradient f) := by
  apply vectorCurry.injective
  change vectorCurry (vectorCurry.symm (firstChaosGradient.compLp (scalarCurry _))) =
    ProductL2Curry.curry volume gaussianProduct _
  rw [vectorCurry.apply_symm_apply, scalarCurry_productTensor, ProductL2Curry.curry_productTensor]
  apply Lp.ext
  filter_upwards [firstChaosGradient.coeFn_compLp (BochnerClosedOperator.tensor volume a f),
    BochnerClosedOperator.tensor_coeFn volume a f,
    BochnerClosedOperator.tensor_coeFn volume a (firstChaosGradient f)] with t hc ht hg
  rw [hc, ht, map_smul, hg]

theorem firstChaosGradient_past_linear (r : ℝ≥0) :
    firstChaosGradient (pastCoefficient (fun _ : Fin 1 => r) (MvPolynomial.X 0)) =
      polynomialDerivative (pastCoefficient (fun _ : Fin 1 => r) (MvPolynomial.X 0)) := by
  have hf : (pastCoefficient (fun _ : Fin 1 => r) (MvPolynomial.X 0) : GaussianL2) =
      firstChaosEmbedding (hilbertEmbedding TimeHilbert (timeVector r)) := by
    apply Lp.ext
    filter_upwards [pastCoefficient_coeFn (fun _ : Fin 1 => r) (MvPolynomial.X 0)] with ω hf
    calc
      _ = process r ω := by simpa only [MvPolynomial.eval_X] using hf
      _ = _ := rfl
  rw [hf, firstChaosGradient_apply]
  apply Lp.ext
  have hg : polynomialDerivative (pastCoefficient (fun _ : Fin 1 => r) (MvPolynomial.X 0)) =
      isonormalCylinderGradientL2 (fun _ : Fin 1 => hilbertEmbedding TimeHilbert (timeVector r))
        (MvPolynomial.X 0) := polynomialDerivative_on_cylinder _ _
  rw [hg]
  filter_upwards [Lp.coeFn_const (p := 2) (μ := gaussianProduct)
    (c := hilbertEmbedding TimeHilbert (timeVector r)),
    isonormalCylinderGradientL2_coeFn
      (fun _ : Fin 1 => hilbertEmbedding TimeHilbert (timeVector r)) (MvPolynomial.X 0)]
    with ω hc hg
  simpa only [hc, hg, Function.const_apply, isonormalCylinderGradient_X]

theorem linear_past_step_graph (r s t : ℝ≥0) (hrs : r ≤ s) (hst : s ≤ t) :
    (productTensor (intervalVector s t) (pastCoefficient (fun _ : Fin 1 => r) (MvPolynomial.X 0)),
      fieldFirstChaosGradient (productTensor (intervalVector s t)
        (pastCoefficient (fun _ : Fin 1 => r) (MvPolynomial.X 0)))) ∈ completedGraph := by
  rw [fieldFirstChaosGradient_tensor, firstChaosGradient_past_linear]
  exact polynomialGraph.le_topologicalClosure (Submodule.subset_span
    ⟨1, s, t, (fun _ => r), MvPolynomial.X 0, (fun _ => hrs), hst, rfl⟩)

theorem leftStepField_graph {n : ℕ} (τ : Fin (n + 1) → ℝ≥0) (hτ : Monotone τ) :
    ((leftStepField τ : TimeProbabilityL2),
      fieldFirstChaosGradient (leftStepField τ : TimeProbabilityL2)) ∈ completedGraph := by
  have hg := completedGraph.sum_mem (t := Finset.univ) (fun i (_ : i ∈ Finset.univ) =>
    linear_past_step_graph (τ i.castSucc) (τ i.castSucc) (τ i.succ) le_rfl
      (hτ (Fin.castSucc_le_succ i)))
  simpa only [leftStepField, Submodule.coe_sum, map_sum, ← prod_mk_sum, pastStep] using hg

/-- The SAME explicit left-point fields converge in the actual derivative graph.
No density theorem for the full independent Sobolev domain is assumed. -/
theorem quadraticIntegrand_graph (T : ℝ≥0) :
    ((quadraticIntegrand T : TimeProbabilityL2),
      fieldFirstChaosGradient (quadraticIntegrand T : TimeProbabilityL2)) ∈ completedGraph := by
  have hu := continuous_subtype_val.continuousAt.tendsto.comp (leftStepField_tendsto T)
  have hv := fieldFirstChaosGradient.continuous.continuousAt.tendsto.comp hu
  exact polynomialGraph.isClosed_topologicalClosure.mem_of_tendsto (hu.prodMk_nhds hv)
    (Eventually.of_forall fun n => leftStepField_graph _
      (GaussianBrownianQuadraticVariation.uniformTime_monotone T n))

theorem quadraticIntegrand_mem_independentSobolev (T : ℝ≥0) :
    (quadraticIntegrand T : TimeProbabilityL2) ∈ predictableSobolev :=
  completedGraph_mem_predictableSobolev (quadraticIntegrand_graph T)

/-- An independently specified running Brownian field has genuine graph-core
membership; no derivative or approximation hypothesis is imposed on u. -/
theorem runningBrownian_graph_of_slices (T : ℝ≥0) (u : fullPredictable)
    (hu : scalarCurry (u : TimeProbabilityL2) =ᵐ[volume] GaussianQuadraticIto.horizonValue T) :
    ((u : TimeProbabilityL2), fieldFirstChaosGradient u) ∈ completedGraph := by
  have he : u = quadraticIntegrand T := by
    apply Subtype.ext
    apply scalarCurry.injective
    exact Lp.ext (hu.trans (GaussianQuadraticIto.quadraticIntegrand_slices T).symm)
  rw [he]
  exact quadraticIntegrand_graph T

theorem quadraticIntegrand_sensitivity (T : ℝ≥0) :
    (itoIntegral (quadraticIntegrand T), fieldEmbedding (quadraticIntegrand T) +
      GaussianSensitivityIntegral.correction
        (fieldFirstChaosGradient (quadraticIntegrand T))) ∈ closedCylindricalDerivative.graph :=
  completedGraph_sensitivity (quadraticIntegrand_graph T)

theorem quadraticIntegrand_sensitivity_norm (T : ℝ≥0) :
    ‖GaussianSensitivityIntegral.correction (fieldFirstChaosGradient (quadraticIntegrand T))‖ =
      ‖fieldFirstChaosGradient (quadraticIntegrand T)‖ :=
  completedGraph_correction_norm
    (z := ((quadraticIntegrand T : TimeProbabilityL2),
      fieldFirstChaosGradient (quadraticIntegrand T : TimeProbabilityL2)))
    (quadraticIntegrand_graph T)

theorem firstChaosGradient_norm (h : CoefficientSpace) :
    ‖firstChaosGradient (firstChaosEmbedding h)‖ = ‖firstChaosEmbedding h‖ := by
  rw [firstChaosGradient_apply, firstChaosEmbedding.norm_map]
  simp [Lp.norm_const]

theorem quadraticIntegrand_gradient_norm (T : ℝ≥0) :
    ‖fieldFirstChaosGradient (quadraticIntegrand T)‖ = ‖quadraticIntegrand T‖ := by
  have he : vectorCurry (fieldFirstChaosGradient (quadraticIntegrand T)) =
      firstChaosGradient.compLp (scalarCurry (quadraticIntegrand T : TimeProbabilityL2)) :=
    vectorCurry.apply_symm_apply _
  rw [← vectorCurry.norm_map, he]
  change ‖firstChaosGradient.compLp (scalarCurry (quadraticIntegrand T : TimeProbabilityL2))‖ =
    ‖(quadraticIntegrand T : TimeProbabilityL2)‖
  rw [← scalarCurry.norm_map (quadraticIntegrand T : TimeProbabilityL2), Lp.norm_def, Lp.norm_def]
  congr 1
  apply eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _)
  filter_upwards [firstChaosGradient.coeFn_compLp
    (scalarCurry (quadraticIntegrand T : TimeProbabilityL2)),
    GaussianQuadraticIto.quadraticIntegrand_slices T] with t hc ht
  rw [hc, ht]
  unfold GaussianQuadraticIto.horizonValue
  by_cases h : t ∈ Ioc 0 (T : ℝ)
  · rw [indicator_of_mem h]
    exact firstChaosGradient_norm _
  · rw [indicator_of_notMem h, map_zero, norm_zero, norm_zero]

theorem quadraticIntegrand_norm_sq (T : ℝ≥0) :
    ‖quadraticIntegrand T‖ ^ 2 = (T : ℝ) ^ 2 / 2 := by
  have hs := GaussianQuadraticIncrement.centeredSquare_norm_sq
    (hilbertEmbedding TimeHilbert (timeVector T))
  rw [(hilbertEmbedding TimeHilbert).norm_map, timeVector_norm_sq] at hs
  change ‖terminalSquare T‖ ^ 2 = 2 * (T : ℝ) ^ 2 at hs
  rw [← itoIntegral.norm_map, integral_quadraticIntegrand, norm_smul, mul_pow, hs]
  norm_num
  ring

def quadraticIntegralDomain (T : ℝ≥0) : closedCylindricalDerivative.domain :=
  ⟨itoIntegral (quadraticIntegrand T), integral_mem_derivative_domain (quadraticIntegrand_graph T)⟩

/-- The full sensitivity correction for the running Brownian coefficient has
strictly positive energy T^2/2 whenever T>0. -/
theorem quadraticIntegral_sensitivity_energy (T : ℝ≥0) :
    ‖closedCylindricalDerivative (quadraticIntegralDomain T) -
      fieldEmbedding (quadraticIntegrand T)‖ ^ 2 = (T : ℝ) ^ 2 / 2 := by
  have he := closedCylindricalDerivative.mem_graph_snd_inj
    (closedCylindricalDerivative.mem_graph (quadraticIntegralDomain T))
    (quadraticIntegrand_sensitivity T) rfl
  rw [he, add_sub_cancel_left, quadraticIntegrand_sensitivity_norm,
    quadraticIntegrand_gradient_norm, quadraticIntegrand_norm_sq]

/-- The full derivative contains the terminal Brownian value; its predictable
projection, proved next, contains the running value instead. -/
theorem quadraticIntegral_derivative (T : ℝ≥0) :
    closedCylindricalDerivative (quadraticIntegralDomain T) =
      scalarTensor (hilbertEmbedding TimeHilbert (timeVector T)) (wienerL2 T) := by
  let h := hilbertEmbedding TimeHilbert (timeVector T)
  have hg := closedCylindricalDerivative_core_graph
    ((1 / 2 : ℝ) • GaussianQuadraticIncrement.centeredSquare h)
  have hf : (GaussianTimePolynomialPairing.firstChaosPolynomial h : GaussianL2) = wienerL2 T :=
    Lp.ext (firstChaosPolynomial_coeFn h)
  change ((1 / 2 : ℝ) • terminalSquare T,
    polynomialDerivative ((1 / 2 : ℝ) • GaussianQuadraticIncrement.centeredSquare h)) ∈
      closedCylindricalDerivative.graph at hg
  rw [map_smul, GaussianQuadraticIncrement.centeredSquare_derivative, smul_smul] at hg
  norm_num only [one_div, inv_mul_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), one_smul] at hg
  rw [hf, ← integral_quadraticIntegrand T] at hg
  exact closedCylindricalDerivative.mem_graph_snd_inj
    (closedCylindricalDerivative.mem_graph (quadraticIntegralDomain T)) hg rfl

/-- Concrete quadratic Clark--Ocone coefficient on the genuine full derivative
domain. The terminal-to-running projection is proved, not presumed. -/
theorem predictableProjection_terminalBrownian (T : ℝ≥0) :
    GaussianPredictableAdjoint.predictableProjection
      (scalarTensor (hilbertEmbedding TimeHilbert (timeVector T)) (wienerL2 T)) =
        quadraticIntegrand T := by
  have h := GaussianPredictableAdjoint.predictableAdjoint_eq_projected_derivative
    (quadraticIntegralDomain T)
  rw [quadraticIntegral_derivative] at h
  change GaussianPredictableAdjoint.predictableAdjoint (itoIntegral (quadraticIntegrand T)) = _ at h
  rw [GaussianPredictableAdjoint.predictableAdjoint_integral] at h
  exact h.symm

theorem quadraticIntegral_full_energy (T : ℝ≥0) :
    ‖closedCylindricalDerivative (quadraticIntegralDomain T)‖ ^ 2 = (T : ℝ) ^ 2 := by
  rw [quadraticIntegral_derivative, ← real_inner_self_eq_norm_sq,
    GaussianTimeFieldNorm.scalarTensor_pair_inner, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq, (hilbertEmbedding TimeHilbert).norm_map, timeVector_norm_sq]
  have h := wienerL2_sub_norm_sq 0 T (by positivity)
  simp only [wienerL2_zero, sub_zero, NNReal.coe_zero] at h
  rw [h]
  ring

/-- A verified random-volatility example: full Malliavin energy is NOT even
the expected stochastic increment energy. No pathwise bracket is asserted. -/
theorem quadraticIntegral_full_energy_ne_variance (T : ℝ≥0) (hT : 0 < T) :
    ‖closedCylindricalDerivative (quadraticIntegralDomain T)‖ ^ 2 ≠
      ‖itoIntegral (quadraticIntegrand T)‖ ^ 2 := by
  rw [quadraticIntegral_full_energy, itoIntegral.norm_map, quadraticIntegrand_norm_sq]
  have hp : (0 : ℝ) < T := hT
  nlinarith [sq_pos_of_pos hp]

end OperatorDerivativeRewrite.Foundation.GaussianBrownianSobolevField
