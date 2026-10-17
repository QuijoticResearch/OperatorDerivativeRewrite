import Foundation.BrownianWeightedSquareAdjoint

/-! Explicit coefficient identification in the actual Brownian-square weighted measure. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.BrownianWeightedSquareCoefficient
open InfiniteGaussian GaussianTimeSpaceHermite GaussianHermiteRepresentation GaussianHermiteIntegrand
open GaussianPredictableFull GaussianTimeProductL2 GaussianProductDerivative GaussianCubicDiagnostic
open BrownianClockWeightedEnergy BrownianWeightedPredictableIntegral
open BrownianVolatilitySquare BrownianWeightedSquareAdjoint IBMConstructedSources
set_option backward.isDefEq.respectTransparency false

theorem correct_slices (T : ℝ≥0) :
    scalarCurry (correct T : TimeProbabilityL2) =ᵐ[volume]
      (Ioc 0 (T : ℝ)).indicator (fun t => (brownianCore t.toNNReal 3 : GaussianL2) +
        (2*(T : ℝ)) • (brownianCore t.toNNReal 1 : GaussianL2)) := by
  change scalarCurry ((hermiteIntegrand 3 T : TimeProbabilityL2) +
    (2*(T : ℝ)) • (hermiteIntegrand 1 T : TimeProbabilityL2)) =ᵐ[volume] _
  rw [map_add, map_smul]
  filter_upwards [Lp.coeFn_add (scalarCurry (hermiteIntegrand 3 T))
      ((2*(T : ℝ)) • scalarCurry (hermiteIntegrand 1 T)),
    Lp.coeFn_smul (2*(T : ℝ)) (scalarCurry (hermiteIntegrand 1 T)),
    hermiteIntegrand_slices 3 T, hermiteIntegrand_slices 1 T] with t ha hs h3 h1
  rw [ha, Pi.add_apply, hs, Pi.smul_apply, h3, h1]
  by_cases ht : t ∈ Ioc 0 (T : ℝ)
  · simp only [horizonValue, indicator_of_mem ht]
  · simp [horizonValue, ht]

theorem correct_joint (T : ℝ≥0) :
    (correct T : TimeProbabilityL2) =ᵐ[base T] fun z =>
      sigma z * (sigma z^2+2*(T : ℝ)-3*z.1) := by
  change ∀ᵐ z ∂PredictableRealL2.horizonMeasure T gaussianProduct,
    (correct T : TimeProbabilityL2) z = sigma z * (sigma z^2+2*(T : ℝ)-3*z.1)
  rw [PredictableRealL2.horizonMeasure_eq_product]
  have hm : MeasurableSet {z : ℝ × SampleSpace |
      (correct T : TimeProbabilityL2) z = sigma z * (sigma z^2+2*(T : ℝ)-3*z.1)} :=
    measurableSet_eq_fun (Lp.stronglyMeasurable _).measurable
      (sigma_measurable.mul ((sigma_measurable.pow_const 2).add_const _ |>.sub
        (measurable_fst.const_mul 3)))
  apply (Measure.ae_prod_iff_ae_ae hm).mpr
  filter_upwards [ae_restrict_of_ae (correct_slices T),
    ae_restrict_of_ae (scalarCurry_coeFn (correct T : TimeProbabilityL2)),
    ae_restrict_mem measurableSet_Ioc] with t ht hc hpos
  rw [indicator_of_mem hpos] at ht
  filter_upwards [hc, clockPath_coordinate_ae t.toNNReal,
    brownianCore_coeFn t.toNNReal 3, brownianCore_coeFn t.toNNReal 1,
    Lp.coeFn_add (brownianCore t.toNNReal 3 : GaussianL2)
      ((2*(T : ℝ)) • (brownianCore t.toNNReal 1 : GaussianL2)),
    Lp.coeFn_smul (2*(T : ℝ)) (brownianCore t.toNNReal 1 : GaussianL2)]
      with ω hc hw h3 h1 ha hs
  rw [← hc, ht, ha, Pi.add_apply, hs, Pi.smul_apply, h3, h1]
  simp only [sigma, hw, value_three, value_one, smul_eq_mul,
    Real.coe_toNNReal _ hpos.1.le]
  ring

theorem squareCoefficient_formula (T : ℝ≥0) :
    (squareCoefficient T : Lp ℝ 2 (energy T)) =ᵐ[energy T]
      fun z => sigma z^2+2*(T : ℝ)-3*z.1 := by
  have hc := (energy_absolutelyContinuous T).ae_eq (correct_joint T)
  have hn := (energy_absolutelyContinuous T).ae_le (sigma_nonzero T)
  filter_upwards [pullback_coeFn T (correct T), hc, hn] with z hp hc hn
  change (pullback T (correct T) : Lp ℝ 2 (energy T)) z = _
  rw [hp, hc]
  field_simp

end OperatorDerivativeRewrite.Foundation.BrownianWeightedSquareCoefficient
