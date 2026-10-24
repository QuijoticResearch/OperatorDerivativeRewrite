import Foundation.IBMPhysicalCellSlope

/-! Exact stochastic representatives of the original physical cell-error
integrand, including its support and frozen ACTUAL left clock value. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal BesselPotentialSpace
namespace OperatorDerivativeRewrite.Foundation.IBMPhysicalCellSlopeActual
open InfiniteGaussian GaussianTimeProcess GaussianTimeHilbert GaussianTimeProductL2
open GaussianHermiteRepresentation BrownianClockWeightedEnergy IBMConstructedSources
open IBMPhysicalCellSlope IBMPhysicalReflectedPrimitive IBMPhysicalWeakWiener
local instance : InnerProductSpace ℝ Kernel := InnerProductSpace.rclikeToReal ℂ _
attribute [local irreducible] IBMPhysicalReflectedPrimitive.slope IBMConstructedSources.clockPath

theorem currentClass_ae (a b : ℝ≥0) : currentClass a b =ᵐ[
    PredictableRealL2.horizonMeasure b gaussianProduct] fun z =>
      (Ioc (a : ℝ) (b : ℝ)).indicator (fun _ => sigma z) z.1 := by
  filter_upwards [LpToLpRestrictCLM_coeFn ℝ (PredictableRealL2.horizon b) (current a b).val,
    ae_restrict_of_ae (Lp.coeFn_sub (hermiteIntegrand 1 b).val (hermiteIntegrand 1 a).val),
    ae_restrict_of_ae (BrownianSignIntegral.brownian_field_joint b),
    ae_restrict_of_ae (BrownianSignIntegral.brownian_field_joint a),
    ae_restrict_mem (PredictableRealL2.horizon_measurable b)] with z hr hd hb ha hz
  change currentClass a b z = (current a b).val z at hr
  change (current a b).val z = (hermiteIntegrand 1 b).val z - (hermiteIntegrand 1 a).val z at hd
  rw [hr, hd, hb, ha, indicator_of_mem hz]
  by_cases hza : z ∈ PredictableRealL2.horizon a
  · have hn : z.1 ∉ Ioc (a : ℝ) (b : ℝ) := by
      intro hc
      linarith [hza.1.2, hc.1]
    simp only [indicator_of_mem hza, indicator_of_notMem hn, sub_self]
  · have hax : (a : ℝ) < z.1 := by
      by_contra h
      apply hza
      exact ⟨⟨hz.1.1, le_of_not_gt h⟩, mem_univ _⟩
    have hc : z.1 ∈ Ioc (a : ℝ) (b : ℝ) := ⟨hax, hz.1.2⟩
    simp only [indicator_of_notMem hza, indicator_of_mem hc, sub_zero]

theorem past_global_ae (a b : ℝ≥0) : (past a b).val =ᵐ[timeProbability] fun z =>
    (Ioc (a : ℝ) (b : ℝ)).indicator (fun _ => clockPath z.2 a) z.1 := by
  have ht := (Measure.quasiMeasurePreserving_fst
    (μ := (volume : Measure ℝ)) (ν := gaussianProduct)).ae_eq_comp (intervalVector_coeFn a b)
  have hc := (Measure.quasiMeasurePreserving_snd
    (μ := (volume : Measure ℝ)) (ν := gaussianProduct)).ae_eq_comp (clockPath_coordinate_ae a)
  filter_upwards [productTensor_coeFn (intervalVector a b) (wienerL2 a), ht, hc]
    with z hp ht hc
  change (past a b).val z = _ at hp
  change clockPath z.2 a = (wienerL2 a) z.2 at hc
  simp only [Function.comp_def] at ht
  rw [hp, ht, ← hc]
  by_cases hz : z.1 ∈ Ioc (a : ℝ) (b : ℝ) <;> simp [hz]

theorem pastClass_ae (a b : ℝ≥0) : pastClass a b =ᵐ[
    PredictableRealL2.horizonMeasure b gaussianProduct] fun z =>
      (Ioc (a : ℝ) (b : ℝ)).indicator (fun _ => clockPath z.2 a) z.1 := by
  filter_upwards [LpToLpRestrictCLM_coeFn ℝ (PredictableRealL2.horizon b) (past a b).val,
    ae_restrict_of_ae (past_global_ae a b)] with z hr hp
  change pastClass a b z = (past a b).val z at hr
  rw [hr, hp]

theorem errorClass_actual_ae (a b : ℝ≥0) : errorClass a b =ᵐ[
    PredictableRealL2.horizonMeasure b gaussianProduct] fun z =>
      (Ioc (a : ℝ) (b : ℝ)).indicator
        (fun _ => slope (sigma z) - slope (clockPath z.2 a)) z.1 := by
  filter_upwards [errorClass_ae a b, currentClass_ae a b, pastClass_ae a b] with z he hc hp
  rw [he, error, hc, hp]
  by_cases hz : z.1 ∈ Ioc (a : ℝ) (b : ℝ)
  · simp only [indicator_of_mem hz]
  · simp only [indicator_of_notMem hz, slope_zero, sub_self]

theorem integral_energy (a b : ℝ≥0) : ‖IBMPhysicalCellSlope.integral a b‖^2 =
    ∫ z, ‖error a b z‖^2 ∂(PredictableRealL2.horizonMeasure b gaussianProduct) := by
  rw [IBMPhysicalCellSlope.integral_norm, BochnerL2Dominated.norm_sq_integral]
  exact integral_congr_ae ((errorClass_ae a b).mono fun z he => congrArg (fun x : Kernel => ‖x‖^2) he)

theorem integral_actual_energy (a b : ℝ≥0) : ‖IBMPhysicalCellSlope.integral a b‖^2 =
    ∫ z, (Ioc (a : ℝ) (b : ℝ)).indicator
      (fun _ => ‖slope (sigma z) - slope (clockPath z.2 a)‖^2) z.1
        ∂(PredictableRealL2.horizonMeasure b gaussianProduct) := by
  rw [IBMPhysicalCellSlope.integral_norm, BochnerL2Dominated.norm_sq_integral]
  apply integral_congr_ae
  filter_upwards [errorClass_actual_ae a b] with z he
  rw [he]
  by_cases hz : z.1 ∈ Ioc (a : ℝ) (b : ℝ) <;> simp [hz]

theorem scalar_distance_ae (a b : ℝ≥0) :
    (fun z => |pastClass a b z-currentClass a b z|) =ᵐ[
      PredictableRealL2.horizonMeasure b gaussianProduct] fun z =>
        (Ioc (a : ℝ) (b : ℝ)).indicator (fun _ => |sigma z-clockPath z.2 a|) z.1 := by
  filter_upwards [currentClass_ae a b, pastClass_ae a b] with z hc hp
  rw [hp, hc]
  by_cases hz : z.1 ∈ Ioc (a : ℝ) (b : ℝ)
  · simp only [indicator_of_mem hz, abs_sub_comm]
  · simp only [indicator_of_notMem hz, sub_self, abs_zero]

theorem scalar_distance_integrable (a b : ℝ≥0) :
    Integrable (fun z => |pastClass a b z-currentClass a b z|)
      (PredictableRealL2.horizonMeasure b gaussianProduct) := by
  have h := ((Lp.memLp (pastClass a b)).sub (Lp.memLp (currentClass a b))).integrable
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  simpa only [Real.norm_eq_abs, Pi.sub_apply] using h.norm

theorem actual_distance_integrable (a b : ℝ≥0) :
    Integrable (fun z : ℝ × SampleSpace => (Ioc (a : ℝ) (b : ℝ)).indicator
      (fun _ => |sigma z-clockPath z.2 a|) z.1)
        (PredictableRealL2.horizonMeasure b gaussianProduct) :=
  (scalar_distance_integrable a b).congr (scalar_distance_ae a b)

theorem integral_clock_distance_bound (a b : ℝ≥0) :
    ‖IBMPhysicalCellSlope.integral a b‖^2 ≤ 4*‖IBMPhysicalNoiseClock.physicalDerivative‖^2 *
      ∫ z, (Ioc (a : ℝ) (b : ℝ)).indicator
        (fun _ => |sigma z-clockPath z.2 a|) z.1
          ∂(PredictableRealL2.horizonMeasure b gaussianProduct) := by
  rw [integral_energy]
  have he := (memLp_two_iff_integrable_sq_norm (error_memLp a b).aestronglyMeasurable).mp
    (error_memLp a b)
  calc
    _ ≤ ∫ z, 4*‖IBMPhysicalNoiseClock.physicalDerivative‖^2 *
        |pastClass a b z-currentClass a b z|
          ∂(PredictableRealL2.horizonMeasure b gaussianProduct) :=
      integral_mono_ae he ((scalar_distance_integrable a b).const_mul _)
        (Eventually.of_forall fun z => error_square_bound a b z)
    _ = _ := by
      rw [integral_const_mul]
      congr 1
      exact integral_congr_ae (scalar_distance_ae a b)

theorem integral_scalarization (a b : ℝ≥0) (L : Tests) :
    L.compLpL 2 gaussianProduct (IBMPhysicalCellSlope.integral a b) =
      GaussianComplexHorizonIto.realIto b
        (L.compLpL 2 (GaussianComplexHorizonIto.predictableMeasure b)
          (IBMPhysicalClockIto.trimEquiv b (integrand a b))) :=
  IBMPhysicalClockItoScalar.native_scalarization b L (integrand a b)

end OperatorDerivativeRewrite.Foundation.IBMPhysicalCellSlopeActual
