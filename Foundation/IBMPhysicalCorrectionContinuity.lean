import Foundation.IBMPhysicalNativeCorrectionSteps

/-! Time-L2 continuity of the ORIGINAL physical IBM correction.
The origin term uses the already constructed Tanaka mass, not a new version. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal ENNReal BesselPotentialSpace
namespace OperatorDerivativeRewrite.Foundation.IBMPhysicalCorrectionContinuity
open InfiniteGaussian IBMPhysicalWeakWiener IBMPhysicalCorrectedVariation
open IBMPhysicalMeshVariation IBMPhysicalCorrectionLocalTime
local instance : InnerProductSpace ℝ Kernel := InnerProductSpace.rclikeToReal ℂ _

theorem residual_energy (a b : ℝ≥0) (hab : a ≤ b) :
    ‖residualClass b-residualClass a‖^2 ≤
      rateConstant * (((b : ℝ)-a)*Real.sqrt ((b : ℝ)-a)) := by
  rw [BochnerL2Dominated.norm_sq_integral]
  have he : (∫ Y, ‖(residualClass b-residualClass a) Y‖^2 ∂gaussianProduct) =
      ∫ Y, ‖residual b Y-residual a Y‖^2 ∂gaussianProduct := by
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (residualClass b) (residualClass a),
      residualClass_ae b, residualClass_ae a] with Y hs hb ha
    simp only [hs, Pi.sub_apply, hb, ha]
  rw [he]
  exact cell_rate a b hab

theorem residual_energy_abs (a b : ℝ≥0) :
    ‖residualClass b-residualClass a‖^2 ≤
      rateConstant * (|(b : ℝ)-a| * Real.sqrt |(b : ℝ)-a|) := by
  rcases le_total a b with h | h
  · simpa only [abs_of_nonneg (sub_nonneg.mpr (show (a : ℝ) ≤ b from h))] using
      residual_energy a b h
  · have he := residual_energy b a h
    rw [norm_sub_rev] at he
    have ha : |(b : ℝ)-a| = (a : ℝ)-b := abs_of_nonpos
      (sub_nonpos.mpr (show (b : ℝ) ≤ a from h)) |>.trans (neg_sub _ _)
    simpa only [ha] using he

theorem residual_continuous : Continuous residualClass := by
  apply continuous_iff_continuousAt.mpr
  intro a
  have hc : Continuous (fun b : ℝ≥0 =>
      rateConstant * (|(b : ℝ)-a| * Real.sqrt |(b : ℝ)-a|)) := by fun_prop
  have hu : Tendsto (fun b : ℝ≥0 =>
      rateConstant * (|(b : ℝ)-a| * Real.sqrt |(b : ℝ)-a|)) (𝓝 a) (𝓝 0) := by
    simpa using (hc.continuousAt (x := a)).tendsto
  have hs : Tendsto (fun b : ℝ≥0 => ‖residualClass b-residualClass a‖^2)
      (𝓝 a) (𝓝 0) := squeeze_zero (fun b => sq_nonneg _)
        (fun b => residual_energy_abs a b) hu
  have hn := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simp only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] at hn
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hn

theorem localTime_continuous : Continuous localTimeClass := by
  exact ((ContinuousLinearMap.toSpanSingleton ℂ (IBMPhysicalDirac.dirac 0)).compLpL
    2 gaussianProduct).continuous.comp
      ((ComplexL2Isometry.ofReal gaussianProduct).continuous.comp
        BrownianTanakaResidual.mass_continuous)

theorem correction_continuous : Continuous IBMPhysicalPointKernelIto.correctionLimit := by
  have he : IBMPhysicalPointKernelIto.correctionLimit =
      fun t => residualClass t+localTimeClass t := funext original_correction_split
  rw [he]
  exact residual_continuous.add localTime_continuous

theorem correction_uniformContinuousOn (T : ℝ≥0) :
    UniformContinuousOn IBMPhysicalPointKernelIto.correctionLimit (Set.Icc 0 T) :=
  isCompact_Icc.uniformContinuousOn_of_continuous correction_continuous.continuousOn

end OperatorDerivativeRewrite.Foundation.IBMPhysicalCorrectionContinuity


