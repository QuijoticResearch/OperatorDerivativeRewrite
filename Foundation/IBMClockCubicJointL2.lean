import Foundation.IBMSceneryGlobalGrowth
import Foundation.GaussianCubicGrowth

/-! Actual joint clock/scenery L2 for each fixed mollifier and time.
No uniform mollifier-limit or time-integrated joint estimate is assumed. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.IBMClockCubicJointL2
open InfiniteGaussian IBMClockCubicCorrection IBMSceneryCubicProjection
open IBMGaussianSteinMoments IBMCubicFirstChaos GaussianCubicGrowth IBMSceneryGlobalGrowth
attribute [local irreducible] IBMConstructedSources.mollifiedValue IBMDyadicExtension.field

theorem spatialCorrection_global_growth (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖spatialCorrection n x‖ ≤ C*(1+|x|)^3 := by
  obtain ⟨A,hA,hU⟩ := tripleCoefficient_global_growth n 0
  obtain ⟨B,hB,hV⟩ := tripleCoefficient_global_growth n 1
  obtain ⟨D,hD,hW⟩ := tripleCoefficient_global_growth n 2
  refine ⟨18*(A+B+D)^3,by positivity, ?_⟩
  intro x
  have hP : 0 ≤ 1+|x| := by positivity
  have hu : ‖tripleCoefficient n x 0‖ ≤ (A+B+D)*(1+|x|) :=
    (hU x).trans (mul_le_mul_of_nonneg_right (by linarith) hP)
  have hv : ‖tripleCoefficient n x 1‖ ≤ (A+B+D)*(1+|x|) :=
    (hV x).trans (mul_le_mul_of_nonneg_right (by linarith) hP)
  have hw : ‖tripleCoefficient n x 2‖ ≤ (A+B+D)*(1+|x|) :=
    (hW x).trans (mul_le_mul_of_nonneg_right (by linarith) hP)
  have hg := correction_norm_le _ _ _ ((A+B+D)*(1+|x|)) (by positivity) hu hv hw
  simpa only [spatialCorrection,mul_pow,mul_assoc] using hg

theorem clock_memLp_six (t : ℝ≥0) :
    MemLp (fun ω => IBMConstructedSources.clockPath ω t) 6 gaussianProduct :=
  (GaussianTimeProcess.process_memLp t 6 (by norm_num)).ae_eq
    (IBMConstructedSources.clockPath_coordinate_ae t).symm

theorem clock_cubic_growth_memLp (t : ℝ≥0) :
    MemLp (fun ω => (1+|IBMConstructedSources.clockPath ω t|)^3) 2 gaussianProduct := by
  have hf : MemLp (fun ω => 1+|IBMConstructedSources.clockPath ω t|) 6 gaussianProduct := by
    have hnorm : MemLp (fun ω => |IBMConstructedSources.clockPath ω t|) 6 gaussianProduct := by
      simpa only [Real.norm_eq_abs] using (clock_memLp_six t).norm
    have hconst : MemLp (fun _ : SampleSpace => (1 : ℝ)) 6 gaussianProduct := memLp_const 1
    exact hconst.add hnorm
  have hp := hf.norm_rpow_div (3 : ℝ≥0∞)
  norm_num at hp
  convert hp using 1
  · funext ω
    rw [abs_of_nonneg (by positivity : 0 ≤ 1+|IBMConstructedSources.clockPath ω t|)]
  · rw [show (6 : ℝ≥0∞)=2*3 by norm_num,div_eq_mul_inv,mul_assoc,
      ENNReal.mul_inv_cancel (by norm_num) (by norm_num),mul_one]

theorem section_energy (n : ℕ) (t : ℝ≥0) (ωY : SampleSpace) :
    ‖sectionClass n t ωY‖^2=∫ ωX, (value n t (ωX,ωY))^2 ∂gaussianProduct := by
  rw [← real_inner_self_eq_norm_sq,L2_inner_eq_integral]
  apply integral_congr_ae
  filter_upwards [sectionClass_coeFn n t ωY] with ωX hx
  simp only [real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs,hx]

theorem value_memLp_joint (n : ℕ) (t : ℝ≥0) :
    MemLp (value n t) 2 IBMSourceLaws.jointMeasure := by
  have hm : Measurable (value n t) := (value_jointly_measurable n).comp
    (measurable_const.prodMk measurable_id)
  apply (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr
  change Integrable (fun p : SampleSpace × SampleSpace => (value n t p)^2)
    (gaussianProduct.prod gaussianProduct)
  apply (integrable_prod_iff' (hm.pow_const 2).aestronglyMeasurable).mpr
  constructor
  · exact Eventually.of_forall fun ωY => (section_memLp n t ωY).integrable_sq
  · obtain ⟨C,hC,hgrowth⟩ := spatialCorrection_global_growth n
    apply ((clock_cubic_growth_memLp t).integrable_sq.const_mul (C^2)).mono'
      (hm.pow_const 2).stronglyMeasurable.norm.integral_prod_left'.aestronglyMeasurable
    exact Eventually.of_forall fun ωY => by
      rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      have he : (∫ ωX, ‖(value n t (ωX,ωY))^2‖ ∂gaussianProduct)=‖sectionClass n t ωY‖^2 := by
        rw [section_energy]
        apply integral_congr_ae
        exact Eventually.of_forall fun _ => Real.norm_of_nonneg (sq_nonneg _)
      rw [he]
      have hb : ‖sectionClass n t ωY‖ ≤ C*(1+|IBMConstructedSources.clockPath ωY t|)^3 := by
        simpa only [sectionClass,abs_abs] using hgrowth |IBMConstructedSources.clockPath ωY t|
      calc
        _ ≤ (C*(1+|IBMConstructedSources.clockPath ωY t|)^3)^2 := by gcongr
        _ = _ := by ring

end OperatorDerivativeRewrite.Foundation.IBMClockCubicJointL2
