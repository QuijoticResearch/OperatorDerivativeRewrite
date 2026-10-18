import Foundation.IBMSchwartzScalarRecovery
import Foundation.IBMClockEighthMoment
import Foundation.FiniteMeasureL2Integration

/-! Genuine clock-parametrized source-L2 domain of the entire nonlinear Schwartz
correction, before taking any source projection. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.IBMSchwartzBochnerDomain
open InfiniteGaussian IBMConstructedSources IBMSchwartzSecondProjection
open IBMSchwartzTimeProjection IBMSchwartzSourceContinuity IBMSchwartzHeatBounds IBMClockEighthMoment
open IBMCorrectionStein

variable (g : SchwartzMap ℝ ℝ) (a : ℝ)

theorem mollified_growth (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r, ‖mollifiedClass g a n r‖ ≤ C*(1+|r|)^2 := by
  obtain ⟨B,hB,hb⟩ := IBMSceneryGlobalGrowth.tripleCoefficient_global_growth n 1
  obtain ⟨D,hD,hd⟩ := IBMSceneryGlobalGrowth.tripleCoefficient_global_growth n 2
  refine ⟨2*SchwartzMap.seminorm ℝ 0 0 (jet g 2)*B^2+
    SchwartzMap.seminorm ℝ 0 0 (jet g 1)*D, by positivity, fun r => ?_⟩
  have hq : 1+|r| ≤ (1+|r|)^2 := by nlinarith [abs_nonneg r]
  have hv := pow_le_pow_left₀ (norm_nonneg _) (hb r) 2
  have h1 := mul_le_mul_of_nonneg_left (hd r)
    (by positivity : 0 ≤ SchwartzMap.seminorm ℝ 0 0 (jet g 1))
  have h2 := mul_le_mul_of_nonneg_left hv
    (by positivity : 0 ≤ 2*SchwartzMap.seminorm ℝ 0 0 (jet g 2))
  have h3 := mul_le_mul_of_nonneg_left hq
    (by positivity : 0 ≤ SchwartzMap.seminorm ℝ 0 0 (jet g 1)*D)
  apply (correction_norm_le g a _ _ _).trans
  nlinarith



def timeSource (n : ℕ) (p : ℝ × SampleSpace) : GaussianL2 :=
  mollifiedClass g a n |clockPath p.2 p.1.toNNReal|

theorem timeSource_stronglyMeasurable (n : ℕ) : StronglyMeasurable (timeSource g a n) :=
  (mollifiedClass_continuous g a n).stronglyMeasurable.comp_measurable
    (continuous_abs.measurable.comp BrownianClockWeightedEnergy.sigma_measurable)

theorem timeSource_memLp (n : ℕ) (T : ℝ≥0) :
    MemLp (timeSource g a n) 2 ((volume.restrict (Set.Ioc 0 (T : ℝ))).prod gaussianProduct) := by
  obtain ⟨C,hC,hc⟩ := mollified_growth g a n
  apply (memLp_two_iff_integrable_sq_norm (timeSource_stronglyMeasurable g a n).aestronglyMeasurable).mpr
  apply ((horizon_growth_integrable T).const_mul (C^2)).mono'
    ((timeSource_stronglyMeasurable g a n).norm.pow 2).aestronglyMeasurable
  exact Eventually.of_forall fun p => by
    change ‖‖timeSource g a n p‖^2‖ ≤ C^2*(1+|clockPath p.2 p.1.toNNReal|)^8
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have hb : ‖timeSource g a n p‖ ≤ C*(1+|clockPath p.2 p.1.toNNReal|)^2 := by
      simpa only [timeSource, abs_abs] using hc |clockPath p.2 p.1.toNNReal|
    have hs := pow_le_pow_left₀ (norm_nonneg _) hb 2
    have hs' : ‖timeSource g a n p‖^2 ≤ C^2*(1+|clockPath p.2 p.1.toNNReal|)^4 := by
      simpa only [mul_pow, ← pow_mul] using hs
    have hp : (1+|clockPath p.2 p.1.toNNReal|)^4 ≤ (1+|clockPath p.2 p.1.toNNReal|)^8 :=
      pow_le_pow_right₀ (by linarith [abs_nonneg (clockPath p.2 p.1.toNNReal)]) (by norm_num)
    exact hs'.trans (mul_le_mul_of_nonneg_left hp (sq_nonneg C))

theorem integratedCurvature_memLp (n : ℕ) (T : ℝ≥0) :
    MemLp (fun ω => ∫ s in 0..(T : ℝ), mollifiedClass g a n |clockPath ω s.toNNReal|)
      2 gaussianProduct := by
  have hi := FiniteMeasureL2Integration.column_integral_memLp
    (fun p => ‖timeSource g a n p‖) (timeSource_memLp g a n T).norm
  have hm : StronglyMeasurable (fun ω => ∫ s in Set.Ioc 0 (T : ℝ), timeSource g a n (s,ω)) :=
    (timeSource_stronglyMeasurable g a n).integral_prod_left'
  simp only [intervalIntegral.integral_of_le T.coe_nonneg]
  apply hi.mono' hm.aestronglyMeasurable
  exact Eventually.of_forall fun ω => norm_integral_le_integral_norm _

theorem origin_memLp (n : ℕ) (T : ℝ≥0) :
    MemLp (fun ω => BrownianMassLimitIdentification.coordinateClass T ω • originClass g a n)
      2 gaussianProduct :=
  (Lp.memLp (BochnerClosedOperator.tensor gaussianProduct
    (BrownianMassLimitIdentification.coordinateClass T) (originClass g a n))).ae_eq
    (BochnerClosedOperator.tensor_coeFn gaussianProduct _ _)

theorem wholeCorrection_memLp (n : ℕ) (T : ℝ≥0) : MemLp (wholeCorrection g a n T) 2 gaussianProduct := by
  have hi := (origin_memLp g a n T).add ((integratedCurvature_memLp g a n T).const_smul (1/2 : ℝ))
  convert hi using 1
  funext ω
  rfl

def wholeClass (n : ℕ) (T : ℝ≥0) : Lp GaussianL2 2 gaussianProduct :=
  (wholeCorrection_memLp g a n T).toLp _

theorem wholeClass_coeFn (n : ℕ) (T : ℝ≥0) :
    wholeClass g a n T =ᵐ[gaussianProduct] wholeCorrection g a n T := MemLp.coeFn_toLp _

end OperatorDerivativeRewrite.Foundation.IBMSchwartzBochnerDomain
