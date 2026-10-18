import Foundation.IBMClockEighthMoment
import Foundation.FiniteMeasureL2Integration

/-! Genuine clock-parametrized source-L2 domain of the entire quartic
correction, before taking any source projection. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.IBMQuarticBochnerDomain
open InfiniteGaussian IBMConstructedSources IBMQuarticSecondGeometry
open IBMQuarticTimeProjection IBMQuarticSourceGrowth IBMClockEighthMoment

def timeSource (n : ℕ) (p : ℝ × SampleSpace) : GaussianL2 :=
  spatialQuartic n |clockPath p.2 p.1.toNNReal|

theorem timeSource_stronglyMeasurable (n : ℕ) : StronglyMeasurable (timeSource n) :=
  (spatialQuartic_continuous n).stronglyMeasurable.comp_measurable
    (continuous_abs.measurable.comp BrownianClockWeightedEnergy.sigma_measurable)

theorem timeSource_memLp (n : ℕ) (T : ℝ≥0) :
    MemLp (timeSource n) 2 ((volume.restrict (Set.Ioc 0 (T : ℝ))).prod gaussianProduct) := by
  obtain ⟨C,hC,hc⟩ := spatialQuartic_growth n
  apply (memLp_two_iff_integrable_sq_norm (timeSource_stronglyMeasurable n).aestronglyMeasurable).mpr
  apply ((horizon_growth_integrable T).const_mul (C^2)).mono'
    ((timeSource_stronglyMeasurable n).norm.pow 2).aestronglyMeasurable
  exact Eventually.of_forall fun p => by
    change ‖‖timeSource n p‖^2‖ ≤ C^2*(1+|clockPath p.2 p.1.toNNReal|)^8
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have hb : ‖timeSource n p‖ ≤ C*(1+|clockPath p.2 p.1.toNNReal|)^4 := by
      simpa only [timeSource, abs_abs] using hc |clockPath p.2 p.1.toNNReal|
    have hs := pow_le_pow_left₀ (norm_nonneg _) hb 2
    simpa only [mul_pow, ← pow_mul] using hs

theorem integratedCurvature_memLp (n : ℕ) (T : ℝ≥0) :
    MemLp (fun ω => ∫ s in 0..(T : ℝ), spatialQuartic n |clockPath ω s.toNNReal|)
      2 gaussianProduct := by
  have hi := FiniteMeasureL2Integration.column_integral_memLp
    (fun p => ‖timeSource n p‖) (timeSource_memLp n T).norm
  have hm : StronglyMeasurable (fun ω => ∫ s in Set.Ioc 0 (T : ℝ), timeSource n (s,ω)) :=
    (timeSource_stronglyMeasurable n).integral_prod_left'
  simp only [intervalIntegral.integral_of_le T.coe_nonneg]
  apply hi.mono' hm.aestronglyMeasurable
  exact Eventually.of_forall fun ω => norm_integral_le_integral_norm _

theorem origin_memLp (n : ℕ) (T : ℝ≥0) :
    MemLp (fun ω => BrownianMassLimitIdentification.coordinateClass T ω • IBMQuarticOriginProjection.originClass n)
      2 gaussianProduct :=
  (Lp.memLp (BochnerClosedOperator.tensor gaussianProduct
    (BrownianMassLimitIdentification.coordinateClass T) (IBMQuarticOriginProjection.originClass n))).ae_eq
    (BochnerClosedOperator.tensor_coeFn gaussianProduct _ _)

theorem wholeCorrection_memLp (n : ℕ) (T : ℝ≥0) : MemLp (wholeCorrection n T) 2 gaussianProduct := by
  have hi := (origin_memLp n T).add ((integratedCurvature_memLp n T).const_smul (1/2 : ℝ))
  convert hi using 1
  funext ω
  rfl

def wholeClass (n : ℕ) (T : ℝ≥0) : Lp GaussianL2 2 gaussianProduct :=
  (wholeCorrection_memLp n T).toLp _

theorem wholeClass_coeFn (n : ℕ) (T : ℝ≥0) :
    wholeClass n T =ᵐ[gaussianProduct] wholeCorrection n T := MemLp.coeFn_toLp _

end OperatorDerivativeRewrite.Foundation.IBMQuarticBochnerDomain
