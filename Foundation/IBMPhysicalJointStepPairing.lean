import Foundation.IBMPhysicalConditionalPairing

/-! Genuine time-clock product integrability and exact predictable-step covariance.
Fubini is justified before passing from rowwise to joint pairings. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.IBMPhysicalJointStepPairing
open InfiniteGaussian GaussianTimeHilbert GaussianTimeProductL2 GaussianConditionalIto
open IBMPhysicalWeakWiener IBMPhysicalConditionalPairing
attribute [local instance] GaussianTimeHilbert.timeHilbert_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩

def joint (T : ℝ≥0) (L : Tests) (z : ℝ × SampleSpace) : ℝ :=
  L (IBMPhysicalNegativeEmbedding.embedding (IBMFoldedHeatPredictable.raw T z))

theorem joint_memLp (T : ℝ≥0) (L : Tests) :
    MemLp (joint T L) 2 (BrownianClockWeightedEnergy.base T) :=
  (L.comp IBMPhysicalNegativeEmbedding.embedding).comp_memLp' (IBMFoldedHeatPredictable.raw_memLp T)

private theorem past_lift_memLp (T : ℝ≥0) (V : GaussianL2) :
    MemLp (fun z : ℝ × SampleSpace => V z.2) 2 (BrownianClockWeightedEnergy.base T) := by
  have hm := (productTensor_memLp (timeVector T) V).restrict (s := PredictableRealL2.horizon T)
  apply hm.ae_eq
  have ht := (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure ℝ))
    (ν := gaussianProduct)).ae_eq_comp (timeVector_coeFn T)
  filter_upwards [ae_restrict_of_ae ht,
    ae_restrict_mem (PredictableRealL2.horizon_measurable T)] with z ht hz
  simp only [Function.comp_def] at ht
  rw [ht, indicator_of_mem hz.1, one_mul]

theorem joint_product_integrable (T : ℝ≥0) (L : Tests) (V : GaussianL2) :
    Integrable (fun z : ℝ × SampleSpace => joint T L z*V z.2)
      (BrownianClockWeightedEnergy.base T) :=
  (joint_memLp T L).integrable_mul (past_lift_memLp T V)

theorem joint_step_covariance (a b T : ℝ≥0) (hab : a ≤ b) (hbT : b ≤ T)
    (L : Tests) (V : GaussianL2) (hV : V ∈ pastL2 a) :
    (∫ z : ℝ × SampleSpace, joint T L z*V z.2
      ∂((volume.restrict (Ioc (a : ℝ) b)).prod gaussianProduct)) =
        ((b : ℝ)-a)*inner ℝ (IBMSchwartzWeakWienerClosure.evaluate L
          (IBMPhysicalPointSlope.slopeLimit T)) V := by
  have hi : Integrable (fun z : ℝ × SampleSpace => joint T L z*V z.2)
      ((volume.restrict (Ioc (a : ℝ) b)).prod gaussianProduct) := by
    rw [Measure.restrict_prod_eq_prod_univ]
    have hfull : IntegrableOn (fun z : ℝ × SampleSpace => joint T L z*V z.2)
        (PredictableRealL2.horizon T) timeProbability := joint_product_integrable T L V
    apply hfull.mono_set
    intro z hz
    exact ⟨⟨lt_of_le_of_lt a.coe_nonneg hz.1.1,
      hz.1.2.trans (show (b : ℝ) ≤ T from hbT)⟩, hz.2⟩
  rw [integral_prod _ hi]
  have he : (∫ s in Ioc (a : ℝ) b, ∫ Y, joint T L (s,Y)*V Y ∂gaussianProduct) =
      ∫ s in Ioc (a : ℝ) b, ∫ Y, tested s.toNNReal T L Y*V Y ∂gaussianProduct := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have hsn : 0 ≤ s := a.coe_nonneg.trans hs.1.le
    apply integral_congr_ae
    exact ae_of_all _ fun Y => by
      simp only [joint, tested, Real.coe_toNNReal s hsn]
  rw [he, ← intervalIntegral.integral_of_le (show (a : ℝ) ≤ b from hab)]
  exact integrated_covariance a b T hab hbT L V hV

end OperatorDerivativeRewrite.Foundation.IBMPhysicalJointStepPairing
