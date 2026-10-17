import Foundation.IBMConstructedSources
import Foundation.WeightedL2Transport
import Foundation.PredictableRealL2

/-! The actual continuous Brownian coefficient gives an almost-everywhere positive energy weight. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.BrownianClockWeightedEnergy
open InfiniteGaussian GaussianTimeProcess IBMConstructedSources

def sigma (z : ℝ × SampleSpace) : ℝ := clockPath z.2 z.1.toNNReal

theorem sigma_measurable : Measurable sigma :=
  continuous_eval.measurable.comp
    ((clockPath_measurable.comp measurable_snd).prodMk measurable_fst.real_toNNReal)

abbrev base (T : ℝ≥0) := PredictableRealL2.horizonMeasure T gaussianProduct

theorem sigma_nonzero (T : ℝ≥0) : ∀ᵐ z ∂base T, sigma z ≠ 0 := by
  change ∀ᵐ z ∂PredictableRealL2.horizonMeasure T gaussianProduct, sigma z ≠ 0
  rw [PredictableRealL2.horizonMeasure_eq_product]
  apply (Measure.ae_prod_iff_ae_ae
    (measurableSet_eq_fun sigma_measurable measurable_const).compl).mpr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have hp : t.toNNReal ≠ 0 := ne_of_gt (Real.toNNReal_pos.mpr ht.1)
  let _ : NullSingletonClass (gaussianReal 0 t.toNNReal) := nullSingletonClass_gaussianReal hp
  have hn : ∀ᵐ ω ∂gaussianProduct, process t.toNNReal ω ≠ 0 :=
    ((process_hasLaw t.toNNReal).ae_iff (by fun_prop)).mpr
      ((gaussianReal 0 t.toNNReal).ae_ne 0)
  filter_upwards [clockPath_coordinate_ae t.toNNReal, hn] with ω hc hn
  change clockPath ω t.toNNReal ≠ 0
  rwa [hc]

def energy (T : ℝ≥0) : Measure (ℝ × SampleSpace) :=
  WeightedL2Transport.weightedMeasure (base T) sigma

theorem energy_absolutelyContinuous (T : ℝ≥0) : energy T ≪ base T :=
  WeightedL2Transport.weightedMeasure_absolutelyContinuous _ _

theorem base_absolutelyContinuous (T : ℝ≥0) : base T ≪ energy T :=
  WeightedL2Transport.absolutelyContinuous_weightedMeasure _ _ sigma_measurable (sigma_nonzero T)

def transport (T : ℝ≥0) : Lp ℝ 2 (energy T) ≃ₗᵢ[ℝ] Lp ℝ 2 (base T) :=
  WeightedL2Transport.unitary (base T) sigma sigma_measurable (sigma_nonzero T)

theorem transport_coeFn (T : ℝ≥0) (u : Lp ℝ 2 (energy T)) :
    transport T u =ᵐ[base T] fun z => sigma z * u z :=
  WeightedL2Transport.unitary_coeFn _ _ _ _ _

theorem inverse_coeFn (T : ℝ≥0) (v : Lp ℝ 2 (base T)) :
    (transport T).symm v =ᵐ[energy T] fun z => v z / sigma z :=
  WeightedL2Transport.unitary_symm_coeFn _ _ _ _ _

end OperatorDerivativeRewrite.Foundation.BrownianClockWeightedEnergy
