import Foundation.IBMScenerySignSymmetry

/-! A genuine observed IBM variable outside the completed deterministic
integral range. Random predictable representations are not excluded. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMDeterministicRangeObstruction
open IBMTimeAveragedObservable IBMNaturalFiltrationObstruction
open IBMIntrinsicRightGerm IBMRightGermDeterministicIntegral
open IBMRightGermFullDeterministicIntegral IBMRightGermCovarianceAdjoint
open IBMScenerySignSymmetry
set_option backward.isDefEq.respectTransparency false

def observed (t : ℝ≥0) : JointL2 := intrinsicCurve t

theorem observed_ae (t : ℝ≥0) : observed t =ᵐ[IBMSourceLaws.jointMeasure]
    IBMConstructedSources.ibmValue t := joint_point_actual_ae t

theorem observed_mem_past (t : ℝ≥0) : observed t ∈ past t :=
  (point_stronglyAdapted t).aestronglyMeasurable.congr (observed_ae t).symm

theorem observed_odd (t : ℝ≥0) : action (observed t) = -observed t := by
  apply Lp.ext
  filter_upwards [action_ae (observed t), preserving.quasiMeasurePreserving.ae_eq_comp
    (observed_ae t), ibm_reflect_simultaneous, observed_ae t,
    Lp.coeFn_neg (observed t)] with ω ha hc hi ho hn
  simp only [Function.comp_def] at hc
  rw [ha, hc, hi t, hn, Pi.neg_apply, ho]

theorem dictionary_fixed (a : ℝ≥0 →₀ ℝ) : action (stochasticDictionary a) = stochasticDictionary a := by
  simp only [stochasticDictionary, Finsupp.linearCombination_apply, Finsupp.sum,
    map_sum, map_smul, rightLimit_fixed]

theorem integral_fixed (f : TimeL2) : action (integral f) = integral f := by
  obtain ⟨a, _, hs⟩ := exists_dictionary_approximation f
  have ha := (action.continuous.tendsto (integral f)).comp hs
  have hb : Tendsto (fun n => action (stochasticDictionary (a n))) atTop
      (𝓝 (integral f)) := by simpa only [dictionary_fixed] using hs
  exact tendsto_nhds_unique ha hb

theorem observed_inner_integral_zero (t : ℝ≥0) (f : TimeL2) :
    inner ℝ (observed t) (integral f) = 0 := by
  have h := action.inner_map_map (observed t) (integral f)
  rw [observed_odd, integral_fixed, inner_neg_left] at h
  linarith

theorem observed_adjoint_zero (t : ℝ≥0) : covarianceAdjoint (observed t) = 0 := by
  apply ext_inner_left ℝ
  intro f
  rw [duality, inner_zero_right, real_inner_comm, observed_inner_integral_zero]

theorem observed_reconstruction_zero (t : ℝ≥0) : reconstruction (observed t) = 0 := by
  rw [reconstruction, observed_adjoint_zero, map_zero]

theorem observed_residual (t : ℝ≥0) : residual (observed t) = observed t := by
  rw [IBMRightGermCovarianceAdjoint.residual, observed_reconstruction_zero, sub_zero]

theorem observed_centered (t : ℝ≥0) :
    (∫ ω, observed t ω ∂IBMSourceLaws.jointMeasure) = 0 := by
  have ha := action_ae (observed t)
  rw [observed_odd] at ha
  have hn := ha.symm.trans (Lp.coeFn_neg (observed t))
  have he := preserving.integral_comp
    (MeasurableEquiv.ofInvolutive reflectScenery involutive preserving.measurable).measurableEmbedding
      (observed t)
  rw [integral_congr_ae hn] at he
  change (∫ ω, -observed t ω ∂IBMSourceLaws.jointMeasure) =
    ∫ ω, observed t ω ∂IBMSourceLaws.jointMeasure at he
  rw [integral_neg] at he
  linarith

theorem approximation_error (t : ℝ≥0) (f : TimeL2) :
    ‖observed t - integral f‖ ^ 2 = ‖observed t‖ ^ 2 + ‖f‖ ^ 2 := by
  rw [norm_sub_sq_real, observed_inner_integral_zero, integral_norm]
  ring

theorem observed_one_ne_zero : observed 1 ≠ 0 := by
  intro hz
  have hn := IBMTemporalCovarianceObstruction.actual_increment_pairing_negative
  change inner ℝ (observed 1) ((intrinsicCurve 2 : JointL2) - observed 1) < 0 at hn
  rw [hz, inner_zero_left] at hn
  exact (lt_irrefl 0) hn

theorem observed_one_not_range : observed 1 ∉ integral.toLinearMap.range := by
  intro h
  have he := (reconstruction_iff_range (observed 1)).mpr h
  rw [observed_reconstruction_zero] at he
  exact observed_one_ne_zero he.symm

theorem no_deterministic_representation :
    ¬ ∃ f : TimeL2, integral f =ᵐ[IBMSourceLaws.jointMeasure] IBMConstructedSources.ibmValue 1 := by
  rintro ⟨f, hf⟩
  apply observed_one_not_range
  exact ⟨f, Lp.ext (hf.trans (observed_ae 1).symm)⟩

end OperatorDerivativeRewrite.Foundation.IBMDeterministicRangeObstruction
