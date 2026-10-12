import Foundation.GaussianSmoothHeatMartingale
import Foundation.GaussianQuadraticCylinders

/-! A bounded smooth diagnostic for the terminal-adjoint/running-derivative
substitution. All fields below are the independently constructed fields. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianSmoothProjectionDiagnostic
open InfiniteGaussian GaussianTimeProcess GaussianTimeProductL2 GaussianProductDerivative
open GaussianLipschitzIntegrands GaussianPredictableFull GaussianPredictableAdjoint
open GaussianSmoothHeatMartingale GaussianTimeWeightedSmoothIto

/-- All derivatives through order three, including the function, are bounded.
This diagnostic really belongs to the manuscript's bounded C3 test class. -/
theorem sin_bounded_C3 : ContDiff ℝ 3 Real.sin ∧
    ∀ n : ℕ, n ≤ 3 → ∀ x : ℝ, ‖iteratedDeriv n Real.sin x‖ ≤ 1 := by
  refine ⟨Real.contDiff_sin, ?_⟩
  intro n hn x
  interval_cases n
  · simpa using Real.abs_sin_le_one x
  · simpa using Real.abs_cos_le_one x
  · simpa [iteratedDeriv_succ, Real.deriv_sin, Real.deriv_cos', Real.norm_eq_abs]
      using Real.abs_sin_le_one x
  · exact sin_third_bound x

/-- The terminal sine's actual bounded predictable adjoint, deduced from its
heat martingale representation and J*J=identity. -/
theorem sin_predictableAdjoint (T : ℝ≥0) :
    predictableAdjoint (valueL2 Real.lipschitzWith_sin T) =
      Real.exp (-((T:ℝ)/2)) • weightedField expHalf expHalf_contDiff.continuous
        Real.lipschitzWith_cos T := by
  have he := heat_representation Real.sin Real.contDiff_sin Real.lipschitzWith_sin
    sin_deriv_lipschitz sin_second_lipschitz 1 sin_third_bound expHalf
    expHalf_contDiff sin_heat_equation T
  simp only [GaussianSmoothIto.valueL2_zero, Real.sin_zero, zero_smul, smul_zero, sub_zero] at he
  have hw : weightedField expHalf expHalf_contDiff.continuous sin_deriv_lipschitz T =
      weightedField expHalf expHalf_contDiff.continuous Real.lipschitzWith_cos T := by
    congr 1
    exact Real.deriv_sin
  rw [hw] at he
  have hp := congrArg predictableAdjoint he
  rw [map_smul, predictableAdjoint_integral] at hp
  have hs := congrArg (fun U : fullPredictable => Real.exp (-((T:ℝ)/2)) • U) hp
  rw [smul_smul] at hs
  simpa only [expHalf, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_smul] using hs

theorem sin_predictableAdjoint_slices (T : ℝ≥0) :
    scalarCurry (predictableAdjoint (valueL2 Real.lipschitzWith_sin T) : TimeProbabilityL2)
      =ᵐ[volume] (Ioc 0 (T:ℝ)).indicator
        (fun t => (Real.exp (-((T:ℝ)/2)) * expHalf t) •
          valueL2 Real.lipschitzWith_cos t.toNNReal) := by
  rw [sin_predictableAdjoint]
  change scalarCurry (Real.exp (-((T:ℝ)/2)) •
    (weightedField expHalf expHalf_contDiff.continuous Real.lipschitzWith_cos T : TimeProbabilityL2)) =ᵐ[volume] _
  rw [map_smul]
  filter_upwards [Lp.coeFn_smul (Real.exp (-((T:ℝ)/2)))
    (scalarCurry (weightedField expHalf expHalf_contDiff.continuous Real.lipschitzWith_cos T)),
    weightedField_slices expHalf expHalf_contDiff.continuous Real.lipschitzWith_cos T] with t hs hw
  rw [hs]
  simp only [Pi.smul_apply, hw]
  by_cases ht : t ∈ Ioc 0 (T:ℝ)
  · simp only [indicator_of_mem ht, smul_smul]
  · simp [ht]

/-- For every positive horizon the bounded C-infinity sine already disproves
replacing the terminal predictable adjoint by the running spatial derivative. -/
theorem sin_projection_ne_running_derivative (T : ℝ≥0) (hT : 0 < T) :
    predictableAdjoint (valueL2 Real.lipschitzWith_sin T) ≠
      integrand Real.lipschitzWith_cos T := by
  intro he
  have hs := sin_predictableAdjoint_slices T
  rw [he] at hs
  have hp : ∀ᵐ t ∂volume, t ∈ Ioo 0 (T:ℝ) →
      (Real.exp (-((T:ℝ)/2))*expHalf t) • valueL2 Real.lipschitzWith_cos t.toNNReal =
        valueL2 Real.lipschitzWith_cos t.toNNReal := by
    filter_upwards [hs, integrand_slices Real.lipschitzWith_cos T] with t ht hi hm
    have hc : t ∈ Ioc 0 (T:ℝ) := ⟨hm.1, hm.2.le⟩
    rw [indicator_of_mem hc] at ht hi
    exact ht.symm.trans hi
  obtain ⟨t, ht, heq⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (show volume (Ioo 0 (T:ℝ)) ≠ 0 by simp [Real.volume_Ioo, ne_of_gt hT])
    (ae_restrict_of_ae hp)
  have hv := congrArg (fun X : GaussianL2 => inner ℝ gaussianOne X) (heq ht)
  rw [real_inner_smul_right, gaussianOne_inner_eq_integral] at hv
  have hc : (∫ ω, valueL2 Real.lipschitzWith_cos t.toNNReal ω ∂gaussianProduct) =
      Real.exp (-(t/2)) := by
    rw [integral_congr_ae (valueL2_coeFn Real.lipschitzWith_cos t.toNNReal), cos_mean,
      Real.coe_toNNReal _ ht.1.le]
  rw [hc] at hv
  have hm : Real.exp (-((T:ℝ)/2))*expHalf t = 1 := by
    exact (mul_right_cancel₀ (Real.exp_ne_zero (-(t/2)))) (by simpa using hv)
  have htT : t = T := by
    rw [expHalf, ← Real.exp_add, ← Real.exp_zero, Real.exp_eq_exp] at hm
    linarith
  linarith [ht.2]

end OperatorDerivativeRewrite.Foundation.GaussianSmoothProjectionDiagnostic


