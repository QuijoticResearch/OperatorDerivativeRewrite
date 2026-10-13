import Foundation.GaussianPowerVolterra
import Foundation.GaussianKernelTransfer
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-! Exact temporal threshold for a one-mode fractional forcing kernel.
This is the zero-generator response t^(alpha-1)/Gamma(alpha), not an assumed
Mittag-Leffler or infinite-dimensional SPDE existence theorem. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.FractionalForcingKernel
open GaussianPowerVolterra GaussianTimeHilbert InfiniteGaussian
attribute [local instance] timeHilbert_secondCountable

theorem power_kernel_memLp_iff (β : ℝ) (t : ℝ≥0) (ht : 0 < t) :
    MemLp (kernel β t) 2 volume ↔ -1/2 < β := by
  constructor
  · intro hm
    have hi := hm.integrable_sq
    rw [kernel_sq, integrable_indicator_iff measurableSet_Ioc] at hi
    have hj := (intervalIntegrable_iff_integrableOn_Ioc_of_le t.coe_nonneg).mpr hi
    have hr := hj.comp_sub_left (t : ℝ)
    simp only [sub_self, sub_zero, sub_sub_cancel] at hr
    have hpos : 0 < (t : ℝ) := ht
    have hh := (intervalIntegrable_iff_integrableOn_Ioo_of_le hpos.le).mp hr.symm
    have hh' := (intervalIntegral.integrableOn_Ioo_rpow_iff hpos).mp hh
    linarith
  · exact fun hb => kernel_memLp β hb t

def response (α : ℝ) (t : ℝ≥0) : ℝ → ℝ :=
  fun s => (Real.Gamma α)⁻¹ * kernel (α-1) t s

theorem response_memLp_iff (α : ℝ) (hα : 0 < α) (t : ℝ≥0) (ht : 0 < t) :
    MemLp (response α t) 2 volume ↔ 1/2 < α := by
  have hg : (Real.Gamma α)⁻¹ ≠ 0 := inv_ne_zero (ne_of_gt (Real.Gamma_pos_of_pos hα))
  change MemLp ((Real.Gamma α)⁻¹ • kernel (α-1) t) 2 volume ↔ _
  constructor
  · intro hm
    have hk := hm.const_smul (Real.Gamma α)
    have hk' : MemLp (kernel (α-1) t) 2 volume := by
      simpa only [smul_smul, inv_mul_cancel₀ (ne_of_gt (Real.Gamma_pos_of_pos hα)),
        mul_inv_cancel₀ (ne_of_gt (Real.Gamma_pos_of_pos hα)), one_smul] using hk
    have hb := (power_kernel_memLp_iff (α-1) t ht).mp hk'
    linarith
  · intro ha
    exact (kernel_memLp (α-1) (by linarith) t).const_smul _

def responseVector (α : ℝ) (hα : 1/2 < α) (t : ℝ≥0) : TimeHilbert :=
  (Real.Gamma α)⁻¹ • vector (α-1) (by linarith) t

theorem responseVector_coeFn (α : ℝ) (hα : 1/2 < α) (t : ℝ≥0) :
    responseVector α hα t =ᵐ[volume] response α t := by
  filter_upwards [Lp.coeFn_smul (Real.Gamma α)⁻¹ (vector (α-1) (by linarith) t),
    vector_coeFn (α-1) (by linarith) t] with s hs hk
  simpa [responseVector, response, hk] using hs

theorem responseVector_norm_sq (α : ℝ) (hα : 1/2 < α) (t : ℝ≥0) :
    ‖responseVector α hα t‖^2 =
      (t : ℝ)^(2*α-1) / ((Real.Gamma α)^2 * (2*α-1)) := by
  rw [responseVector, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, vector_norm_sq]
  rw [show 2*(α-1)+1 = 2*α-1 by ring]
  simp only [inv_pow, div_eq_mul_inv, mul_inv_rev]
  ring

def stochasticResponse (α : ℝ) (hα : 1/2 < α) (t : ℝ≥0) : GaussianL2 :=
  GaussianHilbertProcess.isonormalEmbedding TimeHilbert (responseVector α hα t)

theorem stochasticResponse_norm_sq (α : ℝ) (hα : 1/2 < α) (t : ℝ≥0) :
    ‖stochasticResponse α hα t‖^2 =
      (t : ℝ)^(2*α-1) / ((Real.Gamma α)^2 * (2*α-1)) := by
  rw [stochasticResponse, LinearIsometry.norm_map, responseVector_norm_sq]

theorem stochasticResponse_derivative (α : ℝ) (hα : 1/2 < α) (t : ℝ≥0) :
    (stochasticResponse α hα t, GaussianContinuousRigidity.fieldEmbedding
      (GaussianTimeProductL2.productTensor (responseVector α hα t) gaussianOne)) ∈
        closedCylindricalDerivative.graph :=
  GaussianDeterministicIntegral.firstChaos_closedDerivative_graph _

theorem stochasticResponse_zero (α : ℝ) (hα : 1/2 < α) :
    stochasticResponse α hα 0 = 0 := by
  simp [stochasticResponse, responseVector, vector_zero]

theorem stochasticResponse_order_one (t : ℝ≥0) :
    stochasticResponse 1 (by norm_num) t = GaussianTimeProcess.wienerL2 t := by
  simp [stochasticResponse, responseVector, Real.Gamma_one, vector_exponent_zero]
  rfl

end OperatorDerivativeRewrite.Foundation.FractionalForcingKernel
