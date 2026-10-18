import Foundation.RootMarkL2Limit
import Foundation.RootMarkL2Integral
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! Genuine infinite L2 Clark representation and its total positive Ito energy. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.RootMarkInfiniteIto
open RootMarkStochasticIntegral RootMarkL2Integral RootMarkGKWConditioning
open RootMarkConditionalEnergy
open MarkedRootRenewalProcess (MarkSample marks)

theorem infinite_clark_isometry (a : ℝ) (ha : a ≠ 0) (Y : Lp ℂ 2 marks)
    (hmean : (∫ η, Y η ∂marks) = 0) :
    ∃ H : Fin 3 → Coefficients,
      (∀ n : ℕ, (fun η => marks[(Y : MarkSample → ℂ) | history n] η) =ᵐ[marks]
        RootMarkItoIsometry.totalIntegral a H n) ∧
      Tendsto (fun n : ℕ => integralL2 a H n) atTop (𝓝 Y) ∧
      HasSum (fun j : ℕ => ∫ η, energy a H j η ∂marks) (‖Y‖^2) := by
  obtain ⟨H,hH⟩ := RootMarkComplexClarkLimit.coherent_clark a ha (Y : MarkSample → ℂ)
  have hrepr (n : ℕ) : marks[(Y : MarkSample → ℂ) | history n] =ᵐ[marks]
      RootMarkItoIsometry.totalIntegral a H n := by
    simpa only [hmean,sub_zero] using hH n
  have heq (n : ℕ) : integralL2 a H n = conditionalValue n Y := by
    apply Lp.ext
    have hc : conditionalValue n Y =ᵐ[marks] marks[(Y : MarkSample → ℂ) | history n] :=
      RootMarkL2Limit.prefix_projection_condExp_ae n Y
    exact (integralL2_ae a H n).trans ((hrepr n).symm.trans hc.symm)
  have ht : Tendsto (fun n : ℕ => integralL2 a H n) atTop (𝓝 Y) := by
    simpa only [heq] using RootMarkL2Limit.conditionalValue_L2_limit Y
  refine ⟨H,hrepr,ht,?_⟩
  apply (hasSum_iff_tendsto_nat_of_nonneg
    (fun j => integral_nonneg (RootMarkIntegralUniqueness.energy_nonneg a H j)) _).mpr
  simpa only [integralL2_norm_square] using ht.norm.pow 2

end OperatorDerivativeRewrite.Foundation.RootMarkInfiniteIto
