import Foundation.RootMarkHilbertIntegrands

/-! Actual infinite Clark identities for the constructed Hilbert integration operator. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology InnerProductSpace
namespace OperatorDerivativeRewrite.Foundation.RootMarkInfiniteClarkOperator
open RootMarkStochasticIntegral RootMarkInfiniteOperator RootMarkHilbertIntegrands
open MarkedRootRenewalProcess (MarkSample marks)

def classOf (a : ℝ) (H : integrands a) : IntegrandQuotient a := Submodule.Quotient.mk H

instance centeredComplete : CompleteSpace centered :=
  (RootMarkL2Limit.prefixSpace 0).starProjection.isClosed_ker.completeSpace_coe

theorem integral_mk (a : ℝ) (H : integrands a) :
    infiniteIntegral a (classOf a H) = integration a H := rfl

theorem integral_norm (a : ℝ) (u : IntegrandQuotient a) : ‖infiniteIntegral a u‖ = ‖u‖ := rfl

theorem quotient_energy (a : ℝ) (H : integrands a) :
    ‖(classOf a H)‖^2 =
      ∑' j : ℕ, ∫ η, RootMarkConditionalEnergy.energy a H j η ∂marks :=
  integration_isometry a H

theorem derivative_integral (a : ℝ) [Fact (a ≠ 0)] :
    (derivative a).comp (infiniteIntegral a) = 1 :=
  (ContinuousLinearMap.norm_map_iff_adjoint_comp_self (infiniteIntegral a)).mp (integral_norm a)

theorem derivative_integral_apply (a : ℝ) [Fact (a ≠ 0)] (u : IntegrandQuotient a) :
    derivative a (infiniteIntegral a u) = u := by
  change ((derivative a).comp (infiniteIntegral a)) u = (1 : IntegrandQuotient a →L[ℂ] _) u
  rw [derivative_integral]

theorem centered_clark (a : ℝ) [ha : Fact (a ≠ 0)] (Y : Lp ℂ 2 marks)
    (hmean : (∫ η, Y η ∂marks) = 0) : infiniteIntegral a (derivative a Y) = Y := by
  obtain ⟨H,hH⟩ := integration_surjective_centered a ha.out Y hmean
  have hu : infiniteIntegral a (classOf a H) = Y :=
    (integral_mk a H).trans hH
  rw [← hu,derivative_integral_apply]

theorem clark_projection (a : ℝ) [ha : Fact (a ≠ 0)] (Y : Lp ℂ 2 marks) :
    infiniteIntegral a (derivative a Y) = centered.starProjection Y := by
  have hm : infiniteIntegral a (derivative a Y) ∈ (integration a).range :=
    (quotientIsometry a (derivative a Y)).property
  rw [integration_range a ha.out] at hm
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero hm
  intro w hw
  obtain ⟨H,rfl⟩ := integration_surjective_centered a ha.out w ((centered_iff w).mp hw)
  let u : IntegrandQuotient a := classOf a H
  have hu : infiniteIntegral a u = integration a H := integral_mk a H
  rw [← hu,inner_sub_left]
  have he := adjoint_identity a u Y
  have hi := (ContinuousLinearMap.inner_map_map_iff_adjoint_comp_self
    (infiniteIntegral a)).mpr (derivative_integral a) (derivative a Y) u
  rw [hi,← he,sub_self]

theorem centered_eq_orthogonal : centered = (RootMarkL2Limit.prefixSpace 0)ᗮ :=
  Submodule.ker_starProjection _

theorem clark_centering (a : ℝ) [Fact (a ≠ 0)] (Y : Lp ℂ 2 marks) :
    infiniteIntegral a (derivative a Y) = Y-RootMarkGKWConditioning.conditionalValue 0 Y := by
  rw [clark_projection]
  change centered.starProjection Y = Y-(RootMarkL2Limit.prefixSpace 0).starProjection Y
  simpa only [← centered_eq_orthogonal] using
    (Submodule.starProjection_orthogonal_val (K := RootMarkL2Limit.prefixSpace 0) Y)

theorem clark_centered_ae (a : ℝ) [Fact (a ≠ 0)] (Y : Lp ℂ 2 marks) :
    infiniteIntegral a (derivative a Y) =ᵐ[marks] fun η => Y η-(∫ ξ, Y ξ ∂marks) := by
  rw [clark_centering]
  have he := RootMarkL2Limit.prefix_projection_condExp_ae 0 Y
  rw [RootMarkFiniteClark.history_zero,condExp_bot] at he
  filter_upwards [Lp.coeFn_sub Y (RootMarkGKWConditioning.conditionalValue 0 Y),he] with η hη heη
  exact hη.trans (congrArg (Y η- ·) heη)

end OperatorDerivativeRewrite.Foundation.RootMarkInfiniteClarkOperator
