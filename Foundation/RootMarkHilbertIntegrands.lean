import Foundation.RootMarkInfiniteOperator
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! The actual centered L2 integration range and its integrand quotient. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology InnerProductSpace
namespace OperatorDerivativeRewrite.Foundation.RootMarkHilbertIntegrands
open RootMarkStochasticIntegral RootMarkL2Limit RootMarkGKWConditioning RootMarkInfiniteOperator
open MarkedRootRenewalProcess (MarkSample marks)

def centered : Submodule ℂ (Lp ℂ 2 marks) :=
  ((prefixSpace 0).starProjection : Lp ℂ 2 marks →L[ℂ] Lp ℂ 2 marks).ker

theorem centered_iff (Y : Lp ℂ 2 marks) : Y ∈ centered ↔ (∫ η, Y η ∂marks) = 0 := by
  constructor
  · intro hY
    have he : conditionalValue 0 Y = 0 := hY
    have hm := conditionalValue_mean 0 Y
    rw [he] at hm
    exact hm.symm.trans ((integral_congr_ae (Lp.coeFn_zero ℂ 2 marks)).trans (by simp))
  · intro hY
    change conditionalValue 0 Y = 0
    apply Lp.ext
    have he := prefix_projection_condExp_ae 0 Y
    rw [RootMarkFiniteClark.history_zero,condExp_bot] at he
    filter_upwards [he,Lp.coeFn_zero ℂ 2 marks] with η hη hz
    exact hη.trans (hY.trans hz.symm)

theorem integration_range (a : ℝ) (ha : a ≠ 0) : (integration a).range = centered := by
  ext Y
  rw [centered_iff]
  constructor
  · rintro ⟨H,rfl⟩
    exact integration_mean_zero a H
  · exact integration_surjective_centered a ha Y

theorem integration_range_closed (a : ℝ) (ha : a ≠ 0) :
    IsClosed ((integration a).range : Set (Lp ℂ 2 marks)) := by
  rw [integration_range a ha]
  exact (prefixSpace 0).starProjection.isClosed_ker

def IntegrandQuotient (a : ℝ) := (integrands a) ⧸ (integration a).ker

instance quotientAddGroup (a : ℝ) : AddCommGroup (IntegrandQuotient a) :=
  inferInstanceAs (AddCommGroup ((integrands a) ⧸ (integration a).ker))

instance quotientModule (a : ℝ) : Module ℂ (IntegrandQuotient a) :=
  inferInstanceAs (Module ℂ ((integrands a) ⧸ (integration a).ker))

def quotientRealization (a : ℝ) : IntegrandQuotient a ≃ₗ[ℂ] (integration a).range :=
  (integration a).quotKerEquivRange

instance quotientNorm (a : ℝ) : NormedAddCommGroup (IntegrandQuotient a) :=
  NormedAddCommGroup.induced _ _ (quotientRealization a) (quotientRealization a).injective

instance quotientNormedSpace (a : ℝ) : NormedSpace ℂ (IntegrandQuotient a) :=
  NormedSpace.induced ℂ _ _ (quotientRealization a)

instance quotientInner (a : ℝ) : InnerProductSpace ℂ (IntegrandQuotient a) :=
  InnerProductSpace.induced (quotientRealization a)

def quotientIsometry (a : ℝ) : IntegrandQuotient a ≃ₗᵢ[ℂ] (integration a).range where
  toLinearEquiv := quotientRealization a
  norm_map' _ := rfl

instance quotientComplete (a : ℝ) [ha : Fact (a ≠ 0)] : CompleteSpace (IntegrandQuotient a) := by
  letI : CompleteSpace ((integration a).range) := (integration_range_closed a ha.out).completeSpace_coe
  exact (quotientIsometry a).toIsometryEquiv.completeSpace

def infiniteIntegral (a : ℝ) : IntegrandQuotient a →L[ℂ] Lp ℂ 2 marks :=
  (integration a).range.subtypeL.comp (quotientIsometry a : IntegrandQuotient a →L[ℂ] (integration a).range)

def derivative (a : ℝ) [Fact (a ≠ 0)] : Lp ℂ 2 marks →L[ℂ] IntegrandQuotient a :=
  (infiniteIntegral a).adjoint

theorem adjoint_identity (a : ℝ) [Fact (a ≠ 0)] (u : IntegrandQuotient a) (Y : Lp ℂ 2 marks) :
    ⟪derivative a Y,u⟫_ℂ = ⟪Y,infiniteIntegral a u⟫_ℂ :=
  (infiniteIntegral a).adjoint_inner_left u Y

end OperatorDerivativeRewrite.Foundation.RootMarkHilbertIntegrands
