import Foundation.RootMarkFiniteOperator
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-! Genuine closed-range GKW geometry for the constructed finite predictable integration operator. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace
namespace OperatorDerivativeRewrite.Foundation.RootMarkGKWProjection
open RootMarkFiniteOperator
open MarkedRootRenewalProcess (marks)

def predictableRange (a : ℝ) (N : ℕ) : ClosedSubmodule ℂ (Lp ℂ 2 marks) where
  toSubmodule := LinearMap.range (finiteIntegral a N).toLinearMap
  isClosed' := range_closed a N

def projection (a : ℝ) (N : ℕ) : Lp ℂ 2 marks →L[ℂ] Lp ℂ 2 marks :=
  ((predictableRange a N : Submodule ℂ (Lp ℂ 2 marks))).starProjection

theorem projection_representable (a : ℝ) (N : ℕ) (Y : Lp ℂ 2 marks) :
    ∃ u : Table N, finiteIntegral a N u = projection a N Y := by
  have he := Submodule.starProjection_apply_mem
    (predictableRange a N : Submodule ℂ (Lp ℂ 2 marks)) Y
  exact he

theorem residual_orthogonal (a : ℝ) (N : ℕ) (Y : Lp ℂ 2 marks) (u : Table N) :
    ⟪Y-projection a N Y,finiteIntegral a N u⟫_ℂ = 0 :=
  Submodule.starProjection_inner_eq_zero
    (K := (predictableRange a N : Submodule ℂ (Lp ℂ 2 marks))) Y (finiteIntegral a N u) ⟨u,rfl⟩

theorem residual_derivative_zero (a : ℝ) (N : ℕ) (Y : Lp ℂ 2 marks) :
    derivative a N (Y-projection a N Y) = 0 := by
  have he := (adjoint_identity a N (derivative a N (Y-projection a N Y))
    (Y-projection a N Y)).trans
    (residual_orthogonal a N Y (derivative a N (Y-projection a N Y)))
  exact inner_self_eq_zero.mp he

theorem gkw_decomposition (a : ℝ) (N : ℕ) (Y : Lp ℂ 2 marks) :
    ∃ u : Table N, ∃ R : Lp ℂ 2 marks,
      Y = finiteIntegral a N u+R ∧ derivative a N R = 0 ∧
      ∀ v : Table N, ⟪R,finiteIntegral a N v⟫_ℂ = 0 := by
  obtain ⟨u,hu⟩ := projection_representable a N Y
  refine ⟨u,Y-projection a N Y,?_,residual_derivative_zero a N Y,fun v => residual_orthogonal a N Y v⟩
  rw [hu]
  abel

end OperatorDerivativeRewrite.Foundation.RootMarkGKWProjection
