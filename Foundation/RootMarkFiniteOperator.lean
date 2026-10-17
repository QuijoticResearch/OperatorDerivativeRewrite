import Foundation.RootMarkL2Integral
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! A genuine bounded finite predictable integration operator and its Hilbert adjoint. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal InnerProductSpace
namespace OperatorDerivativeRewrite.Foundation.RootMarkFiniteOperator
open RootMarkStochasticIntegral RootMarkL2Integral RootMarkItoIsometry RootMarkConditionalEnergy
open MarkedRootRenewalProcess (MarkSample marks)

abbrev Node (N : ℕ) := Σ j : Fin N, ComplexFourthRootWalk.Sample j.val × Fin 3
abbrev Table (N : ℕ) := EuclideanSpace ℂ (Node N)

def coefficients (N : ℕ) (u : Table N) : Fin 3 → Coefficients :=
  fun r j ξ => if h : j < N then u ⟨⟨j,h⟩,(ξ,r)⟩ else 0

def coefficientsLinear (N : ℕ) : Table N →ₗ[ℂ] (Fin 3 → Coefficients) where
  toFun := coefficients N
  map_add' u v := by
    funext r j ξ
    by_cases h : j < N <;> simp [coefficients, h, PiLp.add_apply]
  map_smul' c u := by
    change coefficients N (c • u) = c • coefficients N u
    funext r j ξ
    by_cases h : j < N <;> simp [coefficients, h, PiLp.smul_apply]

def finiteIntegralLinear (a : ℝ) (N : ℕ) : Table N →ₗ[ℂ] Lp ℂ 2 marks :=
  (integralOperator a N).comp (coefficientsLinear N)

def finiteIntegral (a : ℝ) (N : ℕ) : Table N →L[ℂ] Lp ℂ 2 marks :=
  (finiteIntegralLinear a N).toContinuousLinearMap

def derivative (a : ℝ) (N : ℕ) : Lp ℂ 2 marks →L[ℂ] Table N :=
  (finiteIntegral a N).adjoint

theorem finiteIntegral_ae (a : ℝ) (N : ℕ) (u : Table N) :
    finiteIntegral a N u =ᵐ[marks] totalIntegral a (coefficients N u) N :=
  integralL2_ae a (coefficients N u) N

theorem finiteIntegral_norm_square (a : ℝ) (N : ℕ) (u : Table N) :
    ‖finiteIntegral a N u‖^2 = ∑ j ∈ Finset.range N, ∫ η, energy a (coefficients N u) j η ∂marks :=
  integralL2_norm_square a (coefficients N u) N

theorem adjoint_identity (a : ℝ) (N : ℕ) (u : Table N) (Y : Lp ℂ 2 marks) :
    ⟪derivative a N Y,u⟫_ℂ = ⟪Y,finiteIntegral a N u⟫_ℂ :=
  (finiteIntegral a N).adjoint_inner_left u Y

theorem range_closed (a : ℝ) (N : ℕ) :
    IsClosed (LinearMap.range (finiteIntegral a N).toLinearMap : Set (Lp ℂ 2 marks)) :=
  Submodule.closed_of_finiteDimensional _

theorem finiteIntegral_mean_zero (a : ℝ) (N : ℕ) (u : Table N) :
    (∫ η, finiteIntegral a N u η ∂marks) = 0 := by
  have hm := totalIntegral_martingale a (coefficients N u)
  have he := hm.2 0 N (Nat.zero_le N)
  calc
    _ = ∫ η, totalIntegral a (coefficients N u) N η ∂marks := integral_congr_ae (finiteIntegral_ae a N u)
    _ = ∫ η, marks[totalIntegral a (coefficients N u) N | history 0] η ∂marks :=
      (integral_condExp (history.le 0)).symm
    _ = ∫ η, totalIntegral a (coefficients N u) 0 η ∂marks := integral_congr_ae he
    _ = 0 := by rw [totalIntegral_zero]; simp

end OperatorDerivativeRewrite.Foundation.RootMarkFiniteOperator
