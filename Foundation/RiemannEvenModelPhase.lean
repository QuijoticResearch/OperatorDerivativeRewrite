import Foundation.RiemannEvenSaddleBranch
import Foundation.RiemannQuarticSaddleNeighborhood

/-! Integer-even leading phases and their exact arithmetic error. The model
is distinguished from the actual logarithmic kernel slope throughout. -/
noncomputable section
open Set Metric
namespace OperatorDerivativeRewrite.Foundation.RiemannEvenModelPhase
open RiemannEvenSaddleBranch RiemannEvenRealSaddle

def modelDerivative (m : ℕ) (t : ℝ) (w : ℂ) : ℂ :=
  ((2*m : ℕ) : ℂ)*(t : ℂ)*w^(2*m-1)+9-4*(Real.pi : ℂ)*Complex.exp (4*w)

def modelPhase (m : ℕ) (t : ℝ) (w : ℂ) : ℂ :=
  (t : ℂ)*w^(2*m)+9*w-(Real.pi : ℂ)*Complex.exp (4*w)

theorem modelPhase_hasDerivAt (m : ℕ) (t : ℝ) (w : ℂ) :
    HasDerivAt (modelPhase m t) (modelDerivative m t w) w := by
  have h := ((((hasDerivAt_id w).pow (2*m)).const_mul (t : ℂ)).add
    ((hasDerivAt_id w).const_mul (9 : ℂ))).sub
    ((((hasDerivAt_id w).const_mul (4 : ℂ)).cexp).const_mul (Real.pi : ℂ))
  convert h using 1
  · funext v; rfl
  · simp only [modelDerivative,id_eq]
    ring

theorem modelDerivative_hasDerivAt (m : ℕ) (t : ℝ) (w : ℂ) :
    HasDerivAt (modelDerivative m t)
      (((2*m : ℕ) : ℂ)*((2*m-1 : ℕ) : ℂ)*(t : ℂ)*w^(2*m-2)-
        16*(Real.pi : ℂ)*Complex.exp (4*w)) w := by
  have h := (((((hasDerivAt_id w).pow (2*m-1)).const_mul (((2*m : ℕ) : ℂ)*(t : ℂ))).add_const 9).sub
    ((((hasDerivAt_id w).const_mul (4 : ℂ)).cexp).const_mul (4*(Real.pi : ℂ))))
  convert h using 1
  · funext v; rfl
  · simp only [id_eq,show 2*m-1-1 = 2*m-2 by omega]
    ring

theorem modelDerivative_quartic (t : ℝ) : modelDerivative 2 t = RiemannQuarticSaddleTheta.modelDerivative t := rfl
theorem modelPhase_quartic (t : ℝ) : modelPhase 2 t = RiemannQuarticSaddleTheta.modelPhase t := rfl

theorem arithmetic_error_eq_quartic (m : ℕ) (t : ℝ) (w : ℂ) :
    complexSlope m t w-modelDerivative m t w =
      RiemannQuarticSaddleBranch.complexSlope 0 w-RiemannQuarticSaddleTheta.modelDerivative 0 w := by
  unfold complexSlope modelDerivative RiemannQuarticSaddleBranch.complexSlope RiemannQuarticSaddleTheta.modelDerivative
  ring

theorem arithmetic_error_on_neighborhood (m : ℕ) (t u : ℝ) (hu : 1 ≤ u) (w : ℂ)
    (hw : w ∈ closedBall (u : ℂ) (1/16)) :
    ‖complexSlope m t w-modelDerivative m t w‖ ≤ 1 := by
  rw [arithmetic_error_eq_quartic]
  exact RiemannQuarticSaddleNeighborhood.slope_model_error_on_neighborhood 0 u hu w hw

theorem arithmetic_error_analytic_on_neighborhood (m : ℕ) (t u : ℝ) (hu : 1 ≤ u) :
    AnalyticOnNhd ℂ (fun w => complexSlope m t w-modelDerivative m t w) (closedBall (u : ℂ) (1/16)) := by
  have he : (fun w => complexSlope m t w-modelDerivative m t w) =
      (fun w => RiemannQuarticSaddleBranch.complexSlope 0 w-RiemannQuarticSaddleTheta.modelDerivative 0 w) :=
    funext (arithmetic_error_eq_quartic m t)
  rw [he]
  exact RiemannQuarticSaddleNeighborhood.slope_error_analytic_on_neighborhood 0 u hu

theorem arithmetic_error_cauchy_bound (m : ℕ) (t u : ℝ) (hu : 1 ≤ u) (k : ℕ) :
    ‖iteratedDeriv k (fun w => complexSlope m t w-modelDerivative m t w) (u : ℂ)‖ ≤
      (k.factorial : ℝ)*(16 : ℝ)^k := by
  have he : (fun w => complexSlope m t w-modelDerivative m t w) =
      (fun w => RiemannQuarticSaddleBranch.complexSlope 0 w-RiemannQuarticSaddleTheta.modelDerivative 0 w) :=
    funext (arithmetic_error_eq_quartic m t)
  rw [he]
  exact RiemannQuarticSaddleNeighborhood.slope_error_cauchy_bound 0 u hu k

theorem real_stationary_model_residual (m : ℕ) (t u : ℝ) (hu : 1 ≤ u) (hs : phaseSlope m t u = 0) :
    ‖modelDerivative m t (u : ℂ)‖ ≤ 1 := by
  have h := arithmetic_error_on_neighborhood m t u hu (u : ℂ) (mem_closedBall_self (by norm_num))
  rw [complexSlope_real,hs,Complex.ofReal_zero,zero_sub,norm_neg] at h
  exact h

end OperatorDerivativeRewrite.Foundation.RiemannEvenModelPhase
