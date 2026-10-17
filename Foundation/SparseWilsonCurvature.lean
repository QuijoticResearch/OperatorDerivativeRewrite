import Foundation.SU2ExponentialMembership

/-! Actual reduced sparse action and an exact rational-angle comparison. -/
noncomputable section
open scoped Matrix Matrix.Norms.Operator
namespace OperatorDerivativeRewrite.Foundation.SparseWilsonCurvature
set_option backward.isDefEq.respectTransparency false
open SU2TraceHessianModel SU2MatrixExponentialBridge SU2ProductCurveHessian
open SU2OrderedLinkHessian SU2NullPlaquetteWord

def curvatureValue (θ : ℝ) : ℝ := 2+(Real.cos θ-Real.sin θ)/2
def proposedLower (θ : ℝ) : ℝ := Real.sin (2*θ)/(2*θ)*(10/4)-9*(2*θ)^2*2
def witnessAngle : ℝ := 1/1000

theorem shared_curvature (θ : ℝ) :
    deriv (deriv (action (rotation θ) (tangent 1) (tangent 0))) 0=
      (Real.cos θ-Real.sin θ)/2 := by
  have he : algebraElement ![1,1,0]=tangent 1+tangent 0 := by
    simp [algebraElement, Fin.sum_univ_three, add_comm]
  have hs : deriv (deriv (curve (rotation θ) (tangent 1+tangent 0))) 0=Real.cos θ/2 := by
    rw [← he, curve_second_derivative_model, quadratic_rotation]
    norm_num [Fin.sum_univ_three]
    ring
  have hn := reversed_null_curvature θ
  rw [null_action_second_derivative] at hn
  have hd := ordered_difference (rotation θ) (tangent 1) (tangent 0)
  rw [hs, hn] at hd
  linarith

def reducedAction (θ t : ℝ) : ℝ :=
  action (rotation θ) (tangent 1) (tangent 0) t+8*axisCurve 0 t+3*wilson (rotation θ)
def reducedSlope (θ t : ℝ) : ℝ :=
  actionSlope (rotation θ) (tangent 1) (tangent 0) t+8*(Real.sin (t/2)/2)

theorem reducedAction_hasDerivAt (θ t : ℝ) :
    HasDerivAt (reducedAction θ) (reducedSlope θ t) t := by
  have hh := ((action_hasDerivAt (rotation θ) (tangent 1) (tangent 0) t).add
    ((axisCurve_hasDerivAt 0 t).const_mul 8)).add
    (hasDerivAt_const t (3*wilson (rotation θ)))
  convert hh using 1 <;> first | rfl | (simp [reducedSlope])

theorem reducedSlope_hasDerivAt_zero (θ : ℝ) :
    HasDerivAt (reducedSlope θ) (curvatureValue θ) 0 := by
  have ha := actionSlope_hasDerivAt (rotation θ) (tangent 1) (tangent 0) 0
  have hh := ha.add ((axisSlope_hasDerivAt 0 0).const_mul 8)
  have he : deriv (action (rotation θ) (tangent 1) (tangent 0))=
      actionSlope (rotation θ) (tangent 1) (tangent 0) :=
    funext (fun t => (action_hasDerivAt (rotation θ) (tangent 1) (tangent 0) t).deriv)
  have hv := shared_curvature θ
  rw [he, ha.deriv] at hv
  convert hh using 1
  · funext t
    simp [reducedSlope]
  · simp only [zero_add, zero_div, Real.cos_zero]
    unfold curvatureValue
    linarith

theorem reducedAction_second_derivative (θ : ℝ) :
    deriv (deriv (reducedAction θ)) 0=curvatureValue θ := by
  have he : deriv (reducedAction θ)=reducedSlope θ :=
    funext (fun t => (reducedAction_hasDerivAt θ t).deriv)
  rw [he]
  exact (reducedSlope_hasDerivAt_zero θ).deriv

theorem rational_angle_strict : curvatureValue witnessAngle < proposedLower witnessAngle := by
  have hs := Real.sin_ge_sub_cube (show 0 ≤ witnessAngle by norm_num [witnessAngle])
  have hs2 := Real.sin_ge_sub_cube (show 0 ≤ 2*witnessAngle by norm_num [witnessAngle])
  have hc := Real.cos_le_one witnessAngle
  norm_num [witnessAngle] at hs hs2 hc
  norm_num [curvatureValue, proposedLower, witnessAngle]
  linarith

end OperatorDerivativeRewrite.Foundation.SparseWilsonCurvature
