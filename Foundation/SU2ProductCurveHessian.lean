import Foundation.SU2MatrixExponentialBridge
import Mathlib.Analysis.SpecialFunctions.Exponential

/-! Actual second derivatives of right-multiplication exponential curves. -/
noncomputable section
open scoped Matrix Matrix.Norms.Operator
namespace OperatorDerivativeRewrite.Foundation.SU2ProductCurveHessian
set_option backward.isDefEq.respectTransparency false
open SU2TraceHessianModel SU2MatrixExponentialBridge

def complexTraceCLM : M2 →L[ℝ] ℂ :=
  { Matrix.traceLinearMap (Fin 2) ℝ ℂ with cont := continuous_id.matrix_trace }

def realTraceCLM : M2 →L[ℝ] ℝ := Complex.reCLM.comp complexTraceCLM

theorem realTraceCLM_apply (U : M2) : realTraceCLM U=traceReal U := rfl

def curve (U B : M2) (t : ℝ) : ℝ := wilson (U*NormedSpace.exp (t • B))
def slope (U B : M2) (t : ℝ) : ℝ := -traceReal (U*(B*NormedSpace.exp (t • B)))/2

theorem curve_hasDerivAt (U B : M2) (t : ℝ) :
    HasDerivAt (curve U B) (slope U B t) t := by
  have hm := (hasDerivAt_exp_smul_const' (𝕂 := ℝ) B t).const_mul U
  have ht := realTraceCLM.hasFDerivAt.comp_hasDerivAt t hm
  change HasDerivAt (fun s : ℝ => traceReal (U*NormedSpace.exp (s • B)))
    (traceReal (U*(B*NormedSpace.exp (t • B)))) t at ht
  have hh := (hasDerivAt_const t (1:ℝ)).sub (ht.div_const 2)
  convert hh using 1 <;> first | rfl | (dsimp [slope]; ring)

theorem slope_hasDerivAt (U B : M2) (t : ℝ) :
    HasDerivAt (slope U B)
      (-traceReal (U*(B*(B*NormedSpace.exp (t • B))))/2) t := by
  have hm := ((hasDerivAt_exp_smul_const' (𝕂 := ℝ) B t).const_mul B).const_mul U
  have ht := realTraceCLM.hasFDerivAt.comp_hasDerivAt t hm
  have hh := ht.neg.div_const 2
  change HasDerivAt (slope U B)
    (-traceReal (U*(B*(B*NormedSpace.exp (t • B))))/2) t at hh
  exact hh

theorem curve_second_derivative (U B : M2) :
    deriv (deriv (curve U B)) 0= -traceReal (U*B^2)/2 := by
  have he : deriv (curve U B)=slope U B :=
    funext (fun t => (curve_hasDerivAt U B t).deriv)
  rw [he]
  simpa [pow_two] using (slope_hasDerivAt U B 0).deriv

theorem traceReal_real_smul (s : ℝ) (U : M2) :
    traceReal ((s:ℂ) • U)=s*traceReal U := by
  simp [traceReal, Matrix.trace_smul, Complex.mul_re]

theorem curve_second_derivative_model (U : M2) (v : Fin 3 → ℝ) :
    deriv (deriv (curve U (algebraElement v))) 0=quadratic U v := by
  rw [curve_second_derivative, algebraElement_sq, quadratic_exact]
  rw [mul_smul_comm, mul_one]
  have hs : (-(lengthSq v/4):ℂ)=((-lengthSq v/4:ℝ):ℂ) := by push_cast; ring
  rw [hs, traceReal_real_smul]
  unfold lengthSq
  ring

theorem curve_second_derivative_exp (a v : Fin 3 → ℝ) :
    deriv (deriv (curve (NormedSpace.exp (algebraElement a)) (algebraElement v))) 0=
      Real.cos (angle a)/4*lengthSq v := by
  have ht : traceReal (NormedSpace.exp (algebraElement a))=2*Real.cos (angle a) := by
    have hh := algebraElement_exp_wilson a
    unfold wilson at hh
    linarith
  rw [curve_second_derivative_model, quadratic_exact, ht]
  unfold lengthSq
  ring

theorem curve_second_derivative_rotation (r : ℝ) (v : Fin 3 → ℝ) :
    deriv (deriv (curve (rotation (r/2)) (algebraElement v))) 0=
      Real.cos (r/2)/4*lengthSq v := by
  rw [curve_second_derivative_model, quadratic_rotation]
  rfl

theorem actual_affine_product_difference {r : ℝ} (hr : 0 < r) (v : Fin 3 → ℝ) :
    deriv (deriv (fun t : ℝ => wilson (NormedSpace.exp
      (algebraElement (affineVector r (v 0) (v 1) (v 2) t))))) 0-
      deriv (deriv (curve (rotation (r/2)) (algebraElement v))) 0=
      (Real.sin (r/2)/(2*r)-Real.cos (r/2)/4)*((v 0)^2+(v 1)^2) := by
  rw [exp_wilson_affine_second_derivative hr, curve_second_derivative_rotation]
  simp only [lengthSq, Fin.sum_univ_three]
  ring

theorem angle_affine_zero {r : ℝ} (hr : 0 < r) (x y z : ℝ) :
    angle (affineVector r x y z 0)=r/2 := by
  unfold angle
  rw [affine_lengthSq]
  simp [Real.sqrt_sq hr.le]

theorem matched_base_difference {r : ℝ} (hr : 0 < r) (v : Fin 3 → ℝ) :
    deriv (deriv (fun t : ℝ => wilson (NormedSpace.exp
      (algebraElement (affineVector r (v 0) (v 1) (v 2) t))))) 0-
      deriv (deriv (curve (NormedSpace.exp (algebraElement
        (affineVector r (v 0) (v 1) (v 2) 0))) (algebraElement v))) 0=
      (Real.sin (r/2)/(2*r)-Real.cos (r/2)/4)*((v 0)^2+(v 1)^2) := by
  rw [exp_wilson_affine_second_derivative hr, curve_second_derivative_exp,
    angle_affine_zero hr]
  simp only [lengthSq, Fin.sum_univ_three]
  ring

theorem matched_base_difference_pi :
    deriv (deriv (fun t : ℝ => wilson (NormedSpace.exp
      (algebraElement (affineVector Real.pi 1 0 0 t))))) 0-
      deriv (deriv (curve (NormedSpace.exp (algebraElement
        (affineVector Real.pi 1 0 0 0))) (algebraElement ![1,0,0]))) 0=
      1/(2*Real.pi) := by
  simpa using matched_base_difference Real.pi_pos ![1,0,0]

theorem matched_base_difference_pi_pos :
    0 < deriv (deriv (fun t : ℝ => wilson (NormedSpace.exp
      (algebraElement (affineVector Real.pi 1 0 0 t))))) 0-
      deriv (deriv (curve (NormedSpace.exp (algebraElement
        (affineVector Real.pi 1 0 0 0))) (algebraElement ![1,0,0]))) 0 := by
  rw [matched_base_difference_pi]
  positivity

end OperatorDerivativeRewrite.Foundation.SU2ProductCurveHessian
