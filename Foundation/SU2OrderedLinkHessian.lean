import Foundation.SU2ProductCurveHessian
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! The order-sensitive second derivative of an actual two-exponential Wilson action. -/
noncomputable section
open scoped Matrix Matrix.Norms.Operator
namespace OperatorDerivativeRewrite.Foundation.SU2OrderedLinkHessian
set_option backward.isDefEq.respectTransparency false
open SU2TraceHessianModel SU2ProductCurveHessian ChristoffelSkewCancellation

def matrixPath (B C : M2) (t : ℝ) : M2 :=
  NormedSpace.exp (t • B)*NormedSpace.exp (t • C)
def matrixSlope (B C : M2) (t : ℝ) : M2 :=
  (B*NormedSpace.exp (t • B))*NormedSpace.exp (t • C)+
    NormedSpace.exp (t • B)*(C*NormedSpace.exp (t • C))
def matrixSecond (B C : M2) (t : ℝ) : M2 :=
  (B*(B*NormedSpace.exp (t • B)))*NormedSpace.exp (t • C)+
    (B*NormedSpace.exp (t • B))*(C*NormedSpace.exp (t • C))+
    ((B*NormedSpace.exp (t • B))*(C*NormedSpace.exp (t • C))+
      NormedSpace.exp (t • B)*(C*(C*NormedSpace.exp (t • C))))

theorem matrixPath_hasDerivAt (B C : M2) (t : ℝ) :
    HasDerivAt (matrixPath B C) (matrixSlope B C t) t := by
  exact (hasDerivAt_exp_smul_const' (𝕂 := ℝ) B t).mul
    (hasDerivAt_exp_smul_const' (𝕂 := ℝ) C t)

theorem matrixSlope_hasDerivAt (B C : M2) (t : ℝ) :
    HasDerivAt (matrixSlope B C) (matrixSecond B C t) t := by
  have hb := hasDerivAt_exp_smul_const' (𝕂 := ℝ) B t
  have hc := hasDerivAt_exp_smul_const' (𝕂 := ℝ) C t
  exact ((hb.const_mul B).mul hc).add (hb.mul (hc.const_mul C))

def action (U B C : M2) (t : ℝ) : ℝ := wilson (U*matrixPath B C t)
def actionSlope (U B C : M2) (t : ℝ) : ℝ := -traceReal (U*matrixSlope B C t)/2

theorem action_hasDerivAt (U B C : M2) (t : ℝ) :
    HasDerivAt (action U B C) (actionSlope U B C t) t := by
  have hm := (matrixPath_hasDerivAt B C t).const_mul U
  have ht := realTraceCLM.hasFDerivAt.comp_hasDerivAt t hm
  change HasDerivAt (fun s : ℝ => traceReal (U*matrixPath B C s))
    (traceReal (U*matrixSlope B C t)) t at ht
  have hh := (hasDerivAt_const t (1:ℝ)).sub (ht.div_const 2)
  convert hh using 1 <;> first | rfl | (dsimp [actionSlope]; ring)

theorem actionSlope_hasDerivAt (U B C : M2) (t : ℝ) :
    HasDerivAt (actionSlope U B C) (-traceReal (U*matrixSecond B C t)/2) t := by
  have hm := (matrixSlope_hasDerivAt B C t).const_mul U
  have ht := realTraceCLM.hasFDerivAt.comp_hasDerivAt t hm
  have hh := ht.neg.div_const 2
  change HasDerivAt (actionSlope U B C) (-traceReal (U*matrixSecond B C t)/2) t at hh
  exact hh

theorem action_second_derivative (U B C : M2) :
    deriv (deriv (action U B C)) 0=
      -traceReal (U*(B^2+B*C+B*C+C^2))/2 := by
  have he : deriv (action U B C)=actionSlope U B C :=
    funext (fun t => (action_hasDerivAt U B C t).deriv)
  rw [he]
  simpa [matrixSecond, pow_two, add_assoc] using (actionSlope_hasDerivAt U B C 0).deriv

theorem ordered_difference (U B C : M2) :
    deriv (deriv (action U B C)) 0-deriv (deriv (curve U (B+C))) 0=
      -traceReal (U*(B*C-C*B))/2 := by
  rw [action_second_derivative, curve_second_derivative]
  simp only [pow_two, mul_add, add_mul, mul_sub, traceReal, Matrix.trace_add,
    Matrix.trace_sub, Complex.add_re, Complex.sub_re]
  ring

theorem opposite_order_difference (U B C : M2) :
    deriv (deriv (action U B C)) 0-deriv (deriv (action U C B)) 0=
      -traceReal (U*(B*C-C*B)) := by
  rw [action_second_derivative, action_second_derivative]
  simp only [mul_add, mul_sub, traceReal, Matrix.trace_add, Matrix.trace_sub,
    Complex.add_re, Complex.sub_re]
  ring

theorem order_average (U B C : M2) :
    (deriv (deriv (action U B C)) 0+deriv (deriv (action U C B)) 0)/2=
      deriv (deriv (curve U (B+C))) 0 := by
  rw [action_second_derivative, action_second_derivative, curve_second_derivative]
  simp only [pow_two, mul_add, add_mul, traceReal, Matrix.trace_add, Complex.add_re]
  ring

theorem normalized_commutator (θ : ℝ) :
    -traceReal (rotation θ*(tangent 0*tangent 1-tangent 1*tangent 0))/2=
      Real.sin θ/2 := by
  norm_num [traceReal, rotation, tangent, generator, generatorX, generatorY, generatorZ,
    Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Complex.mul_re, Complex.mul_im]
  simp only [Complex.sin_ofReal_re]
  ring

theorem normalized_ordered_difference (θ : ℝ) :
    deriv (deriv (action (rotation θ) (tangent 0) (tangent 1))) 0-
      deriv (deriv (curve (rotation θ) (tangent 0+tangent 1))) 0=Real.sin θ/2 := by
  rw [ordered_difference, normalized_commutator]

theorem ordered_difference_pi_six :
    deriv (deriv (action (rotation (Real.pi/6)) (tangent 0) (tangent 1))) 0-
      deriv (deriv (curve (rotation (Real.pi/6)) (tangent 0+tangent 1))) 0=1/4 := by
  rw [normalized_ordered_difference, Real.sin_pi_div_six]
  norm_num

theorem ordered_difference_nonzero (θ : ℝ) (hθ : Real.sin θ ≠ 0) :
    deriv (deriv (action (rotation θ) (tangent 0) (tangent 1))) 0 ≠
      deriv (deriv (curve (rotation θ) (tangent 0+tangent 1))) 0 := by
  intro he
  have hh := normalized_ordered_difference θ
  rw [he, sub_self] at hh
  exact hθ (by linarith)

theorem matrixPath_zero (B C : M2) : matrixPath B C 0=1 := by simp [matrixPath]

theorem matrixPath_hasDerivAt_zero (B C : M2) :
    HasDerivAt (matrixPath B C) (B+C) 0 := by
  simpa [matrixSlope] using matrixPath_hasDerivAt B C 0

theorem summedPath_hasDerivAt_zero (B C : M2) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp (t • (B+C))) (B+C) 0 := by
  simpa using hasDerivAt_exp_smul_const' (𝕂 := ℝ) (B+C) 0

def correction (θ : ℝ) : ℝ :=
  deriv (deriv (action (rotation θ) (tangent 0) (tangent 1))) 0-
    deriv (deriv (curve (rotation θ) (tangent 0+tangent 1))) 0

theorem correction_eq (θ : ℝ) : correction θ=Real.sin θ/2 :=
  normalized_ordered_difference θ

theorem correction_hasDerivAt_zero : HasDerivAt correction (1/2) 0 := by
  have he : correction=(fun θ : ℝ => Real.sin θ/2) := funext correction_eq
  rw [he]
  simpa using (Real.hasDerivAt_sin 0).div_const 2

theorem correction_exceeds_quadratic (K ε : ℝ) (hK : 0 ≤ K) (hε : 0 < ε) :
    ∃ θ : ℝ, 0 < θ ∧ θ < ε ∧ K*θ^2 < correction θ := by
  let θ : ℝ := min (ε/2) (min (1/2) (1/(8*(K+1))))
  have ht : 0 < θ := by dsimp [θ]; positivity
  have htε : θ < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hth : θ ≤ 1/2 := le_trans (min_le_right _ _) (min_le_left _ _)
  have htd : θ ≤ 1/(8*(K+1)) := le_trans (min_le_right _ _) (min_le_right _ _)
  have hp : 0 < 8*(K+1) := by positivity
  have hm : θ*(8*(K+1)) ≤ 1 := (le_div_iff₀ hp).mp htd
  have hk : K*θ ≤ 1/8 := by nlinarith
  have hsq : θ^2 ≤ 1 := by
    have hh := mul_self_le_mul_self ht.le (le_trans hth (by norm_num : (1/2:ℝ) ≤ 1))
    nlinarith
  have hcube : θ^3 ≤ θ := by nlinarith [mul_nonneg ht.le (sub_nonneg.mpr hsq)]
  have hquad : K*θ^2 ≤ θ/8 := by nlinarith [mul_nonneg ht.le (sub_nonneg.mpr hk)]
  refine ⟨θ, ht, htε, ?_⟩
  rw [correction_eq]
  nlinarith [Real.sin_ge_sub_cube ht.le]

theorem no_local_quadratic_bound :
    ¬ ∃ K ε : ℝ, 0 ≤ K ∧ 0 < ε ∧
      ∀ θ : ℝ, 0 < θ → θ < ε → |correction θ| ≤ K*θ^2 := by
  rintro ⟨K, ε, hK, hε, hb⟩
  obtain ⟨θ, ht, htε, hc⟩ := correction_exceeds_quadratic K ε hK hε
  have hh := le_trans (le_abs_self (correction θ)) (hb θ ht htε)
  linarith

end OperatorDerivativeRewrite.Foundation.SU2OrderedLinkHessian
