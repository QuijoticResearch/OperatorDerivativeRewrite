import Foundation.SU2NullPlaquetteWord

/-! Four-factor exponential second variations, reusing the verified three-factor jets. -/
noncomputable section
open scoped Matrix Matrix.Norms.Operator
namespace OperatorDerivativeRewrite.Foundation.SU2FourWordVariation
open SU2TraceHessianModel SU2MatrixExponentialBridge SU2ProductCurveHessian
open SU2OrderedLinkHessian SU2NullPlaquetteWord

def path (B C D E : M2) (t : ℝ) : M2 := threePath B C D t*NormedSpace.exp (t • E)
def pathSlope (B C D E : M2) (t : ℝ) : M2 :=
  threeSlope B C D t*NormedSpace.exp (t • E)+threePath B C D t*(E*NormedSpace.exp (t • E))
def pathSecond (B C D E : M2) (t : ℝ) : M2 :=
  threeSecond B C D t*NormedSpace.exp (t • E)+threeSlope B C D t*(E*NormedSpace.exp (t • E))+
    (threeSlope B C D t*(E*NormedSpace.exp (t • E))+
      threePath B C D t*(E*(E*NormedSpace.exp (t • E))))

theorem path_hasDerivAt (B C D E : M2) (t : ℝ) :
    HasDerivAt (path B C D E) (pathSlope B C D E t) t :=
  (threePath_hasDerivAt B C D t).mul (hasDerivAt_exp_smul_const' (𝕂 := ℝ) E t)

theorem pathSlope_hasDerivAt (B C D E : M2) (t : ℝ) :
    HasDerivAt (pathSlope B C D E) (pathSecond B C D E t) t := by
  have he := hasDerivAt_exp_smul_const' (𝕂 := ℝ) E t
  exact ((threeSlope_hasDerivAt B C D t).mul he).add
    ((threePath_hasDerivAt B C D t).mul (he.const_mul E))

def action (B C D E : M2) (t : ℝ) : ℝ := wilson (path B C D E t)
def actionSlope (B C D E : M2) (t : ℝ) : ℝ := -traceReal (pathSlope B C D E t)/2

theorem action_hasDerivAt (B C D E : M2) (t : ℝ) :
    HasDerivAt (action B C D E) (actionSlope B C D E t) t := by
  have hh := realTraceCLM.hasFDerivAt.comp_hasDerivAt t (path_hasDerivAt B C D E t)
  change HasDerivAt (fun s => traceReal (path B C D E s))
    (traceReal (pathSlope B C D E t)) t at hh
  have ht := (hasDerivAt_const t (1 : ℝ)).sub (hh.div_const 2)
  convert ht using 1 <;> first | rfl | (dsimp [actionSlope]; ring)

theorem actionSlope_hasDerivAt (B C D E : M2) (t : ℝ) :
    HasDerivAt (actionSlope B C D E) (-traceReal (pathSecond B C D E t)/2) t := by
  exact ((realTraceCLM.hasFDerivAt.comp_hasDerivAt t
    (pathSlope_hasDerivAt B C D E t)).neg).div_const 2

private theorem trace_comm (B C : M2) : traceReal (B*C)=traceReal (C*B) := by
  unfold traceReal
  rw [Matrix.trace_mul_comm]

theorem trace_second_zero (B C D E : M2) :
    traceReal (pathSecond B C D E 0)=traceReal ((B+C+D+E)^2) := by
  simp only [pathSecond,threeSecond,threeSlope,threePath,matrixSecond,matrixSlope,
    matrixPath,zero_smul,NormedSpace.exp_zero,mul_one,one_mul]
  simp only [pow_two,mul_add,add_mul,traceReal,Matrix.trace_add,Complex.add_re]
  have hBC := trace_comm B C
  have hBD := trace_comm B D
  have hBE := trace_comm B E
  have hCD := trace_comm C D
  have hCE := trace_comm C E
  have hDE := trace_comm D E
  unfold traceReal at hBC hBD hBE hCD hCE hDE
  linarith

theorem action_second_zero (B C D E : M2) :
    deriv (deriv (action B C D E)) 0= -traceReal ((B+C+D+E)^2)/2 := by
  have he : deriv (action B C D E)=actionSlope B C D E :=
    funext (fun t => (action_hasDerivAt B C D E t).deriv)
  rw [he,(actionSlope_hasDerivAt B C D E 0).deriv,trace_second_zero]

theorem algebraElement_add (u v : Fin 3 → ℝ) :
    algebraElement (u+v)=algebraElement u+algebraElement v := by
  simp [algebraElement,Complex.ofReal_add,add_smul,Finset.sum_add_distrib]

theorem algebraElement_neg (u : Fin 3 → ℝ) : algebraElement (-u)= -algebraElement u := by
  simp [algebraElement,Complex.ofReal_neg,neg_smul,Finset.sum_neg_distrib]

theorem signed_generator_sum (u v w z : Fin 3 → ℝ) :
    algebraElement u+algebraElement v+(-algebraElement w)+(-algebraElement z)=
      algebraElement (u+v-w-z) := by
  simp [sub_eq_add_neg,algebraElement_add,algebraElement_neg]

theorem signed_second_zero (u v w z : Fin 3 → ℝ) :
    deriv (deriv (action (algebraElement u) (algebraElement v)
      (-algebraElement w) (-algebraElement z))) 0=lengthSq (u+v-w-z)/4 := by
  rw [action_second_zero,signed_generator_sum]
  have hh := algebraElement_metric_sq (u+v-w-z)
  linarith

theorem signed_slope_second_zero (u v w z : Fin 3 → ℝ) :
    -traceReal (pathSecond (algebraElement u) (algebraElement v)
      (-algebraElement w) (-algebraElement z) 0)/2=lengthSq (u+v-w-z)/4 := by
  rw [trace_second_zero,signed_generator_sum]
  have hh := algebraElement_metric_sq (u+v-w-z)
  linarith


theorem pathSlope_zero (B C D E : M2) : pathSlope B C D E 0=B+C+D+E := by
  simp [pathSlope,threeSlope,threePath,matrixSlope,matrixPath]

theorem signed_first_zero (u v w z : Fin 3 → ℝ) :
    actionSlope (algebraElement u) (algebraElement v)
      (-algebraElement w) (-algebraElement z) 0=0 := by
  rw [actionSlope,pathSlope_zero,signed_generator_sum]
  simp [traceReal,algebraElement_trace]

end OperatorDerivativeRewrite.Foundation.SU2FourWordVariation
