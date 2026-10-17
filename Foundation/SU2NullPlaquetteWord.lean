import Foundation.SU2MixedLinkBlocks
import Mathlib.Tactic.NoncommRing

/-! A three-factor exponential word with zero abelian first variation. -/
noncomputable section
open scoped Matrix Matrix.Norms.Operator
namespace OperatorDerivativeRewrite.Foundation.SU2NullPlaquetteWord
set_option backward.isDefEq.respectTransparency false
open SU2TraceHessianModel SU2MatrixExponentialBridge SU2ProductCurveHessian
open SU2OrderedLinkHessian

def threePath (B C D : M2) (t : ℝ) : M2 := matrixPath B C t*NormedSpace.exp (t • D)
def threeSlope (B C D : M2) (t : ℝ) : M2 :=
  matrixSlope B C t*NormedSpace.exp (t • D)+matrixPath B C t*(D*NormedSpace.exp (t • D))
def threeSecond (B C D : M2) (t : ℝ) : M2 :=
  matrixSecond B C t*NormedSpace.exp (t • D)+matrixSlope B C t*(D*NormedSpace.exp (t • D))+
    (matrixSlope B C t*(D*NormedSpace.exp (t • D))+
      matrixPath B C t*(D*(D*NormedSpace.exp (t • D))))

theorem threePath_hasDerivAt (B C D : M2) (t : ℝ) :
    HasDerivAt (threePath B C D) (threeSlope B C D t) t :=
  (matrixPath_hasDerivAt B C t).mul (hasDerivAt_exp_smul_const' (𝕂 := ℝ) D t)

theorem threeSlope_hasDerivAt (B C D : M2) (t : ℝ) :
    HasDerivAt (threeSlope B C D) (threeSecond B C D t) t := by
  have hd := hasDerivAt_exp_smul_const' (𝕂 := ℝ) D t
  exact ((matrixSlope_hasDerivAt B C t).mul hd).add
    ((matrixPath_hasDerivAt B C t).mul (hd.const_mul D))

theorem null_path_zero (B C : M2) : threePath B C (-(B+C)) 0=1 := by
  simp [threePath, matrixPath]

theorem null_path_hasDerivAt_zero (B C : M2) :
    HasDerivAt (threePath B C (-(B+C))) 0 0 := by
  simpa [threeSlope, matrixSlope, matrixPath] using threePath_hasDerivAt B C (-(B+C)) 0

theorem null_second_zero (B C : M2) : threeSecond B C (-(B+C)) 0=B*C-C*B := by
  simp only [threeSecond, matrixSecond, matrixSlope, matrixPath, zero_smul,
    NormedSpace.exp_zero, mul_one, one_mul]
  noncomm_ring

theorem null_path_second_derivative (B C : M2) :
    deriv (deriv (threePath B C (-(B+C)))) 0=B*C-C*B := by
  have he : deriv (threePath B C (-(B+C)))=threeSlope B C (-(B+C)) :=
    funext (fun t => (threePath_hasDerivAt B C (-(B+C)) t).deriv)
  rw [he]
  rw [(threeSlope_hasDerivAt B C (-(B+C)) 0).deriv, null_second_zero]

def threeAction (U B C D : M2) (t : ℝ) : ℝ := wilson (U*threePath B C D t)
def threeActionSlope (U B C D : M2) (t : ℝ) : ℝ := -traceReal (U*threeSlope B C D t)/2

theorem threeAction_hasDerivAt (U B C D : M2) (t : ℝ) :
    HasDerivAt (threeAction U B C D) (threeActionSlope U B C D t) t := by
  have hm := (threePath_hasDerivAt B C D t).const_mul U
  have ht := realTraceCLM.hasFDerivAt.comp_hasDerivAt t hm
  change HasDerivAt (fun s : ℝ => traceReal (U*threePath B C D s))
    (traceReal (U*threeSlope B C D t)) t at ht
  have hh := (hasDerivAt_const t (1:ℝ)).sub (ht.div_const 2)
  convert hh using 1 <;> first | rfl | (dsimp [threeActionSlope]; ring)

theorem threeActionSlope_hasDerivAt (U B C D : M2) (t : ℝ) :
    HasDerivAt (threeActionSlope U B C D) (-traceReal (U*threeSecond B C D t)/2) t := by
  have hm := (threeSlope_hasDerivAt B C D t).const_mul U
  have ht := realTraceCLM.hasFDerivAt.comp_hasDerivAt t hm
  have hh := ht.neg.div_const 2
  change HasDerivAt (threeActionSlope U B C D) (-traceReal (U*threeSecond B C D t)/2) t at hh
  exact hh

theorem null_action_second_derivative (U B C : M2) :
    deriv (deriv (threeAction U B C (-(B+C)))) 0= -traceReal (U*(B*C-C*B))/2 := by
  have he : deriv (threeAction U B C (-(B+C)))=threeActionSlope U B C (-(B+C)) :=
    funext (fun t => (threeAction_hasDerivAt U B C (-(B+C)) t).deriv)
  rw [he, (threeActionSlope_hasDerivAt U B C (-(B+C)) 0).deriv, null_second_zero]

theorem normalized_null_curvature (θ : ℝ) :
    deriv (deriv (threeAction (rotation θ) (tangent 0) (tangent 1)
      (-(tangent 0+tangent 1)))) 0=Real.sin θ/2 := by
  rw [null_action_second_derivative, normalized_commutator]

theorem reversed_null_curvature (θ : ℝ) :
    deriv (deriv (threeAction (rotation θ) (tangent 1) (tangent 0)
      (-(tangent 1+tangent 0)))) 0= -Real.sin θ/2 := by
  rw [null_action_second_derivative]
  have hh := normalized_commutator θ
  simp only [mul_sub, traceReal, Matrix.trace_sub, Complex.sub_re] at hh ⊢
  linarith

theorem null_abelian_sum (B C : M2) : B+C+(-(B+C))=0 := by simp

def plaquette (U1 U2 U3 U4 : M2) : M2 := U1*U2*U3⁻¹*U4⁻¹

theorem plaquette_embedding (U B C : M2) (t : ℝ) :
    plaquette U (NormedSpace.exp (t • B)) (NormedSpace.exp (t • (-C)))
      (NormedSpace.exp (t • (B+C)))=U*threePath B C (-(B+C)) t := by
  simp [plaquette, ← Matrix.exp_neg, threePath, matrixPath, smul_neg, Matrix.mul_assoc]

theorem plaquette_signed_direction (B C : M2) : B-(-C)-(B+C)=0 := by abel

def negativeCurvature (θ : ℝ) : ℝ :=
  deriv (deriv (threeAction (rotation θ) (tangent 1) (tangent 0)
    (-(tangent 1+tangent 0)))) 0

theorem negativeCurvature_eq (θ : ℝ) : negativeCurvature θ= -correction θ := by
  rw [negativeCurvature, reversed_null_curvature, correction_eq]
  ring

theorem normalized_direction_metric_sq :
    (-2*traceReal ((tangent 1)^2))+(-2*traceReal ((tangent 0)^2))+
      (-2*traceReal ((-(tangent 1+tangent 0))^2))=4 := by
  norm_num [traceReal, tangent, generator, ChristoffelSkewCancellation.generatorX,
    ChristoffelSkewCancellation.generatorY, ChristoffelSkewCancellation.generatorZ,
    Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, pow_two]

theorem no_quadratic_lower_bound :
    ¬ ∃ K ε : ℝ, 0 ≤ K ∧ 0 < ε ∧
      ∀ θ : ℝ, 0 < θ → θ < ε → -K*θ^2 ≤ negativeCurvature θ := by
  rintro ⟨K, ε, hK, hε, hb⟩
  obtain ⟨θ, ht, htε, hc⟩ := correction_exceeds_quadratic K ε hK hε
  have hh := hb θ ht htε
  rw [negativeCurvature_eq] at hh
  linarith

theorem no_direction_normalized_quadratic_lower_bound :
    ¬ ∃ K ε : ℝ, 0 ≤ K ∧ 0 < ε ∧
      ∀ θ : ℝ, 0 < θ → θ < ε → -K*θ^2*4 ≤ negativeCurvature θ := by
  rintro ⟨K, ε, hK, hε, hb⟩
  apply no_quadratic_lower_bound
  refine ⟨4*K, ε, by positivity, hε, ?_⟩
  intro θ ht htε
  have hh := hb θ ht htε
  nlinarith

end OperatorDerivativeRewrite.Foundation.SU2NullPlaquetteWord
