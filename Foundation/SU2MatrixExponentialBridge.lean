import Foundation.SU2DirectionalCoordinateProbe
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-! A convergent-series bridge from normalized SU(2) matrices to the radial action. -/
noncomputable section
open scoped Matrix Matrix.Norms.Operator Nat
namespace OperatorDerivativeRewrite.Foundation.SU2MatrixExponentialBridge
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open SU2TraceHessianModel ChristoffelSkewCancellation

def algebraElement (v : Fin 3 → ℝ) : M2 := ∑ a, (v a:ℂ) • tangent a
def lengthSq (v : Fin 3 → ℝ) : ℝ := ∑ a, (v a)^2
def angle (v : Fin 3 → ℝ) : ℝ := Real.sqrt (lengthSq v)/2

theorem algebraElement_trace (v : Fin 3 → ℝ) : Matrix.trace (algebraElement v)=0 := by
  simp [algebraElement, Matrix.trace_sum, Matrix.trace_smul, tangent_trace_zero]

theorem algebraElement_sq (v : Fin 3 → ℝ) :
    (algebraElement v)^2=(-(lengthSq v/4):ℂ) • (1:M2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [algebraElement, lengthSq, tangent, generator, generatorX, generatorY,
      generatorZ, Fin.sum_univ_three, Matrix.mul_apply, Fin.sum_univ_two, pow_two] <;>
    ring_nf <;> norm_num [Complex.I_sq] <;> ring

theorem lengthSq_nonneg (v : Fin 3 → ℝ) : 0 ≤ lengthSq v :=
  Finset.sum_nonneg (fun a _ => sq_nonneg (v a))

theorem angle_sq (v : Fin 3 → ℝ) : (angle v)^2=lengthSq v/4 := by
  unfold angle
  rw [div_pow, Real.sq_sqrt (lengthSq_nonneg v)]
  norm_num

theorem algebraElement_sq_angle (v : Fin 3 → ℝ) :
    (algebraElement v)^2=(-(angle v)^2:ℂ) • (1:M2) := by
  rw [algebraElement_sq, ← Complex.ofReal_pow, angle_sq]
  push_cast
  rfl

theorem even_power (A : M2) (ρ : ℝ) (hsq : A^2=(-(ρ^2):ℂ) • (1:M2)) (n : ℕ) :
    A^(2*n)=((-(ρ^2):ℂ)^n) • (1:M2) := by
  rw [pow_mul, hsq, smul_pow, one_pow]

theorem odd_trace (A : M2) (ρ : ℝ) (ht : Matrix.trace A=0)
    (hsq : A^2=(-(ρ^2):ℂ) • (1:M2)) (n : ℕ) : Matrix.trace (A^(2*n+1))=0 := by
  rw [pow_succ, even_power A ρ hsq, smul_mul_assoc, one_mul, Matrix.trace_smul, ht,
    smul_zero]

theorem exp_trace_of_sq (A : M2) (ρ : ℝ) (ht : Matrix.trace A=0)
    (hsq : A^2=(-(ρ^2):ℂ) • (1:M2)) :
    Matrix.trace (NormedSpace.exp A)=2*Complex.cos (ρ:ℂ) := by
  have he : HasSum (fun n : ℕ => Matrix.trace ((n !⁻¹:ℂ) • A^n))
      (Matrix.trace (NormedSpace.exp A)) :=
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) A).map
      (Matrix.traceAddMonoidHom (Fin 2) ℂ) continuous_id.matrix_trace
  have hc := (Complex.hasSum_cos (ρ:ℂ)).mul_left 2
  have heven : HasSum (fun n : ℕ => Matrix.trace (((((2*n)!:ℂ)⁻¹)) • A^(2*n)))
      (2*Complex.cos (ρ:ℂ)) := by
    convert hc using 1
    funext n
    rw [Matrix.trace_smul, even_power A ρ hsq, Matrix.trace_smul]
    simp only [Matrix.trace_one, Fintype.card_fin, smul_eq_mul]
    push_cast
    rw [neg_pow, ← pow_mul]
    ring
  have hodd : HasSum (fun n : ℕ => Matrix.trace (((((2*n+1)!:ℂ)⁻¹)) • A^(2*n+1))) 0 := by
    simpa only [Matrix.trace_smul, odd_trace A ρ ht hsq, smul_zero] using
      (hasSum_zero : HasSum (fun _ : ℕ => (0:ℂ)) 0)
  have hh : HasSum (fun n : ℕ => Matrix.trace ((n !⁻¹:ℂ) • A^n))
      (2*Complex.cos (ρ:ℂ)+0) := HasSum.even_add_odd heven hodd
  simpa only [add_zero] using he.unique hh

theorem algebraElement_exp_trace (v : Fin 3 → ℝ) :
    Matrix.trace (NormedSpace.exp (algebraElement v))=2*Complex.cos (angle v:ℂ) :=
  exp_trace_of_sq _ _ (algebraElement_trace v) (algebraElement_sq_angle v)

theorem algebraElement_exp_wilson (v : Fin 3 → ℝ) :
    wilson (NormedSpace.exp (algebraElement v))=1-Real.cos (angle v) := by
  unfold wilson traceReal
  rw [algebraElement_exp_trace]
  norm_num [Complex.mul_re, Complex.cos_ofReal_re]

theorem algebraElement_skewHermitian (v : Fin 3 → ℝ) :
    (algebraElement v)ᴴ= -algebraElement v := by
  simp [algebraElement, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul,
    tangent_skewHermitian, Finset.sum_neg_distrib]

theorem algebraElement_metric_sq (v : Fin 3 → ℝ) :
    -2*traceReal ((algebraElement v)^2)=lengthSq v := by
  rw [algebraElement_sq]
  norm_num [traceReal, Matrix.trace_smul, Matrix.trace_one, Complex.mul_re]
  ring

theorem algebraElement_exp_unitary_left (v : Fin 3 → ℝ) :
    (NormedSpace.exp (algebraElement v))ᴴ*NormedSpace.exp (algebraElement v)=1 := by
  rw [← Matrix.exp_conjTranspose, algebraElement_skewHermitian,
    ← Matrix.exp_add_of_commute _ _ (Commute.refl (algebraElement v)).neg_left]
  simp

theorem algebraElement_exp_unitary_right (v : Fin 3 → ℝ) :
    NormedSpace.exp (algebraElement v)*(NormedSpace.exp (algebraElement v))ᴴ=1 := by
  rw [← Matrix.exp_conjTranspose, algebraElement_skewHermitian,
    ← Matrix.exp_add_of_commute _ _ (Commute.refl (algebraElement v)).neg_right]
  simp

def affineVector (r x y z t : ℝ) : Fin 3 → ℝ := ![t*x,t*y,r+t*z]

theorem affine_lengthSq (r x y z t : ℝ) :
    lengthSq (affineVector r x y z t)=(t*x)^2+(t*y)^2+(r+t*z)^2 := by
  simp [lengthSq, affineVector, Fin.sum_univ_three]

theorem exp_wilson_affine (r x y z t : ℝ) :
    wilson (NormedSpace.exp (algebraElement (affineVector r x y z t)))=
      SU2DirectionalCoordinateProbe.path r x y z t := by
  rw [algebraElement_exp_wilson, SU2DirectionalCoordinateProbe.path_eq]
  unfold angle
  rw [affine_lengthSq]

theorem exp_wilson_affine_second_derivative {r : ℝ} (hr : 0 < r) (x y z : ℝ) :
    deriv (deriv (fun t : ℝ => wilson
      (NormedSpace.exp (algebraElement (affineVector r x y z t))))) 0=
      Real.sin (r/2)/(2*r)*(x^2+y^2)+Real.cos (r/2)/4*z^2 := by
  have he : (fun t : ℝ => wilson (NormedSpace.exp
      (algebraElement (affineVector r x y z t))))=
      SU2DirectionalCoordinateProbe.path r x y z := funext (exp_wilson_affine r x y z)
  rw [he]
  exact SU2DirectionalCoordinateProbe.path_second_derivative hr x y z

theorem coordinate_frame_difference (r : ℝ) (v : Fin 3 → ℝ) :
    SU2DirectionalCoordinateProbe.coordinateQuadratic r v-
      quadratic (rotation (r/2)) v=
      (Real.sin (r/2)/(2*r)-Real.cos (r/2)/4)*((v 0)^2+(v 1)^2) := by
  rw [SU2DirectionalCoordinateProbe.coordinateQuadratic_eq, quadratic_rotation]
  simp only [Fin.sum_univ_three]
  ring

end OperatorDerivativeRewrite.Foundation.SU2MatrixExponentialBridge
