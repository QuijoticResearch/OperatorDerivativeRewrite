import Foundation.SU2RadialFrameCalculus

/-! Sum of actual second exponential-frame derivatives on radial SU(2) observables.
This is a pointwise differential expression, not yet a closed L2 generator. -/
noncomputable section
open scoped Matrix Matrix.Norms.Operator
namespace OperatorDerivativeRewrite.Foundation.SU2RadialLaplacian
set_option backward.isDefEq.respectTransparency false
open QuaternionSU2Representation SU2TraceHessianModel SU2TiltEnergyResponse
open SU2BoundedObservableGradient SU2RadialFrameCalculus SU2ProductCurveHessian
open ChristoffelSkewCancellation

def traceVelocity (U : M2) (a : Fin 3) (t : ℝ) : ℝ :=
  traceReal (U*(tangent a*NormedSpace.exp (t • tangent a)))/2

theorem trace_derivative (U : M2) (a : Fin 3) (t : ℝ) :
    HasDerivAt (traceCurve U a) (traceVelocity U a t) t := by
  have hm := (hasDerivAt_exp_smul_const' (𝕂 := ℝ) (tangent a) t).const_mul U
  exact (realTraceCLM.hasFDerivAt.comp_hasDerivAt t hm).div_const 2

theorem tangent_square (a : Fin 3) : tangent a*tangent a = (-(1/4) : ℂ) • (1 : M2) := by
  fin_cases a <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [tangent, generator, generatorX, generatorY, generatorZ,
      Matrix.mul_apply, Fin.sum_univ_two] <;> ring_nf <;> norm_num [Complex.I_sq]

theorem velocity_derivative (U : M2) (a : Fin 3) :
    HasDerivAt (traceVelocity U a) (-traceReal U/8) 0 := by
  have h := (slope_hasDerivAt U (tangent a) 0).neg
  have hf : -SU2ProductCurveHessian.slope U (tangent a) = traceVelocity U a := by
    funext t
    change -SU2ProductCurveHessian.slope U (tangent a) t = traceVelocity U a t
    unfold SU2ProductCurveHessian.slope traceVelocity
    ring
  rw [hf] at h
  have hv : -(-traceReal (U*(tangent a*(tangent a*
      NormedSpace.exp ((0 : ℝ) • tangent a))))/2) = -traceReal U/8 := by
    rw [zero_smul, NormedSpace.exp_zero, mul_one, tangent_square, mul_smul_comm, mul_one]
    norm_num [traceReal, Matrix.trace_smul, Complex.mul_re]
    ring
  rw [hv] at h
  exact h

theorem radial_curve_derivative (F G : ℝ → ℝ)
    (hF : ∀ r, HasDerivAt F (G r) r) (A : SU2) (a : Fin 3) :
    deriv (fun t => radial F (groupCurve A a t)) = fun t =>
      G (traceCurve (A : M2) a t)*traceVelocity (A : M2) a t := by
  funext t
  exact ((hF _).comp t (trace_derivative (A : M2) a t)).deriv

theorem radial_second (F G H : ℝ → ℝ)
    (hF : ∀ r, HasDerivAt F (G r) r) (hG : ∀ r, HasDerivAt G (H r) r)
    (A : SU2) (a : Fin 3) :
    deriv (deriv (fun t => radial F (groupCurve A a t))) 0 =
      H (halfTrace A)*(traceSlope (A : M2) a)^2 - G (halfTrace A)*halfTrace A/4 := by
  rw [radial_curve_derivative F G hF A a]
  have h := ((hG _).comp 0 (trace_derivative (A : M2) a 0)).mul
    (velocity_derivative (A : M2) a)
  simp only [Function.comp_apply] at h
  have ht : traceCurve (A : M2) a 0 = halfTrace A := by simp [traceCurve, halfTrace]
  have hv : traceVelocity (A : M2) a 0 = traceSlope (A : M2) a := by
    simp [traceVelocity, traceSlope]
  rw [ht, hv] at h
  convert h.deriv using 1 <;> first | rfl | (unfold halfTrace; ring)

def laplacian (f : SU2 → ℝ) (A : SU2) : ℝ :=
  ∑ a : Fin 3, deriv (deriv (fun t => f (groupCurve A a t))) 0

theorem radial_formula (F G H : ℝ → ℝ)
    (hF : ∀ r, HasDerivAt F (G r) r) (hG : ∀ r, HasDerivAt G (H r) r) (A : SU2) :
    laplacian (radial F) A =
      ((1-(halfTrace A)^2)*H (halfTrace A)-3*halfTrace A*G (halfTrace A))/4 := by
  unfold laplacian
  simp_rw [radial_second F G H hF hG A]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, traceSlope_square_sum]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

def quadraticMode (r : ℝ) : ℝ := 4*r^2-1
def quarticMode (r : ℝ) : ℝ := 16*r^4-12*r^2+1

theorem quadratic_eigen (A : SU2) :
    laplacian (radial quadraticMode) A = -2*quadraticMode (halfTrace A) := by
  have hF : ∀ r : ℝ, HasDerivAt quadraticMode (8*r) r := by
    intro r
    convert ((hasDerivAt_id' r).pow 2).const_mul 4 |>.sub_const 1 using 1 <;>
      first | rfl | (dsimp [quadraticMode]; ring)
  have hG : ∀ r : ℝ, HasDerivAt (fun r : ℝ => 8*r) 8 r := by
    intro r
    simpa using (hasDerivAt_id' r).const_mul 8
  rw [radial_formula quadraticMode (fun r => 8*r) (fun _ => 8) hF hG]
  unfold quadraticMode
  ring

theorem quartic_eigen (A : SU2) :
    laplacian (radial quarticMode) A = -6*quarticMode (halfTrace A) := by
  have hF : ∀ r : ℝ, HasDerivAt quarticMode (64*r^3-24*r) r := by
    intro r
    have h := (((hasDerivAt_id' r).pow 4).const_mul 16).sub
      (((hasDerivAt_id' r).pow 2).const_mul 12) |>.add_const 1
    convert h using 1 <;> first | rfl | (dsimp [quarticMode]; ring)
  have hG : ∀ r : ℝ, HasDerivAt (fun r : ℝ => 64*r^3-24*r) (192*r^2-24) r := by
    intro r
    convert (((hasDerivAt_id' r).pow 3).const_mul 64).sub
      ((hasDerivAt_id' r).const_mul 24) using 1 <;> first | rfl | (dsimp; ring)
  rw [radial_formula quarticMode (fun r => 64*r^3-24*r)
    (fun r => 192*r^2-24) hF hG]
  unfold quarticMode
  ring

theorem observable_decomposition (A : SU2) : observable A =
    (quarticMode (halfTrace A)-quadraticMode (halfTrace A))/2 := by
  unfold observable ambient polynomial quarticMode quadraticMode halfTrace
  ring

theorem observable_laplacian (A : SU2) : laplacian observable A =
    -3*quarticMode (halfTrace A)+quadraticMode (halfTrace A) := by
  have hG : ∀ r : ℝ, HasDerivAt (fun r : ℝ => 32*r^3-16*r) (96*r^2-16) r := by
    intro r
    convert (((hasDerivAt_id' r).pow 3).const_mul 32).sub
      ((hasDerivAt_id' r).const_mul 16) using 1 <;> first | rfl | (dsimp; ring)
  change laplacian (radial polynomial) A = _
  rw [radial_formula polynomial (fun r => 32*r^3-16*r) (fun r => 96*r^2-16)
    polynomial_derivative hG]
  unfold quarticMode quadraticMode
  ring

theorem observable_not_eigen_four : laplacian observable (1 : SU2) ≠ -4*observable 1 := by
  rw [observable_laplacian]
  norm_num [observable, ambient, polynomial, halfTrace, traceReal, Matrix.trace_one,
    quarticMode, quadraticMode]

end OperatorDerivativeRewrite.Foundation.SU2RadialLaplacian
