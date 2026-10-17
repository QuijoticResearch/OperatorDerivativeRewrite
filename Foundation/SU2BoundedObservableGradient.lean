import Foundation.SU2TiltEnergyResponse
import Foundation.SU2ExplicitRotationLog

/-! A bounded polynomial observable with directional derivative two in a trace-unit
SU(2) frame. Supremum bounds alone do not bound the Lipschitz/gradient seminorm. -/
noncomputable section
open scoped Matrix Matrix.Norms.Operator ContDiff
namespace OperatorDerivativeRewrite.Foundation.SU2BoundedObservableGradient
set_option backward.isDefEq.respectTransparency false
open SU2TraceHessianModel QuaternionSU2Representation SU2TiltEnergyResponse

def polynomial (r : ℝ) : ℝ := 8*r^4 - 8*r^2 + 1

theorem polynomial_bound (r : ℝ) (hr : |r| ≤ 1) : |polynomial r| ≤ 1 := by
  have hsq : r^2 ≤ 1 := by nlinarith [(abs_le.mp hr).1, (abs_le.mp hr).2]
  have hprod : 0 ≤ r^2*(1-r^2) := mul_nonneg (sq_nonneg r) (by linarith)
  rw [abs_le]
  unfold polynomial
  constructor <;> nlinarith [sq_nonneg (r^2-1/2)]

def ambient (A : M2) : ℝ := polynomial (traceReal A / 2)

theorem ambient_smooth : ContDiff ℝ ∞ ambient := by
  unfold ambient polynomial
  have h : ContDiff ℝ ∞ (fun A : M2 => traceReal A / 2) :=
    SU2ProductCurveHessian.realTraceCLM.contDiff.div_const (2 : ℝ)
  exact ((contDiff_const.mul (h.pow 4)).sub (contDiff_const.mul (h.pow 2))).add
    contDiff_const

def observable (A : SU2) : ℝ := ambient (A : M2)

theorem observable_bound (A : SU2) : |observable A| ≤ 1 :=
  polynomial_bound (halfTrace A) (halfTrace_bound A)

theorem observable_conjugate (U A : SU2) : observable (U*A*U⁻¹) = observable A := by
  change polynomial (halfTrace (U*A*U⁻¹)) = polynomial (halfTrace A)
  rw [halfTrace_conjugate]

theorem polynomial_cos (θ : ℝ) : polynomial (Real.cos θ) = Real.cos (4*θ) := by
  rw [show 4*θ = 2*(2*θ) by ring, Real.cos_two_mul, Real.cos_two_mul]
  unfold polynomial
  ring

def groupCurve (A : SU2) (a : Fin 3) (t : ℝ) : SU2 :=
  ⟨(A : M2)*NormedSpace.exp (t • tangent a), curve_mem A a t⟩

theorem direction_unit (A : SU2) (a : Fin 3) :
    traceMetric ((A : M2)*tangent a) ((A : M2)*tangent a) = 1 := by
  simpa using frame_orthonormal A a a

def rotationPoint (θ : ℝ) : SU2 := ⟨rotation θ, SU2ExponentialMembership.rotation_mem θ⟩

theorem curve_formula (θ t : ℝ) :
    observable (groupCurve (rotationPoint θ) 2 t) = Real.cos (4*θ+2*t) := by
  have he : NormedSpace.exp (t • tangent 2) = rotation (t/2) := by
    have h := SU2ExplicitRotationLog.exp_explicitLog (t/2)
    simpa only [SU2ExplicitRotationLog.explicitLog, show 2*(t/2)=t by ring] using h
  change polynomial (traceReal (rotation θ * NormedSpace.exp (t • tangent 2)) / 2) = _
  rw [he, ← rotation_add, rotation_trace]
  have h : (2*Real.cos (θ+t/2))/2 = Real.cos (θ+t/2) := by ring
  rw [h, polynomial_cos]
  congr 1
  ring

theorem curve_derivative (θ : ℝ) :
    HasDerivAt (fun t => observable (groupCurve (rotationPoint θ) 2 t))
      (-2*Real.sin (4*θ)) 0 := by
  have ha : HasDerivAt (fun t : ℝ => 4*θ+2*t) 2 0 := by
    convert (hasDerivAt_id' (0 : ℝ)).const_mul 2 |>.const_add (4*θ) using 1
    ring
  have h := ha.cos
  simp only [mul_zero, add_zero] at h
  simpa only [curve_formula, neg_mul, mul_neg, mul_comm] using h

theorem witness_derivative :
    deriv (fun t => observable (groupCurve (rotationPoint (Real.pi/8)) 2 t)) 0 = -2 := by
  rw [(curve_derivative _).deriv]
  have h : 4*(Real.pi/8) = Real.pi/2 := by ring
  rw [h, Real.sin_pi_div_two]
  ring

theorem witness_not_lipschitz_one :
    ¬ LipschitzWith 1 (fun t => observable (groupCurve (rotationPoint (Real.pi/8)) 2 t)) := by
  intro h
  have hh := norm_deriv_le_of_lipschitz (x₀ := (0 : ℝ)) h
  rw [witness_derivative] at hh
  norm_num at hh

theorem no_supnorm_gradient_bound :
    ∃ f : SU2 → ℝ, (∀ A, |f A| ≤ 1) ∧ ∃ A : SU2,
      traceMetric ((A : M2)*tangent 2) ((A : M2)*tangent 2) = 1 ∧
      1 < |deriv (fun t => f (groupCurve A 2 t)) 0| := by
  refine ⟨observable, observable_bound, rotationPoint (Real.pi/8), direction_unit _ _, ?_⟩
  rw [witness_derivative]
  norm_num

def frameEnergy (f : SU2 → ℝ) (A : SU2) : ℝ :=
  ∑ a : Fin 3, (deriv (fun t => f (groupCurve A a t)) 0)^2

theorem witness_energy_lower_bound :
    4 ≤ frameEnergy observable (rotationPoint (Real.pi/8)) := by
  have h := Finset.single_le_sum (f := fun a : Fin 3 =>
    (deriv (fun t => observable (groupCurve (rotationPoint (Real.pi/8)) a t)) 0)^2)
    (fun a _ => sq_nonneg _) (Finset.mem_univ (2 : Fin 3))
  rw [witness_derivative] at h
  norm_num at h
  exact h

end OperatorDerivativeRewrite.Foundation.SU2BoundedObservableGradient
