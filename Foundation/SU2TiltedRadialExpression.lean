import Foundation.SU2PolynomialHeatTrajectory

/-! Actual normalized half-trace tilt, its logarithmic score and the corresponding
pointwise score-weighted frame expression. No closed generator is asserted. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Matrix Matrix.Norms.Operator
namespace OperatorDerivativeRewrite.Foundation.SU2TiltedRadialExpression
set_option backward.isDefEq.respectTransparency false
open QuaternionSU2Representation SU2TraceHessianModel SU2TiltEnergyResponse
open SU2BoundedObservableGradient SU2RadialFrameCalculus SU2RadialLaplacian
open SU2PolynomialHeatTrajectory
variable (ν : Measure SU2) [IsProbabilityMeasure ν]

def linkLaw (β : ℝ) : Measure SU2 :=
  BoundedExponentialTiltResponse.tiltedMeasure ν halfTrace β

instance linkLaw_probability (β : ℝ) : IsProbabilityMeasure (linkLaw ν β) :=
  BoundedExponentialTiltResponse.tiltedMeasure_probability ν halfTrace
    halfTrace_measurable halfTrace_bound β

theorem density_positive (β : ℝ) (A : SU2) :
    0 < BoundedExponentialTiltResponse.density ν halfTrace β A :=
  div_pos (Real.exp_pos _) (BoundedExponentialTiltResponse.partition_pos ν halfTrace
    halfTrace_measurable halfTrace_bound β)

theorem log_density (β : ℝ) (A : SU2) :
    Real.log (BoundedExponentialTiltResponse.density ν halfTrace β A) =
      β*halfTrace A-Real.log (BoundedExponentialTiltResponse.partition ν halfTrace β) := by
  unfold BoundedExponentialTiltResponse.density
  rw [Real.log_div (Real.exp_ne_zero _) (ne_of_gt
    (BoundedExponentialTiltResponse.partition_pos ν halfTrace halfTrace_measurable halfTrace_bound β)),
    Real.log_exp]

theorem score_derivative (β : ℝ) (A : SU2) (a : Fin 3) :
    HasDerivAt (fun t => Real.log
      (BoundedExponentialTiltResponse.density ν halfTrace β (groupCurve A a t)))
      (β*traceSlope (A : M2) a) 0 := by
  have hr := radial_derivative (fun r : ℝ => r) 1 A a (hasDerivAt_id' (halfTrace A))
  have h := hr.const_mul β |>.sub_const
    (Real.log (BoundedExponentialTiltResponse.partition ν halfTrace β))
  simpa only [log_density, radial, one_mul] using h

def score (β : ℝ) (A : SU2) (a : Fin 3) : ℝ :=
  deriv (fun t => Real.log
    (BoundedExponentialTiltResponse.density ν halfTrace β (groupCurve A a t))) 0

theorem score_exact (β : ℝ) (A : SU2) (a : Fin 3) :
    score ν β A a = β*traceSlope (A : M2) a := (score_derivative ν β A a).deriv

def tiltedExpression (β : ℝ) (f : SU2 → ℝ) (A : SU2) : ℝ :=
  laplacian f A + ∑ a : Fin 3, score ν β A a*deriv (fun t => f (groupCurve A a t)) 0

theorem radial_tilted_formula (β : ℝ) (F G H : ℝ → ℝ)
    (hF : ∀ r, HasDerivAt F (G r) r) (hG : ∀ r, HasDerivAt G (H r) r) (A : SU2) :
    tiltedExpression ν β (radial F) A =
      ((1-(halfTrace A)^2)*(H (halfTrace A)+β*G (halfTrace A))-
        3*halfTrace A*G (halfTrace A))/4 := by
  unfold tiltedExpression
  rw [radial_formula F G H hF hG]
  simp_rw [score_exact, (radial_derivative F (G (halfTrace A)) A _ (hF _)).deriv]
  have he : (∑ a : Fin 3, (β*traceSlope (A : M2) a)*
      (G (halfTrace A)*traceSlope (A : M2) a)) =
      β*G (halfTrace A)*(∑ a : Fin 3, (traceSlope (A : M2) a)^2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [he, traceSlope_square_sum]
  ring

theorem zero_tilt (f : SU2 → ℝ) (A : SU2) : tiltedExpression ν 0 f A = laplacian f A := by
  simp [tiltedExpression, score_exact]

theorem observable_tilted (β : ℝ) (A : SU2) :
    tiltedExpression ν β observable A =
      -3*quarticMode (halfTrace A)+quadraticMode (halfTrace A)+
        β*(32*(halfTrace A)^3-16*halfTrace A)*(1-(halfTrace A)^2)/4 := by
  have hG : ∀ r : ℝ, HasDerivAt (fun r : ℝ => 32*r^3-16*r) (96*r^2-16) r := by
    intro r
    convert (((hasDerivAt_id' r).pow 3).const_mul 32).sub
      ((hasDerivAt_id' r).const_mul 16) using 1 <;> first | rfl | (dsimp; ring)
  change tiltedExpression ν β (radial polynomial) A = _
  rw [radial_tilted_formula ν β polynomial (fun r => 32*r^3-16*r)
    (fun r => 96*r^2-16) polynomial_derivative hG]
  unfold quarticMode quadraticMode
  ring

theorem initial_tilt_residual (β : ℝ) :
    deriv (fun t => observableTrajectory t (rotationPoint (Real.pi/3))) 0 -
      tiltedExpression ν β observable (rotationPoint (Real.pi/3)) = 3*β/4 := by
  have ht : halfTrace (rotationPoint (Real.pi/3)) = 1/2 := by
    change traceReal (rotation (Real.pi/3))/2 = 1/2
    rw [rotation_trace, Real.cos_pi_div_three]
    ring
  rw [observable_tilted]
  change deriv (fun t => evolve t (1/2) (-1/2) (rotationPoint (Real.pi/3))) 0 - _ = _
  rw [(evolve_time_derivative 0 (1/2) (-1/2) _).deriv, ht]
  norm_num [quarticMode, quadraticMode]
  ring

theorem not_tilted_heat_initial (β : ℝ) (hβ : β ≠ 0) :
    deriv (fun t => observableTrajectory t (rotationPoint (Real.pi/3))) 0 ≠
      tiltedExpression ν β observable (rotationPoint (Real.pi/3)) := by
  intro h
  have hr := initial_tilt_residual ν β
  rw [h, sub_self] at hr
  apply hβ
  linarith

end OperatorDerivativeRewrite.Foundation.SU2TiltedRadialExpression
