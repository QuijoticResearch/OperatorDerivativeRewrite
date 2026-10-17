import Foundation.SU2BoundedObservableGradient

/-! Actual radial chain rule and sharp frame energy for the bounded trace polynomial. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Quaternion Matrix Matrix.Norms.Operator
namespace OperatorDerivativeRewrite.Foundation.SU2RadialFrameCalculus
set_option backward.isDefEq.respectTransparency false
open QuaternionSU2Representation SU2TraceHessianModel SU2TiltEnergyResponse
open SU2BoundedObservableGradient

def radial (F : ℝ → ℝ) (A : SU2) : ℝ := F (halfTrace A)

theorem radial_derivative (F : ℝ → ℝ) (d : ℝ) (A : SU2) (a : Fin 3)
    (hF : HasDerivAt F d (halfTrace A)) :
    HasDerivAt (fun t => radial F (groupCurve A a t)) (d*traceSlope (A : M2) a) 0 := by
  have hd := traceCurve_derivative (A : M2) a
  have hz : traceCurve (A : M2) a 0 = halfTrace A := by
    simp [traceCurve, halfTrace]
  rw [← hz] at hF
  exact hF.comp 0 hd

theorem traceSlope_square_sum (A : SU2) :
    (∑ a : Fin 3, (traceSlope (A : M2) a)^2) = (1-(halfTrace A)^2)/4 := by
  obtain ⟨u, rfl⟩ := hom_surjective A
  have hn : Quaternion.normSq (u : ℍ) = 1 := by
    rw [Quaternion.normSq_eq_norm_mul_self, CStarRing.norm_coe_unitary, one_mul]
  have hi : (u : ℍ).imJ^2+(u : ℍ).imK^2+(u : ℍ).imI^2 = 1-(u : ℍ).re^2 := by
    rw [Quaternion.normSq_def'] at hn
    linarith
  change (∑ a : Fin 3, (traceSlope (repr (u : ℍ)) a)^2) = _
  simp [traceSlope_repr, imagCoord, Fin.sum_univ_three, halfTrace_map,
    QuaternionAngularHaar.realCoordinate]
  nlinarith [hi]

theorem radial_energy (F : ℝ → ℝ) (d : ℝ) (A : SU2)
    (hF : HasDerivAt F d (halfTrace A)) :
    SU2BoundedObservableGradient.frameEnergy (radial F) A = d^2*(1-(halfTrace A)^2)/4 := by
  unfold SU2BoundedObservableGradient.frameEnergy
  simp_rw [(radial_derivative F d A _ hF).deriv, mul_pow]
  rw [← Finset.mul_sum, traceSlope_square_sum]
  ring

theorem polynomial_derivative (r : ℝ) :
    HasDerivAt polynomial (32*r^3-16*r) r := by
  have h := (((hasDerivAt_id' r).pow 4).const_mul 8).sub
    (((hasDerivAt_id' r).pow 2).const_mul 8) |>.add_const 1
  convert h using 1 <;> first | rfl | (dsimp; ring)

theorem energy_identity (A : SU2) :
    SU2BoundedObservableGradient.frameEnergy observable A = 4*(1-(observable A)^2) := by
  have h := radial_energy polynomial (32*(halfTrace A)^3-16*(halfTrace A)) A
    (polynomial_derivative _)
  change SU2BoundedObservableGradient.frameEnergy (radial polynomial) A = _
  rw [h]
  unfold observable ambient polynomial
  change (32*(halfTrace A)^3-16*halfTrace A)^2*(1-(halfTrace A)^2)/4 =
    4*(1-(8*(halfTrace A)^4-8*(halfTrace A)^2+1)^2)
  ring

theorem energy_bounds (A : SU2) :
    0 ≤ SU2BoundedObservableGradient.frameEnergy observable A ∧
      SU2BoundedObservableGradient.frameEnergy observable A ≤ 4 := by
  rw [energy_identity]
  have hb := (sq_le_one_iff_abs_le_one (observable A)).mpr (observable_bound A)
  constructor <;> nlinarith [sq_nonneg (observable A)]

theorem witness_energy_exact :
    SU2BoundedObservableGradient.frameEnergy observable (rotationPoint (Real.pi/8)) = 4 := by
  exact le_antisymm (energy_bounds _).2 witness_energy_lower_bound

theorem energy_measurable :
    Measurable (SU2BoundedObservableGradient.frameEnergy observable) := by
  have he : SU2BoundedObservableGradient.frameEnergy observable = fun A =>
      4*(1-polynomial (halfTrace A)^2) := funext energy_identity
  rw [he]
  have hm : Measurable (fun r : ℝ => 4*(1-polynomial r^2)) := by
    unfold polynomial
    fun_prop
  exact hm.comp halfTrace_measurable

theorem energy_integrable (μ : Measure SU2) [IsProbabilityMeasure μ] :
    Integrable (SU2BoundedObservableGradient.frameEnergy observable) μ := by
  apply Integrable.mono' (integrable_const (4 : ℝ)) energy_measurable.aestronglyMeasurable
  filter_upwards with A
  rw [Real.norm_eq_abs, abs_of_nonneg (energy_bounds A).1]
  exact (energy_bounds A).2

theorem energy_mean_le_four (μ : Measure SU2) [IsProbabilityMeasure μ] :
    (∫ A, SU2BoundedObservableGradient.frameEnergy observable A ∂μ) ≤ 4 := by
  calc
    _ ≤ ∫ _ : SU2, (4 : ℝ) ∂μ :=
      integral_mono_ae (energy_integrable μ) (integrable_const _)
        (Eventually.of_forall fun A => (energy_bounds A).2)
    _ = 4 := by simp

end OperatorDerivativeRewrite.Foundation.SU2RadialFrameCalculus
