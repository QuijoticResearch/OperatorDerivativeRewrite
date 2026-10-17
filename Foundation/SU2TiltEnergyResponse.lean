import Foundation.QuaternionSU2Representation
import Foundation.SU2ProductCurveHessian

/-! Actual exponential-frame energy and its response under the Haar half-trace tilt.
The frame is orthonormal for the explicitly specified ambient trace metric. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Quaternion Matrix Matrix.Norms.Operator Topology
namespace OperatorDerivativeRewrite.Foundation.SU2TiltEnergyResponse
open SU2TraceHessianModel SU2MatrixExponentialBridge QuaternionSU2Representation
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

def traceMetric (X Y : M2) : ℝ := 2*traceReal (Xᴴ*Y)

theorem traceMetric_repr (q : ℍ) : traceMetric (repr q) (repr q) = 4*‖q‖^2 := by
  rw [traceMetric, ← repr_star, ← repr_mul, Quaternion.star_mul_self, repr_traceReal]
  simp only [Quaternion.re_coe, Quaternion.normSq_eq_norm_mul_self]
  ring

theorem frame_orthonormal (A : SU2) (a b : Fin 3) :
    traceMetric ((A : M2)*tangent a) ((A : M2)*tangent b) = if a=b then 1 else 0 := by
  have hu : (A : M2)ᴴ*(A : M2)=1 := Matrix.mem_unitaryGroup_iff'.mp A.property.1
  calc
    _ = 2*traceReal ((tangent a)ᴴ*(((A : M2)ᴴ*(A : M2))*tangent b)) := by
      simp only [traceMetric, Matrix.conjTranspose_mul, mul_assoc]
    _ = -2*traceReal (tangent a*tangent b) := by
      rw [hu, one_mul, tangent_skewHermitian, neg_mul]
      simp only [traceReal, Matrix.trace_neg, Complex.neg_re]
      ring
    _ = _ := trace_metric_normalization a b

def traceCurve (U : M2) (a : Fin 3) (t : ℝ) : ℝ :=
  traceReal (U*NormedSpace.exp (t • tangent a))/2
def observableCurve (U : M2) (a : Fin 3) (t : ℝ) : ℝ :=
  traceCurve U a t+(traceCurve U a t)^2
def traceSlope (U : M2) (a : Fin 3) : ℝ := traceReal (U*tangent a)/2

theorem traceCurve_derivative (U : M2) (a : Fin 3) :
    HasDerivAt (traceCurve U a) (traceSlope U a) 0 := by
  have hm := (hasDerivAt_exp_smul_const' (𝕂 := ℝ) (tangent a) 0).const_mul U
  have ht := SU2ProductCurveHessian.realTraceCLM.hasFDerivAt.comp_hasDerivAt 0 hm
  have hd := ht.div_const 2
  change HasDerivAt (fun t => traceReal (U*NormedSpace.exp (t • tangent a))/2)
    (traceReal (U*(tangent a*NormedSpace.exp (0 • tangent a)))/2) 0 at hd
  change HasDerivAt (fun t => traceReal (U*NormedSpace.exp (t • tangent a))/2) _ 0
  simpa only [zero_smul, NormedSpace.exp_zero, mul_one, traceSlope] using hd

theorem observableCurve_derivative (U : M2) (a : Fin 3) :
    HasDerivAt (observableCurve U a)
      ((1+2*(traceReal U/2))*traceSlope U a) 0 := by
  have hd := traceCurve_derivative U a
  have hf := hd.add (hd.pow 2)
  have hz : traceCurve U a 0=traceReal U/2 := by simp [traceCurve]
  rw [hz] at hf
  convert hf using 1 <;> first | rfl | (norm_num; ring)

theorem observableCurve_deriv (U : M2) (a : Fin 3) :
    deriv (observableCurve U a) 0=(1+2*(traceReal U/2))*traceSlope U a :=
  (observableCurve_derivative U a).deriv

theorem curve_mem (A : SU2) (a : Fin 3) (t : ℝ) :
    (A : M2)*NormedSpace.exp (t • tangent a) ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  have hb : algebraElement (Pi.single a (1 : ℝ))=tangent a := by
    fin_cases a <;> simp [algebraElement, Fin.sum_univ_three, Pi.single_apply]
  have he := SU2ExponentialMembership.scaled_algebraElement_exp_mem t (Pi.single a (1 : ℝ))
  rw [hb] at he
  exact (Matrix.specialUnitaryGroup (Fin 2) ℂ).mul_mem A.property he

def frameEnergy (A : SU2) : ℝ := ∑ a : Fin 3, (deriv (observableCurve (A : M2) a) 0)^2
def shape (r : ℝ) : ℝ := (1+2*r)^2*(1-r^2)/4
def imagCoord (q : ℍ) : Fin 3 → ℝ := ![q.imJ,q.imK,q.imI]

theorem traceSlope_repr (q : ℍ) (a : Fin 3) : traceSlope (repr q) a = -imagCoord q a/2 := by
  fin_cases a <;>
    norm_num [traceSlope, QuaternionSU2Representation.repr, tangent, generator, ChristoffelSkewCancellation.generatorX,
      ChristoffelSkewCancellation.generatorY, ChristoffelSkewCancellation.generatorZ,
      imagCoord, traceReal, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
      Complex.mul_re, Complex.mul_im] <;> ring

theorem frameEnergy_shape (A : SU2) : frameEnergy A=shape (halfTrace A) := by
  obtain ⟨u, rfl⟩ := hom_surjective A
  have hn : Quaternion.normSq (u : ℍ)=1 := by
    rw [Quaternion.normSq_eq_norm_mul_self, CStarRing.norm_coe_unitary, one_mul]
  have hi : (u : ℍ).imJ^2+(u : ℍ).imK^2+(u : ℍ).imI^2=1-(u : ℍ).re^2 := by
    rw [Quaternion.normSq_def'] at hn
    linarith
  simp only [frameEnergy, observableCurve_deriv, halfTrace_map]
  change (∑ a : Fin 3, ((1+2*(traceReal (repr (u : ℍ))/2))*traceSlope (repr (u : ℍ)) a)^2) = _
  simp [repr_halfTrace, traceSlope_repr, imagCoord, Fin.sum_univ_three]
  calc
    _ = (1+2*(u : ℍ).re)^2*((u : ℍ).imJ^2+(u : ℍ).imK^2+(u : ℍ).imI^2)/4 := by ring
    _ = _ := by rw [hi]; rfl

theorem shape_bounds (r : ℝ) (hr : |r| ≤ 1) : 0 ≤ shape r ∧ shape r ≤ 9/4 := by
  have hs : r^2 ≤ 1 := (sq_le_one_iff_abs_le_one r).mpr hr
  have hf : |1+2*r| ≤ 3 := by
    calc
      |1+2*r| ≤ |(1 : ℝ)|+|2*r| := abs_add_le _ _
      _ ≤ 3 := by rw [abs_mul]; norm_num; linarith
  have hf2 : (1+2*r)^2 ≤ 9 := by
    have h := pow_le_pow_left₀ (abs_nonneg (1+2*r)) hf 2
    norm_num [sq_abs] at h
    exact h
  have hp := mul_le_mul hf2 (show 1-r^2 ≤ 1 by nlinarith) (by linarith : 0 ≤ 1-r^2)
    (by norm_num : (0 : ℝ) ≤ 9)
  constructor
  · unfold shape; positivity
  · unfold shape; nlinarith

theorem frameEnergy_measurable : Measurable frameEnergy := by
  have he : frameEnergy=fun A => shape (halfTrace A) := funext frameEnergy_shape
  rw [he]
  unfold shape
  have hf : Measurable (fun r : ℝ => (1+2*r)^2*(1-r^2)/4) := by fun_prop
  exact hf.comp halfTrace_measurable

theorem frameEnergy_bound (A : SU2) : |frameEnergy A| ≤ 9/4 := by
  rw [frameEnergy_shape, abs_of_nonneg (shape_bounds _ (halfTrace_bound A)).1]
  exact (shape_bounds _ (halfTrace_bound A)).2

section Haar
variable (ν : Measure SU2) [IsProbabilityMeasure ν] [ν.IsHaarMeasure]

theorem moment_transfer (k : ℕ) : (∫ A, halfTrace A^k ∂ν) =
    ∫ x, GaussianAngularSphere.coord 0 x^k ∂GaussianAngularSphere.gaussian := by
  have h0 := weighted_halfTrace ν (fun r => r^k) (measurable_id.pow_const k) 0
  rw [BoundedExponentialTiltResponse.weighted_zero, BoundedExponentialTiltResponse.weighted_zero] at h0
  have h1 := QuaternionAngularHaar.weighted_realCoordinate QuaternionAngularHaar.law
    (fun r => r^k) (measurable_id.pow_const k) 0
  rw [BoundedExponentialTiltResponse.weighted_zero, BoundedExponentialTiltResponse.weighted_zero] at h1
  exact h0.trans (h1.trans (GaussianAngularSphere.angular_coord_power 0 k))

theorem moment_values : (∫ A, halfTrace A ∂ν)=0 ∧ (∫ A, halfTrace A^2 ∂ν)=1/4 ∧
    (∫ A, halfTrace A^3 ∂ν)=0 ∧ (∫ A, halfTrace A^4 ∂ν)=1/8 ∧ (∫ A, halfTrace A^5 ∂ν)=0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [pow_one] using (moment_transfer ν 1).trans
      (by simpa using GaussianAngularSphere.coord_odd_moment 0 0)
  · exact (moment_transfer ν 2).trans (GaussianAngularSphere.coord_second_moment 0)
  · exact (moment_transfer ν 3).trans (by simpa using GaussianAngularSphere.coord_odd_moment 0 1)
  · exact (moment_transfer ν 4).trans (GaussianAngularSphere.coord_fourth_moment 0)
  · exact (moment_transfer ν 5).trans (by simpa using GaussianAngularSphere.coord_odd_moment 0 2)

theorem power_integrable (k : ℕ) : Integrable (fun A => halfTrace A^k) ν :=
  BoundedExponentialTiltResponse.bounded_power_integrable ν halfTrace halfTrace_measurable halfTrace_bound k

theorem frameEnergy_integrable : Integrable frameEnergy ν := by
  apply Integrable.mono' (integrable_const (9/4 : ℝ)) frameEnergy_measurable.aestronglyMeasurable
  exact Eventually.of_forall frameEnergy_bound

theorem energy_mean : (∫ A, frameEnergy A ∂ν) = 5/16 := by
  obtain ⟨h1, h2, h3, h4, _⟩ := moment_values ν
  have hi := power_integrable ν
  have hi1 : Integrable halfTrace ν := by simpa only [pow_one] using hi 1
  have hs1 : Integrable (fun A => 1/4+halfTrace A) ν := (integrable_const (1/4 : ℝ)).add hi1
  have hs2 : Integrable (fun A => (1/4+halfTrace A)+(3/4)*halfTrace A^2) ν :=
    hs1.add ((hi 2).const_mul (3/4))
  have hs3 : Integrable (fun A => ((1/4+halfTrace A)+(3/4)*halfTrace A^2)-halfTrace A^3) ν :=
    hs2.sub (hi 3)
  calc
    _ = ∫ A, (((1/4+halfTrace A)+(3/4)*halfTrace A^2)-halfTrace A^3)-halfTrace A^4 ∂ν := by
      apply integral_congr_ae; filter_upwards with A; rw [frameEnergy_shape]; unfold shape; ring
    _ = _ := by
      rw [integral_sub hs3 (hi 4), integral_sub hs2 (hi 3),
        integral_add hs1 ((hi 2).const_mul (3/4)), integral_add (integrable_const _) hi1,
        integral_const_mul, h1, h2, h3, h4]
      norm_num

theorem energy_cross_mean : (∫ A, frameEnergy A*halfTrace A ∂ν) = 1/8 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := moment_values ν
  have hi := power_integrable ν
  have hi1 : Integrable halfTrace ν := by simpa only [pow_one] using hi 1
  have hs1 : Integrable (fun A => (1/4)*halfTrace A+halfTrace A^2) ν :=
    (hi1.const_mul (1/4)).add (hi 2)
  have hs2 : Integrable (fun A => ((1/4)*halfTrace A+halfTrace A^2)+(3/4)*halfTrace A^3) ν :=
    hs1.add ((hi 3).const_mul (3/4))
  have hs3 : Integrable
      (fun A => (((1/4)*halfTrace A+halfTrace A^2)+(3/4)*halfTrace A^3)-halfTrace A^4) ν :=
    hs2.sub (hi 4)
  calc
    _ = ∫ A, ((((1/4)*halfTrace A+halfTrace A^2)+(3/4)*halfTrace A^3)-halfTrace A^4)-halfTrace A^5 ∂ν := by
      apply integral_congr_ae; filter_upwards with A; rw [frameEnergy_shape]; unfold shape; ring
    _ = _ := by
      rw [integral_sub hs3 (hi 5), integral_sub hs2 (hi 4),
        integral_add hs1 ((hi 3).const_mul (3/4)), integral_add (hi1.const_mul (1/4)) (hi 2),
        integral_const_mul, integral_const_mul, h1, h2, h3, h4, h5]
      norm_num

def energy (t : ℝ) : ℝ := BoundedExponentialTiltResponse.expectation ν halfTrace frameEnergy t

theorem energy_zero : energy ν 0 = 5/16 := by
  rw [energy, BoundedExponentialTiltResponse.expectation_zero, energy_mean]

theorem energy_derivative : HasDerivAt (energy ν) (1/8) 0 := by
  have hd := BoundedExponentialTiltResponse.expectation_hasDerivAt_zero ν halfTrace frameEnergy
    halfTrace_measurable frameEnergy_measurable halfTrace_bound (9/4) (by norm_num) frameEnergy_bound
  rw [energy_cross_mean, (moment_values ν).1, mul_zero, sub_zero] at hd
  exact hd

theorem energy_increases (ε : ℝ) (hε : 0 < ε) :
    ∃ t, 0 < t ∧ t < ε ∧ energy ν 0 < energy ν t :=
  BoundedExponentialTiltResponse.positive_derivative_arbitrarily_small_increase _ _
    (energy_derivative ν) (by norm_num) ε hε

def rayleigh (t : ℝ) : ℝ := energy ν t /
  BoundedExponentialTiltResponse.variance ν halfTrace (fun A => halfTrace A+halfTrace A^2) t

theorem rayleigh_zero : rayleigh ν 0 = 1 := by
  rw [rayleigh, energy_zero, su2_variance_zero]
  norm_num

theorem rayleigh_derivative : HasDerivAt (rayleigh ν) 0 0 := by
  have hd := (energy_derivative ν).div (su2_variance_derivative ν)
    (by rw [su2_variance_zero]; norm_num)
  rw [energy_zero, su2_variance_zero] at hd
  norm_num at hd
  exact hd

end Haar

end OperatorDerivativeRewrite.Foundation.SU2TiltEnergyResponse
