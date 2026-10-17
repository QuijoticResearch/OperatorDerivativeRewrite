import Foundation.BurgersGaussianHessianMoments

/-! Actual base-Hessian pairing and its precise axial flux correction on the
finite slab. The prescribed repaired vorticity has unit base core. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Interval Topology
namespace OperatorDerivativeRewrite.Foundation.BurgersHessianProductIntegral
open HelicalVorticityDiagnostics HelicalRadialGaussianBridge HelicalPressureProjection
open GaussianPlaneParity BurgersGaussianPressureResponse BurgersRepairedHessian
open BurgersGaussianHessianMoments BurgersPhaseProductIntegral
set_option backward.isDefEq.respectTransparency false
local instance : IsProbabilityMeasure physicalGaussian := by unfold physicalGaussian; infer_instance

def normalized (ε ν γ : ℝ) (q : ℝ × ℝ) (θ : ℝ) : ℝ :=
  (ε^2*(Real.cos θ)^2)*Dxx ν γ q + (2*ε^2*Real.sin θ*Real.cos θ)*mixed ν γ q +
    (ε^2*(Real.sin θ)^2)*Dyy ν γ q - (16*ν^2)*(1+2*ε*phase q.1 q.2 θ)^2

theorem normalized_integrable (ε ν γ θ : ℝ) :
    Integrable (fun q => normalized ε ν γ q θ) physicalGaussian :=
  ((((pressure_domain ν γ 0).dxx_integrable.const_mul _).add
    ((mixed_integrable ν γ).const_mul _)).add
      ((pressure_domain ν γ 0).dyy_integrable.const_mul _)).sub
        ((axial_square_integrable ε θ).const_mul _)

theorem normalized_mean (ε ν γ θ : ℝ) :
    (∫ q, normalized ε ν γ q θ ∂physicalGaussian) =
      ε^2*(γ^2*Real.log (9/8 : ℝ)-20*ν^2)-16*ν^2 := by
  have h1 := (pressure_domain ν γ 0).dxx_integrable.const_mul (ε^2*(Real.cos θ)^2)
  have h2 := (mixed_integrable ν γ).const_mul (2*ε^2*Real.sin θ*Real.cos θ)
  have h3 := (pressure_domain ν γ 0).dyy_integrable.const_mul (ε^2*(Real.sin θ)^2)
  have h4 := (axial_square_integrable ε θ).const_mul (16*ν^2)
  have ho := integral_sub ((h1.add h2).add h3) h4
  have hm := integral_add (h1.add h2) h3
  simp only [Pi.add_apply] at ho hm
  unfold normalized
  rw [ho, hm, integral_add h1 h2,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
    dxx_mean, dyy_mean, mixed_mean_zero, axial_square_mean]
  calc
    _ = (4*ε^2*(γ^2*Real.log (9/8 : ℝ)/4-ν^2))*
        ((Real.sin θ)^2+(Real.cos θ)^2)-16*ν^2*(1+ε^2) := by ring
    _ = _ := by rw [Real.sin_sq_add_cos_sq]; ring

theorem pairing_weighted (ε ν γ : ℝ) (q : ℝ × ℝ) (θ : ℝ) :
    pairing ε ν γ q θ = (profile q.1 q.2)^2*normalized ε ν γ q θ := pairing_expansion ε ν γ q θ

theorem pairing_integrable (ε ν γ θ : ℝ) :
    Integrable (fun q => pairing ε ν γ q θ) (volume.prod volume) := by
  simp_rw [pairing_weighted]
  exact weighted_integrable (normalized_integrable ε ν γ θ)

def crossSection (ε ν γ θ : ℝ) : ℝ := ∫ q, pairing ε ν γ q θ ∂volume.prod volume

theorem crossSection_exact (ε ν γ θ : ℝ) : crossSection ε ν γ θ =
    (Real.pi/2)*(ε^2*(γ^2*Real.log (9/8 : ℝ)-20*ν^2)-16*ν^2) := by
  rw [crossSection]
  simp_rw [pairing_weighted]
  rw [weighted_integral _ (normalized_integrable ε ν γ θ), normalized_mean]

def spatial (ν γ : ℝ) (i : Fin 9) (q : ℝ × ℝ) : ℝ :=
  ![(profile q.1 q.2)^2*Dxx ν γ q, (profile q.1 q.2)^2*Dyy ν γ q,
    (profile q.1 q.2)^2*mixed ν γ q, (profile q.1 q.2)^2*1,
    (profile q.1 q.2)^2*q.1, (profile q.1 q.2)^2*q.2,
    (profile q.1 q.2)^2*q.1^2, (profile q.1 q.2)^2*q.2^2,
    (profile q.1 q.2)^2*(q.1*q.2)] i

def temporal (ε ν : ℝ) (i : Fin 9) (θ : ℝ) : ℝ :=
  ![ε^2*(Real.cos θ)^2, ε^2*(Real.sin θ)^2, 2*ε^2*Real.sin θ*Real.cos θ,
    -16*ν^2, -64*ε*ν^2*Real.sin θ, 64*ε*ν^2*Real.cos θ,
    -64*ε^2*ν^2*(Real.sin θ)^2, -64*ε^2*ν^2*(Real.cos θ)^2,
    128*ε^2*ν^2*Real.sin θ*Real.cos θ] i

theorem spatial_integrable (ν γ : ℝ) (i : Fin 9) :
    Integrable (spatial ν γ i) (volume.prod volume) := by
  fin_cases i
  · exact weighted_integrable (pressure_domain ν γ 0).dxx_integrable
  · exact weighted_integrable (pressure_domain ν γ 0).dyy_integrable
  · exact weighted_integrable (mixed_integrable ν γ)
  · exact weighted_integrable (integrable_const 1)
  · exact weighted_integrable (x_memLp.integrable (by norm_num))
  · exact weighted_integrable (y_memLp.integrable (by norm_num))
  · exact weighted_integrable x2_integrable
  · exact weighted_integrable y2_integrable
  · exact weighted_integrable xy_integrable

theorem temporal_integrable (ε ν a b : ℝ) (hab : a ≤ b) (i : Fin 9) :
    Integrable (temporal ε ν i) (phaseMeasure a b) := by
  have hc : Continuous (fun θ => temporal ε ν i θ) := by
    fin_cases i <;> dsimp [temporal] <;> fun_prop
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp (hc.intervalIntegrable a b)

theorem pairing_sum (ε ν γ : ℝ) (q : ℝ × ℝ) (θ : ℝ) :
    pairing ε ν γ q θ = ∑ i : Fin 9, spatial ν γ i q * temporal ε ν i θ := by
  rw [pairing_expansion]
  simp [spatial, temporal, Fin.sum_univ_succ, phase]
  ring

theorem joint_integrable (ε ν γ a b : ℝ) (hab : a ≤ b) :
    Integrable (fun z : (ℝ × ℝ) × ℝ => pairing ε ν γ z.1 z.2)
      ((volume.prod volume).prod (phaseMeasure a b)) := by
  have hs : Integrable
      (fun z : (ℝ × ℝ) × ℝ => ∑ i : Fin 9, spatial ν γ i z.1 * temporal ε ν i z.2)
      ((volume.prod volume).prod (phaseMeasure a b)) := by
    apply integrable_finsetSum
    intro i _
    exact (spatial_integrable ν γ i).mul_prod (temporal_integrable ε ν a b hab i)
  exact hs.congr (Eventually.of_forall fun z => (pairing_sum ε ν γ z.1 z.2).symm)

def total (ε ν γ : ℝ) : ℝ := ∫ z : (ℝ × ℝ) × ℝ, pairing ε ν γ z.1 z.2
  ∂(volume.prod volume).prod (phaseMeasure 0 (2*Real.pi))

theorem total_exact (ε ν γ : ℝ) : total ε ν γ =
    Real.pi^2*ε^2*(γ^2*Real.log (9/8 : ℝ)-20*ν^2)-16*Real.pi^2*ν^2 := by
  rw [total, integral_prod_symm _ (joint_integrable ε ν γ 0 (2*Real.pi) (by positivity))]
  change (∫ θ in Ioc 0 (2*Real.pi), crossSection ε ν γ θ) = _
  rw [← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 2*Real.pi by positivity)]
  simp_rw [crossSection_exact]
  rw [intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

theorem phase_first_exact (ε ν γ : ℝ) :
    (∫ q : ℝ × ℝ, (∫ θ in (0 : ℝ)..(2*Real.pi), pairing ε ν γ q θ)
      ∂volume.prod volume) =
        Real.pi^2*ε^2*(γ^2*Real.log (9/8 : ℝ)-20*ν^2)-16*Real.pi^2*ν^2 := by
  simp_rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 2*Real.pi by positivity)]
  exact (integral_prod _ (joint_integrable ε ν γ 0 (2*Real.pi) (by positivity))).symm.trans
    (total_exact ε ν γ)

theorem axial_self_advection_zero (ε x y θ : ℝ) :
    (∑ i : Fin 3, corrected ε x y θ i * correctedJacobian ε x y θ 2 i) = 0 := by
  simp [corrected, correctedJacobian_eq, Fin.sum_univ_succ, phase]
  ring

def axialFlux (ε ν γ : ℝ) (q : ℝ × ℝ) (θ : ℝ) : ℝ :=
  corrected ε q.1 q.2 θ 2 *
    dotProduct (corrected ε q.1 q.2 θ) (StrainedBurgersVortex.pressureGradient ν γ q.1 q.2 θ) -
      P ν γ θ q * ∑ i : Fin 3, corrected ε q.1 q.2 θ i * correctedJacobian ε q.1 q.2 θ 2 i

theorem axial_flux_jump (ε ν γ : ℝ) (q : ℝ × ℝ) :
    axialFlux ε ν γ q (2*Real.pi) - axialFlux ε ν γ q 0 =
      (-32*Real.pi*ν^2)*(profile q.1 q.2)^2*(1-2*ε*q.2)^2 := by
  simp only [axialFlux, axial_self_advection_zero, mul_zero, sub_zero]
  simp [corrected,
    StrainedBurgersVortex.pressureGradient_eq, dotProduct, Fin.sum_univ_succ]
  ring

theorem flux_jump_integrable (ε ν γ : ℝ) :
    Integrable (fun q => axialFlux ε ν γ q (2*Real.pi)-axialFlux ε ν γ q 0)
      (volume.prod volume) := by
  have hi := (weighted_integrable (axial_square_integrable ε 0)).const_mul (-32*Real.pi*ν^2)
  apply hi.congr
  exact Eventually.of_forall fun q => by
    change (-32*Real.pi*ν^2)*((profile q.1 q.2)^2*(1+2*ε*phase q.1 q.2 0)^2) =
      axialFlux ε ν γ q (2*Real.pi)-axialFlux ε ν γ q 0
    rw [axial_flux_jump]
    simp [phase]
    ring

theorem flux_jump_integral (ε ν γ : ℝ) :
    (∫ q, axialFlux ε ν γ q (2*Real.pi)-axialFlux ε ν γ q 0 ∂volume.prod volume) =
      -16*Real.pi^2*ν^2*(1+ε^2) := by
  have he : (fun q : ℝ × ℝ => axialFlux ε ν γ q (2*Real.pi)-axialFlux ε ν γ q 0) =
      fun q => (-32*Real.pi*ν^2)*((profile q.1 q.2)^2*(1+2*ε*phase q.1 q.2 0)^2) := by
    funext q
    rw [axial_flux_jump]
    simp [phase]
    ring
  rw [he, integral_const_mul, weighted_integral _ (axial_square_integrable ε 0), axial_square_mean]
  ring

theorem slab_boundary_identity (ε ν γ : ℝ) : total ε ν γ =
    (∫ z : (ℝ × ℝ) × ℝ, BurgersRepairedTracePairing.integrand ε ν γ z.1 z.2
      ∂(volume.prod volume).prod (phaseMeasure 0 (2*Real.pi))) +
        ∫ q, axialFlux ε ν γ q (2*Real.pi)-axialFlux ε ν γ q 0 ∂volume.prod volume := by
  rw [total_exact, period_product_exact, flux_jump_integral]
  ring

theorem no_boundary_free_identity (ε ν γ : ℝ) (hν : ν ≠ 0) : total ε ν γ ≠
    (∫ z : (ℝ × ℝ) × ℝ, BurgersRepairedTracePairing.integrand ε ν γ z.1 z.2
      ∂(volume.prod volume).prod (phaseMeasure 0 (2*Real.pi))) := by
  rw [total_exact, period_product_exact]
  have hp : 0 < 16*Real.pi^2*ν^2*(1+ε^2) := by positivity
  intro h
  nlinarith

end OperatorDerivativeRewrite.Foundation.BurgersHessianProductIntegral
