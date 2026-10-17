import Foundation.BurgersRepairedHessian

/-! Actual Gaussian coordinate moments and mean transverse Hessian entries. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
namespace OperatorDerivativeRewrite.Foundation.BurgersGaussianHessianMoments
open HelicalRadialGaussianBridge HelicalPressureProjection HelicalWeightedPressureIBP
open GaussianPlaneParity BurgersGaussianPressureResponse BurgersRepairedHessian
set_option backward.isDefEq.respectTransparency false
local instance : IsProbabilityMeasure physicalGaussian := by unfold physicalGaussian; infer_instance

theorem x_memLp : MemLp (fun q : ℝ × ℝ => q.1) 2 physicalGaussian := by
  simpa using HelicalPolynomialPressureIBP.polynomial_memLp (MvPolynomial.X (0 : Fin 2)) 2
    (by simp)
theorem y_memLp : MemLp (fun q : ℝ × ℝ => q.2) 2 physicalGaussian := by
  simpa using HelicalPolynomialPressureIBP.polynomial_memLp (MvPolynomial.X (1 : Fin 2)) 2
    (by simp)
theorem x2_integrable : Integrable (fun q : ℝ × ℝ => q.1^2) physicalGaussian := by
  apply (x_memLp.integrable_mul x_memLp).congr
  exact Eventually.of_forall fun q => by change q.1*q.1=q.1^2; ring
theorem y2_integrable : Integrable (fun q : ℝ × ℝ => q.2^2) physicalGaussian := by
  apply (y_memLp.integrable_mul y_memLp).congr
  exact Eventually.of_forall fun q => by change q.2*q.2=q.2^2; ring
theorem xy_integrable : Integrable (fun q : ℝ × ℝ => q.1*q.2) physicalGaussian :=
  x_memLp.integrable_mul y_memLp

theorem x_mean_zero : (∫ q : ℝ × ℝ, q.1 ∂physicalGaussian) = 0 :=
  odd_integral_zero _ (fun _ => rfl)
theorem y_mean_zero : (∫ q : ℝ × ℝ, q.2 ∂physicalGaussian) = 0 :=
  odd_integral_zero _ (fun _ => rfl)

theorem x2_mean : (∫ q : ℝ × ℝ, q.1^2 ∂physicalGaussian) = 1/4 := by
  have h := GaussianSwirlPressureDomain.stein_x
    (G := fun q : ℝ × ℝ => q.1) (K := fun _ => 1)
    (fun x _ => hasDerivAt_id' x) x_memLp (integrable_const 1)
  simp only [pow_two]
  norm_num at h
  linarith

theorem y2_mean : (∫ q : ℝ × ℝ, q.2^2 ∂physicalGaussian) = 1/4 := by
  have h := GaussianSwirlPressureDomain.stein_y
    (G := fun q : ℝ × ℝ => q.2) (K := fun _ => 1)
    (fun _ y => hasDerivAt_id' y) y_memLp (integrable_const 1)
  simp only [pow_two]
  norm_num at h
  linarith

theorem xy_mean_zero : (∫ q : ℝ × ℝ, q.1*q.2 ∂physicalGaussian) = 0 := by
  have h := GaussianSwirlPressureDomain.stein_x
    (G := fun q : ℝ × ℝ => q.2) (K := fun _ => 0)
    (fun x y => hasDerivAt_const x y) y_memLp (integrable_const 0)
  simp only [integral_zero] at h
  linarith

theorem swap_preserving : MeasurePreserving (Prod.swap : ℝ × ℝ → ℝ × ℝ)
    physicalGaussian physicalGaussian := Measure.measurePreserving_swap

theorem flip_preserving : MeasurePreserving (Prod.map (Neg.neg : ℝ → ℝ) id)
    physicalGaussian physicalGaussian := by
  have h : MeasurePreserving (Neg.neg : ℝ → ℝ) (gaussianReal 0 (1/4)) (gaussianReal 0 (1/4)) :=
    ⟨by fun_prop, by simpa only [neg_zero] using gaussianReal_map_neg (μ := 0) (v := (1/4))⟩
  exact h.prod (MeasurePreserving.id _)

theorem dxx_swap (ν γ : ℝ) (q : ℝ × ℝ) : Dxx ν γ q.swap = Dyy ν γ q := by
  simp [Dxx, Dyy, GaussianSwirlPressureDomain.Dxx, GaussianSwirlPressureDomain.Dyy,
    GaussianSwirlPressureDomain.radiusSq, add_comm]

theorem dxx_mean (ν γ : ℝ) : (∫ q, Dxx ν γ q ∂physicalGaussian) =
    4*(γ^2*Real.log (9/8 : ℝ)/4-ν^2) := by
  have he := swap_preserving.integral_comp MeasurableEquiv.prodComm.measurableEmbedding (Dxx ν γ)
  simp only [dxx_swap] at he
  have hr := pressure_response (pressure_domain ν γ 0)
  rw [integral_add (pressure_domain ν γ 0).dxx_integrable
    (pressure_domain ν γ 0).dyy_integrable] at hr
  change physicalResponse (pressureClass ν γ 0) =
    (1/8 : ℝ)*((∫ q, Dxx ν γ q ∂physicalGaussian)+(∫ q, Dyy ν γ q ∂physicalGaussian)) at hr
  rw [response_exact, he] at hr
  linarith

theorem dyy_mean (ν γ : ℝ) : (∫ q, Dyy ν γ q ∂physicalGaussian) =
    4*(γ^2*Real.log (9/8 : ℝ)/4-ν^2) := by
  have he := swap_preserving.integral_comp MeasurableEquiv.prodComm.measurableEmbedding (Dxx ν γ)
  simp only [dxx_swap] at he
  exact he.trans (dxx_mean ν γ)

theorem mixed_mean_zero (ν γ : ℝ) : (∫ q, mixed ν γ q ∂physicalGaussian) = 0 := by
  have he (q : ℝ × ℝ) : mixed ν γ (Prod.map Neg.neg id q) = -mixed ν γ q := by
    dsimp [mixed, GaussianSwirlPressureDomain.radiusSq]
    simp only [neg_sq]
    ring
  have h := flip_preserving.integral_comp
    ((Homeomorph.neg ℝ).measurableEmbedding.prodMap MeasurableEmbedding.id) (mixed ν γ)
  simp only [he, integral_neg] at h
  linarith

theorem phase_memLp (θ : ℝ) : MemLp (fun q : ℝ × ℝ => phase q.1 q.2 θ) 2 physicalGaussian := by
  convert (x_memLp.mul_const (Real.sin θ)).sub (y_memLp.mul_const (Real.cos θ)) using 1
  funext q
  dsimp [phase]

theorem phase_mean_zero (θ : ℝ) : (∫ q, phase q.1 q.2 θ ∂physicalGaussian) = 0 := by
  simpa only [one_mul] using even_phase_zero (fun _ => 1) (fun _ => rfl) θ

theorem phase_square_integrable (θ : ℝ) :
    Integrable (fun q => (phase q.1 q.2 θ)^2) physicalGaussian := by
  apply ((phase_memLp θ).integrable_mul (phase_memLp θ)).congr
  exact Eventually.of_forall fun q => by
    change phase q.1 q.2 θ * phase q.1 q.2 θ = (phase q.1 q.2 θ)^2
    ring

theorem phase_square_mean (θ : ℝ) :
    (∫ q, (phase q.1 q.2 θ)^2 ∂physicalGaussian) = 1/4 := by
  have he : (fun q : ℝ × ℝ => (phase q.1 q.2 θ)^2) = fun q =>
      (Real.sin θ)^2*q.1^2+(Real.cos θ)^2*q.2^2-(2*Real.sin θ*Real.cos θ)*(q.1*q.2) := by
    funext q
    dsimp [phase]
    ring
  have hs := integral_sub ((x2_integrable.const_mul ((Real.sin θ)^2)).add
    (y2_integrable.const_mul ((Real.cos θ)^2)))
      (xy_integrable.const_mul (2*Real.sin θ*Real.cos θ))
  simp only [Pi.add_apply] at hs
  rw [he, hs, integral_add (x2_integrable.const_mul _) (y2_integrable.const_mul _),
    integral_const_mul, integral_const_mul, integral_const_mul, x2_mean, y2_mean, xy_mean_zero]
  nlinarith [Real.sin_sq_add_cos_sq θ]

theorem axial_square_integrable (ε θ : ℝ) :
    Integrable (fun q => (1+2*ε*phase q.1 q.2 θ)^2) physicalGaussian := by
  have hc : MemLp (fun _ : ℝ × ℝ => (1 : ℝ)) 2 physicalGaussian := memLp_const 1
  have h := hc.add ((phase_memLp θ).const_mul (2*ε))
  have hg : Integrable (fun q : ℝ × ℝ => (1+2*ε*phase q.1 q.2 θ)*(1+2*ε*phase q.1 q.2 θ))
      physicalGaussian := by
    convert h.integrable_mul h using 1
  apply hg.congr
  exact Eventually.of_forall fun q => by ring

theorem axial_square_mean (ε θ : ℝ) :
    (∫ q, (1+2*ε*phase q.1 q.2 θ)^2 ∂physicalGaussian) = 1+ε^2 := by
  have hp := (phase_memLp θ).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have he : (fun q : ℝ × ℝ => (1+2*ε*phase q.1 q.2 θ)^2) =
      fun q => 1+(4*ε)*phase q.1 q.2 θ+(4*ε^2)*(phase q.1 q.2 θ)^2 := by
    funext q
    ring
  have hi : Integrable (fun _ : ℝ × ℝ => (1 : ℝ)) physicalGaussian := integrable_const 1
  have houter := integral_add (hi.add (hp.const_mul (4*ε)))
    ((phase_square_integrable θ).const_mul (4*ε^2))
  simp only [Pi.add_apply] at houter
  rw [he, houter, integral_add hi (hp.const_mul _),
    integral_const_mul, integral_const_mul, phase_mean_zero, phase_square_mean]
  norm_num <;> ring

end OperatorDerivativeRewrite.Foundation.BurgersGaussianHessianMoments
