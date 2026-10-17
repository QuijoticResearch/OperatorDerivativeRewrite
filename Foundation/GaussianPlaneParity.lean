import Foundation.PressureDomainLinearCalculus

/-! Gaussian parity and density transport for genuine transverse pressure pairings. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
namespace OperatorDerivativeRewrite.Foundation.GaussianPlaneParity
open HelicalRadialGaussianBridge HelicalWeightedPressureIBP HelicalVorticityDiagnostics
set_option backward.isDefEq.respectTransparency false

theorem physicalGaussian_neg : MeasurePreserving (Neg.neg : ℝ × ℝ → ℝ × ℝ)
    physicalGaussian physicalGaussian := by
  have h : MeasurePreserving (Neg.neg : ℝ → ℝ) (gaussianReal 0 (1/4)) (gaussianReal 0 (1/4)) :=
    ⟨by fun_prop, by simpa only [neg_zero] using gaussianReal_map_neg (μ := 0) (v := (1/4))⟩
  exact h.prod h

theorem odd_integral_zero (f : ℝ × ℝ → ℝ) (ho : ∀ q, f (-q) = -f q) :
    (∫ q, f q ∂physicalGaussian) = 0 := by
  have h := physicalGaussian_neg.integral_comp (Homeomorph.neg (ℝ × ℝ)).measurableEmbedding f
  simp only [ho, integral_neg] at h
  linarith

theorem weighted_integrable {f : ℝ × ℝ → ℝ} (hf : Integrable f physicalGaussian) :
    Integrable (fun q => (profile q.1 q.2)^2*f q) (volume.prod volume) := by
  rw [physicalGaussian_density] at hf
  have hw := (integrable_withDensity_iff_integrable_smul'
    (by unfold profile; fun_prop) (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).mp hf
  have hn (q : ℝ × ℝ) : 0 ≤ (2/Real.pi)*(profile q.1 q.2)^2 := by positivity
  simp only [ENNReal.toReal_ofReal (hn _), smul_eq_mul] at hw
  apply (hw.const_mul (Real.pi/2)).congr
  exact Eventually.of_forall fun q => by field_simp [Real.pi_ne_zero] <;> ring

theorem weighted_integral (f : ℝ × ℝ → ℝ) (_hf : Integrable f physicalGaussian) :
    (∫ q, (profile q.1 q.2)^2*f q ∂volume.prod volume) =
      (Real.pi/2)*(∫ q, f q ∂physicalGaussian) := by
  have hn (q : ℝ × ℝ) : 0 ≤ (2/Real.pi)*(profile q.1 q.2)^2 := by positivity
  have hi : (∫ q, f q ∂physicalGaussian) =
      (2/Real.pi)*(∫ q, (profile q.1 q.2)^2*f q ∂volume.prod volume) := by
    rw [physicalGaussian_density, integral_withDensity_eq_integral_toReal_smul
      (by unfold profile; fun_prop) (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    simp only [ENNReal.toReal_ofReal (hn _), smul_eq_mul, mul_assoc]
    rw [integral_const_mul]
  rw [hi]
  field_simp [Real.pi_ne_zero]

theorem phase_integrable {F : ℝ × ℝ → ℝ} (hF : MemLp F 2 physicalGaussian) (θ : ℝ) :
    Integrable (fun q => F q * phase q.1 q.2 θ) physicalGaussian := by
  have hx := (x_weights_integrable hF).1
  have hy := (y_weights_integrable hF).1
  apply ((hx.mul_const (Real.sin θ)).sub (hy.mul_const (Real.cos θ))).congr
  exact Eventually.of_forall fun q => by dsimp [phase]; ring

theorem even_phase_zero (F : ℝ × ℝ → ℝ) (he : ∀ q, F (-q) = F q) (θ : ℝ) :
    (∫ q, F q * phase q.1 q.2 θ ∂physicalGaussian) = 0 := by
  apply odd_integral_zero
  intro q
  rw [he]
  dsimp [phase]
  ring

theorem weighted_linearTrace_integrable {F : ℝ × ℝ → ℝ}
    (hF : MemLp F 2 physicalGaussian) (θ : ℝ) :
    Integrable (fun q => F q * linearTrace q.1 q.2 θ) (volume.prod volume) := by
  apply ((weighted_integrable (phase_integrable hF θ)).const_mul 4).congr
  exact Eventually.of_forall fun q => by dsimp [linearTrace, phase]; ring

theorem weighted_linearTrace_zero {F : ℝ × ℝ → ℝ}
    (hF : MemLp F 2 physicalGaussian) (he : ∀ q, F (-q) = F q) (θ : ℝ) :
    (∫ q, F q * linearTrace q.1 q.2 θ ∂volume.prod volume) = 0 := by
  have hh : (fun q : ℝ × ℝ => F q * linearTrace q.1 q.2 θ) =
      fun q => 4*((profile q.1 q.2)^2*(F q*phase q.1 q.2 θ)) := by
    funext q
    dsimp [linearTrace, phase]
    ring
  rw [hh, integral_const_mul, weighted_integral _ (phase_integrable hF θ), even_phase_zero F he]
  ring

end OperatorDerivativeRewrite.Foundation.GaussianPlaneParity
