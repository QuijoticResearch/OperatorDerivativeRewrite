import Foundation.StochasticCauchyContinuousPolynomials

/-! Correct polynomial variance--energy identity for the ACTUAL continuous
process Z=B1+iB2, with component variances t. Its factor2 is obtained from
the original native isometry and physical input, not guessed from notation. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.StochasticCauchyPolynomialEnergy
open InfiniteGaussian ProductL2Curry ComplexL2Isometry
open StochasticCauchyParameterizedObstruction StochasticCauchyJointPastIntegral
open StochasticCauchyComplexChannels StochasticCauchyPhysicalInput StochasticCauchyExponentialInput
open StochasticCauchyPolynomialInput StochasticCauchyPolynomialPrediction
open StochasticCauchyPolynomialReconstruction StochasticCauchyContinuousPolynomials
attribute [local instance] StochasticCauchyParameterizedObstruction.finiteL2Exponent
  StochasticCauchyJointPastIntegral.input_complete StochasticCauchyJointPastIntegral.swapped_complete
  StochasticCauchyComplexChannels.complexInput_complete

private theorem parts_energy (t : ℝ≥0) (p : Polynomial ℂ) :
    ‖valuePart p false t‖^2+‖valuePart p true t‖^2=‖polynomialClass t p‖^2 := by
  have hr : realPart (gaussianProduct.prod gaussianProduct) (polynomialClass t p)=valuePart p false t :=
    realPart_combine _ _ _
  have hi : imagPart (gaussianProduct.prod gaussianProduct) (polynomialClass t p)=valuePart p true t :=
    imagPart_combine _ _ _
  rw [← hr,← hi,← norm_sq_parts]

/-- Exact energy of BOTH original native components, before channel normalization. -/
theorem component_energy (T : ℝ≥0) (p : Polynomial ℂ) :
    ‖partInput T p false‖^2+‖partInput T p true‖^2=
      ∫ r,‖polynomialClass r.toNNReal p‖^2 ∂timeLaw T := by
  have hn (b : Bool) : ‖partInput T p b‖^2=
      ‖running (valuePart p b) (valuePart_continuous p b) T‖^2 := by
    rw [← partInput_sections,(timeSections T).norm_map,(fieldEmbedding T).norm_map]
  rw [hn false,hn true,BochnerL2Dominated.norm_sq_integral,BochnerL2Dominated.norm_sq_integral]
  rw [← integral_add
    ((Lp.memLp (running (valuePart p false) (valuePart_continuous p false) T)).norm.integrable_sq)
    ((Lp.memLp (running (valuePart p true) (valuePart_continuous p true) T)).norm.integrable_sq)]
  apply integral_congr_ae
  filter_upwards [running_ae (valuePart p false) (valuePart_continuous p false) T,
    running_ae (valuePart p true) (valuePart_continuous p true) T] with r hr hi
  rw [hr,hi,parts_energy]

theorem time_energy_integrable (T : ℝ≥0) (p : Polynomial ℂ) :
    Integrable (fun r : ℝ => ‖polynomialClass r.toNNReal p‖^2) (timeLaw T) := by
  have hi := ((Lp.memLp (running (valuePart p false) (valuePart_continuous p false) T)).norm.integrable_sq).add
    ((Lp.memLp (running (valuePart p true) (valuePart_continuous p true) T)).norm.integrable_sq)
  apply hi.congr
  filter_upwards [running_ae (valuePart p false) (valuePart_continuous p false) T,
    running_ae (valuePart p true) (valuePart_continuous p true) T] with r hr hi
  simp only [Pi.add_apply]
  rw [hr,hi,parts_energy]

attribute [local instance] StochasticCauchyParameterizedObstruction.predictableTime

/-- Normalization is fixed by the original physical native input. -/
theorem normalizedInput_energy (T : ℝ≥0) (p : Polynomial ℂ) :
    ‖StochasticCauchyPolynomialInput.normalizedInput T p‖^2=
      2*(∫ r,‖polynomialClass r.toNNReal p.derivative‖^2 ∂timeLaw T) := by
  have hs (u : Input T) : ‖Real.sqrt 2 • u‖^2=2*‖u‖^2 := by
    rw [norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  rw [input_norm_sq,(StochasticCauchyPolynomialInput.normalizedInput_parts T p).1,
    (StochasticCauchyPolynomialInput.normalizedInput_parts T p).2,hs,hs,← mul_add,component_energy]

theorem centered_energy (T : ℝ≥0) (p : Polynomial ℂ) :
    ‖StochasticCauchyMeanResidual.complexCenter (polynomialClass T p)‖^2=
      2*(∫ r,‖polynomialClass r.toNNReal p.derivative‖^2 ∂timeLaw T) := by
  rw [← polynomial_reconstruction T p,(channel T false).norm_map,normalizedInput_energy]

private theorem actual_polynomial_energy (t : ℝ≥0) (p : Polynomial ℂ) :
    ‖polynomialClass t p‖^2=
      ∫ w,‖p.eval (StochasticCauchyBrownianRealization.value t w)‖^2
        ∂gaussianProduct.prod gaussianProduct := by
  rw [BochnerL2Dominated.norm_sq_integral]
  apply integral_congr_ae
  exact (continuous_polynomial_ae t p).mono (fun w hw => congrArg (fun z : ℂ => ‖z‖^2) hw)

/-- The deterministic center in the formula is the actual expectation. -/
theorem continuous_mean (T : ℝ≥0) (p : Polynomial ℂ) :
    (∫ w,p.eval (StochasticCauchyBrownianRealization.value T w)
      ∂gaussianProduct.prod gaussianProduct)=p.eval 0 := by
  rw [← integral_congr_ae (continuous_polynomial_ae T p),polynomialClass,
    integral_congr_ae (StochasticCauchyPolynomials.polynomial_value_ae (timeDirection T) p)]
  exact StochasticCauchyGaussianStein.polynomial_mean (timeDirection T) p

theorem continuous_variance_integrable (T : ℝ≥0) (p : Polynomial ℂ) :
    Integrable (fun w => ‖p.eval (StochasticCauchyBrownianRealization.value T w)-p.eval 0‖^2)
      (gaussianProduct.prod gaussianProduct) := by
  apply ((Lp.memLp (channel T false (StochasticCauchyPolynomialInput.normalizedInput T p))).norm.integrable_sq).congr
  exact (native_reconstruction_ae T p).mono (fun w hw => congrArg (fun z : ℂ => ‖z‖^2) hw)

/-- The actual expected slope energy is integrable in physical time. -/
theorem continuous_time_energy_integrable (T : ℝ≥0) (p : Polynomial ℂ) :
    Integrable (fun r : ℝ => ∫ w,‖p.derivative.eval
      (StochasticCauchyBrownianRealization.value r.toNNReal w)‖^2
        ∂gaussianProduct.prod gaussianProduct) (timeLaw T) :=
  (time_energy_integrable T p.derivative).congr
    (Eventually.of_forall (fun r => actual_polynomial_energy r.toNNReal p.derivative))

/-- Actual variance--energy identity for Z=B1+iB2. The factor2 is essential.
Both source and time integrals are genuine finite-energy quantities. -/
theorem continuous_variance_energy (T : ℝ≥0) (p : Polynomial ℂ) :
    (∫ w,‖p.eval (StochasticCauchyBrownianRealization.value T w)-p.eval 0‖^2
      ∂gaussianProduct.prod gaussianProduct) =
      2*(∫ r,(∫ w,‖p.derivative.eval
        (StochasticCauchyBrownianRealization.value r.toNNReal w)‖^2
          ∂gaussianProduct.prod gaussianProduct) ∂timeLaw T) := by
  have hk : StochasticCauchyMeanResidual.complexCenter (polynomialClass T p)
      =ᵐ[gaussianProduct.prod gaussianProduct] fun w =>
        p.eval (StochasticCauchyBrownianRealization.value T w)-p.eval 0 := by
    rw [← polynomial_reconstruction T p]
    exact native_reconstruction_ae T p
  have he : ‖StochasticCauchyMeanResidual.complexCenter (polynomialClass T p)‖^2=
      ∫ w,‖p.eval (StochasticCauchyBrownianRealization.value T w)-p.eval 0‖^2
        ∂gaussianProduct.prod gaussianProduct := by
    rw [BochnerL2Dominated.norm_sq_integral]
    apply integral_congr_ae
    exact hk.mono (fun w hw => congrArg (fun z : ℂ => ‖z‖^2) hw)
  rw [← he,centered_energy]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall (fun r => actual_polynomial_energy r.toNNReal p.derivative)

/-- One formula for both source conventions: a common complex scale c gives
noise energy2*norm(c)^2. No anisotropic or fractional transfer is inferred. -/
theorem scaled_continuous_variance_energy (T : ℝ≥0) (p : Polynomial ℂ) (c : ℂ) :
    (∫ w,‖p.eval (c*StochasticCauchyBrownianRealization.value T w)-p.eval 0‖^2
      ∂gaussianProduct.prod gaussianProduct) =
      2*‖c‖^2*(∫ r,(∫ w,‖p.derivative.eval
        (c*StochasticCauchyBrownianRealization.value r.toNNReal w)‖^2
          ∂gaussianProduct.prod gaussianProduct) ∂timeLaw T) := by
  have h := continuous_variance_energy T (p.comp (Polynomial.C c*Polynomial.X))
  simp only [Polynomial.derivative_comp,Polynomial.derivative_mul,Polynomial.derivative_C,
    Polynomial.derivative_X,Polynomial.eval_comp,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_X,mul_zero,zero_add,mul_one,Polynomial.eval_add,Polynomial.eval_zero,
    norm_mul,mul_pow] at h
  simp only [zero_mul,zero_add,integral_const_mul] at h
  convert h using 1 <;> ring

end OperatorDerivativeRewrite.Foundation.StochasticCauchyPolynomialEnergy
