import Foundation.BandLimitedComplexExtension
import Foundation.ComplexRootNormTransform
import Foundation.MarkedExponentialTimeIntegral
import Foundation.ComplexRootMarkRepresentation

/-! The actual finite-mark jump generator on the admissible unbounded Fourier domain. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.BandLimitedJumpGenerator
open BandLimitedComplexExtension ComplexFourthRootNoise

def generatorProfile (a : ℝ) (φ : ℝ → ℂ) (ξ : ℝ) : ℂ :=
  φ ξ*MarkedHolomorphicExponential.symbol a ξ

theorem generatorProfile_integrable (R : ℝ≥0) (φ : ℝ → ℂ) (hφ : Integrable φ (band R))
    (a : ℝ) : Integrable (generatorProfile a φ) (band R) := by
  have hc : Continuous (MarkedHolomorphicExponential.symbol a) := by
    have he : MarkedHolomorphicExponential.symbol a =
        (fun ξ : ℝ => ((Real.cos (a*ξ)*Real.cosh (a*ξ)-1 : ℝ) : ℂ)) :=
      funext (ComplexRootNormTransform.symbol_real a)
    rw [he]
    fun_prop
  obtain ⟨C,hC⟩ := (isCompact_Icc : IsCompact (Icc (-(R : ℝ)) (R : ℝ))).exists_bound_of_continuousOn
    hc.continuousOn
  apply hφ.mul_bdd (c := C) hc.aestronglyMeasurable
  filter_upwards [frequency_bound R] with ξ hξ
  exact hC ξ (abs_le.mp hξ)

def jumpGenerator (a : ℝ) (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  (∫ k, F (z+noise a k) ∂ComplexFourthRootNoise.probability)-F z

theorem mark_frequency_integrable (R : ℝ≥0) (φ : ℝ → ℂ) (hφ : Integrable φ (band R))
    (a : ℝ) (z : ℂ) :
    Integrable (fun p : Fin 4 × ℝ => φ p.2*Complex.exp (Complex.I*(p.2 : ℂ)*(z+noise a p.1)))
      (ComplexFourthRootNoise.probability.prod (band R)) := by
  have hN := (noise_measurable a).comp (measurable_fst : Measurable (Prod.fst : Fin 4 × ℝ → Fin 4))
  have hm : Measurable (fun p : Fin 4 × ℝ =>
      Complex.exp (Complex.I*(p.2 : ℂ)*(z+noise a p.1))) := by fun_prop
  apply (integrable_prod_iff (hφ.aestronglyMeasurable.comp_snd.mul hm.aestronglyMeasurable)).mpr
  exact ⟨Eventually.of_forall fun k => integrand_integrable R φ hφ (z+noise a k),
    Integrable.of_finite⟩

theorem generator_spectral_identity (R : ℝ≥0) (φ : ℝ → ℂ) (hφ : Integrable φ (band R))
    (a : ℝ) (z : ℂ) :
    jumpGenerator a (extension R φ) z = extension R (generatorProfile a φ) z := by
  have hi := mark_frequency_integrable R φ hφ a z
  change (∫ k, (∫ ξ, φ ξ*Complex.exp (Complex.I*(ξ : ℂ)*(z+noise a k)) ∂band R)
    ∂ComplexFourthRootNoise.probability)-(∫ ξ, φ ξ*Complex.exp (Complex.I*(ξ : ℂ)*z) ∂band R) = _
  rw [integral_integral_swap hi, ← integral_sub hi.integral_prod_right (integrand_integrable R φ hφ z)]
  apply integral_congr_ae
  filter_upwards with ξ
  have he (k : Fin 4) : φ ξ*Complex.exp (Complex.I*(ξ : ℂ)*(z+noise a k)) =
      (φ ξ*Complex.exp (Complex.I*(ξ : ℂ)*z))*Complex.exp (Complex.I*(ξ : ℂ)*noise a k) := by
    rw [mul_add, Complex.exp_add]
    ring
  simp_rw [he]
  rw [integral_const_mul]
  change (φ ξ*Complex.exp (Complex.I*(ξ : ℂ)*z))*ComplexFourthRootWalk.stepTransform a ξ-
    φ ξ*Complex.exp (Complex.I*(ξ : ℂ)*z) =
      generatorProfile a φ ξ*Complex.exp (Complex.I*(ξ : ℂ)*z)
  unfold generatorProfile MarkedHolomorphicExponential.symbol
  ring

theorem generator_process_integrable (R : ℝ≥0) (φ : ℝ → ℂ)
    (hφ : Integrable φ (band R)) (a : ℝ) (t : ℝ≥0) :
    Integrable (fun ω => jumpGenerator a (extension R φ)
      (MarkedRenewalMartingale.process a t ω)) MarkedRootRenewalProcess.probability := by
  have he : jumpGenerator a (extension R φ) = extension R (generatorProfile a φ) :=
    funext (generator_spectral_identity R φ hφ a)
  rw [he]
  exact process_integrable R _ (generatorProfile_integrable R φ hφ a) t a

theorem generator_drift_adapted (R : ℝ≥0) (φ : ℝ → ℂ)
    (hφ : Integrable φ (band R)) (a : ℝ) :
    StronglyAdapted (MarkedRenewalMartingale.history a)
      (MarkedExponentialTimeIntegral.primitive a (jumpGenerator a (extension R φ))) := by
  have he : jumpGenerator a (extension R φ) = extension R (generatorProfile a φ) :=
    funext (generator_spectral_identity R φ hφ a)
  rw [he]
  exact MarkedExponentialTimeIntegral.primitive_adapted a _
    (extension_continuous R _ (generatorProfile_integrable R φ hφ a))

theorem generator_drift_integrable (R : ℝ≥0) (φ : ℝ → ℂ)
    (hφ : Integrable φ (band R)) (a : ℝ) (t : ℝ≥0) :
    Integrable (MarkedExponentialTimeIntegral.primitive a (jumpGenerator a (extension R φ)) t)
      MarkedRootRenewalProcess.probability := by
  have he : jumpGenerator a (extension R φ) = extension R (generatorProfile a φ) :=
    funext (generator_spectral_identity R φ hφ a)
  rw [he]
  exact MarkedExponentialTimeIntegral.band_primitive_integrable R _
    (generatorProfile_integrable R φ hφ a) a t

theorem jump_kernel_channels (R : ℝ≥0) (φ : ℝ → ℂ) (a : ℝ) (ha : a ≠ 0)
    (z : ℂ) (k : Fin 4) :
    extension R φ (z+noise a k)-extension R φ z = jumpGenerator a (extension R φ) z+
      ComplexRootMarkRepresentation.coefficient a (fun j => extension R φ (z+noise a j)) 0*noise a k+
      ComplexRootMarkRepresentation.coefficient a (fun j => extension R φ (z+noise a j)) 1*(noise a k)^2+
      ComplexRootMarkRepresentation.coefficient a (fun j => extension R φ (z+noise a j)) 2*(noise a k)^3 := by
  have he := ComplexRootMarkRepresentation.centered_representation a ha
    (fun j => extension R φ (z+noise a j)) k
  unfold jumpGenerator
  linear_combination he

end OperatorDerivativeRewrite.Foundation.BandLimitedJumpGenerator
