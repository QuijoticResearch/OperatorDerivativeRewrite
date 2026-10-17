import Foundation.GaussianTiltL2Domain

/-! Half-density multiplication transports the actual L2 domains with matching square energies. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace OperatorDerivativeRewrite.Foundation.GaussianTiltHalfDensity
open InfiniteGaussian GaussianCriticalExponential GaussianTiltL2Domain GaussianLinearTiltLaw
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
local instance : IsProbabilityMeasure Qlinear := Qlinear_probability

def transport (f : SampleSpace → ℝ) (ω : SampleSpace) : ℝ := rootDensity ω * f ω

def inverse (f : SampleSpace → ℝ) (ω : SampleSpace) : ℝ := f ω / rootDensity ω

theorem rootDensity_positive (ω : SampleSpace) : 0 < rootDensity ω :=
  Real.sqrt_pos.mpr (linearDensity_positive ω)

theorem transport_measurable {f : SampleSpace → ℝ} (hf : Measurable f) :
    Measurable (transport f) := rootDensity_measurable.mul hf

theorem inverse_measurable {f : SampleSpace → ℝ} (hf : Measurable f) :
    Measurable (inverse f) := hf.div rootDensity_measurable

theorem transport_square (f : SampleSpace → ℝ) (ω : SampleSpace) :
    transport f ω ^ 2 = linearDensity ω * f ω ^ 2 := by
  rw [transport, mul_pow, rootDensity_sq]

theorem square_lintegral {f : SampleSpace → ℝ} (hf : Measurable f) :
    (∫⁻ ω, ENNReal.ofReal (transport f ω ^ 2) ∂gaussianProduct) =
      ∫⁻ ω, ENNReal.ofReal (f ω ^ 2) ∂Qlinear := by
  rw [Qlinear, lintegral_withDensity_eq_lintegral_mul gaussianProduct
    linearDensity_measurable.ennreal_ofReal (hf.pow_const 2).ennreal_ofReal]
  change (∫⁻ ω, ENNReal.ofReal (transport f ω ^ 2) ∂gaussianProduct) =
    ∫⁻ ω, ENNReal.ofReal (linearDensity ω)*ENNReal.ofReal (f ω ^ 2) ∂gaussianProduct
  apply lintegral_congr_ae
  exact Filter.Eventually.of_forall (fun ω => by
    change ENNReal.ofReal (transport f ω ^ 2) =
      ENNReal.ofReal (linearDensity ω)*ENNReal.ofReal (f ω ^ 2)
    rw [transport_square, ENNReal.ofReal_mul (linearDensity_positive ω).le])

theorem transport_memLp_iff {f : SampleSpace → ℝ} (hf : Measurable f) :
    MemLp (transport f) 2 gaussianProduct ↔ MemLp f 2 Qlinear := by
  rw [memLp_two_iff_integrable_sq (transport_measurable hf).aestronglyMeasurable,
    memLp_two_iff_integrable_sq hf.aestronglyMeasurable,
    Qlinear, integrable_withDensity_iff linearDensity_measurable.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  have he : (fun ω => f ω ^ 2 * (ENNReal.ofReal (linearDensity ω)).toReal) =
      fun ω => transport f ω ^ 2 := by
    funext ω
    rw [transport_square, ENNReal.toReal_ofReal (linearDensity_positive ω).le]
    ring
  rw [he]

theorem transport_inverse (f : SampleSpace → ℝ) : transport (inverse f) = f := by
  funext ω
  dsimp [transport, inverse]
  field_simp [(rootDensity_positive ω).ne']

theorem inverse_transport (f : SampleSpace → ℝ) : inverse (transport f) = f := by
  funext ω
  dsimp [transport, inverse]
  field_simp [(rootDensity_positive ω).ne']

theorem inverse_memLp_iff {f : SampleSpace → ℝ} (hf : Measurable f) :
    MemLp (inverse f) 2 Qlinear ↔ MemLp f 2 gaussianProduct := by
  have h := transport_memLp_iff (inverse_measurable hf)
  rw [transport_inverse] at h
  exact h.symm

end OperatorDerivativeRewrite.Foundation.GaussianTiltHalfDensity
