import Foundation.HigherHeatSchwartzSquare

/-! Actual Schwartz heat expectation has a continuous-spectrum L1 Fourier bound. -/
noncomputable section
open MeasureTheory Filter FourierTransform
open scoped Topology NNReal SchwartzMap
namespace OperatorDerivativeRewrite.Foundation.HigherHeatSchwartzSpectrum
open GaussianSchwartzKernel HigherHeatCylindricalOperator HigherHeatCylindricalExpectation

def spectral (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (f : 𝓢(ℝ,ℝ)) : 𝓢(ℝ,ℂ) :=
  SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) (evenSymbol m hm T hT) (𝓕 (complexify f))

theorem evolved_inverse (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (f : 𝓢(ℝ,ℝ)) :
    evolved m hm T hT f=𝓕⁻ (spectral m hm T hT f) := by
  apply (fourierEquiv ℂ 𝓢(ℝ,ℂ)).injective
  change 𝓕 (evolved m hm T hT f)=𝓕 (𝓕⁻ (spectral m hm T hT f))
  rw [fourier_fourierInv_eq]
  change 𝓕 (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ)
    (evenKernel m hm T hT) (complexify f))=_
  rw [SchwartzMap.fourier_convolution,evenKernel_fourier]
  rfl

theorem spectral_l1_bound (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (f : 𝓢(ℝ,ℝ)) (x : ℝ) :
    |cylindricalExpectation m hm T hT (observationCylinder f x)| ≤
      ∫ ξ : ℝ, ‖𝓕 (complexify f) ξ‖ := by
  have he := expectation_evolved m hm T hT f x
  have hn := congrArg norm he
  rw [Complex.norm_real,Real.norm_eq_abs] at hn
  rw [hn,evolved_inverse,SchwartzMap.fourierInv_coe,Real.fourierInv_eq]
  apply (norm_integral_le_integral_norm _).trans
  simp only [Circle.norm_smul]
  apply integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
    (𝓕 (complexify f)).integrable.norm
  apply Eventually.of_forall
  intro ξ
  change ‖evenSymbol m hm T hT ξ * 𝓕 (complexify f) ξ‖ ≤ _
  rw [norm_mul,evenSymbol_apply]
  exact mul_le_of_le_one_left (norm_nonneg _) (HigherHeatL2.symbol_norm_le m T ξ)

end OperatorDerivativeRewrite.Foundation.HigherHeatSchwartzSpectrum
