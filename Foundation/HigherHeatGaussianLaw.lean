import Foundation.HigherHeatSignedRepresentation
import Mathlib.Probability.Distributions.Gaussian.Real

/-! The order-two signed heat law is the actual Gaussian probability law with variance twice time. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.HigherHeatGaussianLaw
open HigherHeatSignedLaws HigherHeatCylinderFourier SignedFourierUniqueness

def frequency (L : StrongDual ℝ ℝ) : ℝ := -(L 1)/(2*Real.pi)

theorem dual_apply (L : StrongDual ℝ ℝ) (x : ℝ) : L x=x*L 1 := by
  simpa using L.map_smul x (1 : ℝ)

theorem character_phase (L : StrongDual ℝ ℝ) (x : ℝ) : character L x=phase (frequency L) x := by
  rw [character,dual_apply]
  simp only [phase,Real.fourierChar_apply,frequency]
  congr 1
  push_cast
  field_simp <;> ring

theorem law_character (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (L : StrongDual ℝ ℝ) :
    signedCharFun (HigherHeatSignedLaws.law m hm T hT) L=HigherHeatL2.symbol m T (frequency L) := by
  unfold signedCharFun HigherHeatSignedLaws.law
  rw [SignedDensityIntegral.integral_density volume _ (realKernel m hm T hT).integrable
    (realKernel m hm T hT).continuous.measurable (character L) (character_measurable L)
    1 (fun x => (character_norm L x).le)]
  convert kernel_fourier m hm T hT (frequency L) using 1
  congr 1
  funext x
  rw [character_phase,Complex.real_smul]
  ring

theorem gaussian_signed_character (v : ℝ≥0) (L : StrongDual ℝ ℝ) :
    signedCharFun (gaussianReal 0 v).toSignedMeasure L=charFun (gaussianReal 0 v) (L 1) := by
  unfold signedCharFun
  rw [VectorMeasure.integral_toSignedMeasure,charFun_apply_real]
  apply integral_congr_ae
  filter_upwards with x
  unfold character
  rw [dual_apply L x,Complex.ofReal_mul]
  congr 1
  ring

theorem symbol_gaussian (T : ℝ≥0) (L : StrongDual ℝ ℝ) :
    HigherHeatL2.symbol 1 T (frequency L)=charFun (gaussianReal 0 (2*T)) (L 1) := by
  rw [HigherHeatL2.symbol,charFun_gaussianReal,Complex.ofReal_exp]
  simp only [Complex.ofReal_zero,mul_zero,zero_mul,zero_sub]
  unfold frequency
  push_cast
  congr 1
  field_simp <;> ring

theorem gaussian_law (T : ℝ≥0) (hT : 0 < T) :
    HigherHeatSignedLaws.law 1 (by norm_num) T hT=(gaussianReal 0 (2*T)).toSignedMeasure := by
  apply signed_ext
  funext L
  rw [law_character,gaussian_signed_character,symbol_gaussian]

end OperatorDerivativeRewrite.Foundation.HigherHeatGaussianLaw
