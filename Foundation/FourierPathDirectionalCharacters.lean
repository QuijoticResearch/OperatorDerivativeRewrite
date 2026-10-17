import Foundation.HigherHeatFourierTranslationContinuity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! Actual Fourier characters along continuous path directions and their derivatives. -/
noncomputable section
open Filter
open scoped lp NNReal ENNReal Topology BoundedContinuousFunction
namespace OperatorDerivativeRewrite.Foundation.FourierPathDirectionalCharacters
open HigherHeatDyadicLaws HigherHeatContinuousCylinders HigherHeatFourierBanach
open HigherHeatFourierTranslations HigherHeatFourierTranslationContinuity

def wave (w t : ℝ) : ℂ := Complex.exp (Complex.I * ((t*w : ℝ) : ℂ))

def eigenvalue (w : ℝ) : ℂ := Complex.I * (w:ℂ)

theorem eigenvalue_norm (w : ℝ) : ‖eigenvalue w‖=‖w‖ := by
  simp [eigenvalue, norm_mul]

theorem wave_zero (w : ℝ) : wave w 0=1 := by simp [wave]

theorem wave_hasDerivAt (w : ℝ) : HasDerivAt (wave w) (eigenvalue w) 0 := by
  have hd := (((hasDerivAt_id (0:ℝ)).mul_const w).ofReal_comp.const_mul Complex.I).cexp
  change HasDerivAt (fun t : ℝ => Complex.exp (Complex.I * ((t*w : ℝ) : ℂ)))
    (Complex.I * (w:ℂ)) 0
  simpa only [id_eq, Complex.ofReal_mul, Function.comp_def, zero_mul, Complex.ofReal_zero, mul_zero,
    Complex.exp_zero, mul_one, one_mul] using hd

def quotient (w t : ℝ) : ℂ := t⁻¹ • (wave w t-1)

theorem quotient_bound (w t : ℝ) : ‖quotient w t‖ ≤ ‖w‖ := by
  by_cases ht : t=0
  · simp [quotient, ht]
  calc
    ‖quotient w t‖ = ‖t‖⁻¹ * ‖wave w t-1‖ := by rw [quotient, norm_smul, norm_inv]
    _ ≤ ‖t‖⁻¹ * ‖t*w‖ := mul_le_mul_of_nonneg_left
      (Real.norm_exp_I_mul_ofReal_sub_one_le (x := t*w)) (by positivity)
    _ = ‖w‖ := by rw [norm_mul, ← mul_assoc, inv_mul_cancel₀ (norm_ne_zero_iff.mpr ht), one_mul]

theorem quotient_tendsto (w : ℝ) :
    Tendsto (quotient w) (𝓝[≠] 0) (𝓝 (eigenvalue w)) := by
  change Tendsto (fun t : ℝ => t⁻¹ • (wave w t-1)) (𝓝[≠] 0) (𝓝 (eigenvalue w))
  simpa only [zero_add, wave_zero] using (wave_hasDerivAt w).tendsto_slope_zero

variable (levels : ℕ → ℕ) (ξ : (i : ℕ) → Grid (levels i))

def frequency (h : Path) (i : ℕ) : ℝ :=
  2*Real.pi * (-(∑ j, spectrumFrequency levels ξ i j * sample (spectrumLevels levels i) h j))

theorem character_along (h : Path) (i : ℕ) (t : ℝ) :
    characterTest levels ξ i (scalePath t h)=wave (frequency levels ξ h i) t := by
  change SignedDensityIntegral.configurationPhase (spectrumFrequency levels ξ i)
    (sample (spectrumLevels levels i) (scalePath t h))=_
  unfold SignedDensityIntegral.configurationPhase
  have he : (∑ j, spectrumFrequency levels ξ i j *
      sample (spectrumLevels levels i) (scalePath t h) j)=
      t*(∑ j, spectrumFrequency levels ξ i j * sample (spectrumLevels levels i) h j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    change spectrumFrequency levels ξ i j * (t*sample (spectrumLevels levels i) h j)=_
    ring
  rw [he, Real.fourierChar_apply]
  unfold wave frequency
  congr 1
  push_cast
  ring

theorem character_hasDerivAt (h : Path) (i : ℕ) :
    HasDerivAt (fun t => characterTest levels ξ i (scalePath t h))
      (eigenvalue (frequency levels ξ h i)) 0 := by
  simpa only [character_along] using wave_hasDerivAt (frequency levels ξ h i)

theorem character_quotient_bound (h : Path) (i : ℕ) (t : ℝ) :
    ‖t⁻¹ • (characterTest levels ξ i (scalePath t h)-1)‖ ≤
      ‖eigenvalue (frequency levels ξ h i)‖ := by
  rw [character_along, eigenvalue_norm]
  exact quotient_bound _ _

end OperatorDerivativeRewrite.Foundation.FourierPathDirectionalCharacters
