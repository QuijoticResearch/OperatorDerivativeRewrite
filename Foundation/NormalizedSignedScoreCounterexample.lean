import Foundation.SignedScoreSimpleZero

/-! An actual normalized signed Schwartz density with an L1 but non-L2 score. -/
noncomputable section
open MeasureTheory Polynomial Set
open scoped SchwartzMap NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.NormalizedSignedScoreCounterexample
open SchwartzPolynomialSeparation SignedSchwartzLogDerivative SignedAbsoluteIntegration

def oddPart : 𝓢(ℝ,ℝ) := polynomialKernel X GaussianSchwartzKernel.realSchwartz
def evenPart : 𝓢(ℝ,ℝ) := polynomialKernel (X^2) GaussianSchwartzKernel.realSchwartz
def raw : 𝓢(ℝ,ℝ) := oddPart+evenPart

theorem odd_apply (x : ℝ) : oddPart x=x*Real.exp (-x^2) := by
  rw [oddPart, polynomialKernel_apply]
  simp only [eval_X]
  rfl

theorem even_apply (x : ℝ) : evenPart x=x^2*Real.exp (-x^2) := by
  rw [evenPart, polynomialKernel_apply]
  simp only [eval_pow, eval_X]
  rfl

theorem raw_apply (x : ℝ) : raw x=(x+x^2)*Real.exp (-x^2) := by
  change oddPart x+evenPart x=_
  rw [odd_apply, even_apply]
  ring

theorem odd_integral : (∫ x : ℝ, oddPart x)=0 := by
  have h := integral_neg_eq_self (fun x : ℝ => oddPart x) volume
  have he : (fun x : ℝ => oddPart (-x)) = -(fun x : ℝ => oddPart x) := by
    funext x
    simp [odd_apply]
  rw [he] at h
  change (∫ x : ℝ, -oddPart x) = _ at h
  rw [integral_neg] at h
  linarith

theorem even_integral_positive : 0 < (∫ x : ℝ, evenPart x) := by
  apply (integral_pos_iff_support_of_nonneg (fun x => by rw [even_apply]; positivity)
    evenPart.integrable).mpr
  have hs : Ioo (1:ℝ) 2 ⊆ Function.support evenPart := by
    intro x hx
    change evenPart x≠0
    rw [even_apply]
    exact ne_of_gt (mul_pos (sq_pos_of_pos (lt_trans (by norm_num) hx.1)) (Real.exp_pos _))
  exact lt_of_lt_of_le (by norm_num : (0:ℝ≥0∞) < volume (Ioo (1:ℝ) 2)) (measure_mono hs)

def mass : ℝ := ∫ x : ℝ, raw x

theorem mass_positive : 0 < mass := by
  change 0 < ∫ x : ℝ, oddPart x+evenPart x
  rw [integral_add oddPart.integrable evenPart.integrable, odd_integral, zero_add]
  exact even_integral_positive

theorem raw_zero : raw 0=0 := by rw [raw_apply]; norm_num

theorem raw_derivative : deriv raw 0=1 := by
  have he : (raw : ℝ → ℝ) = (fun x : ℝ => (x+x^2)*GaussianSchwartzKernel.gaussian x) := by
    funext x
    exact raw_apply x
  have hh : HasDerivAt (fun x : ℝ => (x+x^2)*GaussianSchwartzKernel.gaussian x) 1 0 := by
    convert ((hasDerivAt_id (0:ℝ)).add ((hasDerivAt_id (0:ℝ)).pow 2)).mul
      (GaussianSchwartzKernel.gaussian_hasDerivAt 0) using 1 <;>
      norm_num [GaussianSchwartzKernel.gaussian]
    rfl
  rw [he]
  exact hh.deriv

def normalized : 𝓢(ℝ,ℝ) := mass⁻¹ • raw

theorem normalized_mass : (∫ x : ℝ, normalized x)=1 := by
  change (∫ x : ℝ, mass⁻¹*raw x)=1
  rw [integral_const_mul]
  exact inv_mul_cancel₀ (ne_of_gt mass_positive)

theorem normalized_zero : normalized 0=0 := by
  change mass⁻¹*raw 0=0
  rw [raw_zero, mul_zero]

theorem normalized_derivative : deriv normalized 0=mass⁻¹ := by
  have he : (normalized : ℝ → ℝ) = (fun x : ℝ => mass⁻¹*raw x) := rfl
  rw [he]
  simpa only [raw_derivative, mul_one] using ((raw.hasDerivAt 0).const_mul mass⁻¹).deriv

theorem normalized_negative : normalized (-(1:ℝ)/2) < 0 := by
  change mass⁻¹*raw (-(1:ℝ)/2) < 0
  apply mul_neg_of_pos_of_neg (inv_pos.mpr mass_positive)
  rw [raw_apply]
  apply mul_neg_of_neg_of_pos
  · norm_num
  · exact Real.exp_pos _

def law : SignedMeasure ℝ := volume.withDensityᵥ (normalized : ℝ → ℝ)

theorem law_mass : law Set.univ=1 := by
  rw [law, withDensityᵥ_apply normalized.integrable MeasurableSet.univ, Measure.restrict_univ]
  exact normalized_mass

theorem counterexample :
    ∃ K : 𝓢(ℝ,ℝ), (∫ x : ℝ, K x)=1 ∧ K (-(1:ℝ)/2)<0 ∧
      Integrable (fun x : ℝ => (score K x:ℂ)) (absoluteDensity volume K) ∧
      ¬ MemLp (fun x : ℝ => (score K x:ℂ)) 2 (absoluteDensity volume K) := by
  refine ⟨normalized, normalized_mass, normalized_negative, score_absolute_integrable _, ?_⟩
  apply SignedScoreSimpleZero.score_not_memLp_two _ normalized_zero
  rw [normalized_derivative]
  exact inv_ne_zero (ne_of_gt mass_positive)

end OperatorDerivativeRewrite.Foundation.NormalizedSignedScoreCounterexample
