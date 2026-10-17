import Foundation.HigherHeatUniformQuarticVariation
import Foundation.HigherHeatProbabilitySampling

/-! Signed quartic cancellation coexists with divergent actual total-variation square error. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.HigherHeatAbsoluteVariationObstruction
open HigherHeatSignedLaws HigherHeatPowerVariation HigherHeatQuarticVariation
open HigherHeatUniformQuarticVariation HigherHeatPositionVariation

def absoluteError (T : ℝ≥0) (hT : 0 < T) (n : ℕ) : ℝ :=
  ∫ x, ‖powerSum 4 x + 24*((T : ℝ) : ℂ)‖^2 ∂(law T hT n).variation

theorem error_integrable (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    Integrable (fun x => ‖powerSum 4 x + 24*((T : ℝ) : ℂ)‖^2) (law T hT n).variation := by
  let ν := law T hT n
  letI : IsFiniteMeasure ν.variation := by
    rw [← SignedMeasure.totalVariation_eq_variation]
    infer_instance
  have hQ : Integrable (fun x : Fin (n+1) → ℝ => ‖powerSum 4 x‖^2) ν.variation := by
    have hh := (square_sum_integrable (fun _ : Fin (n+1) => duration T n)
      (fun _ => duration_pos T hT n) 4).norm
    have he : (fun x : Fin (n+1) → ℝ => ‖(powerSum 4 x)^2‖) =
        (fun x => ‖powerSum 4 x‖^2) := by
      funext x
      rw [norm_pow]
    rw [he] at hh
    simpa only [ν, HigherHeatUniformQuarticVariation.law] using hh
  have hm : AEStronglyMeasurable (fun x : Fin (n+1) → ℝ =>
      ‖powerSum 4 x + 24*((T : ℝ) : ℂ)‖^2) ν.variation := by
    apply Continuous.aestronglyMeasurable
    unfold powerSum
    fun_prop
  apply ((hQ.const_mul 2).add
    (integrable_const (2*‖24*((T : ℝ) : ℂ)‖^2))).mono' hm
  exact Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    change ‖powerSum 4 x + 24*((T : ℝ) : ℂ)‖^2 ≤
      2*‖powerSum 4 x‖^2 + 2*‖24*((T : ℝ) : ℂ)‖^2
    have hn := norm_add_le (powerSum 4 x) (24*((T : ℝ) : ℂ))
    have h₁ := norm_nonneg (powerSum 4 x)
    have h₂ := norm_nonneg (24*((T : ℝ) : ℂ))
    have h₃ := norm_nonneg (powerSum 4 x + 24*((T : ℝ) : ℂ))
    nlinarith [sq_nonneg (‖powerSum 4 x‖ - ‖24*((T : ℝ) : ℂ)‖)])

theorem centered_norm_lower (T : ℝ≥0) {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    24*(T : ℝ) ≤ ‖powerSum 4 x + 24*((T : ℝ) : ℂ)‖ := by
  have hs : 0 ≤ ∑ i, (x i)^4 := Finset.sum_nonneg (fun _ _ => by positivity)
  have he : powerSum 4 x + 24*((T : ℝ) : ℂ) =
      (((∑ i, (x i)^4) + 24*(T : ℝ) : ℝ) : ℂ) := by
    simp only [powerSum, Complex.ofReal_add, Complex.ofReal_sum, Complex.ofReal_pow,
      Complex.ofReal_mul, Complex.ofReal_ofNat]
  rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  linarith

theorem variation_mass (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    ((law T hT n).variation Set.univ).toReal =
      (∫ x : ℝ, ‖realKernel 2 (by norm_num) T hT x‖)^(n+1) := by
  unfold HigherHeatUniformQuarticVariation.law
  rw [incrementLaw_variation_mass]
  simp_rw [norm_integral_time_independent 2 (by norm_num) (duration T n) T
    (duration_pos T hT n) hT]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem absoluteError_lower (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    576*(T : ℝ)^2 * (∫ x : ℝ, ‖realKernel 2 (by norm_num) T hT x‖)^(n+1) ≤
      absoluteError T hT n := by
  letI : IsFiniteMeasure (law T hT n).variation := by
    rw [← SignedMeasure.totalVariation_eq_variation]
    infer_instance
  calc
    _ = ∫ _ : Fin (n+1) → ℝ, (576*(T : ℝ)^2) ∂(law T hT n).variation := by
      rw [integral_const, smul_eq_mul]
      change _ = ((law T hT n).variation Set.univ).toReal * (576*(T : ℝ)^2)
      rw [variation_mass]
      ring
    _ ≤ _ := integral_mono_ae (integrable_const _) (error_integrable T hT n)
      (Eventually.of_forall (fun x => by
        have hh := centered_norm_lower T x
        have hp := T.property
        nlinarith [norm_nonneg (powerSum 4 x + 24*((T : ℝ) : ℂ))]))

theorem absoluteError_tendsto (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (absoluteError T hT) atTop atTop := by
  have hC : 1 < ∫ x : ℝ, ‖realKernel 2 (by norm_num) T hT x‖ :=
    HigherHeatKernelMoments.norm_integral_gt_one 2 (by norm_num) T hT
  have hp := (tendsto_pow_atTop_atTop_of_one_lt hC).comp (tendsto_add_atTop_nat 1)
  have hl := hp.const_mul_atTop (by positivity : 0 < 576*(T : ℝ)^2)
  exact tendsto_atTop_mono (fun n => absoluteError_lower T hT n) hl

end OperatorDerivativeRewrite.Foundation.HigherHeatAbsoluteVariationObstruction
