import Foundation.DifferentiableZeroSet
import Foundation.SignedAbsoluteIntegration
import Foundation.SignedSchwartzFirstOrder

/-! A genuine measurable L1 logarithmic-derivative weight for real Schwartz signed densities. -/
noncomputable section
open MeasureTheory Filter Polynomial
open scoped SchwartzMap NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.SignedSchwartzLogDerivative
open SignedAbsoluteIntegration

def score (K : 𝓢(ℝ,ℝ)) (x : ℝ) : ℝ := -(deriv K x) / K x

theorem score_measurable (K : 𝓢(ℝ,ℝ)) : Measurable (score K) := by
  have hd : Continuous (fun x : ℝ => deriv K x) := by
    have he : (fun x : ℝ => deriv K x) = (SchwartzMap.derivCLM ℝ ℝ K : ℝ → ℝ) := by
      funext x
      rw [SchwartzMap.derivCLM_apply]
    rw [he]
    exact (SchwartzMap.derivCLM ℝ ℝ K).continuous
  exact hd.measurable.neg.div K.continuous.measurable

theorem score_cancel (K : 𝓢(ℝ,ℝ)) :
    (fun x : ℝ => K x * score K x) =ᵐ[volume] (fun x => -(deriv K x)) :=
  DifferentiableZeroSet.logarithmic_cancel_ae K (fun x => deriv K x)
    (fun x => K.hasDerivAt x)

theorem score_absolute_integrable (K : 𝓢(ℝ,ℝ)) :
    Integrable (fun x : ℝ => (score K x : ℂ)) (absoluteDensity volume K) := by
  apply (absolute_integrable_iff volume K K.continuous.measurable _).mpr
  have hi : Integrable (fun x : ℝ => |deriv K x|) := by
    simpa only [SchwartzMap.derivCLM_apply, Real.norm_eq_abs] using
      (SchwartzMap.derivCLM ℝ ℝ K).integrable.norm
  refine hi.mono' ?_ ?_
  · have hmabs : Measurable (fun x : ℝ => |K x|) := by
      simpa only [Real.norm_eq_abs] using K.continuous.measurable.norm
    exact (hmabs.smul
      (Complex.measurable_ofReal.comp (score_measurable K))).aestronglyMeasurable
  · filter_upwards [score_cancel K] with x hx
    simp only [norm_smul, Real.norm_eq_abs, abs_abs, Complex.norm_real]
    rw [← abs_mul, hx, abs_neg]

theorem score_l1_norm (K : 𝓢(ℝ,ℝ)) :
    (∫ x : ℝ, ‖(score K x:ℂ)‖ ∂absoluteDensity volume K) =
      (∫ x : ℝ, |deriv K x|) := by
  have hmabs : Measurable (fun x : ℝ => |K x|) := by
    simpa only [Real.norm_eq_abs] using K.continuous.measurable.norm
  rw [absoluteDensity, integral_withDensity_eq_integral_toReal_smul hmabs.ennreal_ofReal
    (Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [score_cancel K] with x hx
  rw [ENNReal.toReal_ofReal (abs_nonneg _)]
  simp only [smul_eq_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [← abs_mul, hx, abs_neg]

theorem score_test_absolute_integrable (K : 𝓢(ℝ,ℝ)) (g : 𝓢(ℝ,ℂ)) :
    Integrable (fun x : ℝ => (score K x:ℂ)*g x) (absoluteDensity volume K) := by
  exact (score_absolute_integrable K).mul_bdd g.continuous.aestronglyMeasurable
    (Eventually.of_forall (SchwartzMap.norm_le_seminorm ℝ g))

theorem test_absolute_integrable (K : 𝓢(ℝ,ℝ)) (g : 𝓢(ℝ,ℂ)) :
    Integrable (g : ℝ → ℂ) (absoluteDensity volume K) := by
  apply (absolute_integrable_iff volume K K.continuous.measurable _).mpr
  have hi : Integrable (fun x : ℝ => ((‖K x‖:ℝ):ℂ)) := K.integrable.norm.ofReal
  have hp := hi.mul_bdd g.continuous.aestronglyMeasurable
    (Eventually.of_forall (SchwartzMap.norm_le_seminorm ℝ g))
  simpa only [Real.norm_eq_abs, Complex.real_smul] using hp

theorem real_stein (K g : 𝓢(ℝ,ℝ)) :
    (∫ x : ℝ, deriv g x*K x) = (∫ x : ℝ, g x*score K x*K x) := by
  calc
    _ = ∫ x : ℝ, K x*deriv g x := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => mul_comm _ _
    _ = -(∫ x : ℝ, deriv K x*g x) :=
      SchwartzMap.integral_mul_deriv_eq_neg_deriv_mul K g
    _ = _ := by
      rw [← integral_neg]
      apply integral_congr_ae
      filter_upwards [score_cancel K] with x hx
      linear_combination -g x * hx

theorem complex_stein (K : 𝓢(ℝ,ℝ)) (g : 𝓢(ℝ,ℂ)) :
    (∫ x : ℝ, K x • deriv g x) =
      (∫ x : ℝ, K x • ((score K x:ℂ)*g x)) := by
  rw [SchwartzMap.integral_smul_deriv_right_eq_neg_left K g, ← integral_neg]
  apply integral_congr_ae
  filter_upwards [score_cancel K] with x hx
  simp only [Complex.real_smul]
  rw [← mul_assoc, ← Complex.ofReal_mul, hx, Complex.ofReal_neg, neg_mul]

theorem signed_stein (K : 𝓢(ℝ,ℝ)) (g : 𝓢(ℝ,ℂ)) :
    (∫ᵛ x : ℝ, deriv g x ∂<•volume.withDensityᵥ (K:ℝ → ℝ)) =
      (∫ᵛ x : ℝ, (score K x:ℂ)*g x ∂<•volume.withDensityᵥ (K:ℝ → ℝ)) := by
  have hd : Integrable (fun x : ℝ => deriv g x) (absoluteDensity volume K) := by
    have he : (SchwartzMap.derivCLM ℂ ℂ g : ℝ → ℂ) = (fun x : ℝ => deriv g x) := by
      funext x
      rw [SchwartzMap.derivCLM_apply]
    rw [← he]
    exact test_absolute_integrable K (SchwartzMap.derivCLM ℂ ℂ g)
  rw [integral_density volume K K.integrable K.continuous.measurable _ hd,
    integral_density volume K K.integrable K.continuous.measurable _
      (score_test_absolute_integrable K g)]
  exact complex_stein K g

theorem higher_heat_signed_stein (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t)
    (g : 𝓢(ℝ,ℂ)) :
    (∫ᵛ x : ℝ, deriv g x ∂<•HigherHeatSignedLaws.law m hm t ht) =
      (∫ᵛ x : ℝ, (score (HigherHeatSignedLaws.realKernel m hm t ht) x:ℂ)*g x
        ∂<•HigherHeatSignedLaws.law m hm t ht) := by
  exact signed_stein _ g

theorem higher_heat_score_not_polynomial (m : ℕ) (hm : 2 ≤ m)
    (t : ℝ≥0) (ht : 0 < t) :
    ¬ ∃ W : Polynomial ℝ, ∀ x : ℝ,
      score (HigherHeatSignedLaws.realKernel m (by omega) t ht) x = W.eval x := by
  rintro ⟨W, hW⟩
  apply SignedSchwartzFirstOrder.higher_heat_no_first_order_polynomial_weight m hm t ht
  refine ⟨W, fun g => ?_⟩
  simpa only [hW] using real_stein (HigherHeatSignedLaws.realKernel m (by omega) t ht) g

end OperatorDerivativeRewrite.Foundation.SignedSchwartzLogDerivative
