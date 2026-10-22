import Foundation.InfiniteGaussianFirstChaos
import Foundation.FixedLawPathObstruction
import Mathlib.Probability.Martingale.Basic

/-! Continuous observations can have a raw natural filtration with instantaneous
information arrival and a square-integrable martingale without right continuity.
This is a counterexample to a general inference, not an IBM path assertion. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.ContinuousObservationFiltrationObstruction
open InfiniteGaussian
set_option backward.isDefEq.respectTransparency false

def observation (t : ℝ) (ω : SampleSpace) : ℝ := max t 0 * coordinate 0 ω

theorem observation_continuous (ω : SampleSpace) : Continuous (fun t => observation t ω) :=
  (continuous_id.max continuous_const).mul continuous_const

theorem observation_measurable (t : ℝ) : StronglyMeasurable (observation t) :=
  (measurable_const.mul (coordinate_measurePreserving 0).measurable).stronglyMeasurable

def filtration : Filtration ℝ (inferInstance : MeasurableSpace SampleSpace) :=
  Filtration.natural observation observation_measurable

theorem filtration_before {t : ℝ} (ht : t ≤ 0) : filtration t = ⊥ := by
  apply bot_unique
  change (⨆ s ≤ t, MeasurableSpace.comap (observation s) inferInstance) ≤ ⊥
  apply iSup₂_le
  intro s hs
  have he : observation s = (fun _ : SampleSpace => (0 : ℝ)) := by
    funext ω
    simp only [observation, max_eq_right (hs.trans ht), zero_mul]
  have hm : Measurable[⊥] (observation s) := by rw [he]; exact measurable_const
  exact hm.comap_le

theorem coordinate_adapted {t : ℝ} (ht : 0 < t) :
    StronglyMeasurable[filtration t] (coordinate 0) := by
  have hp := Filtration.stronglyAdapted_natural observation_measurable t
  have he : coordinate 0 = fun ω => t⁻¹ * observation t ω := by
    funext ω
    simp only [observation, max_eq_left ht.le, ← mul_assoc, inv_mul_cancel₀ ht.ne', one_mul]
  rw [he]
  exact hp.const_mul _

theorem coordinate_not_adapted_zero :
    ¬ StronglyMeasurable[filtration 0] (coordinate 0) := by
  intro hm
  rw [filtration_before le_rfl] at hm
  obtain ⟨c, hc⟩ := stronglyMeasurable_bot_iff.mp hm
  have h0 := congrFun hc (fun _ => (0 : ℝ))
  have h1 := congrFun hc (fun _ => (1 : ℝ))
  change (0 : ℝ) = c at h0
  change (1 : ℝ) = c at h1
  linarith

theorem filtration_not_right_continuous : ¬ filtration.IsRightContinuous := by
  intro h
  have he := Filtration.rightCont_eq filtration (0 : ℝ)
  have hc : MeasurableSpace.comap (coordinate 0) inferInstance ≤ ⨅ t > (0 : ℝ), filtration t :=
    le_iInf₂ fun t ht => (coordinate_adapted ht).measurable.comap_le
  rw [← he] at hc
  have hm : Measurable[filtration 0] (coordinate 0) := Measurable.of_comap_le (hc.trans (h.RC 0))
  exact coordinate_not_adapted_zero hm.stronglyMeasurable

def value (t : ℝ) : SampleSpace → ℝ := if 0 < t then coordinate 0 else 0

theorem value_adapted : StronglyAdapted filtration value := by
  intro t
  by_cases ht : 0 < t
  · simpa only [value, ite_eq_left ht] using coordinate_adapted ht
  · simp only [value, ite_eq_right ht]
    exact stronglyMeasurable_zero

theorem value_memLp (t : ℝ) : MemLp (value t) 2 gaussianProduct := by
  by_cases ht : 0 < t
  · simpa only [value, ite_eq_left ht] using coordinate_memLp 0 2 (by norm_num)
  · simp only [value, ite_eq_right ht]
    exact MemLp.zero

theorem value_mean (t : ℝ) : (∫ ω, value t ω ∂gaussianProduct) = 0 := by
  by_cases ht : 0 < t
  · simpa only [value, ite_eq_left ht] using coordinate_integral 0
  · simp [value, ht]

theorem actual_martingale : Martingale value filtration gaussianProduct := by
  refine ⟨value_adapted, ?_⟩
  intro s t hst
  by_cases hs : 0 < s
  · have ht : 0 < t := hs.trans_le hst
    simp only [value, ite_eq_left hs, ite_eq_left ht]
    exact Filter.EventuallyEq.of_eq (condExp_of_stronglyMeasurable (filtration.le s)
      (coordinate_adapted hs) ((coordinate_memLp 0 2 (by norm_num)).integrable (by norm_num)))
  · rw [filtration_before (le_of_not_gt hs), condExp_bot, value_mean]
    simp only [value, ite_eq_right hs]
    rfl

theorem positive_law {t : ℝ} (ht : 0 < t) : HasLaw (value t) GaussianCore.γ gaussianProduct := by
  simpa only [value, ite_eq_left ht] using
    (show HasLaw (coordinate 0) GaussianCore.γ gaussianProduct from
      ⟨(coordinate_measurePreserving 0).measurable.aemeasurable, coordinate_law 0⟩)

theorem no_ae_right_continuous_paths :
    ¬ ∀ᵐ ω ∂gaussianProduct, ContinuousWithinAt (fun t => value t ω) (Ici 0) 0 := by
  let : NullSingletonClass GaussianCore.γ := nullSingletonClass_gaussianReal (by norm_num)
  exact FixedLawPathObstruction.not_right_continuous gaussianProduct GaussianCore.γ value 0
    (Filter.EventuallyEq.of_eq (by funext ω; simp [value])) (fun t ht => positive_law ht)

theorem no_ae_right_continuous_modification (Y : ℝ → SampleSpace → ℝ)
    (hY : ∀ t, Y t =ᵐ[gaussianProduct] value t) :
    ¬ ∀ᵐ ω ∂gaussianProduct, ContinuousWithinAt (fun t => Y t ω) (Ici 0) 0 := by
  let : NullSingletonClass GaussianCore.γ := nullSingletonClass_gaussianReal (by norm_num)
  apply FixedLawPathObstruction.not_right_continuous gaussianProduct GaussianCore.γ Y 0
  · exact (hY 0).trans (Filter.EventuallyEq.of_eq (by funext ω; simp [value]))
  · intro t ht
    exact (positive_law ht).congr (hY t)

theorem increment_energy {t : ℝ} (ht : 0 < t) :
    (∫ ω, (value t ω - value 0 ω) ^ 2 ∂gaussianProduct) = 1 := by
  simpa [value, ht, pow_two] using coordinate_product_integral 0 0

end OperatorDerivativeRewrite.Foundation.ContinuousObservationFiltrationObstruction
