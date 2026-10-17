import Foundation.BrownianStickyOccupation
import Foundation.BrownianMassNontriviality

/-! The actual time change has nontrivial physical-time holding for every
positive parameter and every positive deterministic physical horizon. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.BrownianStickyNontriviality
open InfiniteGaussian BrownianRandomMassClock BrownianMassRandomTimeChange
open BrownianClockMeasureTransport BrownianStickyOccupation
open BrownianMassContinuousLimit BrownianMassLimitIdentification

def occupation (κ : ℝ≥0) (ω : SampleSpace) (T : ℝ≥0) : ℝ :=
  (ordinaryTime ({t : ℝ≥0 | changedPath κ ω t = 0} ∩ Iic T)).toReal

theorem occupation_nonneg (κ : ℝ≥0) (ω : SampleSpace) (T : ℝ≥0) :
    0 ≤ occupation κ ω T := ENNReal.toReal_nonneg

theorem occupation_gap : ∀ᵐ ω ∂gaussianProduct, ∀ κ T : ℝ≥0,
    occupation κ ω T = (T : ℝ) - inverse κ ω T := by
  filter_upwards [zero_occupation_gap] with ω hω κ T
  change (ordinaryTime _).toReal = _
  rw [hω, ENNReal.toReal_ofReal (sub_nonneg.mpr (by exact_mod_cast inverse_le κ ω T))]

theorem occupation_integrable (κ T : ℝ≥0) :
    Integrable (fun ω => occupation κ ω T) gaussianProduct := by
  have he : (fun ω => occupation κ ω T) =ᵐ[gaussianProduct]
      (fun ω => (T : ℝ) - (inverse κ ω T : ℝ)) :=
    occupation_gap.mono (fun _ h => h κ T)
  have hg : Measurable (fun ω => (T : ℝ) - (inverse κ ω T : ℝ)) :=
    measurable_const.sub
      (continuous_subtype_val.measurable.comp (inverse_coordinate_measurable κ T))
  apply (integrable_const (T : ℝ)).mono'
    (hg.aestronglyMeasurable.congr he.symm)
  filter_upwards [he] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg (occupation_nonneg κ ω T), hω]
  exact sub_le_self _ (inverse κ ω T).property

theorem occupation_pos_iff : ∀ᵐ ω ∂gaussianProduct, ∀ κ T : ℝ≥0, 0 < κ →
    (0 < occupation κ ω T ↔ 0 < mass ω T) := by
  filter_upwards [occupation_gap] with ω hω κ T hκ
  rw [hω, sub_pos]
  change inverse κ ω T < T ↔ 0 < mass ω T
  rw [inverse_lt_iff]
  simp [forward, StickyTimeChangeClock.clock, hκ]

theorem expected_occupation_pos (κ T : ℝ≥0) (hκ : 0 < κ) (hT : 0 < T) :
    0 < ∫ ω, occupation κ ω T ∂gaussianProduct := by
  have hi := occupation_integrable κ T
  have hn : 0 ≤ᵐ[gaussianProduct] (fun ω => occupation κ ω T) :=
    Eventually.of_forall (fun ω => occupation_nonneg κ ω T)
  have hmass : 0 < ∫ ω, (mass ω T : ℝ) ∂gaussianProduct := by
    rw [integral_congr_ae (mass_agrees.mono (fun _ h => h T))]
    exact BrownianMassNontriviality.expected_mass_pos T hT
  by_contra! hle
  have hz := (integral_eq_zero_iff_of_nonneg_ae hn hi).mp
    (le_antisymm hle (integral_nonneg_of_ae hn))
  have hm : (fun ω => (mass ω T : ℝ)) =ᵐ[gaussianProduct] fun _ => 0 := by
    filter_upwards [hz, occupation_pos_iff] with ω hz hp
    change occupation κ ω T = 0 at hz
    have hm : ¬ 0 < mass ω T := by
      intro hm
      have ho := (hp κ T hκ).mpr hm
      simpa only [hz, lt_self_iff_false] using ho
    have he : mass ω T = 0 := le_antisymm (not_lt.mp hm) bot_le
    simp only [he, NNReal.coe_zero]
  rw [integral_congr_ae hm, integral_zero] at hmass
  exact (lt_irrefl 0) hmass

theorem positive_occupation_probability (κ T : ℝ≥0) (hκ : 0 < κ) (hT : 0 < T) :
    0 < gaussianProduct {ω | 0 < occupation κ ω T} := by
  have hp := (integral_pos_iff_support_of_nonneg
    (fun ω => occupation_nonneg κ ω T) (occupation_integrable κ T)).mp
      (expected_occupation_pos κ T hκ hT)
  have he : Function.support (fun ω => occupation κ ω T) = {ω | 0 < occupation κ ω T} := by
    ext ω
    change occupation κ ω T ≠ 0 ↔ 0 < occupation κ ω T
    exact ne_comm.trans (ne_iff_lt_iff_le.mpr (occupation_nonneg κ ω T))
  rwa [he] at hp

theorem occupation_parameter_zero : ∀ᵐ ω ∂gaussianProduct, ∀ T : ℝ≥0,
    occupation 0 ω T = 0 := by
  filter_upwards [occupation_gap] with ω hω T
  rw [hω, inverse_parameter_zero, sub_self]

end OperatorDerivativeRewrite.Foundation.BrownianStickyNontriviality
