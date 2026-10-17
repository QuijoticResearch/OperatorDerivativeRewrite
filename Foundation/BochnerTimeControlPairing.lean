import Foundation.FourierPathBoundedControls
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

/-! Actual Bochner time-density pairing with bounded controls, with separation. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.BochnerTimeControlPairing
open FourierPathBoundedControls

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

abbrev Field := Lp E 1 (volume : Measure ℝ)

def pairing : Control →L[ℝ] Field E →L[ℝ] E :=
  (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E).lpPairing volume ∞ 1

theorem pairing_integral (u : Control) (f : Field E) :
    pairing E u f = ∫ s, u s • f s :=
  (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E).lpPairing_eq_integral u f

theorem pairing_bound (u : Control) (f : Field E) : ‖pairing E u f‖ ≤ ‖u‖*‖f‖ := by
  let B := (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E)
  change ‖L1.integralCLM ((B.holder 1) u f)‖ ≤ _
  calc
    _ ≤ ‖B.holder 1 u f‖ := by
      simpa only [L1.integral_eq] using L1.norm_integral_le (B.holder 1 u f)
    _ ≤ ‖B‖*‖u‖*‖f‖ := B.norm_holder_apply_apply_le u f
    _ ≤ 1*‖u‖*‖f‖ := by gcongr; exact ContinuousLinearMap.opNorm_lsmul_le
    _ = _ := by ring

theorem pairing_indicator (s : Set ℝ) (hs : MeasurableSet s) (hμs : volume s ≠ ∞) (f : Field E) :
    pairing E (indicatorConstLp ∞ hs hμs (1:ℝ)) f = ∫ t in s, f t := by
  rw [pairing_integral]
  trans ∫ t, s.indicator (fun x => f x) t
  · apply integral_congr_ae
    filter_upwards [@indicatorConstLp_coeFn ℝ ℝ _ ∞ volume _ _ hs hμs 1] with t ht
    rw [ht]
    by_cases hts : t ∈ s
    · simp [hts]
    · simp [hts]
  · exact integral_indicator hs

theorem annihilator_zero (f : Field E) (hf : ∀ u : Control, pairing E u f = 0) : f = 0 := by
  apply Lp.eq_zero_iff_ae_eq_zero.mpr
  apply Lp.ae_eq_zero_of_forall_setIntegral_eq_zero f (by simp) (by simp)
  · intro s hs hμs
    exact (memLp_one_iff_integrable.mp (Lp.memLp f)).integrableOn
  · intro s hs hμs
    rw [← pairing_indicator E s hs hμs.ne f]
    exact hf _

theorem pairing_injective : Function.Injective (pairing E).flip := by
  intro f g hfg
  have hz : f-g=0 := annihilator_zero E (f-g) (fun u => by
    rw [map_sub]
    exact sub_eq_zero.mpr (DFunLike.congr_fun hfg u))
  exact sub_eq_zero.mp hz

end OperatorDerivativeRewrite.Foundation.BochnerTimeControlPairing
