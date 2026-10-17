import Foundation.FourierPathDualControls
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

/-! Actual Bochner L^(2m) fields paired with Holder-dual time controls, with separation. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.BochnerDualControlPairing
open FourierPathDualControls HigherHeatLpControls

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

abbrev Field (m : ℕ) := Lp (α := ℝ) E (power m) volume

def pairing (m : ℕ) [Fact (0 < m)] : FourierPathDualControls.Control m →L[ℝ] Field E m →L[ℝ] E :=
  (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E).lpPairing volume (exponent m) (power m)

theorem pairing_integral (m : ℕ) [Fact (0 < m)] (u : FourierPathDualControls.Control m)
    (f : Field E m) : pairing E m u f = ∫ s, u s • f s :=
  (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E).lpPairing_eq_integral u f

theorem pairing_bound (m : ℕ) [Fact (0 < m)] (u : FourierPathDualControls.Control m)
    (f : Field E m) : ‖pairing E m u f‖ ≤ ‖u‖*‖f‖ := by
  let B := (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E)
  change ‖L1.integralCLM (B.holder 1 u f)‖ ≤ _
  calc
    _ ≤ ‖B.holder 1 u f‖ := by
      simpa only [L1.integral_eq] using L1.norm_integral_le (B.holder 1 u f)
    _ ≤ ‖B‖*‖u‖*‖f‖ := B.norm_holder_apply_apply_le u f
    _ ≤ 1*‖u‖*‖f‖ := by gcongr; exact ContinuousLinearMap.opNorm_lsmul_le
    _ = _ := by ring

theorem pairing_indicator (m : ℕ) [Fact (0 < m)] (s : Set ℝ) (hs : MeasurableSet s)
    (hμs : volume s ≠ ∞) (f : Field E m) :
    pairing E m (indicatorConstLp (exponent m) hs hμs (1 : ℝ)) f = ∫ t in s, f t := by
  rw [pairing_integral]
  trans ∫ t, s.indicator (fun x => f x) t
  · apply integral_congr_ae
    filter_upwards [@indicatorConstLp_coeFn ℝ ℝ _ (exponent m) volume _ _ hs hμs 1] with t ht
    rw [ht]
    by_cases hts : t ∈ s <;> simp [hts]
  · exact integral_indicator hs

theorem annihilator_zero (m : ℕ) [Fact (0 < m)] (f : Field E m)
    (hf : ∀ u : FourierPathDualControls.Control m, pairing E m u f = 0) : f = 0 := by
  apply Lp.eq_zero_iff_ae_eq_zero.mpr
  apply Lp.ae_eq_zero_of_forall_setIntegral_eq_zero f (power_ne_zero m) (power_ne_top m)
  · intro s hs hμs
    letI : IsFiniteMeasure (volume.restrict s) := isFiniteMeasure_restrict.mpr hμs.ne
    exact MemLp.integrable (power_fact m).out ((Lp.memLp f).restrict s)
  · intro s hs hμs
    rw [← pairing_indicator E m s hs hμs.ne f]
    exact hf _

theorem pairing_injective (m : ℕ) [Fact (0 < m)] : Function.Injective (pairing E m).flip := by
  intro f g hfg
  have hz : f-g = 0 := annihilator_zero E m (f-g) (fun u => by
    rw [map_sub]
    exact sub_eq_zero.mpr (DFunLike.congr_fun hfg u))
  exact sub_eq_zero.mp hz

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem pairing_compLp (m : ℕ) [Fact (0 < m)] (L : E →L[ℝ] F)
    (u : FourierPathDualControls.Control m) (f : Field E m) :
    pairing F m u (L.compLpL (power m) volume f) = L (pairing E m u f) := by
  rw [pairing_integral, pairing_integral]
  have hi : Integrable (fun s => u s • f s) :=
    memLp_one_iff_integrable.mp ((Lp.memLp u).smul (Lp.memLp f))
  rw [← L.integral_comp_comm hi]
  apply integral_congr_ae
  filter_upwards [L.coeFn_compLpL f] with s hs
  rw [hs, map_smul]

end OperatorDerivativeRewrite.Foundation.BochnerDualControlPairing
