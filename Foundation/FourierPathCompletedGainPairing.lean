import Foundation.FourierPathCompletedGains

/-! Actual integrability and signed martingale centering of completed backward gains. -/
noncomputable section
open MeasureTheory
open scoped NNReal Topology BoundedContinuousFunction
namespace OperatorDerivativeRewrite.Foundation.FourierPathCompletedGainPairing
open HigherHeatContinuousCylinders HigherHeatFourierBanach FourierPathStopping
open FourierPathTerminalKernels FourierPathCompletedGains FourierPathConditionalPairing
open HigherHeatSignedLaws HigherHeatFourierInnovations SignedDensityIntegral
attribute [local irreducible] state

theorem past_constant {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SigmaFinite μ]
    (ρ : Ω → ℝ) (hρm : Measurable ρ) (hρ : Integrable ρ μ)
    (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (B : Ω → ℂ) (hB : Measurable B) (C : ℝ) (hb : ∀ w, ‖B w‖ ≤ C) :
    (∫ᵛ v, B v.1 ∂<•extendedLaw μ ρ m hm T hT) = ∫ w, (ρ w : ℂ) * B w ∂μ := by
  have hh := HigherHeatPredictablePairing.integral_separable μ ρ hρm hρ m hm T hT
    B hB C hb (fun _ => 1) measurable_const 1 zero_le_one (fun _ => (norm_one : ‖(1 : ℂ)‖ = 1).le)
  simpa only [mul_one, one_mul, integral_complex_ofReal, realKernel_integral,
    Complex.ofReal_one] using hh

theorem gain_pairing {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SigmaFinite μ]
    (ρ : Ω → ℝ) (hρm : Measurable ρ) (hρ : Integrable ρ μ)
    (X : Ω → ℝ) (hX : Measurable X) (G : Ω → ℂ) (hG : Measurable G)
    (C : ℝ) (hb : ∀ w, ‖G w‖ ≤ C) (a : ℕ → ℝ) (m : ℕ) (hm : 0 < m)
    (H s t : ℝ≥0) (hst : s < t) (ht : t ≤ H) (q : TestSpace terminalLevels (frequency a)) :
    (extendedLaw μ ρ m hm (t-s) (tsub_pos_iff_lt.mpr hst)).Integrable
      (fun v => G v.1 * gain a m hm H q s t (X v.1) (X v.1 + v.2)) ∧
    (∫ᵛ v, G v.1 * gain a m hm H q s t (X v.1) (X v.1 + v.2)
      ∂<•extendedLaw μ ρ m hm (t-s) (tsub_pos_iff_lt.mpr hst)) = 0 := by
  let ν := extendedLaw μ ρ m hm (t-s) (tsub_pos_iff_lt.mpr hst)
  let Ft : Ω × ℝ → ℂ := fun v => G v.1 * state a m hm H q t (X v.1 + v.2)
  let B : Ω → ℂ := fun w => G w * state a m hm H q s (X w)
  let Fs : Ω × ℝ → ℂ := fun v => B v.1
  have hstate := (state_continuous a m hm H q).measurable
  have hta : Measurable (fun v : Ω × ℝ => (t, X v.1 + v.2)) :=
    measurable_const.prodMk ((hX.comp measurable_fst).add measurable_snd)
  have hsa : Measurable (fun w : Ω => (s, X w)) := measurable_const.prodMk hX
  have hts := hstate.comp hta
  have hss := hstate.comp hsa
  have htm : Measurable Ft := (hG.comp measurable_fst).mul hts
  have hBm : Measurable B := hG.mul hss
  have htb (v : Ω × ℝ) : ‖Ft v‖ ≤ C * ‖q‖ := by
    change ‖G v.1 * state a m hm H q t (X v.1 + v.2)‖ ≤ _
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (state_bound a m hm H q t _) (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_right (hb v.1) (norm_nonneg _))
  have hBb (w : Ω) : ‖B w‖ ≤ C * ‖q‖ := by
    change ‖G w * state a m hm H q s (X w)‖ ≤ _
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (state_bound a m hm H q s _) (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_right (hb w) (norm_nonneg _))
  have hFt : ν.Integrable Ft := bounded_signed_integrable ν Ft htm (C * ‖q‖) htb
  have hFs : ν.Integrable Fs := bounded_signed_integrable ν Fs
    (hBm.comp measurable_fst) (C * ‖q‖) (fun v => hBb v.1)
  have he : (∫ᵛ v, Ft v ∂<•ν) =
      ∫ w, (ρ w : ℂ) * G w * state a m hm H q s (X w) ∂μ := by
    have hh := backward_pairing μ ρ hρm hρ X hX G hG C hb a m hm H s t hst ht q
    simpa only [Ft, ν, state] using hh
  have he' : (∫ᵛ v, Fs v ∂<•ν) =
      ∫ w, (ρ w : ℂ) * G w * state a m hm H q s (X w) ∂μ := by
    have hh := past_constant μ ρ hρm hρ m hm (t-s) (tsub_pos_iff_lt.mpr hst)
      B hBm (C * ‖q‖) hBb
    simpa only [B, mul_assoc] using hh
  have hg : (fun v : Ω × ℝ => G v.1 * gain a m hm H q s t (X v.1) (X v.1 + v.2)) =
      Ft - Fs := by
    funext v
    simp only [Ft, Fs, B, gain, Pi.sub_apply, mul_sub]
  constructor
  · change ν.Integrable (fun v => G v.1 * gain a m hm H q s t (X v.1) (X v.1 + v.2))
    rw [hg]
    exact hFt.sub hFs
  · change (∫ᵛ v, G v.1 * gain a m hm H q s t (X v.1) (X v.1 + v.2) ∂<•ν) = 0
    have hi := congrArg (fun f : Ω × ℝ → ℂ => ∫ᵛ v, f v ∂<•ν) hg
    rw [hi, VectorMeasure.integral_sub hFt hFs, he, he', sub_self]

end OperatorDerivativeRewrite.Foundation.FourierPathCompletedGainPairing
