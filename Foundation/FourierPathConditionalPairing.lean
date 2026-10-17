import Foundation.FourierPathMeasuredKernels
import Foundation.FourierPathSignedTransitions
import Foundation.HigherHeatPredictablePairing

/-! Actual signed conditional past-test identities for entire Fourier completions. -/
noncomputable section
open MeasureTheory
open scoped NNReal Topology BoundedContinuousFunction
namespace OperatorDerivativeRewrite.Foundation.FourierPathConditionalPairing
open HigherHeatContinuousCylinders HigherHeatFourierBanach HigherHeatCylinderFourier
open HigherHeatFourierPathSemigroup FourierPathStopping FourierPathTerminalKernels
open FourierPathKernelFunctionals FourierPathFutureIntegral HigherHeatFourierInnovations

def mode (a : ℕ → ℝ) : ℕ → ℝ | 0 => 0 | i+1 => a i

theorem atom_all (a : ℕ → ℝ) (i : ℕ) (path : Path) :
    characterTest terminalLevels (frequency a) i path = phase (mode a i) (path.val 1) := by
  cases i with
  | zero => simp [characterTest, HigherHeatMixedFourierPaths.character,
      SignedDensityIntegral.configurationPhase, spectrumFrequency, phase, mode]
  | succ i => exact atom a i path

theorem multiplier_all (a : ℕ → ℝ) (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (i : ℕ) :
    multiplier terminalLevels (frequency a) m T i = HigherHeatL2.symbol m T (mode a i) := by
  cases i with
  | zero =>
    rw [HigherHeatFourierPathC0.multiplier_unit terminalLevels (frequency a) m hm T]
    have hp : 2*m ≠ 0 := Nat.ne_of_gt (Nat.mul_pos (by norm_num) hm)
    simp [mode, HigherHeatL2.symbol, hp]
  | succ i => exact terminal_multiplier a m T i

theorem conditional_pairing {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SigmaFinite μ]
    (ρ : Ω → ℝ) (hρm : Measurable ρ) (hρ : Integrable ρ μ)
    (X : Ω → ℝ) (hX : Measurable X) (G : Ω → ℂ) (hG : Measurable G)
    (C : ℝ) (hb : ∀ w, ‖G w‖ ≤ C)
    (a : ℕ → ℝ) (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (q : TestSpace terminalLevels (frequency a)) :
    (∫ᵛ v, G v.1 * realize terminalLevels (frequency a) q (line (X v.1 + v.2))
      ∂<•extendedLaw μ ρ m hm T hT) =
    ∫ w, (ρ w : ℂ) * G w *
      realize terminalLevels (frequency a) (evolution terminalLevels (frequency a) m hm T q)
        (line (X w)) ∂μ := by
  let wp : Ω → ℂ := fun w => (ρ w : ℂ) * G w
  have hwp : Integrable wp μ := hρ.ofReal.mul_bdd hG.aestronglyMeasurable
    (Filter.Eventually.of_forall hb)
  let wj : Ω × ℝ → ℂ := fun v =>
    (ρ v.1 : ℂ) * (HigherHeatSignedLaws.realKernel m hm T hT v.2 : ℂ) * G v.1
  have hwj : Integrable wj (μ.prod volume) :=
    (hρ.ofReal.mul_prod (HigherHeatSignedLaws.realKernel m hm T hT).integrable.ofReal).mul_bdd
      (hG.comp measurable_fst).aestronglyMeasurable
      (Filter.Eventually.of_forall fun v => hb v.1)
  let Φ : Ω × ℝ → Path := fun v => line (X v.1 + v.2)
  have hΦ : Measurable Φ := line_continuous.measurable.comp
    ((hX.comp measurable_fst).add measurable_snd)
  have hΨ : Measurable (fun w => line (X w)) := line_continuous.measurable.comp hX
  let J := FourierPathMeasuredKernels.functional (μ.prod volume) terminalLevels (frequency a)
    wj hwj Φ hΦ
  let P := (FourierPathMeasuredKernels.functional μ terminalLevels (frequency a)
    wp hwp (fun w => line (X w)) hΨ).comp (evolution terminalLevels (frequency a) m hm T)
  have hJP : J = P := by
    apply ext_generators
    intro i
    change (∫ v, wj v * realize terminalLevels (frequency a)
      (generator terminalLevels (frequency a) i) (Φ v) ∂μ.prod volume) =
      ∫ w, wp w * realize terminalLevels (frequency a)
        (evolution terminalLevels (frequency a) m hm T (generator terminalLevels (frequency a) i))
        (line (X w)) ∂μ
    rw [HigherHeatFourierPathC0.evolution_generator, map_smul]
    simp only [BoundedContinuousFunction.smul_apply, realize_generator, atom_all,
      multiplier_all a m hm T i, smul_eq_mul, Φ, line_apply, mul_one]
    have he (v : Ω × ℝ) : wj v * phase (mode a i) (X v.1 + v.2) =
        (wp v.1 * phase (mode a i) (X v.1)) *
          (phase (mode a i) v.2 * (HigherHeatSignedLaws.realKernel m hm T hT v.2 : ℂ)) := by
      rw [phase_add]
      dsimp [wj, wp]
      ring
    simp_rw [he]
    rw [integral_prod_mul (fun w => wp w * phase (mode a i) (X w))
      (fun y => phase (mode a i) y * (HigherHeatSignedLaws.realKernel m hm T hT y : ℂ)),
      kernel_fourier]
    have he' (w : Ω) : wp w * (HigherHeatL2.symbol m T (mode a i) * phase (mode a i) (X w)) =
        HigherHeatL2.symbol m T (mode a i) * (wp w * phase (mode a i) (X w)) := by ring
    simp_rw [he']
    rw [integral_const_mul, mul_comm]
  calc
    _ = J q := by
      change (∫ᵛ v, G v.1 * realize terminalLevels (frequency a) q (Φ v)
        ∂<•extendedLaw μ ρ m hm T hT) =
        ∫ v, wj v * realize terminalLevels (frequency a) q (Φ v) ∂μ.prod volume
      have hd := hρ.mul_prod
        ((HigherHeatSignedLaws.realKernel m hm T hT).integrable (μ := volume))
      have hdm : Measurable (fun v : Ω × ℝ => ρ v.1 *
          HigherHeatSignedLaws.realKernel m hm T hT v.2) :=
        (hρm.comp measurable_fst).mul
          ((HigherHeatSignedLaws.realKernel m hm T hT).continuous.measurable.comp measurable_snd)
      have hfm : Measurable (fun v : Ω × ℝ => G v.1 *
          realize terminalLevels (frequency a) q (Φ v)) :=
        (hG.comp measurable_fst).mul ((realize terminalLevels (frequency a) q).continuous.measurable.comp hΦ)
      have hfb (v : Ω × ℝ) : ‖G v.1 * realize terminalLevels (frequency a) q (Φ v)‖ ≤ C * ‖q‖ := by
        rw [norm_mul]
        exact (mul_le_mul_of_nonneg_left (test_bound terminalLevels (frequency a) q (Φ v))
          (norm_nonneg _)).trans (mul_le_mul_of_nonneg_right (hb v.1) (norm_nonneg _))
      rw [extendedLaw, SignedDensityIntegral.integral_density (μ.prod volume) _ hd hdm _ hfm
        (C * ‖q‖) hfb]
      change (∫ v, (ρ v.1 * HigherHeatSignedLaws.realKernel m hm T hT v.2) •
        (G v.1 * realize terminalLevels (frequency a) q (Φ v)) ∂μ.prod volume) =
        ∫ v, wj v * realize terminalLevels (frequency a) q (Φ v) ∂μ.prod volume
      apply integral_congr_ae
      filter_upwards with v
      simp only [Complex.real_smul, Complex.ofReal_mul, wj]
      ring
    _ = P q := congrArg (fun L : TestSpace terminalLevels (frequency a) →L[ℂ] ℂ => L q) hJP
    _ = _ := rfl

theorem backward_pairing {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SigmaFinite μ]
    (ρ : Ω → ℝ) (hρm : Measurable ρ) (hρ : Integrable ρ μ)
    (X : Ω → ℝ) (hX : Measurable X) (G : Ω → ℂ) (hG : Measurable G)
    (C : ℝ) (hb : ∀ w, ‖G w‖ ≤ C) (a : ℕ → ℝ) (m : ℕ) (hm : 0 < m)
    (H s t : ℝ≥0) (hst : s < t) (ht : t ≤ H) (q : TestSpace terminalLevels (frequency a)) :
    (∫ᵛ v, G v.1 * realize terminalLevels (frequency a)
      (evolution terminalLevels (frequency a) m hm (H-t) q) (line (X v.1 + v.2))
      ∂<•extendedLaw μ ρ m hm (t-s) (tsub_pos_iff_lt.mpr hst)) =
    ∫ w, (ρ w : ℂ) * G w * realize terminalLevels (frequency a)
      (evolution terminalLevels (frequency a) m hm (H-s) q) (line (X w)) ∂μ := by
  have hh := conditional_pairing μ ρ hρm hρ X hX G hG C hb a m hm
    (t-s) (tsub_pos_iff_lt.mpr hst) (evolution terminalLevels (frequency a) m hm (H-t) q)
  rw [evolution_add, add_comm (t-s), tsub_add_tsub_cancel ht hst.le] at hh
  exact hh

theorem actual_increment_pairing {ι : Type*} [Fintype ι] (m : ℕ) (hm : 0 < m)
    (times : ι → ℝ≥0) (htimes : ∀ i, 0 < times i)
    (G : (ι → ℝ) → ℂ) (hG : Measurable G) (C : ℝ) (hb : ∀ w, ‖G w‖ ≤ C)
    (a : ℕ → ℝ) (T : ℝ≥0) (hT : 0 < T) (q : TestSpace terminalLevels (frequency a)) :
    (∫ᵛ v, G v.1 * realize terminalLevels (frequency a) q (line ((∑ i, v.1 i) + v.2))
      ∂<•extendedLaw (Measure.pi (fun _ : ι => volume))
        (HigherHeatSignedLaws.incrementDensity m hm times htimes) m hm T hT) =
    ∫ w, (HigherHeatSignedLaws.incrementDensity m hm times htimes w : ℂ) * G w *
      realize terminalLevels (frequency a) (evolution terminalLevels (frequency a) m hm T q)
        (line (∑ i, w i)) ∂Measure.pi (fun _ : ι => volume) := by
  exact conditional_pairing (Measure.pi (fun _ : ι => volume))
    (HigherHeatSignedLaws.incrementDensity m hm times htimes)
    (by unfold HigherHeatSignedLaws.incrementDensity; fun_prop)
    (HigherHeatSignedLaws.incrementDensity_integrable m hm times htimes)
    (fun w => ∑ i, w i) (by fun_prop) G hG C hb a m hm T hT q

end OperatorDerivativeRewrite.Foundation.FourierPathConditionalPairing
