import Foundation.HigherHeatFourierTranslations

/-! Actual deterministic stopping and a Fourier-dictionary closure obstruction. -/
noncomputable section
open scoped NNReal Topology BoundedContinuousFunction
namespace OperatorDerivativeRewrite.Foundation.FourierPathStopping
open HigherHeatDyadicLaws HigherHeatContinuousCylinders HigherHeatFourierBanach
open HigherHeatFourierTranslations

def clock (t : ℝ≥0) : C(ℝ, ℝ) := ⟨fun s => min s t, continuous_id.min continuous_const⟩

def stop (t : ℝ≥0) (path : Path) : Path :=
  ⟨path.val.comp (clock t), by simp [clock, path.property]⟩

theorem stop_apply (t : ℝ≥0) (path : Path) (s : ℝ) :
    (stop t path).val s = path.val (min s t) := rfl

theorem stop_continuous (t : ℝ≥0) : Continuous (stop t) := by
  exact ((ContinuousMap.compCLM ℝ ℝ (clock t)).continuous.comp
    continuous_subtype_val).subtype_mk _

theorem stop_stop (s t : ℝ≥0) (path : Path) :
    stop s (stop t path) = stop (min s t) path := by
  apply Subtype.ext
  ext r
  simp only [stop_apply, NNReal.coe_min, min_assoc]

def pullback (t : ℝ≥0) : (Path →ᵇ ℂ) →L[ℂ] (Path →ᵇ ℂ) :=
  BoundedContinuousFunction.compContinuousCLM ℂ ℂ ⟨stop t, stop_continuous t⟩

theorem pullback_apply (t : ℝ≥0) (f : Path →ᵇ ℂ) (path : Path) :
    pullback t f path = f (stop t path) := rfl

theorem pullback_norm (t : ℝ≥0) : ‖pullback t‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  change ‖f.compContinuous ⟨stop t, stop_continuous t⟩‖ ≤ 1 * ‖f‖
  simpa only [one_mul] using
    BoundedContinuousFunction.norm_compContinuous_le f ⟨stop t, stop_continuous t⟩

theorem atoms_determine (levels : ℕ → ℕ) (ξ : (i : ℕ) → Grid (levels i))
    (x y : Path) (h : ∀ i, characterTest levels ξ i x = characterTest levels ξ i y)
    (q : TestSpace levels ξ) : realize levels ξ q x = realize levels ξ q y := by
  obtain ⟨a, rfl⟩ := (kernel levels ξ).mkQ_surjective q
  simp only [realize_mk, realization_apply]
  apply tsum_congr
  intro i
  exact congrArg (fun z : ℂ => a i * z) (h i)

def terminalLevels : ℕ → ℕ := fun _ => 0

def terminalFrequency : (i : ℕ) → Grid (terminalLevels i) := fun _ _ => 1

theorem terminal_sample (path : Path) (j : Fin (gridSize 0)) :
    sample 0 path j = path.val 1 := by
  have hj : j.val = 0 := by have h := j.isLt; change j.val < 1 at h; omega
  simp [sample, coordinate, sampleTime, time, duration, gridSize, hj]

theorem terminal_character (i : ℕ) (path : Path) :
    characterTest terminalLevels terminalFrequency (i+1) path =
      (Real.fourierChar (-path.val 1) : ℂ) := by
  change (Real.fourierChar (-(∑ j : Fin (gridSize 0), 1 * sample 0 path j)) : ℂ) = _
  have hs : (∑ j : Fin (gridSize 0), sample 0 path j) = path.val 1 := by
    calc
      _ = ∑ _j : Fin (gridSize 0), path.val 1 := by
        apply Finset.sum_congr rfl
        intro j _
        exact terminal_sample path j
      _ = path.val 1 := by
        have hc : Fintype.card (Fin (gridSize 0)) = 1 := Fintype.card_fin 1
        rw [Finset.sum_const, Finset.card_univ, hc, one_nsmul]
  simp only [one_mul]
  exact congrArg (fun r : ℝ => (Real.fourierChar (-r) : ℂ)) hs

theorem terminal_depends_endpoint (x y : Path) (h : x.val 1 = y.val 1)
    (q : TestSpace terminalLevels terminalFrequency) :
    realize terminalLevels terminalFrequency q x =
      realize terminalLevels terminalFrequency q y := by
  apply atoms_determine _ _ x y _ q
  intro i
  cases i with
  | zero => simp [characterTest, HigherHeatMixedFourierPaths.character,
      SignedDensityIntegral.configurationPhase, spectrumFrequency]
  | succ i =>
    rw [terminal_character, terminal_character, h]

def arch : Path := ⟨⟨fun s : ℝ => -2 * s * (1-s), by fun_prop⟩, by norm_num⟩

theorem stopped_generator_zero :
    realize terminalLevels terminalFrequency (generator terminalLevels terminalFrequency 1)
      (stop (1/2) zeroPath) = 1 := by
  rw [realize_generator, terminal_character]
  norm_num [stop_apply, zeroPath]

theorem stopped_generator_arch :
    realize terminalLevels terminalFrequency (generator terminalLevels terminalFrequency 1)
      (stop (1/2) arch) = -1 := by
  rw [realize_generator, terminal_character]
  norm_num [stop_apply, arch]
  rw [Real.fourierChar_apply]
  convert Complex.exp_pi_mul_I using 1 <;> congr 1 <;> push_cast <;> ring

theorem stopped_generator_not_representable :
    ¬ ∃ q : TestSpace terminalLevels terminalFrequency,
      ∀ path, realize terminalLevels terminalFrequency q path =
        realize terminalLevels terminalFrequency (generator terminalLevels terminalFrequency 1)
          (stop (1/2) path) := by
  rintro ⟨q, hq⟩
  have he := terminal_depends_endpoint zeroPath arch (by norm_num [zeroPath, arch]) q
  rw [hq, hq, stopped_generator_zero, stopped_generator_arch] at he
  norm_num at he

theorem no_stopping_operator :
    ¬ ∃ P : TestSpace terminalLevels terminalFrequency → TestSpace terminalLevels terminalFrequency,
      ∀ q path, realize terminalLevels terminalFrequency (P q) path =
        realize terminalLevels terminalFrequency q (stop (1/2) path) := by
  rintro ⟨P, hP⟩
  exact stopped_generator_not_representable ⟨P (generator _ _ 1), hP _⟩

end OperatorDerivativeRewrite.Foundation.FourierPathStopping
