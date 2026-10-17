import Foundation.FourierPathKernelFunctionals
import Foundation.HigherHeatFourierPathC0

/-! Actual signed-kernel representation of heat evolution on infinite terminal Fourier classes. -/
noncomputable section
open MeasureTheory
open scoped NNReal Topology BoundedContinuousFunction
namespace OperatorDerivativeRewrite.Foundation.FourierPathTerminalKernels
open HigherHeatDyadicLaws HigherHeatContinuousCylinders HigherHeatFourierBanach
open HigherHeatCylinderFourier
open HigherHeatFourierTranslations HigherHeatFourierPathSemigroup
open FourierPathStopping FourierPathFutureIntegral FourierPathKernelFunctionals

def frequency (a : ℕ → ℝ) : (i : ℕ) → Grid (terminalLevels i) := fun i _ => a i

def unitLine : Path := ⟨⟨id, continuous_id⟩, rfl⟩

def line (x : ℝ) : Path := scalePath x unitLine

theorem line_apply (x s : ℝ) : (line x).val s = x * s := rfl

theorem line_continuous : Continuous line := scalePath_continuous unitLine

theorem atom (a : ℕ → ℝ) (i : ℕ) (path : Path) :
    characterTest terminalLevels (frequency a) (i+1) path = phase (a i) (path.val 1) := by
  change (Real.fourierChar (-(∑ j : Fin (gridSize 0), a i * sample 0 path j)) : ℂ) = _
  have hs : (∑ j : Fin (gridSize 0), a i * sample 0 path j) = a i * path.val 1 := by
    calc
      _ = ∑ _j : Fin (gridSize 0), a i * path.val 1 := by
        apply Finset.sum_congr rfl
        intro j _
        rw [terminal_sample]
      _ = a i * path.val 1 := by
        have hc : Fintype.card (Fin (gridSize 0)) = 1 := Fintype.card_fin 1
        rw [Finset.sum_const, Finset.card_univ, hc, one_nsmul]
  rw [hs]
  simp only [phase, mul_comm]

theorem terminal_multiplier (a : ℕ → ℝ) (m : ℕ) (T : ℝ≥0) (i : ℕ) :
    multiplier terminalLevels (frequency a) m T (i+1) = HigherHeatL2.symbol m T (a i) := by
  unfold multiplier
  change (∏ j : Fin (gridSize 0), HigherHeatL2.symbol m (duration T 0)
    (∑ k ∈ Finset.univ.filter (fun k => j ≤ k), a i)) = _
  simp only [duration, gridSize, Nat.cast_one, div_one]
  have he : (∏ j : Fin 1, HigherHeatL2.symbol m T
      (∑ k ∈ Finset.univ.filter (fun k : Fin 1 => j ≤ k), a i)) =
      HigherHeatL2.symbol m T (a i) := by simp
  exact he

def shiftedLine (x : ℝ) (y : ℝ) : Path := line (x+y)

theorem shiftedLine_continuous (x : ℝ) : Continuous (shiftedLine x) :=
  line_continuous.comp (continuous_const.add continuous_id)

def kernelFunctional (a : ℕ → ℝ) (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (x : ℝ) : TestSpace terminalLevels (frequency a) →L[ℂ] ℂ :=
  functional terminalLevels (frequency a)
    (fun y => (HigherHeatSignedLaws.realKernel m hm T hT y : ℂ))
    (HigherHeatSignedLaws.realKernel m hm T hT).integrable.ofReal
    (shiftedLine x) (shiftedLine_continuous x)

def heatFunctional (a : ℕ → ℝ) (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (x : ℝ) :
    TestSpace terminalLevels (frequency a) →L[ℂ] ℂ :=
  (BoundedContinuousFunction.evalCLM ℂ (line x)).comp
    ((realize terminalLevels (frequency a)).comp
      (evolution terminalLevels (frequency a) m hm T))

theorem kernel_eq_heat (a : ℕ → ℝ) (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (x : ℝ) : kernelFunctional a m hm T hT x = heatFunctional a m hm T x := by
  apply ext_generators
  intro i
  change (∫ y, (HigherHeatSignedLaws.realKernel m hm T hT y : ℂ) *
    realize terminalLevels (frequency a) (generator terminalLevels (frequency a) i)
      (shiftedLine x y)) =
    realize terminalLevels (frequency a)
      (evolution terminalLevels (frequency a) m hm T (generator terminalLevels (frequency a) i))
      (line x)
  rw [HigherHeatFourierPathC0.evolution_generator, map_smul,
    BoundedContinuousFunction.smul_apply, realize_generator]
  cases i with
  | zero =>
    rw [HigherHeatFourierPathC0.multiplier_unit terminalLevels (frequency a) m hm T]
    have hz (path : Path) : characterTest terminalLevels (frequency a) 0 path = 1 := by
      simp [characterTest, HigherHeatMixedFourierPaths.character,
        SignedDensityIntegral.configurationPhase, spectrumFrequency]
    simp only [hz, mul_one, one_smul]
    rw [integral_complex_ofReal, HigherHeatSignedLaws.realKernel_integral]
    rfl
  | succ i =>
    simp only [atom, shiftedLine, line_apply, mul_one, smul_eq_mul]
    rw [terminal_multiplier]
    have he := shifted_kernel_integral m hm T hT x (a i)
    simpa only [mul_comm] using he

theorem heat_kernel_representation (a : ℕ → ℝ) (m : ℕ) (hm : 0 < m)
    (T : ℝ≥0) (hT : 0 < T) (x : ℝ) (q : TestSpace terminalLevels (frequency a)) :
    realize terminalLevels (frequency a) (evolution terminalLevels (frequency a) m hm T q)
      (line x) =
        ∫ y, (HigherHeatSignedLaws.realKernel m hm T hT y : ℂ) *
          realize terminalLevels (frequency a) q (shiftedLine x y) :=
  congrArg (fun L : TestSpace terminalLevels (frequency a) →L[ℂ] ℂ => L q)
    (kernel_eq_heat a m hm T hT x).symm

theorem heat_signed_representation (a : ℕ → ℝ) (m : ℕ) (hm : 0 < m)
    (T : ℝ≥0) (hT : 0 < T) (x : ℝ) (q : TestSpace terminalLevels (frequency a)) :
    realize terminalLevels (frequency a) (evolution terminalLevels (frequency a) m hm T q)
      (line x) = ∫ᵛ y, realize terminalLevels (frequency a) q (shiftedLine x y)
        ∂<•HigherHeatSignedLaws.law m hm T hT := by
  rw [HigherHeatSignedLaws.law, SignedDensityIntegral.integral_density volume _
    (HigherHeatSignedLaws.realKernel m hm T hT).integrable
    (HigherHeatSignedLaws.realKernel m hm T hT).continuous.measurable
    (fun y => realize terminalLevels (frequency a) q (shiftedLine x y))
    ((realize terminalLevels (frequency a) q).continuous.comp (shiftedLine_continuous x)).measurable
    ‖q‖ (fun y => test_bound terminalLevels (frequency a) q (shiftedLine x y))]
  simp only [Complex.real_smul]
  exact heat_kernel_representation a m hm T hT x q

theorem kernel_integral_contraction (a : ℕ → ℝ) (m : ℕ) (hm : 0 < m)
    (T : ℝ≥0) (hT : 0 < T) (x : ℝ) (q : TestSpace terminalLevels (frequency a)) :
    ‖∫ y, (HigherHeatSignedLaws.realKernel m hm T hT y : ℂ) *
      realize terminalLevels (frequency a) q (shiftedLine x y)‖ ≤ ‖q‖ := by
  rw [← heat_kernel_representation a m hm T hT x q]
  exact (test_bound terminalLevels (frequency a) _ (line x)).trans
    (evolution_bound terminalLevels (frequency a) m hm T q)

end OperatorDerivativeRewrite.Foundation.FourierPathTerminalKernels
