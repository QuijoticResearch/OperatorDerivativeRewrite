import Foundation.FourierPathDictionaryTransport

/-! Actual signed future-increment integration and its required midpoint observable. -/
noncomputable section
open MeasureTheory
open scoped NNReal Topology BoundedContinuousFunction
namespace OperatorDerivativeRewrite.Foundation.FourierPathFutureIntegral
open HigherHeatSignedLaws HigherHeatCylinderFourier HigherHeatContinuousCylinders
open HigherHeatDyadicLaws
open HigherHeatFourierBanach FourierPathStopping HigherHeatFourierTranslations

theorem phase_add (ξ x y : ℝ) : phase ξ (x+y) = phase ξ x * phase ξ y := by
  unfold phase
  rw [add_mul, neg_add, AddChar.map_add_eq_mul, Circle.coe_mul]

theorem shifted_kernel_integrable (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (x ξ : ℝ) : Integrable (fun y => phase ξ (x+y) * (realKernel m hm T hT y : ℂ)) := by
  have he : (fun y => phase ξ (x+y) * (realKernel m hm T hT y : ℂ)) =
      fun y => phase ξ x * (phase ξ y * (realKernel m hm T hT y : ℂ)) := by
    funext y
    rw [phase_add, mul_assoc]
  rw [he]
  exact (kernel_phase_integrable m hm T hT ξ).const_mul _

theorem shifted_kernel_integral (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (x ξ : ℝ) : (∫ y, phase ξ (x+y) * (realKernel m hm T hT y : ℂ)) =
      phase ξ x * HigherHeatL2.symbol m T ξ := by
  simp_rw [phase_add, mul_assoc]
  rw [integral_const_mul, kernel_fourier]

theorem shifted_signed_integral (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (x ξ : ℝ) : (∫ᵛ y, phase ξ (x+y) ∂<•HigherHeatSignedLaws.law m hm T hT) =
      phase ξ x * HigherHeatL2.symbol m T ξ := by
  rw [HigherHeatSignedLaws.law, SignedDensityIntegral.integral_density volume _
    (realKernel m hm T hT).integrable (realKernel m hm T hT).continuous.measurable
    (fun y => phase ξ (x+y)) ((phase_continuous ξ).comp (continuous_const.add continuous_id)).measurable
    1 (fun y => (phase_norm ξ (x+y)).le)]
  have he : (fun y => realKernel m hm T hT y • phase ξ (x+y)) =
      fun y => phase ξ (x+y) * (realKernel m hm T hT y : ℂ) := by
    funext y
    simp only [Complex.real_smul, mul_comm]
  rw [he, shifted_kernel_integral]

def futureValue (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (path : Path) : ℂ :=
  ∫ᵛ y, phase 1 (path.val (1/2) + y) ∂<•HigherHeatSignedLaws.law m hm T hT

theorem futureValue_eq (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (path : Path) :
    futureValue m hm T hT path =
      HigherHeatL2.symbol m T 1 *
        realize terminalLevels terminalFrequency (generator terminalLevels terminalFrequency 1)
          (stop (1/2) path) := by
  rw [futureValue, shifted_signed_integral, realize_generator, terminal_character]
  simp only [stop_apply]
  norm_num [phase, mul_comm]

theorem symbol_nonzero (m : ℕ) (T : ℝ≥0) (ξ : ℝ) : HigherHeatL2.symbol m T ξ ≠ 0 := by
  simp only [HigherHeatL2.symbol, ne_eq, Complex.ofReal_eq_zero]
  exact Real.exp_ne_zero _

theorem futureValue_not_terminal (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) :
    ¬ ∃ q : TestSpace terminalLevels terminalFrequency,
      ∀ path, realize terminalLevels terminalFrequency q path = futureValue m hm T hT path := by
  rintro ⟨q, hq⟩
  have he := terminal_depends_endpoint zeroPath arch (by norm_num [zeroPath, arch]) q
  rw [hq, hq, futureValue_eq, futureValue_eq,
    stopped_generator_zero, stopped_generator_arch, mul_one, mul_neg_one] at he
  have hz : HigherHeatL2.symbol m T 1 = 0 := by
    have hh := congrArg Complex.re he
    have hi := congrArg Complex.im he
    apply Complex.ext <;> simp only [Complex.zero_re, Complex.zero_im]
    · simp only [Complex.neg_re] at hh
      linarith
    · simp only [Complex.neg_im] at hi
      linarith
  exact symbol_nonzero m T 1 hz

def midpointIndex : Fin (gridSize 1) := ⟨0, by decide⟩

def midpointLevels : ℕ → ℕ := fun _ => 1

def midpointFrequency : (i : ℕ) → Grid (midpointLevels i) :=
  fun _ => Pi.single midpointIndex 1

theorem midpoint_character (i : ℕ) (path : Path) :
    characterTest midpointLevels midpointFrequency (i+1) path = phase 1 (path.val (1/2)) := by
  change SignedDensityIntegral.configurationPhase
    (Pi.single midpointIndex 1 : Grid 1) (sample 1 path) = _
  have he : (∑ j : Fin (gridSize 1),
      (Pi.single midpointIndex (1 : ℝ) : Grid 1) j * sample 1 path j) =
      path.val (1/2) := by
    rw [Finset.sum_eq_single midpointIndex]
    · simp only [Pi.single_eq_same, one_mul]
      change path.val (sampleTime 1 midpointIndex) = path.val (1/2)
      congr 1
      norm_num [sampleTime, time, duration, gridSize, midpointIndex]
    · intro j _ hj
      rw [Pi.single_eq_of_ne hj, zero_mul]
    · simp
  unfold SignedDensityIntegral.configurationPhase phase
  rw [he, mul_one]

def futureTest (m : ℕ) (T : ℝ≥0) : TestSpace midpointLevels midpointFrequency :=
  HigherHeatL2.symbol m T 1 • generator midpointLevels midpointFrequency 1

theorem futureTest_realize (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (path : Path) :
    realize midpointLevels midpointFrequency (futureTest m T) path = futureValue m hm T hT path := by
  rw [futureTest, map_smul, BoundedContinuousFunction.smul_apply, realize_generator,
    midpoint_character, futureValue, shifted_signed_integral]
  exact mul_comm _ _

end OperatorDerivativeRewrite.Foundation.FourierPathFutureIntegral
