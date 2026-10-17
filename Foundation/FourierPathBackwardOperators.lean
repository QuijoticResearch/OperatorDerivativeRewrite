import Foundation.FourierPathTerminalKernels

/-! Genuine contractive signed backward operators into dyadic point Fourier completions. -/
noncomputable section
open MeasureTheory
open scoped NNReal Topology BoundedContinuousFunction
namespace OperatorDerivativeRewrite.Foundation.FourierPathBackwardOperators
open HigherHeatDyadicLaws HigherHeatContinuousCylinders HigherHeatFourierBanach
open HigherHeatCylinderFourier HigherHeatFourierPathSemigroup FourierPathStopping
open FourierPathTerminalKernels FourierPathDictionaryTransport

def pointLevels (n : ℕ) : ℕ → ℕ := fun _ => n

def pointFrequency (n : ℕ) (k : Fin (gridSize n)) (a : ℕ → ℝ) :
    (i : ℕ) → Grid (pointLevels n i) := fun i => Pi.single k (a i)

theorem point_atom (n : ℕ) (k : Fin (gridSize n)) (a : ℕ → ℝ) (i : ℕ) (path : Path) :
    characterTest (pointLevels n) (pointFrequency n k a) (i+1) path =
      phase (a i) (path.val (sampleTime n k)) := by
  change SignedDensityIntegral.configurationPhase (Pi.single k (a i) : Grid n)
    (sample n path) = _
  have he : (∑ j : Fin (gridSize n), (Pi.single k (a i) : Grid n) j * sample n path j) =
      a i * sample n path k := by
    rw [Finset.sum_eq_single k]
    · rw [Pi.single_eq_same]
    · intro j _ hj
      rw [Pi.single_eq_of_ne hj, zero_mul]
    · simp
  unfold SignedDensityIntegral.configurationPhase phase
  rw [he]
  exact congrArg (fun r : ℝ => (Real.fourierChar (-r) : ℂ))
    (mul_comm (a i) (path.val (sampleTime n k)))

def pointMap (n : ℕ) (k : Fin (gridSize n)) (path : Path) : Path :=
  line (path.val (sampleTime n k))

theorem pointMap_continuous (n : ℕ) (k : Fin (gridSize n)) : Continuous (pointMap n k) :=
  line_continuous.comp (coordinate_continuous _)

theorem point_relation (n : ℕ) (k : Fin (gridSize n)) (a : ℕ → ℝ) (i : ℕ) (path : Path) :
    characterTest (pointLevels n) (pointFrequency n k a) i path =
      characterTest terminalLevels (frequency a) i (pointMap n k path) := by
  cases i with
  | zero => simp [characterTest, HigherHeatMixedFourierPaths.character,
      SignedDensityIntegral.configurationPhase, spectrumFrequency]
  | succ i =>
    rw [point_atom, atom]
    simp only [pointMap, line_apply, mul_one]

def pointTransport (n : ℕ) (k : Fin (gridSize n)) (a : ℕ → ℝ) :
    TestSpace terminalLevels (frequency a) →L[ℂ]
      TestSpace (pointLevels n) (pointFrequency n k a) :=
  transport terminalLevels (pointLevels n) (frequency a) (pointFrequency n k a)
    (pointMap n k) (point_relation n k a)

def backward (n : ℕ) (k : Fin (gridSize n)) (a : ℕ → ℝ) (m : ℕ) (hm : 0 < m) (T : ℝ≥0) :
    TestSpace terminalLevels (frequency a) →L[ℂ]
      TestSpace (pointLevels n) (pointFrequency n k a) :=
  (pointTransport n k a).comp (evolution terminalLevels (frequency a) m hm T)

theorem backward_bound (n : ℕ) (k : Fin (gridSize n)) (a : ℕ → ℝ) (m : ℕ) (hm : 0 < m)
    (T : ℝ≥0) (q : TestSpace terminalLevels (frequency a)) :
    ‖backward n k a m hm T q‖ ≤ ‖q‖ :=
  (transport_bound terminalLevels (pointLevels n) (frequency a) (pointFrequency n k a)
    (pointMap n k) (point_relation n k a) _).trans
    (evolution_bound terminalLevels (frequency a) m hm T q)

theorem backward_norm (n : ℕ) (k : Fin (gridSize n)) (a : ℕ → ℝ) (m : ℕ) (hm : 0 < m)
    (T : ℝ≥0) : ‖backward n k a m hm T‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro q
  simpa only [one_mul] using backward_bound n k a m hm T q

theorem backward_zero (n : ℕ) (k : Fin (gridSize n)) (a : ℕ → ℝ) (m : ℕ) (hm : 0 < m)
    (q : TestSpace terminalLevels (frequency a)) :
    backward n k a m hm 0 q = pointTransport n k a q := by
  change pointTransport n k a (evolution terminalLevels (frequency a) m hm 0 q) = _
  rw [evolution_zero]

theorem backward_kernel (n : ℕ) (k : Fin (gridSize n)) (a : ℕ → ℝ) (m : ℕ) (hm : 0 < m)
    (T : ℝ≥0) (hT : 0 < T) (q : TestSpace terminalLevels (frequency a)) (path : Path) :
    realize (pointLevels n) (pointFrequency n k a) (backward n k a m hm T q) path =
      ∫ y, (HigherHeatSignedLaws.realKernel m hm T hT y : ℂ) *
        realize terminalLevels (frequency a) q (shiftedLine (path.val (sampleTime n k)) y) := by
  change realize (pointLevels n) (pointFrequency n k a)
    (pointTransport n k a (evolution terminalLevels (frequency a) m hm T q)) path = _
  rw [pointTransport, realize_transport]
  exact heat_kernel_representation a m hm T hT _ q

theorem backward_signed (n : ℕ) (k : Fin (gridSize n)) (a : ℕ → ℝ) (m : ℕ) (hm : 0 < m)
    (T : ℝ≥0) (hT : 0 < T) (q : TestSpace terminalLevels (frequency a)) (path : Path) :
    realize (pointLevels n) (pointFrequency n k a) (backward n k a m hm T q) path =
      ∫ᵛ y, realize terminalLevels (frequency a) q (shiftedLine (path.val (sampleTime n k)) y)
        ∂<•HigherHeatSignedLaws.law m hm T hT := by
  change realize (pointLevels n) (pointFrequency n k a)
    (pointTransport n k a (evolution terminalLevels (frequency a) m hm T q)) path = _
  rw [pointTransport, realize_transport]
  exact heat_signed_representation a m hm T hT _ q

theorem backward_source_heat (n : ℕ) (k : Fin (gridSize n)) (a : ℕ → ℝ) (m : ℕ)
    (hm : 0 < m) (S T : ℝ≥0) (q : TestSpace terminalLevels (frequency a)) :
    backward n k a m hm S (evolution terminalLevels (frequency a) m hm T q) =
      backward n k a m hm (S+T) q := by
  change pointTransport n k a
    (evolution terminalLevels (frequency a) m hm S
      (evolution terminalLevels (frequency a) m hm T q)) = _
  rw [evolution_add]
  rfl

end OperatorDerivativeRewrite.Foundation.FourierPathBackwardOperators
