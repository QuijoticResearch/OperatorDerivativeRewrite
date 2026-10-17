import Foundation.FourierPathBackwardOperators

/-! Actual isometric identification of complete point-frequency test spaces. -/
noncomputable section
open scoped NNReal Topology BoundedContinuousFunction
namespace OperatorDerivativeRewrite.Foundation.FourierPathPointEquivalence
open HigherHeatDyadicLaws HigherHeatContinuousCylinders HigherHeatFourierBanach
open FourierPathStopping FourierPathTerminalKernels FourierPathBackwardOperators
open FourierPathDictionaryTransport

def inverseMap (n : ℕ) (k : Fin (gridSize n)) (path : Path) : Path :=
  line (path.val 1 / sampleTime n k)

theorem inverse_relation (n : ℕ) (k : Fin (gridSize n)) (a : ℕ → ℝ)
    (i : ℕ) (path : Path) :
    characterTest terminalLevels (frequency a) i path =
      characterTest (pointLevels n) (pointFrequency n k a) i (inverseMap n k path) := by
  cases i with
  | zero => simp [characterTest, HigherHeatMixedFourierPaths.character,
      SignedDensityIntegral.configurationPhase, spectrumFrequency]
  | succ i =>
    rw [atom, point_atom]
    simp only [inverseMap, line_apply, div_mul_cancel₀ _ (sampleTime_pos n k).ne']

def reverseTransport (n : ℕ) (k : Fin (gridSize n)) (a : ℕ → ℝ) :
    TestSpace (pointLevels n) (pointFrequency n k a) →L[ℂ]
      TestSpace terminalLevels (frequency a) :=
  transport (pointLevels n) terminalLevels (pointFrequency n k a) (frequency a)
    (inverseMap n k) (inverse_relation n k a)

theorem reverse_realize (n : ℕ) (k : Fin (gridSize n)) (a : ℕ → ℝ)
    (q : TestSpace (pointLevels n) (pointFrequency n k a)) (path : Path) :
    realize terminalLevels (frequency a) (reverseTransport n k a q) path =
      realize (pointLevels n) (pointFrequency n k a) q (inverseMap n k path) :=
  realize_transport (pointLevels n) terminalLevels (pointFrequency n k a) (frequency a)
    (inverseMap n k) (inverse_relation n k a) q path

theorem reverse_forward (n : ℕ) (k : Fin (gridSize n)) (a : ℕ → ℝ)
    (q : TestSpace terminalLevels (frequency a)) :
    reverseTransport n k a (pointTransport n k a q) = q := by
  obtain ⟨b, rfl⟩ := (kernel terminalLevels (frequency a)).mkQ_surjective q
  rfl

theorem forward_reverse (n : ℕ) (k : Fin (gridSize n)) (a : ℕ → ℝ)
    (q : TestSpace (pointLevels n) (pointFrequency n k a)) :
    pointTransport n k a (reverseTransport n k a q) = q := by
  obtain ⟨b, rfl⟩ := (kernel (pointLevels n) (pointFrequency n k a)).mkQ_surjective q
  rfl

theorem pointTransport_norm (n : ℕ) (k : Fin (gridSize n)) (a : ℕ → ℝ)
    (q : TestSpace terminalLevels (frequency a)) : ‖pointTransport n k a q‖ = ‖q‖ := by
  apply le_antisymm
  · exact transport_bound terminalLevels (pointLevels n) (frequency a) (pointFrequency n k a)
      (pointMap n k) (point_relation n k a) q
  · have hh := transport_bound (pointLevels n) terminalLevels (pointFrequency n k a) (frequency a)
      (inverseMap n k) (inverse_relation n k a) (pointTransport n k a q)
    change ‖reverseTransport n k a (pointTransport n k a q)‖ ≤ _ at hh
    rw [reverse_forward] at hh
    exact hh

def equivalence (n : ℕ) (k : Fin (gridSize n)) (a : ℕ → ℝ) :
    TestSpace terminalLevels (frequency a) ≃ₗᵢ[ℂ]
      TestSpace (pointLevels n) (pointFrequency n k a) where
  toLinearEquiv :=
    { toLinearMap := (pointTransport n k a).toLinearMap
      invFun := reverseTransport n k a
      left_inv := reverse_forward n k a
      right_inv := forward_reverse n k a }
  norm_map' := pointTransport_norm n k a

end OperatorDerivativeRewrite.Foundation.FourierPathPointEquivalence
