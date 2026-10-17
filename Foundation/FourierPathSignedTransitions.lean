import Foundation.FourierPathPointEquivalence

/-! Actual signed transitions and Chapman--Kolmogorov on complete point Fourier spaces. -/
noncomputable section
open MeasureTheory
open scoped NNReal Topology BoundedContinuousFunction
namespace OperatorDerivativeRewrite.Foundation.FourierPathSignedTransitions
open HigherHeatDyadicLaws HigherHeatContinuousCylinders HigherHeatFourierBanach
open HigherHeatFourierPathSemigroup FourierPathStopping FourierPathTerminalKernels
open FourierPathBackwardOperators FourierPathPointEquivalence FourierPathDictionaryTransport

abbrev Observation := (n : ℕ) × Fin (gridSize n)

abbrev Point (a : ℕ → ℝ) (o : Observation) :=
  TestSpace (pointLevels o.1) (pointFrequency o.1 o.2 a)

def time (o : Observation) : ℝ≥0 := stoppingTime o.1 o.2

def statePath (o : Observation) (x : ℝ) : Path := inverseMap o.1 o.2 (line x)

theorem statePath_coordinate (o : Observation) (x : ℝ) :
    (statePath o x).val (sampleTime o.1 o.2) = x := by
  simp only [statePath, inverseMap, line_apply, mul_one,
    div_mul_cancel₀ _ (sampleTime_pos o.1 o.2).ne']

def transition (a : ℕ → ℝ) (m : ℕ) (hm : 0 < m) (source target : Observation) (T : ℝ≥0) :
    Point a source →L[ℂ] Point a target :=
  (backward target.1 target.2 a m hm T).comp (reverseTransport source.1 source.2 a)

theorem transition_bound (a : ℕ → ℝ) (m : ℕ) (hm : 0 < m)
    (source target : Observation) (T : ℝ≥0) (q : Point a source) :
    ‖transition a m hm source target T q‖ ≤ ‖q‖ := by
  apply (backward_bound target.1 target.2 a m hm T _).trans
  exact transport_bound (pointLevels source.1) terminalLevels
    (pointFrequency source.1 source.2 a) (frequency a) (inverseMap source.1 source.2)
    (inverse_relation source.1 source.2 a) q

theorem transition_zero (a : ℕ → ℝ) (m : ℕ) (hm : 0 < m) (o : Observation) (q : Point a o) :
    transition a m hm o o 0 q = q := by
  change backward o.1 o.2 a m hm 0 (reverseTransport o.1 o.2 a q) = q
  rw [backward_zero, forward_reverse]

theorem transition_tower (a : ℕ → ℝ) (m : ℕ) (hm : 0 < m) (A B C : Observation)
    (S T : ℝ≥0) (q : Point a C) :
    transition a m hm B A S (transition a m hm C B T q) =
      transition a m hm C A (S+T) q := by
  change pointTransport A.1 A.2 a
    (evolution terminalLevels (frequency a) m hm S
      (reverseTransport B.1 B.2 a
        (pointTransport B.1 B.2 a
          (evolution terminalLevels (frequency a) m hm T (reverseTransport C.1 C.2 a q))))) = _
  rw [reverse_forward, evolution_add]
  rfl

theorem transition_signed (a : ℕ → ℝ) (m : ℕ) (hm : 0 < m)
    (source target : Observation) (T : ℝ≥0) (hT : 0 < T) (q : Point a source) (path : Path) :
    realize (pointLevels target.1) (pointFrequency target.1 target.2 a)
      (transition a m hm source target T q) path =
        ∫ᵛ y, realize (pointLevels source.1) (pointFrequency source.1 source.2 a) q
          (statePath source (path.val (sampleTime target.1 target.2) + y))
          ∂<•HigherHeatSignedLaws.law m hm T hT := by
  change realize (pointLevels target.1) (pointFrequency target.1 target.2 a)
    (backward target.1 target.2 a m hm T (reverseTransport source.1 source.2 a q)) path = _
  rw [backward_signed target.1 target.2 a m hm T hT _ path]
  apply congrArg (fun f : ℝ → ℂ => ∫ᵛ y, f y ∂<•HigherHeatSignedLaws.law m hm T hT)
  funext y
  exact reverse_realize source.1 source.2 a q _

theorem transition_kernel (a : ℕ → ℝ) (m : ℕ) (hm : 0 < m)
    (source target : Observation) (T : ℝ≥0) (hT : 0 < T) (q : Point a source) (path : Path) :
    realize (pointLevels target.1) (pointFrequency target.1 target.2 a)
      (transition a m hm source target T q) path =
        ∫ y, (HigherHeatSignedLaws.realKernel m hm T hT y : ℂ) *
          realize (pointLevels source.1) (pointFrequency source.1 source.2 a) q
            (statePath source (path.val (sampleTime target.1 target.2) + y)) := by
  change realize (pointLevels target.1) (pointFrequency target.1 target.2 a)
    (backward target.1 target.2 a m hm T (reverseTransport source.1 source.2 a q)) path = _
  rw [backward_kernel target.1 target.2 a m hm T hT _ path]
  apply congrArg (fun f : ℝ → ℂ => ∫ y, f y)
  funext y
  rw [reverse_realize]
  rfl

def dated (a : ℕ → ℝ) (m : ℕ) (hm : 0 < m) (source target : Observation) :
    Point a source →L[ℂ] Point a target :=
  transition a m hm source target (time source - time target)

theorem dated_tower (a : ℕ → ℝ) (m : ℕ) (hm : 0 < m) (A B C : Observation)
    (hAB : time A ≤ time B) (hBC : time B ≤ time C) (q : Point a C) :
    dated a m hm B A (dated a m hm C B q) = dated a m hm C A q := by
  unfold dated
  rw [transition_tower, add_comm (time B - time A), tsub_add_tsub_cancel hBC hAB]

end OperatorDerivativeRewrite.Foundation.FourierPathSignedTransitions
