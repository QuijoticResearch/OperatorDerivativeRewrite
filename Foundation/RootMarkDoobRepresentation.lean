import Foundation.RootMarkStochasticIntegral

/-! A constructive three-channel Doob representation on the actual finite-prefix source. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
namespace OperatorDerivativeRewrite.Foundation.RootMarkDoobRepresentation
open RootMarkStochasticIntegral
open MarkedRootRenewalProcess (MarkSample marks)
open RootRenewalWalkMarginal (initialSegment)
open ComplexFourthRootNoise (noise)

def kernel (F : Coefficients) (n : ℕ) (ξ : ComplexFourthRootWalk.Sample n) (k : Fin 4) : ℂ :=
  F (n+1) (Fin.snoc ξ k)

def channelCoefficients (a : ℝ) (F : Coefficients) (r : Fin 3) : Coefficients :=
  fun n ξ => ComplexRootMarkRepresentation.coefficient a (kernel F n ξ) r

def driftCoefficient (F : Coefficients) : Coefficients :=
  fun n ξ => (∫ k, kernel F n ξ k ∂ComplexFourthRootNoise.probability)-F n ξ

def observable (F : Coefficients) (n : ℕ) (η : MarkSample) : ℂ := F n (initialSegment n η)

theorem prefix_append (n : ℕ) (η : MarkSample) :
    Fin.snoc (initialSegment n η) (η n) = initialSegment (n+1) η := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [initialSegment]
  · simp [initialSegment]

theorem step_channels (a : ℝ) (ha : a ≠ 0) (F : Coefficients) (n : ℕ) (η : MarkSample) :
    observable F (n+1) η-observable F n η = driftCoefficient F n (initialSegment n η)+
      increment a 0 (channelCoefficients a F 0) n η+
      increment a 1 (channelCoefficients a F 1) n η+
      increment a 2 (channelCoefficients a F 2) n η := by
  have he := ComplexRootMarkRepresentation.centered_representation a ha
    (kernel F n (initialSegment n η)) (η n)
  have hv : kernel F n (initialSegment n η) (η n) = F (n+1) (initialSegment (n+1) η) := by
    rw [kernel, prefix_append]
  rw [hv] at he
  simp only [observable, driftCoefficient, increment, channelCoefficients, freshPower,
    Fin.val_zero, Fin.val_one, Fin.val_two, zero_add, Nat.reduceAdd, pow_one]
  linear_combination he

def driftSum (F : Coefficients) (n : ℕ) (η : MarkSample) : ℂ :=
  ∑ j ∈ Finset.range n, driftCoefficient F j (initialSegment j η)

def compensated (F : Coefficients) (n : ℕ) (η : MarkSample) : ℂ :=
  observable F n η-observable F 0 η-driftSum F n η

theorem compensated_representation (a : ℝ) (ha : a ≠ 0) (F : Coefficients) :
    compensated F = fun n η =>
      stochasticIntegral a 0 (channelCoefficients a F 0) n η+
      stochasticIntegral a 1 (channelCoefficients a F 1) n η+
      stochasticIntegral a 2 (channelCoefficients a F 2) n η := by
  funext n η
  unfold compensated driftSum stochasticIntegral
  rw [← Finset.sum_range_sub (fun j => observable F j η) n]
  simp_rw [step_channels a ha F]
  simp only [Finset.sum_add_distrib]
  ring

theorem compensated_martingale (a : ℝ) (ha : a ≠ 0) (F : Coefficients) :
    Martingale (compensated F) history marks := by
  rw [compensated_representation a ha F]
  have he : (fun n η =>
      stochasticIntegral a 0 (channelCoefficients a F 0) n η+
      stochasticIntegral a 1 (channelCoefficients a F 1) n η+
      stochasticIntegral a 2 (channelCoefficients a F 2) n η) =
      stochasticIntegral a 0 (channelCoefficients a F 0)+
      stochasticIntegral a 1 (channelCoefficients a F 1)+
      stochasticIntegral a 2 (channelCoefficients a F 2) := rfl
  rw [he]
  exact ((stochasticIntegral_martingale a 0 (channelCoefficients a F 0)).add
    (stochasticIntegral_martingale a 1 (channelCoefficients a F 1))).add
    (stochasticIntegral_martingale a 2 (channelCoefficients a F 2))

end OperatorDerivativeRewrite.Foundation.RootMarkDoobRepresentation
