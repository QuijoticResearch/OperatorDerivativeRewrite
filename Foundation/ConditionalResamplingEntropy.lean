import Foundation.ConditionalResamplingKernel
import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-! Exact entropy accounting for a boundary-preserving conditional update.
The KL chain rule does not imply a strictly positive conditional dissipation fraction.
All divergences below are Mathlib's measure-theoretic `klDiv`, including infinity. -/
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal
namespace OperatorDerivativeRewrite.Foundation.ConditionalResamplingEntropy
open ConditionalResamplingKernel

variable {P E : Type*} [MeasurableSpace P] [MeasurableSpace E]
variable (K : Kernel P E) [IsMarkovKernel K]

theorem entropy_after_update (J : Measure (P × E)) [IsFiniteMeasure J]
    (τ : Measure P) [IsFiniteMeasure τ] :
    klDiv (update K ∘ₘ J) (τ ⊗ₘ K) = klDiv J.fst τ := by
  rw [update_law, klDiv_compProd_left]

theorem entropy_decomposition (π τ : Measure P) [IsFiniteMeasure π] [IsFiniteMeasure τ]
    (L : Kernel P E) [IsMarkovKernel L] :
    klDiv (π ⊗ₘ L) (τ ⊗ₘ K) =
      klDiv (update K ∘ₘ (π ⊗ₘ L)) (τ ⊗ₘ K) +
      klDiv (π ⊗ₘ L) (π ⊗ₘ K) := by
  rw [entropy_after_update, Measure.fst_compProd]
  exact klDiv_compProd_eq_add π τ L K

theorem entropy_decomposition_of_conditional (J : Measure (P × E)) [IsFiniteMeasure J]
    (τ : Measure P) [IsFiniteMeasure τ]
    (L : Kernel P E) [IsMarkovKernel L] [J.IsCondKernel L] :
    klDiv J (τ ⊗ₘ K) = klDiv (update K ∘ₘ J) (τ ⊗ₘ K) +
      klDiv J (J.fst ⊗ₘ K) := by
  have h := entropy_decomposition K J.fst τ L
  simpa only [Measure.disintegrate] using h

theorem stationary_entropy (π τ : Measure P) [IsFiniteMeasure π] [IsFiniteMeasure τ] :
    klDiv (update K ∘ₘ (π ⊗ₘ K)) (τ ⊗ₘ K) = klDiv (π ⊗ₘ K) (τ ⊗ₘ K) := by
  rw [every_boundary_stationary]

theorem stationary_conditional_entropy (π : Measure P) [IsFiniteMeasure π] :
    klDiv (π ⊗ₘ K) (π ⊗ₘ K) = 0 := klDiv_self _

theorem stationary_entropy_positive (π τ : Measure P)
    [IsFiniteMeasure π] [IsFiniteMeasure τ] (h : π ≠ τ) :
    0 < klDiv (π ⊗ₘ K) (τ ⊗ₘ K) := by
  rw [klDiv_compProd_left]
  exact bot_lt_iff_ne_bot.mpr (fun hz => h (klDiv_eq_zero_iff.mp hz))

theorem no_positive_dissipation_fraction (π τ : Measure P)
    [IsFiniteMeasure π] [IsFiniteMeasure τ] (h : π ≠ τ)
    (f : ℝ≥0∞) (hf : 0 < f) :
    ¬ f * klDiv (π ⊗ₘ K) (τ ⊗ₘ K) ≤ klDiv (π ⊗ₘ K) (π ⊗ₘ K) := by
  rw [klDiv_self]
  exact not_le_of_gt (bot_lt_iff_ne_bot.mpr
    (mul_ne_zero (ne_of_gt hf) (ne_of_gt (stationary_entropy_positive K π τ h))))

/-- A normalized, two-atom reference; the atoms may belong to any measurable space. -/
def binaryReference (a b : P) : Measure P :=
  (2 : ℝ≥0∞)⁻¹ • (Measure.dirac a + Measure.dirac b)

instance binaryReference_probability (a b : P) : IsProbabilityMeasure (binaryReference a b) := by
  constructor
  norm_num [binaryReference, Measure.smul_apply, Measure.add_apply]
  rw [← mul_two, ENNReal.inv_mul_cancel (by norm_num) (by norm_num)]

theorem dirac_ac_binaryReference (a b : P) : Measure.dirac a ≪ binaryReference a b := by
  apply (Measure.absolutelyContinuous_of_le
    (show Measure.dirac a ≤ Measure.dirac a + Measure.dirac b from
      Measure.le_add_right le_rfl)).smul_right
  norm_num

theorem dirac_ne_binaryReference [MeasurableSingletonClass P] (a b : P) (hab : a ≠ b) :
    Measure.dirac a ≠ binaryReference a b := by
  intro h
  have hh := congrArg (fun μ : Measure P => μ {b}) h
  norm_num [binaryReference, Measure.smul_apply, Measure.add_apply,
    Measure.dirac_apply', hab] at hh
  exact (ENNReal.inv_ne_zero.mpr (by norm_num)) hh.symm

theorem binary_entropy_finite [MeasurableSingletonClass P] (a b : P) :
    klDiv (Measure.dirac a ⊗ₘ K) (binaryReference a b ⊗ₘ K) ≠ ⊤ := by
  rw [klDiv_compProd_left]
  exact klDiv_ne_top (dirac_ac_binaryReference a b) (integrable_dirac (by finiteness))

theorem binary_entropy_positive [MeasurableSingletonClass P] (a b : P) (hab : a ≠ b) :
    0 < (klDiv (Measure.dirac a ⊗ₘ K) (binaryReference a b ⊗ₘ K)).toReal := by
  exact ENNReal.toReal_pos (ne_of_gt (stationary_entropy_positive K _ _
    (dirac_ne_binaryReference a b hab))) (binary_entropy_finite K a b)

/-- The unchanged entropy is finite and strictly positive, so a real contraction factor
strictly below one fails. This is an actual pair of probability measures, not a formal
choice of entropy variables. -/
theorem binary_no_strict_contraction [MeasurableSingletonClass P]
    (a b : P) (hab : a ≠ b) (q : ℝ) (hq : q < 1) :
    ¬ (klDiv (update K ∘ₘ (Measure.dirac a ⊗ₘ K)) (binaryReference a b ⊗ₘ K)).toReal ≤
      q * (klDiv (Measure.dirac a ⊗ₘ K) (binaryReference a b ⊗ₘ K)).toReal := by
  rw [stationary_entropy]
  have hp := binary_entropy_positive K a b hab
  nlinarith

theorem bool_counterexample (B : Kernel Bool E) [IsMarkovKernel B] (q : ℝ) (hq : q < 1) :
    ¬ (klDiv (update B ∘ₘ (Measure.dirac false ⊗ₘ B))
      (binaryReference false true ⊗ₘ B)).toReal ≤
      q * (klDiv (Measure.dirac false ⊗ₘ B) (binaryReference false true ⊗ₘ B)).toReal :=
  binary_no_strict_contraction B false true Bool.false_ne_true q hq

end OperatorDerivativeRewrite.Foundation.ConditionalResamplingEntropy
