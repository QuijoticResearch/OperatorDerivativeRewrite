import Foundation.ComplexFourthRootNoise
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Integral.Pi

/-! Genuine independent complex random walks and their holomorphic exponential transforms. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.ComplexFourthRootWalk
open ComplexFourthRootNoise

abbrev Sample (n : ℕ) := Fin n → Fin 4

def probability (n : ℕ) : Measure (Sample n) :=
  Measure.pi (fun _ => ComplexFourthRootNoise.probability)

instance probability_isProbability (n : ℕ) : IsProbabilityMeasure (probability n) := by
  unfold probability
  infer_instance

def increment (n : ℕ) (a : ℝ) (i : Fin n) (ω : Sample n) : ℂ := noise a (ω i)

def position (n : ℕ) (a : ℝ) (k : ℕ) (ω : Sample n) : ℂ :=
  ∑ i : Fin n, if i.val < k then increment n a i ω else 0

def terminal (n : ℕ) (a : ℝ) (ω : Sample n) : ℂ := ∑ i : Fin n, increment n a i ω

theorem terminal_measurable (n : ℕ) (a : ℝ) : Measurable (terminal n a) :=
  measurable_of_countable _

theorem position_measurable (n : ℕ) (a : ℝ) (k : ℕ) : Measurable (position n a k) :=
  measurable_of_countable _

theorem position_integrable (n : ℕ) (a : ℝ) (k : ℕ) :
    Integrable (position n a k) (probability n) := Integrable.of_finite

theorem position_zero (n : ℕ) (a : ℝ) (ω : Sample n) : position n a 0 ω = 0 := by
  simp [position]

theorem position_terminal (n : ℕ) (a : ℝ) (ω : Sample n) :
    position n a n ω = terminal n a ω := by simp [position, terminal]

theorem increments_independent (n : ℕ) (a : ℝ) :
    iIndepFun (increment n a) (probability n) :=
  iIndepFun_pi (fun _ => (noise_measurable a).aemeasurable)

theorem increment_mean (n : ℕ) (a : ℝ) (i : Fin n) :
    (∫ ω, increment n a i ω ∂probability n) = 0 := by
  change (∫ ω : Fin n → Fin 4, noise a (ω i)
    ∂Measure.pi (fun _ => ComplexFourthRootNoise.probability)) = 0
  rw [integral_comp_eval (μ := fun _ : Fin n => ComplexFourthRootNoise.probability)
    (i := i) (f := noise a) (noise_measurable a).aestronglyMeasurable, mean]

theorem terminal_mean (n : ℕ) (a : ℝ) :
    (∫ ω, terminal n a ω ∂probability n) = 0 := by
  unfold terminal
  rw [integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  simp only [increment_mean, Finset.sum_const_zero]

def law (n : ℕ) (a : ℝ) : Measure ℂ := (probability n).map (terminal n a)

instance law_isProbability (n : ℕ) (a : ℝ) : IsProbabilityMeasure (law n a) := by
  unfold law
  infer_instance

def stepTransform (a ξ : ℝ) : ℂ :=
  ∫ k, Complex.exp (Complex.I * (ξ : ℂ) * noise a k) ∂ComplexFourthRootNoise.probability

theorem terminal_transform (n : ℕ) (a ξ : ℝ) :
    (∫ ω, Complex.exp (Complex.I * (ξ : ℂ) * terminal n a ω) ∂probability n) =
      (stepTransform a ξ)^n := by
  unfold terminal
  simp only [Finset.mul_sum, Complex.exp_sum]
  rw [probability]
  have he := integral_fintype_prod_eq_prod
    (μ := fun _ : Fin n => ComplexFourthRootNoise.probability)
    (fun _ k => Complex.exp (Complex.I * (ξ : ℂ) * noise a k))
  simpa only [increment, stepTransform, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin] using he

end OperatorDerivativeRewrite.Foundation.ComplexFourthRootWalk
