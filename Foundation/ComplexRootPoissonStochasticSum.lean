import Foundation.ComplexRootPoissonDynkinMartingale
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-! Genuine discrete stochastic integrals against the compensated complex-root gains. -/
noncomputable section
open MeasureTheory ProbabilityTheory Preorder Finset
open scoped NNReal BoundedContinuousFunction
namespace OperatorDerivativeRewrite.Foundation.ComplexRootPoissonStochasticSum
open ComplexRootPoissonTrajectory ComplexRootPoissonSemigroup
open ComplexRootPoissonConditionalCalculus ComplexRootPoissonCompensation
open ComplexRootPoissonDynkinMartingale

def stochasticSum (a : ℝ) (δ : ℝ≥0) (f : ComplexRootTransitionOperator.Test)
    (H : ℕ → Sample → ℂ) (n : ℕ) (ω : Sample) : ℂ :=
  ∑ i ∈ range n, H i ω * gain a δ f i ω

variable (a : ℝ) (δ : ℝ≥0) (f : ComplexRootTransitionOperator.Test)
  (H : ℕ → Sample → ℂ) (C : ℝ)
  (hH : ∀ n, StronglyMeasurable[filtration n] (H n))
  (hC : ∀ n ω, ‖H n ω‖ ≤ C)

include hH hC

theorem weighted_gain_integrable (n : ℕ) :
    Integrable (fun ω => H n ω * gain a δ f n ω) (law a δ) :=
  (gain_integrable a δ f n).bdd_mul
    ((hH n).mono (filtration.le n)).aestronglyMeasurable
    (Filter.Eventually.of_forall (hC n))

theorem weighted_gain_conditional_zero (n : ℕ) :
    (law a δ)[fun ω => H n ω * gain a δ f n ω | filtration n] =ᵐ[law a δ] 0 := by
  have he := condExp_bilin_of_aestronglyMeasurable_left
    (ContinuousLinearMap.mul ℝ ℂ) (hH n).aestronglyMeasurable
    (weighted_gain_integrable a δ f H C hH hC n) (gain_integrable a δ f n)
  have hz := gain_conditional_zero a δ f n
  rw [← filtration_eq_past] at hz
  filter_upwards [he, hz] with ω he hz
  change _ = (0 : ℂ)
  calc
    _ = H n ω * (law a δ)[gain a δ f n | filtration n] ω := he
    _ = 0 := by simp only [hz, Pi.zero_apply, mul_zero]

theorem stochasticSum_integrable (n : ℕ) :
    Integrable (stochasticSum a δ f H n) (law a δ) := by
  exact integrable_finsetSum _ (fun i _ => weighted_gain_integrable a δ f H C hH hC i)

omit C hC in
theorem stochasticSum_adapted : StronglyAdapted filtration (stochasticSum a δ f H) := by
  intro n
  apply Finset.stronglyMeasurable_fun_sum
  intro i hi
  have hin : i+1 ≤ n := mem_range.mp hi
  have hi' : i ≤ n := le_trans (Nat.le_succ i) hin
  exact ((hH i).mono (filtration.mono hi')).mul
    (((observable_adapted f (i+1)).mono (filtration.mono hin)).sub
      ((observable_adapted (transition a δ f) i).mono (filtration.mono hi')))

omit C hH hC in
theorem stochasticSum_successor (n : ℕ) (ω : Sample) :
    stochasticSum a δ f H (n+1) ω - stochasticSum a δ f H n ω =
      H n ω * gain a δ f n ω := by
  simp only [stochasticSum, Finset.sum_range_succ]
  abel

theorem stochasticSum_martingale :
    Martingale (stochasticSum a δ f H) filtration (law a δ) := by
  apply martingale_of_condExp_sub_eq_zero_nat
    (stochasticSum_adapted a δ f H hH)
    (fun n => stochasticSum_integrable a δ f H C hH hC n)
  intro n
  have he : stochasticSum a δ f H (n+1) - stochasticSum a δ f H n =
      (fun ω => H n ω * gain a δ f n ω) := by
    funext ω
    exact stochasticSum_successor a δ f H n ω
  rw [he]
  exact weighted_gain_conditional_zero a δ f H C hH hC n

end OperatorDerivativeRewrite.Foundation.ComplexRootPoissonStochasticSum
