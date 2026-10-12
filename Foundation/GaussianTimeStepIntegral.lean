import Foundation.GaussianTimeProcess
import Foundation.GaussianPredictableStep

/-!
# Actual random predictable integrals on the constructed Gaussian time model

The finite increment sum is placed in the existing scalar Gaussian L² space.
Its coefficients may be arbitrary square-integrable measurable functions of
the past. This module does not assert completion of the predictable space.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace OperatorDerivativeRewrite.Foundation.GaussianTimeProcess

open InfiniteGaussian GaussianPredictableStep

/-- The concrete one-step identity for every raw-natural-filtration L² coefficient. -/
theorem timeStep_integrable_sq_and_isometry {s t : ℝ≥0} (hst : s ≤ t)
    {A : SampleSpace → ℝ} (hAm : Measurable[naturalFiltration s] A)
    (hA : MemLp A 2 gaussianProduct) :
    Integrable (fun ω => (A ω * (process t ω - process s ω)) ^ 2) gaussianProduct ∧
      (∫ ω, (A ω * (process t ω - process s ω)) ^ 2 ∂gaussianProduct) =
        ((t : ℝ) - s) * ∫ ω, A ω ^ 2 ∂gaussianProduct :=
  integral_natural_step_sq process_isPreBrownian
    (fun t => (process_stronglyMeasurable t).measurable) hst hAm hA

/-- The actual L² class of a random predictable finite increment sum. -/
def partitionIntegralL2 {n : ℕ} (τ : Fin (n + 1) → ℝ≥0) (hτ : Monotone τ)
    (a : (i : Fin n) → (Set.Iic (τ i.castSucc) → ℝ) → ℝ)
    (ha : ∀ i, Measurable (a i))
    (hA : ∀ i, MemLp (pastCoefficient process (τ i.castSucc) (a i)) 2 gaussianProduct) :
    GaussianL2 :=
  (partitionIntegral_memLp process_isPreBrownian hτ ha hA).toLp _

theorem partitionIntegralL2_coeFn {n : ℕ} (τ : Fin (n + 1) → ℝ≥0) (hτ : Monotone τ)
    (a : (i : Fin n) → (Set.Iic (τ i.castSucc) → ℝ) → ℝ)
    (ha : ∀ i, Measurable (a i))
    (hA : ∀ i, MemLp (pastCoefficient process (τ i.castSucc) (a i)) 2 gaussianProduct) :
    partitionIntegralL2 τ hτ a ha hA =ᵐ[gaussianProduct] partitionIntegral process τ a :=
  MemLp.coeFn_toLp _

/-- Centering of the actual scalar Gaussian L² integral class. -/
theorem partitionIntegralL2_centered {n : ℕ} (τ : Fin (n + 1) → ℝ≥0) (hτ : Monotone τ)
    (a : (i : Fin n) → (Set.Iic (τ i.castSucc) → ℝ) → ℝ)
    (ha : ∀ i, Measurable (a i))
    (hA : ∀ i, MemLp (pastCoefficient process (τ i.castSucc) (a i)) 2 gaussianProduct) :
    (∫ ω, partitionIntegralL2 τ hτ a ha hA ω ∂gaussianProduct) = 0 := by
  rw [integral_congr_ae (partitionIntegralL2_coeFn τ hτ a ha hA)]
  exact integral_partitionIntegral process_isPreBrownian hτ ha hA

/-- Actual Itô isometry with elapsed-time weights and arbitrary L² past coefficients. -/
theorem partitionIntegralL2_norm_sq {n : ℕ} (τ : Fin (n + 1) → ℝ≥0) (hτ : Monotone τ)
    (a : (i : Fin n) → (Set.Iic (τ i.castSucc) → ℝ) → ℝ)
    (ha : ∀ i, Measurable (a i))
    (hA : ∀ i, MemLp (pastCoefficient process (τ i.castSucc) (a i)) 2 gaussianProduct) :
    ‖partitionIntegralL2 τ hτ a ha hA‖ ^ 2 =
      ∑ i, ((τ i.succ : ℝ) - τ i.castSucc) *
        ∫ ω, pastCoefficient process (τ i.castSucc) (a i) ω ^ 2 ∂gaussianProduct := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  have he : (∫ ω, inner ℝ (partitionIntegralL2 τ hτ a ha hA ω)
      (partitionIntegralL2 τ hτ a ha hA ω) ∂gaussianProduct) =
      ∫ ω, partitionIntegral process τ a ω ^ 2 ∂gaussianProduct := by
    apply integral_congr_ae
    filter_upwards [partitionIntegralL2_coeFn τ hτ a ha hA] with ω hω
    simp [hω]
  rw [he]
  exact integral_partitionIntegral_sq process_isPreBrownian hτ ha hA

/-- Every actual step integrand is strongly predictable for this raw natural filtration. -/
theorem timeStep_stronglyPredictable (s t : ℝ≥0)
    {a : (Set.Iic s → ℝ) → ℝ} (ha : Measurable a) :
    IsStronglyPredictable naturalFiltration (stepProcess process s t a) :=
  stepProcess_stronglyPredictable (fun t => (process_stronglyMeasurable t).measurable) s t ha

theorem timePartition_stronglyPredictable {n : ℕ} (τ : Fin (n + 1) → ℝ≥0)
    {a : (i : Fin n) → (Set.Iic (τ i.castSucc) → ℝ) → ℝ}
    (ha : ∀ i, Measurable (a i)) :
    IsStronglyPredictable naturalFiltration (partitionProcess process τ a) :=
  partitionProcess_stronglyPredictable
    (fun t => (process_stronglyMeasurable t).measurable) τ ha

/-- Almost-everywhere changes of the past coefficients preserve the integral class.
This statement fixes the partition; cross-partition refinement is a later obligation. -/
theorem partitionIntegralL2_congr {n : ℕ} (τ : Fin (n + 1) → ℝ≥0) (hτ : Monotone τ)
    (a b : (i : Fin n) → (Set.Iic (τ i.castSucc) → ℝ) → ℝ)
    (ha : ∀ i, Measurable (a i)) (hb : ∀ i, Measurable (b i))
    (hA : ∀ i, MemLp (pastCoefficient process (τ i.castSucc) (a i)) 2 gaussianProduct)
    (hB : ∀ i, MemLp (pastCoefficient process (τ i.castSucc) (b i)) 2 gaussianProduct)
    (hab : ∀ i, pastCoefficient process (τ i.castSucc) (a i) =ᵐ[gaussianProduct]
      pastCoefficient process (τ i.castSucc) (b i)) :
    partitionIntegralL2 τ hτ a ha hA = partitionIntegralL2 τ hτ b hb hB := by
  apply Lp.ext
  filter_upwards [partitionIntegralL2_coeFn τ hτ a ha hA,
    partitionIntegralL2_coeFn τ hτ b hb hB, Filter.eventually_all.2 hab]
      with ω hωa hωb hω
  rw [hωa, hωb]
  apply Finset.sum_congr rfl
  intro i _
  simp only [stepIntegral, hω i]

end OperatorDerivativeRewrite.Foundation.GaussianTimeProcess
