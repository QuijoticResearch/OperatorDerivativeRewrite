import Foundation.GaussianTimeFieldNorm
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Actual time-probability L² fields

This module realizes finite time-step fields in Lebesgue-time times Gaussian
probability L². Integrability follows from separate square integrability and
product integration; the norm agrees with that of the embedded coefficient-space
field. No predictable-space completion or density statement is assumed.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace OperatorDerivativeRewrite.Foundation.GaussianTimeProductL2

open InfiniteGaussian GaussianTimeHilbert GaussianTimeDivergence GaussianTimeFieldNorm
open SeparableHilbertEmbedding
attribute [local instance] timeHilbert_secondCountable

/-- Actual product measure of real Lebesgue time and the constructed Gaussian probability. -/
abbrev timeProbability := (volume : Measure ℝ).prod gaussianProduct

abbrev TimeProbabilityL2 := Lp ℝ 2 timeProbability

theorem productTensor_stronglyMeasurable (h : TimeHilbert) (A : GaussianL2) :
    StronglyMeasurable (fun z : ℝ × SampleSpace => h z.1 * A z.2) :=
  ((Lp.stronglyMeasurable h).comp_measurable measurable_fst).mul
    ((Lp.stronglyMeasurable A).comp_measurable measurable_snd)

/-- A genuine product-measure L² estimate, proved through square integrability and Tonelli. -/
theorem productTensor_memLp (h : TimeHilbert) (A : GaussianL2) :
    MemLp (fun z : ℝ × SampleSpace => h z.1 * A z.2) 2 timeProbability := by
  apply (memLp_two_iff_integrable_sq (productTensor_stronglyMeasurable h A).aestronglyMeasurable).2
  simpa only [mul_pow] using (Lp.memLp h).integrable_sq.mul_prod (Lp.memLp A).integrable_sq

/-- The actual L² class of a scalar tensor product. -/
def productTensor (h : TimeHilbert) (A : GaussianL2) : TimeProbabilityL2 :=
  (productTensor_memLp h A).toLp _

theorem productTensor_coeFn (h : TimeHilbert) (A : GaussianL2) :
    productTensor h A =ᵐ[timeProbability] fun z => h z.1 * A z.2 :=
  MemLp.coeFn_toLp _

/-- Product-measure integration factors the actual L² pairings. -/
theorem productTensor_inner (h k : TimeHilbert) (A B : GaussianL2) :
    inner ℝ (productTensor h A) (productTensor k B) = inner ℝ h k * inner ℝ A B := by
  rw [L2_inner_eq_integral]
  calc
    _ = ∫ z : ℝ × SampleSpace, inner ℝ (h z.1) (k z.1) *
        inner ℝ (A z.2) (B z.2) ∂timeProbability := by
      apply integral_congr_ae
      filter_upwards [productTensor_coeFn h A, productTensor_coeFn k B] with z hA hB
      simp only [hA, hB, Real.inner_apply]
      ring
    _ = _ := by
      unfold timeProbability
      rw [integral_prod_mul (fun x : ℝ => inner ℝ (h x) (k x))
        (fun ω : SampleSpace => inner ℝ (A ω) (B ω)),
        ← L2_inner_eq_integral, ← L2_inner_eq_integral]

/-- The requested pointwise time-step function, with half-open interval conventions. -/
def partitionFunction {n : ℕ} (τ : Fin (n + 1) → ℝ≥0) (A : Fin n → GaussianL2)
    (z : ℝ × SampleSpace) : ℝ :=
  ∑ i, (Ioc (τ i.castSucc : ℝ) (τ i.succ : ℝ)).indicator (fun _ => A i z.2) z.1

theorem partitionFunction_stronglyMeasurable {n : ℕ}
    (τ : Fin (n + 1) → ℝ≥0) (A : Fin n → GaussianL2) :
    StronglyMeasurable (partitionFunction τ A) := by
  unfold partitionFunction
  apply Finset.stronglyMeasurable_fun_sum
  intro i _
  have h := ((Lp.stronglyMeasurable (A i)).comp_measurable measurable_snd).indicator
    (measurableSet_Ioc.preimage measurable_fst :
      MeasurableSet (Prod.fst ⁻¹' Ioc (τ i.castSucc : ℝ) (τ i.succ : ℝ)))
  convert h using 1
  ext z
  simp only [Set.indicator, mem_preimage, Function.comp_apply]

/-- The actual product-measure L² class of a finite time partition. -/
def partitionL2 {n : ℕ} (τ : Fin (n + 1) → ℝ≥0) (A : Fin n → GaussianL2) :
    TimeProbabilityL2 :=
  ∑ i, productTensor (intervalVector (τ i.castSucc) (τ i.succ)) (A i)

theorem partitionL2_coeFn {n : ℕ} (τ : Fin (n + 1) → ℝ≥0) (A : Fin n → GaussianL2) :
    partitionL2 τ A =ᵐ[timeProbability] partitionFunction τ A := by
  have hi (i : Fin n) : productTensor (intervalVector (τ i.castSucc) (τ i.succ)) (A i)
      =ᵐ[timeProbability] fun z =>
        (Ioc (τ i.castSucc : ℝ) (τ i.succ : ℝ)).indicator (fun _ => A i z.2) z.1 := by
    have htime := (Measure.quasiMeasurePreserving_fst
      (μ := (volume : Measure ℝ)) (ν := gaussianProduct)).ae_eq_comp
        (intervalVector_coeFn (τ i.castSucc) (τ i.succ))
    filter_upwards [productTensor_coeFn (intervalVector (τ i.castSucc) (τ i.succ)) (A i),
      htime] with z ht hx
    change intervalVector (τ i.castSucc) (τ i.succ) z.1 = _ at hx
    rw [ht, hx]
    by_cases hz : z.1 ∈ Ioc (τ i.castSucc : ℝ) (τ i.succ : ℝ) <;> simp [hz]
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i =>
      productTensor (intervalVector (τ i.castSucc) (τ i.succ)) (A i)),
    Filter.eventually_all.2 hi] with z hsum hi
  change (∑ i, productTensor (intervalVector (τ i.castSucc) (τ i.succ)) (A i)) z = _
  rw [hsum]
  simp only [Finset.sum_apply, partitionFunction]
  apply Finset.sum_congr rfl
  intro i _
  exact hi i

/-- Square integrability of the pointwise step function, without bounded coefficient assumptions. -/
theorem partitionFunction_memLp {n : ℕ} (τ : Fin (n + 1) → ℝ≥0)
    (A : Fin n → GaussianL2) : MemLp (partitionFunction τ A) 2 timeProbability :=
  (Lp.memLp (partitionL2 τ A)).ae_eq (partitionL2_coeFn τ A)

theorem partitionFunction_sq_integrable {n : ℕ} (τ : Fin (n + 1) → ℝ≥0)
    (A : Fin n → GaussianL2) :
    Integrable (fun z => partitionFunction τ A z ^ 2) timeProbability :=
  (partitionFunction_memLp τ A).integrable_sq

/-- The product-measure field and the embedded vector field have the same actual norm. -/
theorem partitionL2_norm_sq_eq_field {n : ℕ} (τ : Fin (n + 1) → ℝ≥0)
    (A : Fin n → GaussianL2) :
    ‖partitionL2 τ A‖ ^ 2 = ‖partitionField τ A‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, partitionL2, partitionField]
  simp only [sum_inner, inner_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [productTensor_inner, scalarTensor_pair_inner]
  unfold incrementDirection
  rw [(hilbertEmbedding TimeHilbert).inner_map_map, mul_comm]

theorem partitionL2_norm_eq_field {n : ℕ} (τ : Fin (n + 1) → ℝ≥0)
    (A : Fin n → GaussianL2) : ‖partitionL2 τ A‖ = ‖partitionField τ A‖ := by
  have h := partitionL2_norm_sq_eq_field τ A
  nlinarith [norm_nonneg (partitionL2 τ A), norm_nonneg (partitionField τ A)]

/-- Elapsed-time weighted norm formula, including empty partitions and repeated times. -/
theorem partitionL2_norm_sq {n : ℕ} (τ : Fin (n + 1) → ℝ≥0) (hτ : Monotone τ)
    (A : Fin n → GaussianL2) :
    ‖partitionL2 τ A‖ ^ 2 =
      ∑ i, ((τ i.succ : ℝ) - τ i.castSucc) * ‖A i‖ ^ 2 := by
  rw [partitionL2_norm_sq_eq_field, partitionField_norm_sq τ hτ]

end OperatorDerivativeRewrite.Foundation.GaussianTimeProductL2
