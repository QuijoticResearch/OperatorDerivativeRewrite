import Foundation.SignedDensityIntegral
import Foundation.HigherHeatKernelScaling

/-! Actual deterministic step-integral laws and their effective higher-heat clock. -/
noncomputable section
open MeasureTheory
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.HigherHeatStepIntegralLaws
open HigherHeatSignedLaws HigherHeatCylinderFourier SignedDensityIntegral

variable {ι : Type*} [Fintype ι]

def integralMap (u : ι → ℝ) (x : ι → ℝ) : ℝ := ∑ i, u i * x i

theorem integralMap_measurable (u : ι → ℝ) : Measurable (integralMap u) := by
  unfold integralMap
  fun_prop

def integralLaw (m : ℕ) (hm : 0 < m) (t : ι → ℝ≥0) (ht : ∀ i, 0 < t i)
    (u : ι → ℝ) : SignedMeasure ℝ := (incrementLaw m hm t ht).map (integralMap u)

theorem integralLaw_mass (m : ℕ) (hm : 0 < m) (t : ι → ℝ≥0) (ht : ∀ i, 0 < t i)
    (u : ι → ℝ) : integralLaw m hm t ht u Set.univ = 1 := by
  rw [integralLaw, VectorMeasure.map_apply _ (integralMap_measurable u) MeasurableSet.univ,
    Set.preimage_univ, incrementLaw_mass]

theorem integralLaw_fourier (m : ℕ) (hm : 0 < m) (t : ι → ℝ≥0) (ht : ∀ i, 0 < t i)
    (u : ι → ℝ) (ξ : ℝ) :
    (∫ᵛ y, phase ξ y ∂<•integralLaw m hm t ht u) =
      ∏ i, HigherHeatL2.symbol m (t i) (ξ * u i) := by
  have hgm : Measurable (fun x : ι → ℝ => phase ξ (integralMap u x)) :=
    (phase_continuous ξ).measurable.comp (integralMap_measurable u)
  have hgb (x : ι → ℝ) : ‖phase ξ (integralMap u x)‖ ≤ 1 := (phase_norm _ _).le
  have hi := bounded_signed_integrable (incrementLaw m hm t ht) _ hgm 1 hgb
  rw [integralLaw, VectorMeasure.integral_map (integralMap_measurable u)
    (phase_continuous ξ).aestronglyMeasurable hi]
  have hdm : Measurable (incrementDensity m hm t ht) := by
    unfold incrementDensity
    fun_prop
  rw [incrementLaw, integral_density _ _ (incrementDensity_integrable m hm t ht) hdm
    (fun x => phase ξ (integralMap u x)) hgm 1 hgb]
  have he (x : ι → ℝ) : incrementDensity m hm t ht x • phase ξ (integralMap u x) =
      ∏ i, phase (ξ * u i) (x i) * (realKernel m hm (t i) (ht i) (x i) : ℂ) := by
    have hp : phase ξ (integralMap u x) = ∏ i, phase (ξ * u i) (x i) := by
      unfold phase integralMap
      rw [Finset.sum_mul, ← Finset.sum_neg_distrib, character_sum]
      apply Finset.prod_congr rfl
      intro i _
      congr 2
      ring
    rw [hp]
    simp only [Complex.real_smul, incrementDensity, Complex.ofReal_prod,
      Finset.prod_mul_distrib]
    exact mul_comm _ _
  simp_rw [he]
  rw [integral_fintype_prod_eq_prod (fun i (x : ℝ) =>
    phase (ξ * u i) x * (realKernel m hm (t i) (ht i) x : ℂ))]
  apply Finset.prod_congr rfl
  intro i _
  exact kernel_fourier m hm (t i) (ht i) (ξ * u i)

def effectiveTime (m : ℕ) (t : ι → ℝ≥0) (u : ι → ℝ) : ℝ≥0 :=
  ∑ i, t i * ‖u i‖₊ ^ (2*m)

theorem symbol_sum (m : ℕ) (t : ι → ℝ≥0) (ξ : ℝ) :
    HigherHeatL2.symbol m (∑ i, t i) ξ = ∏ i, HigherHeatL2.symbol m (t i) ξ := by
  classical
  have he (s : Finset ι) : HigherHeatL2.symbol m (∑ i ∈ s, t i) ξ =
      ∏ i ∈ s, HigherHeatL2.symbol m (t i) ξ := by
    induction s using Finset.induction_on with
    | empty => simp [HigherHeatL2.symbol_zero]
    | @insert i s hi ih => simp [hi, HigherHeatL2.symbol_add, ih]
  exact he Finset.univ

theorem symbol_control_scaling (m : ℕ) (t : ℝ≥0) (u ξ : ℝ) :
    HigherHeatL2.symbol m (t * ‖u‖₊ ^ (2*m)) ξ = HigherHeatL2.symbol m t (ξ * u) := by
  have hp : |u| ^ (2*m) = u ^ (2*m) := by rw [pow_mul, pow_mul, sq_abs]
  simp only [HigherHeatL2.symbol, NNReal.coe_mul, NNReal.coe_pow, coe_nnnorm,
    Real.norm_eq_abs, hp, mul_pow]
  congr 2
  ring

theorem integralLaw_clock (m : ℕ) (hm : 0 < m) (t : ι → ℝ≥0) (ht : ∀ i, 0 < t i)
    (u : ι → ℝ) (ξ : ℝ) :
    (∫ᵛ y, phase ξ y ∂<•integralLaw m hm t ht u) =
      HigherHeatL2.symbol m (effectiveTime m t u) ξ := by
  rw [integralLaw_fourier, effectiveTime, symbol_sum]
  apply Finset.prod_congr rfl
  intro i _
  exact (symbol_control_scaling m (t i) (u i) ξ).symm

end OperatorDerivativeRewrite.Foundation.HigherHeatStepIntegralLaws
