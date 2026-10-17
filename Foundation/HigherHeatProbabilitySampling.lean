import Foundation.SignedDensityProbabilitySampling
import Foundation.HigherHeatPositionVariation

/-! Actual probability samplers and exact signed weights for finite higher-heat configurations. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.HigherHeatProbabilitySampling
open HigherHeatSignedLaws SignedDensityProbabilitySampling SignedAbsoluteIntegration
open HigherHeatCylinderFourier HigherHeatDyadicLaws HigherHeatPositionVariation

def base (n : ℕ) : Measure (Fin n → ℝ) := Measure.pi (fun _ => volume)

def density (n m : ℕ) (hm : 0 < m) (t : Fin n → ℝ≥0) (ht : ∀ i, 0 < t i) :
    (Fin n → ℝ) → ℝ := incrementDensity m hm t ht

theorem density_measurable (n m : ℕ) (hm : 0 < m) (t : Fin n → ℝ≥0) (ht : ∀ i, 0 < t i) :
    Measurable (density n m hm t ht) := by
  unfold density incrementDensity
  fun_prop

theorem density_integral (n m : ℕ) (hm : 0 < m) (t : Fin n → ℝ≥0) (ht : ∀ i, 0 < t i) :
    (∫ x, density n m hm t ht x ∂base n)=1 := by
  simp only [density, base, incrementDensity, integral_fintype_prod_eq_prod,
    realKernel_integral, Finset.prod_const_one]

theorem density_mass_positive (n m : ℕ) (hm : 0 < m) (t : Fin n → ℝ≥0) (ht : ∀ i, 0 < t i) :
    0 < mass (base n) (density n m hm t ht) :=
  mass_positive_of_integral_one _ _ (density_integral n m hm t ht)

def probability (n m : ℕ) (hm : 0 < m) (t : Fin n → ℝ≥0) (ht : ∀ i, 0 < t i) :
    Measure (Fin n → ℝ) := sampler (base n) (density n m hm t ht)

def samplingWeight (n m : ℕ) (hm : 0 < m) (t : Fin n → ℝ≥0) (ht : ∀ i, 0 < t i) :
    (Fin n → ℝ) → ℝ := weight (base n) (density n m hm t ht)

theorem probability_isProbability (n m : ℕ) (hm : 0 < m)
    (t : Fin n → ℝ≥0) (ht : ∀ i, 0 < t i) : IsProbabilityMeasure (probability n m hm t ht) :=
  sampler_probability _ _ (incrementDensity_integrable m hm t ht) (density_mass_positive n m hm t ht)

theorem sampling_mass (n m : ℕ) (hm : 0 < m) (t : Fin n → ℝ≥0) (ht : ∀ i, 0 < t i) :
    mass (base n) (density n m hm t ht)=∏ i, ∫ x : ℝ, ‖realKernel m hm (t i) (ht i) x‖ := by
  rw [mass_eq_variation (base n) (density n m hm t ht) (incrementDensity_integrable m hm t ht)]
  exact incrementLaw_variation_mass m hm t ht

theorem signed_expectation (n m : ℕ) (hm : 0 < m) (t : Fin n → ℝ≥0) (ht : ∀ i, 0 < t i)
    (g : (Fin n → ℝ) → ℂ)
    (hg : Integrable g (absoluteDensity (base n) (density n m hm t ht))) :
    (∫ᵛ x, g x ∂<•incrementLaw m hm t ht)=
      ∫ x, samplingWeight n m hm t ht x • g x ∂probability n m hm t ht :=
  signed_integral_sampling _ _ (incrementDensity_integrable m hm t ht)
    (density_measurable n m hm t ht) (density_mass_positive n m hm t ht) g hg

theorem weight_moments (n m : ℕ) (hm : 0 < m) (t : Fin n → ℝ≥0) (ht : ∀ i, 0 < t i) :
    (∫ x, samplingWeight n m hm t ht x ∂probability n m hm t ht)=1 ∧
      (∫ x, |samplingWeight n m hm t ht x| ∂probability n m hm t ht)=
        mass (base n) (density n m hm t ht) ∧
      (∫ x, (samplingWeight n m hm t ht x)^2 ∂probability n m hm t ht)=
        (mass (base n) (density n m hm t ht))^2 := by
  refine ⟨?_, weight_l1 _ _ (incrementDensity_integrable m hm t ht)
    (density_mass_positive n m hm t ht), weight_l2_square _ _
      (incrementDensity_integrable m hm t ht) (density_mass_positive n m hm t ht)⟩
  rw [probability, samplingWeight, weight_mean _ _ (density_measurable n m hm t ht)
    (density_mass_positive n m hm t ht), density_integral]

def dyadicProbability (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (n : ℕ) : Measure (Grid n) :=
  probability (gridSize n) m hm (fun _ => duration T n) (fun _ => duration_pos T hT n)

def dyadicWeight (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (n : ℕ) : Grid n → ℝ :=
  samplingWeight (gridSize n) m hm (fun _ => duration T n) (fun _ => duration_pos T hT n)

theorem dyadic_mass (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    mass (base (gridSize n))
      (density (gridSize n) m hm (fun _ => duration T n) (fun _ => duration_pos T hT n))=
      (∫ x : ℝ, ‖realKernel m hm T hT x‖)^(gridSize n) := by
  rw [sampling_mass]
  simp_rw [norm_integral_time_independent m hm (duration T n) T (duration_pos T hT n) hT]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem dyadic_weight_moments (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    (∫ x, dyadicWeight m hm T hT n x ∂dyadicProbability m hm T hT n)=1 ∧
      (∫ x, |dyadicWeight m hm T hT n x| ∂dyadicProbability m hm T hT n)=
        (∫ x : ℝ, ‖realKernel m hm T hT x‖)^(gridSize n) ∧
      (∫ x, (dyadicWeight m hm T hT n x)^2 ∂dyadicProbability m hm T hT n)=
        ((∫ x : ℝ, ‖realKernel m hm T hT x‖)^(gridSize n))^2 := by
  have hh := weight_moments (gridSize n) m hm (fun _ => duration T n)
    (fun _ => duration_pos T hT n)
  rwa [dyadic_mass] at hh

theorem dyadic_weight_l1_unbounded (m : ℕ) (hm : 2 ≤ m) (T : ℝ≥0) (hT : 0 < T) (B : ℝ) :
    ∃ n, B < ∫ x, |dyadicWeight m (by omega) T hT n x| ∂dyadicProbability m (by omega) T hT n := by
  let C : ℝ := ∫ x : ℝ, ‖realKernel m (by omega : 0 < m) T hT x‖
  have hC : 1 < C := HigherHeatKernelMoments.norm_integral_gt_one m hm T hT
  obtain ⟨n,hn⟩ := pow_unbounded_of_one_lt B hC
  refine ⟨n, ?_⟩
  rw [(dyadic_weight_moments m (by omega) T hT n).2.1]
  exact hn.trans_le (pow_le_pow_right₀ hC.le (level_le_size n))

end OperatorDerivativeRewrite.Foundation.HigherHeatProbabilitySampling
