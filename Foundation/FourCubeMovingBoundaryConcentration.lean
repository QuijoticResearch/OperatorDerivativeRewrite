import Foundation.FourCubeBoundaryGibbsComparison

/-! Uniform concentration of actual moving-boundary Gibbs laws in the verified Haar chart. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.FourCubeMovingBoundaryConcentration
open QuaternionSU2Representation OneSidedCapComplex FourCubeIntegratedCubic FourCubePinnedHaar
open FourCubePinnedConcentration FourCubeBoundaryCoercivity FourCubeScaledBoundaryControl
open FourCubeBoundaryGibbsComparison FourCubeHemisphereCoercivity FourCubePhysicalEnergy
open FourCubeHaarPartitionAsymptotic

theorem coefficient_bound (β : ℝ) (b : Boundary → SU2) (A : ℝ)
    (hb : β*boundaryCost b ≤ A) : comparisonCoefficient β b ≤
      Real.exp (4*A)*(normalizer (β/3)/normalizer (3*β)) := by
  exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by nlinarith))
    (div_nonneg (normalizer_positive _).le (normalizer_positive _).le)

def referenceRatio (t : ℝ) := normalizer ((1/t ^ 2)/3)/normalizer (3*(1/t ^ 2))
def referenceLeak (t : ℝ) := (gibbs ((1/t ^ 2)/3)).real localStateDomainᶜ
def leakageEnvelope (R t : ℝ) := Real.exp (864*R)*referenceRatio t*referenceLeak t

theorem referenceRatio_tendsto :
    Tendsto referenceRatio (𝓝[≠] 0)
      (𝓝 (((Real.sqrt (1/3))⁻¹^93)/((Real.sqrt (3 : ℝ))⁻¹^93))) := by
  have hp : (Real.sqrt (3 : ℝ))⁻¹^93 ≠ 0 := by positivity
  have hh := (partition_ratio_tendsto (1/3) (by norm_num)).div
    (partition_ratio_tendsto 3 (by norm_num)) hp
  apply hh.congr'
  filter_upwards with t
  change (normalizer ((1/3)/t ^ 2)/normalizer (1/t ^ 2))/
      (normalizer (3/t ^ 2)/normalizer (1/t ^ 2))=referenceRatio t
  unfold referenceRatio
  have h1 : (1/t ^ 2)/3=(1/3)/t ^ 2 := by ring
  have h2 : 3*(1/t ^ 2)=3/t ^ 2 := by ring
  rw [h1,h2]
  field_simp [(normalizer_positive (1/t ^ 2)).ne',(normalizer_positive (3/t ^ 2)).ne']
  exact mul_div_cancel_right₀ _ (normalizer_positive (1/t ^ 2)).ne'

theorem third_clock_tendsto : Tendsto (fun t : ℝ => (1/t ^ 2)/3) (𝓝[≠] 0) atTop := by
  have hh := inverse_square_tendsto.atTop_mul_const (show (0 : ℝ) < 1/3 by norm_num)
  simpa only [div_eq_mul_inv,one_mul] using hh

theorem referenceLeak_tendsto_zero : Tendsto referenceLeak (𝓝[≠] 0) (𝓝 0) :=
  gibbs_outside_cutoff_tendsto_zero.comp third_clock_tendsto

theorem leakageEnvelope_tendsto_zero (R : ℝ) :
    Tendsto (leakageEnvelope R) (𝓝[≠] 0) (𝓝 0) := by
  have hh := (referenceRatio_tendsto.const_mul (Real.exp (864*R))).mul referenceLeak_tendsto_zero
  unfold leakageEnvelope
  simpa only [mul_zero] using hh

theorem moving_law_real_bound (t : ℝ) (ht : t ≠ 0) (x y z R : ℝ)
    (hR : x ^ 2 + y ^ 2 + z ^ 2 ≤ R) (A : Set PinnedState) :
    (law (1/t ^ 2) (movingBoundary t x y z)).real A ≤
      (Real.exp (864*R)*referenceRatio t)*(gibbs ((1/t ^ 2)/3)).real A := by
  have hβ : 0 ≤ 1/t ^ 2 := by positivity
  have hclock : (1/t ^ 2)*t ^ 2=1 := by field_simp
  have hb : (1/t ^ 2)*boundaryCost (movingBoundary t x y z) ≤ 216*R :=
    (scaled_boundaryCost (1/t ^ 2) t hβ hclock x y z).trans (by nlinarith)
  have hc := coefficient_bound (1/t ^ 2) (movingBoundary t x y z) (216*R) hb
  have hc' : comparisonCoefficient (1/t ^ 2) (movingBoundary t x y z) ≤
      Real.exp (864*R)*referenceRatio t := by
    convert! hc using 1
    congr 2
    ring
  exact (law_real_le_reference (1/t ^ 2) hβ _ A).trans
    (mul_le_mul_of_nonneg_right hc' measureReal_nonneg)

theorem moving_outside_bound (t : ℝ) (ht : t ≠ 0) (x y z R : ℝ)
    (hR : x ^ 2 + y ^ 2 + z ^ 2 ≤ R) :
    (law (1/t ^ 2) (movingBoundary t x y z)).real localStateDomainᶜ ≤ leakageEnvelope R t :=
  moving_law_real_bound t ht x y z R hR localStateDomainᶜ

/-- Uniform in all amplitudes in a fixed ball; the actual normalized probability is used. -/
theorem uniform_outside_concentration (R ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t : ℝ in 𝓝[≠] 0,∀ x y z : ℝ,x ^ 2 + y ^ 2 + z ^ 2 ≤ R →
      (law (1/t ^ 2) (movingBoundary t x y z)).real localStateDomainᶜ < ε := by
  have hh := (leakageEnvelope_tendsto_zero R).eventually (eventually_lt_nhds hε)
  filter_upwards [self_mem_nhdsWithin,hh] with t ht hh x y z hR
  exact (moving_outside_bound t ht x y z R hR).trans_lt hh

theorem uniform_inside_concentration (R ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t : ℝ in 𝓝[≠] 0,∀ x y z : ℝ,x ^ 2 + y ^ 2 + z ^ 2 ≤ R →
      |(law (1/t ^ 2) (movingBoundary t x y z)).real localStateDomain-1| < ε := by
  filter_upwards [uniform_outside_concentration R ε hε] with t ht x y z hR
  have hh := measureReal_compl (μ := law (1/t ^ 2) (movingBoundary t x y z))
    localStateDomain_measurable
  have h1 : (law (1/t ^ 2) (movingBoundary t x y z)).real Set.univ=1 := by simp
  rw [h1] at hh
  have he : (law (1/t ^ 2) (movingBoundary t x y z)).real localStateDomain-1=
      -(law (1/t ^ 2) (movingBoundary t x y z)).real localStateDomainᶜ := by linarith
  rw [he,abs_neg,abs_of_nonneg measureReal_nonneg]
  exact ht x y z hR

theorem moving_outside_tendsto_zero (R : ℝ) (x y z : ℝ → ℝ)
    (hR : ∀ t, x t ^ 2+y t ^ 2+z t ^ 2 ≤ R) :
    Tendsto (fun t : ℝ => (law (1/t ^ 2) (movingBoundary t (x t) (y t) (z t))).real localStateDomainᶜ)
      (𝓝[≠] 0) (𝓝 0) := by
  apply squeeze_zero' (Filter.Eventually.of_forall (fun t => measureReal_nonneg))
    (show ∀ᶠ t : ℝ in 𝓝[≠] 0,
      (law (1/t ^ 2) (movingBoundary t (x t) (y t) (z t))).real localStateDomainᶜ ≤
        leakageEnvelope R t from ?_) (leakageEnvelope_tendsto_zero R)
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact moving_outside_bound t ht (x t) (y t) (z t) R (hR t)

/-- The cutoff can be removed even for varying bounded measurable tests and amplitude profiles. -/
theorem moving_outside_integral_tendsto_zero (R M : ℝ) (x y z : ℝ → ℝ)
    (hR : ∀ t, x t ^ 2+y t ^ 2+z t ^ 2 ≤ R) (f : ℝ → PinnedState → ℝ)
    (hf : ∀ t, Measurable (f t)) (hb : ∀ t U, |f t U| ≤ M) :
    Tendsto (fun t : ℝ => ∫ U in localStateDomainᶜ,f t U
      ∂law (1/t ^ 2) (movingBoundary t (x t) (y t) (z t))) (𝓝[≠] 0) (𝓝 0) := by
  have hp := (moving_outside_tendsto_zero R x y z hR).const_mul M
  simp only [mul_zero] at hp
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Filter.Eventually.of_forall (fun t => norm_nonneg _))
    (Filter.Eventually.of_forall (fun t => ?_)) hp
  rw [Real.norm_eq_abs]
  exact bounded_setIntegral_bound (1/t ^ 2) (movingBoundary t (x t) (y t) (z t))
    localStateDomainᶜ localStateDomain_measurable.compl (f t) (hf t) M (hb t)

end OperatorDerivativeRewrite.Foundation.FourCubeMovingBoundaryConcentration
