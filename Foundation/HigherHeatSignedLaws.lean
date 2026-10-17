import Foundation.GaussianSchwartzKernel
import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec
import Mathlib.MeasureTheory.Integral.Pi

/-! Actual finite-dimensional signed increment laws for higher even-order heat. -/
noncomputable section
open MeasureTheory Filter FourierTransform
open scoped NNReal ENNReal SchwartzMap Topology
namespace OperatorDerivativeRewrite.Foundation.HigherHeatSignedLaws
open GaussianSchwartzKernel

def realKernel (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t) : 𝓢(ℝ,ℝ) :=
  (evenKernel m hm t ht).postcompCLM Complex.reCLM

theorem realKernel_coe (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t) (x : ℝ) :
    (realKernel m hm t ht x : ℂ) = evenKernel m hm t ht x := by
  apply Complex.ext
  · rfl
  · have h := congrArg Complex.im (evenKernel_conj m hm t ht x)
    simp only [Complex.conj_im] at h
    change 0 = (evenKernel m hm t ht x).im
    linarith

theorem realKernel_integral (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t) :
    ∫ x, realKernel m hm t ht x = 1 := by
  change ∫ x, Complex.re (evenKernel m hm t ht x) = 1
  have h := integral_re (evenKernel_integrable m hm t ht)
  rw [evenKernel_normalization] at h
  simpa only [RCLike.re_eq_complex_re,Complex.one_re] using h

def law (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t) : SignedMeasure ℝ :=
  volume.withDensityᵥ (realKernel m hm t ht)

theorem law_apply (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t)
    (s : Set ℝ) (hs : MeasurableSet s) :
    law m hm t ht s = ∫ x in s, realKernel m hm t ht x :=
  withDensityᵥ_apply (realKernel m hm t ht).integrable hs

theorem law_mass (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t) :
    law m hm t ht Set.univ = 1 := by
  rw [law_apply _ _ _ _ _ MeasurableSet.univ,Measure.restrict_univ,realKernel_integral]

variable {ι : Type*} [Fintype ι]

def incrementDensity (m : ℕ) (hm : 0 < m) (t : ι → ℝ≥0) (ht : ∀ i, 0 < t i)
    (x : ι → ℝ) : ℝ := ∏ i, realKernel m hm (t i) (ht i) (x i)

theorem incrementDensity_integrable (m : ℕ) (hm : 0 < m)
    (t : ι → ℝ≥0) (ht : ∀ i, 0 < t i) :
    Integrable (incrementDensity m hm t ht) (Measure.pi (fun _ : ι => volume)) :=
  Integrable.fintype_prod (fun i => (realKernel m hm (t i) (ht i)).integrable)

def incrementLaw (m : ℕ) (hm : 0 < m) (t : ι → ℝ≥0) (ht : ∀ i, 0 < t i) :
    SignedMeasure (ι → ℝ) := (Measure.pi (fun _ : ι => volume)).withDensityᵥ
      (incrementDensity m hm t ht)

theorem incrementLaw_mass (m : ℕ) (hm : 0 < m)
    (t : ι → ℝ≥0) (ht : ∀ i, 0 < t i) :
    incrementLaw m hm t ht Set.univ = 1 := by
  rw [incrementLaw,withDensityᵥ_apply (incrementDensity_integrable m hm t ht) MeasurableSet.univ,
    Measure.restrict_univ]
  simp only [incrementDensity,integral_fintype_prod_eq_prod,realKernel_integral,Finset.prod_const_one]

theorem incrementLaw_variation (m : ℕ) (hm : 0 < m)
    (t : ι → ℝ≥0) (ht : ∀ i, 0 < t i) :
    (incrementLaw m hm t ht).variation =
      (Measure.pi (fun _ : ι => volume)).withDensity
        (fun x => ‖incrementDensity m hm t ht x‖ₑ) :=
  Measure.variation_withDensityᵥ (incrementDensity_integrable m hm t ht)

theorem incrementLaw_variation_mass (m : ℕ) (hm : 0 < m)
    (t : ι → ℝ≥0) (ht : ∀ i, 0 < t i) :
    ((incrementLaw m hm t ht).variation Set.univ).toReal =
      ∏ i, ∫ x, ‖realKernel m hm (t i) (ht i) x‖ := by
  rw [incrementLaw_variation,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
  rw [← integral_norm_eq_lintegral_enorm (incrementDensity_integrable m hm t ht).aestronglyMeasurable]
  simp only [incrementDensity,norm_prod]
  exact integral_fintype_prod_eq_prod (fun i x => ‖realKernel m hm (t i) (ht i) x‖)

theorem l2_kernel_evolution (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t)
    (f : 𝓢(ℝ,ℂ)) :
    HigherHeatL2.evolution m t (f.toLp 2) =
      (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ)
        (evenKernel m hm t ht) f).toLp 2 := by
  have hmul : HigherHeatL2.multiplier m t ((𝓕 f).toLp 2) =
      (SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ)
        (evenSymbol m hm t ht) (𝓕 f)).toLp 2 := by
    apply Lp.ext
    filter_upwards [HigherHeatL2.multiplier_ae m t ((𝓕 f).toLp 2),
      (𝓕 f).coeFn_toLp 2,
      (SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ)
        (evenSymbol m hm t ht) (𝓕 f)).coeFn_toLp 2] with x h1 h2 h3
    rw [h1,h2,h3,SchwartzMap.pairing_apply_apply,ContinuousLinearMap.mul_apply',evenSymbol_apply]
  rw [HigherHeatL2.evolution_apply,SchwartzMap.toLp_fourier_eq,hmul,
    SchwartzMap.toLp_fourierInv_eq]
  congr 1
  apply (fourierEquiv ℂ 𝓢(ℝ,ℂ)).injective
  change 𝓕 (𝓕⁻ (SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ)
    (evenSymbol m hm t ht) (𝓕 f))) =
    𝓕 (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ)
      (evenKernel m hm t ht) f)
  rw [fourier_fourierInv_eq,SchwartzMap.fourier_convolution,evenKernel_fourier]

end OperatorDerivativeRewrite.Foundation.HigherHeatSignedLaws
