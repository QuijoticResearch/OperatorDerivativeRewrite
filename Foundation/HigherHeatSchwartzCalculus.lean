import Foundation.HigherHeatFourierCalculus
import Foundation.SignedDensityIntegral

/-! An actual continuous-spectrum stochastic representation for Schwartz terminal observables. -/
noncomputable section
open MeasureTheory FourierTransform
open scoped NNReal Topology SchwartzMap
namespace OperatorDerivativeRewrite.Foundation.HigherHeatSchwartzCalculus
open HigherHeatL2 HigherHeatCylinderFourier HigherHeatFourierCalculus HigherHeatSignedLaws
open GaussianSchwartzKernel SignedDensityIntegral

def mean (m : ℕ) (T : ℝ≥0) (f : 𝓢(ℝ,ℂ)) : ℂ :=
  ∫ ξ : ℝ, 𝓕 f ξ*symbol m T (-ξ)

def spectralIntegral (m : ℕ) (T : ℝ≥0) (grid : ℕ → ℝ≥0) (n : ℕ)
    (f : 𝓢(ℝ,ℂ)) (x : ℕ → ℝ) : ℂ :=
  ∫ ξ : ℝ, 𝓕 f ξ*fourierIntegral m T grid n (-ξ) x

theorem mean_integrable (m : ℕ) (T : ℝ≥0) (f : 𝓢(ℝ,ℂ)) :
    Integrable (fun ξ : ℝ => 𝓕 f ξ*symbol m T (-ξ)) := by
  refine (𝓕 f).integrable.norm.mono' ?_ ?_
  · exact ((𝓕 f).continuous.mul ((symbol_continuous m T).comp continuous_neg)).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun ξ => by
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (symbol_norm_le m T (-ξ))

theorem inverse_phase_integrable (f : 𝓢(ℝ,ℂ)) (x : ℝ) :
    Integrable (fun ξ : ℝ => 𝓕 f ξ*phase (-ξ) x) := by
  refine (𝓕 f).integrable.norm.mono' ?_ ?_
  · apply Continuous.aestronglyMeasurable
    unfold phase
    fun_prop
  exact Filter.Eventually.of_forall fun ξ => by rw [norm_mul,phase_norm,mul_one]

theorem inverse_phase (f : 𝓢(ℝ,ℂ)) (x : ℝ) :
    (∫ ξ : ℝ, 𝓕 f ξ*phase (-ξ) x)=f x := by
  have h := congrArg (fun g : 𝓢(ℝ,ℂ) => g x)
    (fourierInv_fourier_eq f : (𝓕⁻ (𝓕 f) : 𝓢(ℝ,ℂ))=f)
  rw [SchwartzMap.fourierInv_coe,Real.fourierInv_eq] at h
  convert h using 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ξ => by
    have he : -(x*(-ξ))=ξ*x := by ring
    simp only [phase,he,Circle.smul_def,smul_eq_mul,RCLike.inner_apply,conj_trivial]
    ring

theorem spectral_integrable (m : ℕ) (T : ℝ≥0) (grid : ℕ → ℝ≥0) (n : ℕ)
    (hg : Monotone grid) (h0 : grid 0=0) (hn : grid n=T)
    (f : 𝓢(ℝ,ℂ)) (x : ℕ → ℝ) (hx : x 0=0) :
    Integrable (fun ξ : ℝ => 𝓕 f ξ*fourierIntegral m T grid n (-ξ) x) := by
  have h := (inverse_phase_integrable f (x n)).sub (mean_integrable m T f)
  apply h.congr
  exact Filter.Eventually.of_forall fun ξ => by
    change 𝓕 f ξ*phase (-ξ) (x n)-𝓕 f ξ*symbol m T (-ξ)=
      𝓕 f ξ*fourierIntegral m T grid n (-ξ) x
    rw [← terminal_representation m T grid n hg h0 hn (-ξ) x hx]
    ring

theorem terminal_representation (m : ℕ) (T : ℝ≥0) (grid : ℕ → ℝ≥0) (n : ℕ)
    (hg : Monotone grid) (h0 : grid 0=0) (hn : grid n=T)
    (f : 𝓢(ℝ,ℂ)) (x : ℕ → ℝ) (hx : x 0=0) :
    f (x n)-mean m T f=spectralIntegral m T grid n f x := by
  unfold spectralIntegral
  calc
    _ = (∫ ξ : ℝ, 𝓕 f ξ*phase (-ξ) (x n))-
        (∫ ξ : ℝ, 𝓕 f ξ*symbol m T (-ξ)) := by rw [inverse_phase,mean]
    _ = ∫ ξ : ℝ, 𝓕 f ξ*phase (-ξ) (x n)-𝓕 f ξ*symbol m T (-ξ) :=
      (integral_sub (inverse_phase_integrable f (x n)) (mean_integrable m T f)).symm
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ξ => by
        dsimp only
        rw [← HigherHeatFourierCalculus.terminal_representation m T grid n hg h0 hn (-ξ) x hx]
        ring

theorem mean_eq_kernel (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (f : 𝓢(ℝ,ℂ)) :
    mean m T f=∫ x : ℝ, f x*(realKernel m hm T hT x:ℂ) := by
  have he (ξ : ℝ) : 𝓕⁻ (evenKernel m hm T hT) ξ=symbol m T (-ξ) := by
    rw [SchwartzMap.fourierInv_coe,Real.fourierInv_eq_fourier_neg,
      ← SchwartzMap.fourier_coe,evenKernel_fourier,evenSymbol_apply]
  have h := SchwartzMap.integral_fourierInv_mul_eq (𝓕 f) (evenKernel m hm T hT)
  rw [fourierInv_fourier_eq] at h
  calc
    _ = ∫ ξ : ℝ, 𝓕 f ξ*𝓕⁻ (evenKernel m hm T hT) ξ := by simp only [he,mean]
    _ = ∫ x : ℝ, f x*evenKernel m hm T hT x := h.symm
    _ = _ := by simp only [realKernel_coe]

theorem mean_eq_signed_integral (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (f : 𝓢(ℝ,ℂ)) : mean m T f=∫ᵛ x, f x ∂<•law m hm T hT := by
  rw [law,integral_density volume _ (realKernel m hm T hT).integrable
    (realKernel m hm T hT).continuous.measurable _ f.continuous.measurable
    (SchwartzMap.seminorm ℝ 0 0 f) (SchwartzMap.norm_le_seminorm ℝ f)]
  rw [mean_eq_kernel m hm T hT f]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by simp only [Complex.real_smul]; ring

theorem mean_bound (m : ℕ) (T : ℝ≥0) (f : 𝓢(ℝ,ℂ)) :
    ‖mean m T f‖ ≤ ∫ ξ : ℝ, ‖𝓕 f ξ‖ := by
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun ξ => norm_nonneg _)
    (𝓕 f).integrable.norm
  exact Filter.Eventually.of_forall fun ξ => by
    change ‖𝓕 f ξ*symbol m T (-ξ)‖ ≤ ‖𝓕 f ξ‖
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (symbol_norm_le m T (-ξ))

theorem spectral_bound (m : ℕ) (T : ℝ≥0) (grid : ℕ → ℝ≥0) (n : ℕ)
    (hg : Monotone grid) (h0 : grid 0=0) (hn : grid n=T)
    (f : 𝓢(ℝ,ℂ)) (x : ℕ → ℝ) (hx : x 0=0) :
    ‖spectralIntegral m T grid n f x‖ ≤ 2*∫ ξ : ℝ, ‖𝓕 f ξ‖ := by
  rw [← terminal_representation m T grid n hg h0 hn f x hx]
  have hf : ‖f (x n)‖ ≤ ∫ ξ : ℝ, ‖𝓕 f ξ‖ := by
    rw [← inverse_phase f (x n)]
    apply (norm_integral_le_integral_norm _).trans
    simp only [norm_mul,phase_norm,mul_one]
    exact le_rfl
  exact (norm_sub_le _ _).trans (by linarith [mean_bound m T f])

theorem continuous_path_representation (m : ℕ) (T : ℝ≥0) (grid : ℕ → ℝ≥0) (n : ℕ)
    (hg : Monotone grid) (h0 : grid 0=0) (hn : grid n=T)
    (f : 𝓢(ℝ,ℂ)) (ω : C(ℝ≥0,ℝ)) (hω : ω 0=0) :
    f (ω T)-mean m T f=spectralIntegral m T grid n f (fun j => ω (grid j)) := by
  simpa only [hn] using terminal_representation m T grid n hg h0 hn f
    (fun j => ω (grid j)) (by simpa only [h0] using hω)

end OperatorDerivativeRewrite.Foundation.HigherHeatSchwartzCalculus
