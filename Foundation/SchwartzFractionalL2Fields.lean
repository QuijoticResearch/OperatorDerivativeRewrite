import Foundation.SchwartzDerivativeEnergies
import Foundation.BochnerL2Dominated
import Mathlib.Analysis.Fourier.LpSpace

/-! Actual L2 inverse-Fourier multiplier fields, without assuming Schwartz closure. -/
noncomputable section
open MeasureTheory
open scoped Topology FourierTransform SchwartzMap ENNReal
namespace OperatorDerivativeRewrite.Foundation.SchwartzFractionalL2Fields
set_option backward.isDefEq.respectTransparency false

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def weightedRepresentative (c : ℝ) (f : 𝓢(V, H)) (n : ℕ) (ξ : V) : H :=
  Real.sqrt ((c*‖ξ‖)^n) • 𝓕 f ξ

theorem weighted_norm_sq (c : ℝ) (hc : 0≤c) (f : 𝓢(V, H)) (n : ℕ) (ξ : V) :
    ‖weightedRepresentative c f n ξ‖^2 = (c*‖ξ‖)^n*‖𝓕 f ξ‖^2 := by
  unfold weightedRepresentative
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    Real.sq_sqrt (pow_nonneg (mul_nonneg hc (norm_nonneg ξ)) n)]

theorem weighted_aestronglyMeasurable (c : ℝ) (f : 𝓢(V, H)) (n : ℕ) :
    AEStronglyMeasurable (weightedRepresentative c f n) (volume : Measure V) := by
  exact ((Real.continuous_sqrt.comp ((continuous_const.mul continuous_norm).pow n)).smul
    (𝓕 f).continuous).aestronglyMeasurable

theorem weighted_memLp (c : ℝ) (hc : 0≤c) (f : 𝓢(V, H)) (n : ℕ) :
    MemLp (weightedRepresentative c f n) 2 (volume : Measure V) := by
  apply (memLp_two_iff_integrable_sq_norm (weighted_aestronglyMeasurable c f n)).mpr
  simpa only [weighted_norm_sq c hc, SchwartzSpectralEnergies.amplitude] using
    SchwartzSpectralEnergies.spectral_integrand_integrable c f n

def spectralClass (c : ℝ) (hc : 0≤c) (f : 𝓢(V, H)) (n : ℕ) : Lp H 2 (volume : Measure V) :=
  (weighted_memLp c hc f n).toLp (weightedRepresentative c f n)

def physicalField (c : ℝ) (hc : 0≤c) (f : 𝓢(V, H)) (n : ℕ) : Lp H 2 (volume : Measure V) :=
  𝓕⁻ (spectralClass c hc f n)

theorem spectralClass_coeFn (c : ℝ) (hc : 0≤c) (f : 𝓢(V, H)) (n : ℕ) :
    spectralClass c hc f n =ᵐ[volume] weightedRepresentative c f n :=
  (weighted_memLp c hc f n).coeFn_toLp

theorem fourier_physicalField (c : ℝ) (hc : 0≤c) (f : 𝓢(V, H)) (n : ℕ) :
    𝓕 (physicalField c hc f n) = spectralClass c hc f n :=
  FourierTransform.fourier_fourierInv_eq _

theorem fourier_physicalField_coeFn (c : ℝ) (hc : 0≤c) (f : 𝓢(V, H)) (n : ℕ) :
    ((𝓕 (physicalField c hc f n) : Lp H 2 (volume : Measure V)) : V → H)
      =ᵐ[volume] weightedRepresentative c f n := by
  rw [fourier_physicalField]
  exact spectralClass_coeFn c hc f n

theorem physicalField_norm (c : ℝ) (hc : 0≤c) (f : 𝓢(V, H)) (n : ℕ) :
    ‖physicalField c hc f n‖ = ‖spectralClass c hc f n‖ := by
  have hh := Lp.norm_fourier_eq (physicalField c hc f n)
  rw [fourier_physicalField] at hh
  exact hh.symm

theorem l2_norm_sq_integral (u : Lp H 2 (volume : Measure V)) :
    ‖u‖^2 = ∫ x : V, ‖u x‖^2 := by
  let : InnerProductSpace ℝ H := InnerProductSpace.complexToReal
  exact BochnerL2Dominated.norm_sq_integral u

theorem spectralClass_norm_sq (c : ℝ) (hc : 0≤c) (f : 𝓢(V, H)) (n : ℕ) :
    ‖spectralClass c hc f n‖^2 = SchwartzSpectralEnergies.spectralMoment c f n := by
  rw [l2_norm_sq_integral]
  apply integral_congr_ae
  filter_upwards [spectralClass_coeFn c hc f n] with ξ hξ
  change ‖spectralClass c hc f n ξ‖^2 = (c*‖ξ‖)^n*‖𝓕 f ξ‖^2
  rw [hξ, weighted_norm_sq c hc]

theorem physicalField_norm_sq (c : ℝ) (hc : 0≤c) (f : 𝓢(V, H)) (n : ℕ) :
    ‖physicalField c hc f n‖^2 = SchwartzSpectralEnergies.spectralMoment c f n := by
  rw [physicalField_norm, spectralClass_norm_sq]

theorem physicalField_sq_integrable (c : ℝ) (hc : 0≤c) (f : 𝓢(V, H)) (n : ℕ) :
    Integrable (fun x : V => ‖physicalField c hc f n x‖^2) volume :=
  (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).mp (Lp.memLp _)

theorem physicalField_integral_eq_moment (c : ℝ) (hc : 0≤c) (f : 𝓢(V, H)) (n : ℕ) :
    (∫ x : V, ‖physicalField c hc f n x‖^2) =
      SchwartzSpectralEnergies.spectralMoment c f n := by
  rw [← l2_norm_sq_integral, physicalField_norm_sq]

theorem spectralClass_zero (c : ℝ) (hc : 0≤c) (f : 𝓢(V, H)) :
    spectralClass c hc f 0 = 𝓕 (f.toLp 2) := by
  rw [SchwartzMap.toLp_fourier_eq]
  apply Lp.ext
  filter_upwards [spectralClass_coeFn c hc f 0, (𝓕 f).coeFn_toLp 2] with ξ hξ hF
  rw [hξ, hF]
  simp [weightedRepresentative]

theorem physicalField_zero (c : ℝ) (hc : 0≤c) (f : 𝓢(V, H)) :
    physicalField c hc f 0 = f.toLp 2 := by
  unfold physicalField
  rw [spectralClass_zero]
  exact FourierTransform.fourierInv_fourier_eq _

theorem critical_physical_norm_sq (c : ℝ) (hc : 0≤c) (f : 𝓢(V, H)) :
    ‖physicalField c hc f 1‖^2 = SchwartzSpectralEnergies.criticalEnergy c f :=
  physicalField_norm_sq c hc f 1

theorem dissipation_physical_norm_sq (c : ℝ) (hc : 0≤c) (f : 𝓢(V, H)) :
    ‖physicalField c hc f 3‖^2 = SchwartzSpectralEnergies.dissipation c f :=
  physicalField_norm_sq c hc f 3

theorem gradient_physical_norm_sq {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (f : 𝓢(V, H)) :
    ‖physicalField (2*Real.pi) (by positivity) f 2‖^2 =
      SchwartzDerivativeEnergies.gradientEnergy b f := by
  rw [physicalField_norm_sq, SchwartzDerivativeEnergies.gradient_plancherel]

end OperatorDerivativeRewrite.Foundation.SchwartzFractionalL2Fields
