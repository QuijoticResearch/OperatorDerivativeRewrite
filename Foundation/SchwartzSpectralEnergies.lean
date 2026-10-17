import Foundation.SpectralMomentIntegrals
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Actual Schwartz Fourier energies, with an explicit radial normalization. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology FourierTransform SchwartzMap
namespace OperatorDerivativeRewrite.Foundation.SchwartzSpectralEnergies
set_option backward.isDefEq.respectTransparency false

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem weighted_norm_sq_integrable (g : 𝓢(V, H)) (n : ℕ) :
    Integrable (fun ξ : V => ‖ξ‖^n*‖g ξ‖^2) volume := by
  have hi := g.integrable_pow_mul (volume : Measure V) n
  have hb : ∀ᵐ ξ : V ∂volume, ‖‖g ξ‖‖≤SchwartzMap.seminorm ℝ 0 0 g := by
    apply Filter.Eventually.of_forall
    intro ξ
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact SchwartzMap.norm_le_seminorm ℝ g ξ
  have hh := hi.mul_bdd g.continuous.norm.aestronglyMeasurable hb
  convert hh using 1
  ext ξ
  ring

theorem scaled_weight_integrable (g : 𝓢(V, H)) (c : ℝ) (n : ℕ) :
    Integrable (fun ξ : V => (c*‖ξ‖)^n*‖g ξ‖^2) volume := by
  convert (weighted_norm_sq_integrable g n).const_mul (c^n) using 1
  ext ξ
  rw [mul_pow]
  ring

def amplitude (f : 𝓢(V, H)) (ξ : V) : ℝ := ‖𝓕 f ξ‖
def spectralMoment (c : ℝ) (f : 𝓢(V, H)) (n : ℕ) : ℝ :=
  SpectralMomentIntegrals.moment (volume : Measure V) (fun ξ => c*‖ξ‖) (amplitude f) n
def kinetic (f : 𝓢(V, H)) : ℝ := ∫ x : V, ‖f x‖^2
def criticalEnergy (c : ℝ) (f : 𝓢(V, H)) : ℝ := spectralMoment c f 1
def dissipation (c : ℝ) (f : 𝓢(V, H)) : ℝ := spectralMoment c f 3
def frequency (c : ℝ) (f : 𝓢(V, H)) : ℝ := Real.sqrt (dissipation c f/criticalEnergy c f)

theorem amplitude_aestronglyMeasurable (f : 𝓢(V, H)) :
    AEStronglyMeasurable (amplitude f) (volume : Measure V) := by
  change AEStronglyMeasurable (fun ξ : V => ‖𝓕 f ξ‖) volume
  exact (𝓕 f).continuous.norm.aestronglyMeasurable

theorem frequency_weight_aestronglyMeasurable (c : ℝ) :
    AEStronglyMeasurable (fun ξ : V => c*‖ξ‖) (volume : Measure V) :=
  (continuous_const.mul continuous_norm).aestronglyMeasurable

theorem spectral_integrand_integrable (c : ℝ) (f : 𝓢(V, H)) (n : ℕ) :
    Integrable (fun ξ : V => (c*‖ξ‖)^n*(amplitude f ξ)^2) volume := by
  change Integrable (fun ξ : V => (c*‖ξ‖)^n*‖𝓕 f ξ‖^2) volume
  exact scaled_weight_integrable (𝓕 f) c n

theorem amplitude_sq_integrable (f : 𝓢(V, H)) :
    Integrable (fun ξ : V => (amplitude f ξ)^2) volume := by
  simpa only [pow_zero, one_mul] using spectral_integrand_integrable 1 f 0

theorem kinetic_integrable (f : 𝓢(V, H)) : Integrable (fun x : V => ‖f x‖^2) volume := by
  simpa only [pow_zero, one_mul] using weighted_norm_sq_integrable f 0

theorem spectral_zero_plancherel (c : ℝ) (f : 𝓢(V, H)) : spectralMoment c f 0=kinetic f := by
  change (∫ ξ : V, (c*‖ξ‖)^0*‖𝓕 f ξ‖^2)=(∫ x : V, ‖f x‖^2)
  simpa only [pow_zero, one_mul] using SchwartzMap.integral_norm_sq_fourier f

theorem kinetic_nonneg (f : 𝓢(V, H)) : 0≤kinetic f := integral_nonneg (fun x => sq_nonneg ‖f x‖)

theorem spectral_nonneg (c : ℝ) (hc : 0≤c) (f : 𝓢(V, H)) (n : ℕ) : 0≤spectralMoment c f n :=
  SpectralMomentIntegrals.moment_nonneg volume (fun ξ : V => c*‖ξ‖) (amplitude f)
    (Filter.Eventually.of_forall (fun ξ => mul_nonneg hc (norm_nonneg ξ))) n

theorem critical_interpolation (c : ℝ) (hc : 0≤c) (f : 𝓢(V, H)) :
    (criticalEnergy c f)^3≤(kinetic f)^2*dissipation c f := by
  have hh := SpectralMomentIntegrals.cubic_interpolation (volume : Measure V)
    (frequency_weight_aestronglyMeasurable c) (amplitude_aestronglyMeasurable f)
    (Filter.Eventually.of_forall (fun ξ : V => mul_nonneg hc (norm_nonneg ξ)))
    (amplitude_sq_integrable f) (spectral_integrand_integrable c f 3)
  change (criticalEnergy c f)^3≤(spectralMoment c f 0)^2*dissipation c f at hh
  rw [spectral_zero_plancherel] at hh
  exact hh

theorem critical_le_kinetic_frequency (c : ℝ) (hc : 0≤c) (f : 𝓢(V, H))
    (hE : 0<criticalEnergy c f) : criticalEnergy c f≤kinetic f*frequency c f :=
  SpectralEnergyInterpolation.energy_le_kinetic_mul_frequency (kinetic_nonneg f) hE
    (spectral_nonneg c hc f 3) (critical_interpolation c hc f)

theorem critical_bound_from_caps (c : ℝ) (hc : 0≤c) (f : 𝓢(V, H))
    (hE : 0<criticalEnergy c f) (B L : ℝ) (hK : kinetic f≤B) (hL : 0≤L)
    (hfreq : frequency c f≤L) : criticalEnergy c f≤B*L :=
  SpectralEnergyInterpolation.energy_bound_from_caps (kinetic_nonneg f) hE
    (spectral_nonneg c hc f 3) (critical_interpolation c hc f) hK hL hfreq

theorem normalization_scaling (c : ℝ) (f : 𝓢(V, H)) (n : ℕ) :
    spectralMoment c f n=c^n*spectralMoment 1 f n := by
  unfold spectralMoment SpectralMomentIntegrals.moment
  simp only [one_mul]
  rw [← integral_const_mul]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro ξ
  change (c*‖ξ‖)^n*(amplitude f ξ)^2 = c^n*(‖ξ‖^n*(amplitude f ξ)^2)
  rw [mul_pow]
  ring

theorem two_pi_interpolation (f : 𝓢(V, H)) :
    (criticalEnergy (2*Real.pi) f)^3≤(kinetic f)^2*dissipation (2*Real.pi) f :=
  critical_interpolation _ (by positivity) f

theorem no_schwartz_profile_with_bounded_kinetic (c : ℝ) (hc : 0≤c)
    (f : ℝ → 𝓢(V, H)) (B : ℝ)
    (hK : ∀ t∈Ico (0:ℝ) 1, kinetic (f t)≤B)
    (hE : ∀ t∈Ico (0:ℝ) 1, criticalEnergy c (f t)=CorridorFiniteTimeExit.energy t)
    (hD : ∀ t∈Ico (0:ℝ) 1, dissipation c (f t)=CorridorFiniteTimeExit.dissipation t) : False := by
  apply SpectralEnergyInterpolation.profile_no_bounded_kinetic_interpolation (fun t => kinetic (f t)) B
  · intro t ht
    exact ⟨kinetic_nonneg (f t), hK t ht⟩
  · intro t ht
    have hh := critical_interpolation c hc (f t)
    rwa [hE t ht, hD t ht] at hh

abbrev Spatial3 := EuclideanSpace ℝ (Fin 3)
abbrev Vector3 := EuclideanSpace ℂ (Fin 3)

theorem three_dimensional_interpolation (c : ℝ) (hc : 0≤c) (f : 𝓢(Spatial3, Vector3)) :
    (criticalEnergy c f)^3≤(kinetic f)^2*dissipation c f := critical_interpolation c hc f

end OperatorDerivativeRewrite.Foundation.SchwartzSpectralEnergies
