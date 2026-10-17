import Foundation.SchwartzSpectralEnergies

/-! Physical directional and gradient energies with the actual Fourier normalization. -/
noncomputable section
open MeasureTheory
open scoped Topology FourierTransform SchwartzMap LineDeriv
namespace OperatorDerivativeRewrite.Foundation.SchwartzDerivativeEnergies
set_option backward.isDefEq.respectTransparency false

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem fourier_directional_norm_sq (f : 𝓢(V, H)) (m ξ : V) :
    ‖𝓕 (∂_{m} f) ξ‖^2 =
      (2*Real.pi)^2*(inner ℝ ξ m)^2*‖𝓕 f ξ‖^2 := by
  have hg : (inner ℝ · m).HasTemperateGrowth :=
    ((innerSL ℝ).flip m).hasTemperateGrowth
  rw [SchwartzMap.fourier_lineDerivOp_eq]
  simp only [smul_apply, SchwartzMap.smulLeftCLM_apply_apply hg,
    norm_smul, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat,
    Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

theorem directional_integrand_integrable (f : 𝓢(V, H)) (m : V) :
    Integrable (fun ξ : V => (2*Real.pi)^2*(inner ℝ ξ m)^2*‖𝓕 f ξ‖^2) volume := by
  have hh := SchwartzSpectralEnergies.amplitude_sq_integrable (∂_{m} f)
  change Integrable (fun ξ : V => ‖𝓕 (∂_{m} f) ξ‖^2) volume at hh
  simpa only [fourier_directional_norm_sq] using hh

theorem directional_plancherel (f : 𝓢(V, H)) (m : V) :
    (∫ x : V, ‖fderiv ℝ f x m‖^2) =
      ∫ ξ : V, (2*Real.pi)^2*(inner ℝ ξ m)^2*‖𝓕 f ξ‖^2 := by
  calc
    _ = ∫ ξ : V, ‖𝓕 (∂_{m} f) ξ‖^2 :=
      (SchwartzMap.integral_norm_sq_fourier (∂_{m} f)).symm
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall (fourier_directional_norm_sq f m))

variable {ι : Type*} [Fintype ι]

def gradientDensity (b : OrthonormalBasis ι ℝ V) (f : 𝓢(V, H)) (x : V) : ℝ :=
  ∑ i, ‖fderiv ℝ f x (b i)‖^2

def gradientEnergy (b : OrthonormalBasis ι ℝ V) (f : 𝓢(V, H)) : ℝ :=
  ∫ x : V, gradientDensity b f x

theorem gradient_density_integrable (b : OrthonormalBasis ι ℝ V) (f : 𝓢(V, H)) :
    Integrable (gradientDensity b f) volume := by
  apply integrable_finsetSum
  intro i hi
  exact SchwartzSpectralEnergies.kinetic_integrable (∂_{b i} f)

theorem gradient_plancherel (b : OrthonormalBasis ι ℝ V) (f : 𝓢(V, H)) :
    gradientEnergy b f = SchwartzSpectralEnergies.spectralMoment (2*Real.pi) f 2 := by
  unfold gradientEnergy gradientDensity
  have hi (i : ι) : Integrable (fun x : V => ‖fderiv ℝ f x (b i)‖^2) volume :=
    SchwartzSpectralEnergies.kinetic_integrable (∂_{b i} f)
  rw [integral_finsetSum _ (fun i _ => hi i)]
  simp_rw [directional_plancherel]
  rw [← integral_finsetSum _ (fun i _ => directional_integrand_integrable f (b i))]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro ξ
  change (∑ i, (2*Real.pi)^2*(inner ℝ ξ (b i))^2*‖𝓕 f ξ‖^2) =
    (2*Real.pi*‖ξ‖)^2*‖𝓕 f ξ‖^2
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  have hb := b.sum_sq_norm_inner_left ξ
  simp only [Real.norm_eq_abs, sq_abs] at hb
  rw [hb, mul_pow]
  ring

theorem gradient_basis_independent {κ : Type*} [Fintype κ]
    (b : OrthonormalBasis ι ℝ V) (d : OrthonormalBasis κ ℝ V) (f : 𝓢(V, H)) :
    gradientEnergy b f = gradientEnergy d f := by
  rw [gradient_plancherel, gradient_plancherel]

theorem critical_squared_le_kinetic_gradient (b : OrthonormalBasis ι ℝ V) (f : 𝓢(V, H)) :
    (SchwartzSpectralEnergies.criticalEnergy (2*Real.pi) f)^2 ≤
      SchwartzSpectralEnergies.kinetic f * gradientEnergy b f := by
  have hh := SpectralMomentIntegrals.cauchy_zero (volume : Measure V)
    (SchwartzSpectralEnergies.frequency_weight_aestronglyMeasurable (2*Real.pi))
    (SchwartzSpectralEnergies.amplitude_aestronglyMeasurable f)
    (Filter.Eventually.of_forall (fun ξ : V =>
      mul_nonneg (by positivity : 0≤2*Real.pi) (norm_nonneg ξ)))
    (SchwartzSpectralEnergies.amplitude_sq_integrable f)
    (SchwartzSpectralEnergies.spectral_integrand_integrable (2*Real.pi) f 3)
  change (SchwartzSpectralEnergies.criticalEnergy (2*Real.pi) f)^2 ≤
    SchwartzSpectralEnergies.spectralMoment (2*Real.pi) f 0 *
      SchwartzSpectralEnergies.spectralMoment (2*Real.pi) f 2 at hh
  rwa [SchwartzSpectralEnergies.spectral_zero_plancherel, ← gradient_plancherel b] at hh

theorem gradient_squared_le_critical_dissipation (b : OrthonormalBasis ι ℝ V) (f : 𝓢(V, H)) :
    (gradientEnergy b f)^2 ≤ SchwartzSpectralEnergies.criticalEnergy (2*Real.pi) f *
      SchwartzSpectralEnergies.dissipation (2*Real.pi) f := by
  have hh := SpectralMomentIntegrals.cauchy_one (volume : Measure V)
    (SchwartzSpectralEnergies.frequency_weight_aestronglyMeasurable (2*Real.pi))
    (SchwartzSpectralEnergies.amplitude_aestronglyMeasurable f)
    (Filter.Eventually.of_forall (fun ξ : V =>
      mul_nonneg (by positivity : 0≤2*Real.pi) (norm_nonneg ξ)))
    (SchwartzSpectralEnergies.amplitude_sq_integrable f)
    (SchwartzSpectralEnergies.spectral_integrand_integrable (2*Real.pi) f 3)
  change (SchwartzSpectralEnergies.spectralMoment (2*Real.pi) f 2)^2 ≤
    SchwartzSpectralEnergies.criticalEnergy (2*Real.pi) f *
      SchwartzSpectralEnergies.dissipation (2*Real.pi) f at hh
  rwa [← gradient_plancherel b] at hh

end OperatorDerivativeRewrite.Foundation.SchwartzDerivativeEnergies
