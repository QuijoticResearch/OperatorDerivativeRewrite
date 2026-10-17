import Foundation.HigherHeatGenerator

/-! Identification with the actual higher spatial derivative on Schwartz inputs. -/
noncomputable section
open MeasureTheory FourierTransform Polynomial
open scoped NNReal SchwartzMap Topology
namespace OperatorDerivativeRewrite.Foundation.HigherHeatSpatialGenerator
set_option backward.isDefEq.respectTransparency false
open HigherHeatL2 HigherHeatGenerator

def jet : ℕ → 𝓢(ℝ,ℂ) → 𝓢(ℝ,ℂ)
  | 0,f => f
  | k+1,f => SchwartzMap.derivCLM ℂ ℂ (jet k f)

theorem jet_coe (k : ℕ) (f : 𝓢(ℝ,ℂ)) : (jet k f : ℝ → ℂ) = iteratedDeriv k f := by
  induction k with
  | zero => rfl
  | succ k hk =>
    funext x
    change deriv (jet k f) x = iteratedDeriv (k+1) f x
    rw [hk,iteratedDeriv_succ]

def differential (m : ℕ) (f : 𝓢(ℝ,ℂ)) : 𝓢(ℝ,ℂ) := (-1 : ℂ)^(m+1) • jet (2*m) f

def spectral (m : ℕ) (f : 𝓢(ℝ,ℂ)) : 𝓢(ℝ,ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => ((-weight m x : ℝ) : ℂ)) (𝓕 f)

theorem spectral_apply (m : ℕ) (f : 𝓢(ℝ,ℂ)) (x : ℝ) :
    spectral m f x = ((-weight m x : ℝ) : ℂ) * 𝓕 f x := by
  exact SchwartzMap.smulLeftCLM_apply_apply (by unfold weight; fun_prop) _ _

theorem derivative_factor (m : ℕ) (x : ℝ) :
    (-1 : ℂ)^(m+1) * (2*Real.pi*Complex.I*(x : ℂ))^(2*m) =
      ((-weight m x : ℝ) : ℂ) := by
  have hi : (2*Real.pi*Complex.I*(x : ℂ))^2 = -(2*Real.pi*(x : ℂ))^2 := by
    ring_nf
    simp
  have hn : (-1 : ℂ)^(m+1)*(-1 : ℂ)^m = -1 := by
    rw [← pow_add,show m+1+m=2*m+1 by omega,pow_add,pow_mul]
    norm_num
  have hp : (2*Real.pi*Complex.I*(x : ℂ))^(2*m) =
      (-1 : ℂ)^m * (2*Real.pi*(x : ℂ))^(2*m) := by
    rw [pow_mul,hi,neg_pow,← pow_mul]
  rw [hp,← mul_assoc,hn]
  simp only [weight,Complex.ofReal_neg,Complex.ofReal_pow,Complex.ofReal_mul,Complex.ofReal_ofNat]
  ring

theorem differential_fourier (m : ℕ) (f : 𝓢(ℝ,ℂ)) : 𝓕 (differential m f) = spectral m f := by
  have hi (k : ℕ) : Integrable (iteratedDeriv k (f : ℝ → ℂ)) := by
    rw [← jet_coe]
    exact (jet k f).integrable
  have hf := Real.fourier_iteratedDeriv (N := ⊤) (f.smooth ⊤) (fun k _ => hi k)
    (n := 2*m) (by simp)
  ext x
  rw [differential,FourierTransform.fourier_smul,SchwartzMap.smul_apply,
    SchwartzMap.fourier_coe,jet_coe,hf,spectral_apply]
  simp only [smul_eq_mul]
  rw [← mul_assoc,derivative_factor]
  simp only [SchwartzMap.fourier_coe]

theorem target_ae_spectral (m : ℕ) (f : 𝓢(ℝ,ℂ)) :
    target m (𝓕 (f.toLp 2 volume)) =ᵐ[volume] (spectral m f : ℝ → ℂ) := by
  rw [SchwartzMap.toLp_fourier_eq]
  filter_upwards [(𝓕 f).coeFn_toLp 2] with x hx
  simp only [target,hx,spectral_apply]

theorem in_domain (m : ℕ) (f : 𝓢(ℝ,ℂ)) : MemLp (target m (𝓕 (f.toLp 2 volume))) 2 volume := by
  have h : MemLp (spectral m f : ℝ → ℂ) 2 volume := (spectral m f).memLp 2 volume
  exact (memLp_congr_ae (target_ae_spectral m f)).mpr h

theorem generator_eq_differential (m : ℕ) (f : 𝓢(ℝ,ℂ)) :
    HigherHeatGenerator.generator m (f.toLp 2 volume) (in_domain m f) = (differential m f).toLp 2 volume := by
  have he : (in_domain m f).toLp (target m (𝓕 (f.toLp 2 volume))) = (spectral m f).toLp 2 volume := by
    apply Lp.ext
    filter_upwards [(in_domain m f).coeFn_toLp,(spectral m f).coeFn_toLp 2,
      target_ae_spectral m f] with x h1 h2 h3
    rw [h1,h2,h3]
  rw [generator,he,SchwartzMap.toLp_fourierInv_eq,← differential_fourier,fourierInv_fourier_eq]

theorem evolution_hasDerivWithinAt (m : ℕ) (f : 𝓢(ℝ,ℂ)) :
    HasDerivWithinAt (fun t : ℝ => HigherHeatL2.evolution m t.toNNReal (f.toLp 2 volume))
      ((differential m f).toLp 2 volume) (Set.Ici 0) 0 := by
  rw [← generator_eq_differential]
  exact HigherHeatGenerator.evolution_hasDerivWithinAt m (f.toLp 2 volume) (in_domain m f)

end OperatorDerivativeRewrite.Foundation.HigherHeatSpatialGenerator
