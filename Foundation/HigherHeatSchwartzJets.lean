import Foundation.HigherHeatSpatialGenerator
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

/-! Actual Schwartz weighted Fourier identities and all-order integration by parts. -/
noncomputable section
open MeasureTheory FourierTransform
open scoped SchwartzMap Topology
namespace OperatorDerivativeRewrite.Foundation.HigherHeatSchwartzJets
open HigherHeatSpatialGenerator

def weighted (f : 𝓢(ℝ,ℂ)) : 𝓢(ℝ,ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => x) f

theorem weighted_apply (f : 𝓢(ℝ,ℂ)) (x : ℝ) : weighted f x=(x:ℂ)*f x := by
  rw [weighted,SchwartzMap.smulLeftCLM_apply (by fun_prop)]
  exact Complex.real_smul

theorem weighted_integrable (f : 𝓢(ℝ,ℂ)) : Integrable (fun x : ℝ => x • f x) := by
  convert (weighted f).integrable (μ := volume) using 1
  funext x
  rw [weighted_apply,Complex.real_smul]

theorem fourier_weighted (f : 𝓢(ℝ,ℂ)) (ξ : ℝ) :
    deriv (𝓕 (f : ℝ → ℂ)) ξ=(-2*Real.pi*Complex.I)*𝓕 (weighted f) ξ := by
  rw [Real.deriv_fourier f.integrable (weighted_integrable f)]
  have he : (fun x : ℝ => (-2*Real.pi*Complex.I*(x:ℂ)) • f x)=
      (fun x : ℝ => (-2*Real.pi*Complex.I) • weighted f x) := by
    funext x
    rw [weighted_apply]
    simp only [smul_eq_mul]
    ring
  rw [he]
  change 𝓕 (((-2*Real.pi*Complex.I) • weighted f : 𝓢(ℝ,ℂ)) : ℝ → ℂ) ξ=_
  rw [← SchwartzMap.fourier_coe,FourierTransform.fourier_smul,SchwartzMap.smul_apply]
  rfl

theorem jet_fourier (k : ℕ) (f : 𝓢(ℝ,ℂ)) (ξ : ℝ) :
    𝓕 (jet k f) ξ=(2*Real.pi*Complex.I*(ξ:ℂ))^k*𝓕 f ξ := by
  have hi (j : ℕ) : Integrable (iteratedDeriv j (f : ℝ → ℂ)) := by
    rw [← jet_coe]
    exact (jet j f).integrable
  have hf := Real.fourier_iteratedDeriv (N := ⊤) (f.smooth ⊤) (fun j _ => hi j)
    (n := k) (by simp)
  rw [SchwartzMap.fourier_coe,jet_coe,hf]
  rfl

theorem integral_jet_mul (k : ℕ) (f g : 𝓢(ℝ,ℂ)) :
    (∫ x : ℝ, jet k f x*g x)=(-1:ℂ)^k*(∫ x : ℝ, f x*jet k g x) := by
  induction k generalizing f g with
  | zero => simp [jet]
  | succ k ih =>
    change (∫ x : ℝ, deriv (jet k f) x*g x)=_
    have h := SchwartzMap.integral_mul_deriv_eq_neg_deriv_mul (jet k f) g
    have h' : (∫ x : ℝ, deriv (jet k f) x*g x)=
        -(∫ x : ℝ, jet k f x*deriv g x) := by
      linear_combination h
    rw [h']
    have hh := ih f (SchwartzMap.derivCLM ℂ ℂ g)
    have hj : jet k (SchwartzMap.derivCLM ℂ ℂ g)=jet (k+1) g := by
      apply DFunLike.coe_injective
      rw [jet_coe,jet_coe,iteratedDeriv_succ']
      rfl
    change -(∫ x : ℝ, jet k f x*(SchwartzMap.derivCLM ℂ ℂ g) x)=_
    rw [hh,hj,pow_succ]
    ring

end OperatorDerivativeRewrite.Foundation.HigherHeatSchwartzJets
