import Foundation.DictionaryLowDerivative
import Foundation.GaussianCore

/-! A Gaussian high amplitude of size 1/N does not make its low-direction
projected advection sensitivity small in mean square. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace OperatorDerivativeRewrite.Foundation.DictionaryGaussianSensitivity
open DictionaryLowDerivative
set_option backward.isDefEq.respectTransparency false

abbrev γ := GaussianCore.γ

def background (N : ℤ) (σ c : ℝ) : ℝ := σ*c/(N : ℝ)

theorem gaussian_square : (∫ c : ℝ, c^2 ∂γ)=1 := by
  have h := GaussianCore.polynomial_stein (Polynomial.X : Polynomial ℝ)
  simpa [pow_two] using h

theorem background_mean (N : ℤ) (σ : ℝ) : (∫ c, background N σ c ∂γ)=0 := by
  have he : background N σ = fun c : ℝ => (σ/(N : ℝ))*c := by
    funext c; simp [background]; ring
  rw [he,integral_const_mul]
  simp [γ,GaussianCore.γ]

theorem background_second (N : ℤ) (σ : ℝ) :
    (∫ c, (background N σ c)^2 ∂γ)=σ^2/(N : ℝ)^2 := by
  have he : (fun c => (background N σ c)^2)=fun c : ℝ =>
      (σ^2/(N : ℝ)^2)*c^2 := by
    funext c; simp [background]; ring
  rw [he,integral_const_mul,gaussian_square,mul_one]

def probeSensitivity (N : ℤ) (σ c : ℝ) : ℝ :=
  deriv (fun a => projectedAdvection N a (background N σ c) ![Real.pi/2,0,0] 2) 0

theorem probe_formula (N : ℤ) (hN : N ≠ 0) (σ c : ℝ) :
    probeSensitivity N σ c=4*σ*c := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  unfold probeSensitivity
  rw [(projected_physical_derivative N (background N σ c) ![Real.pi/2,0,0]).deriv]
  simp [background]
  field_simp
  <;> ring

theorem probe_mean (N : ℤ) (hN : N ≠ 0) (σ : ℝ) :
    (∫ c, probeSensitivity N σ c ∂γ)=0 := by
  simp_rw [probe_formula N hN]
  rw [show (fun c : ℝ => 4*σ*c)=fun c => (4*σ)*c from rfl,integral_const_mul]
  simp [γ,GaussianCore.γ]

theorem probe_second (N : ℤ) (hN : N ≠ 0) (σ : ℝ) :
    (∫ c, (probeSensitivity N σ c)^2 ∂γ)=16*σ^2 := by
  have he : (fun c => (probeSensitivity N σ c)^2)=fun c : ℝ =>
      (16*σ^2)*c^2 := by funext c; rw [probe_formula N hN]; ring
  rw [he,integral_const_mul,gaussian_square,mul_one]

theorem expected_physical_energy (N : ℤ) (hN : N ≠ 0) (σ : ℝ) :
    (∫ c, derivativeEnergy N (background N σ c) ∂γ)=4*σ^2 := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  have he : (fun c => derivativeEnergy N (background N σ c))=fun c : ℝ =>
      (4*σ^2)*c^2 := by
    funext c
    rw [derivativeEnergy_formula N hN]
    unfold background
    field_simp
    <;> ring
  rw [he,integral_const_mul,gaussian_square,mul_one]

theorem expected_low_energy_zero (N : ℤ) (hN : 4 ≤ N) (σ : ℝ) :
    (∫ c, lowH1Energy ((N : ℝ)/2) N 0 (background N σ c) ∂γ)=0 := by
  simp_rw [lowH1Energy_zero N hN]
  simp

theorem no_expected_low_only_bound (N : ℤ) (hN : 4 ≤ N) (σ C : ℝ) (hσ : σ ≠ 0) :
    ¬ (∫ c, derivativeEnergy N (background N σ c) ∂γ) ≤
      C*(∫ c, lowH1Energy ((N : ℝ)/2) N 0 (background N σ c) ∂γ) := by
  rw [expected_physical_energy N (by omega),expected_low_energy_zero N hN,mul_zero]
  exact not_le.mpr (mul_pos (by norm_num) (sq_pos_of_ne_zero hσ))

end OperatorDerivativeRewrite.Foundation.DictionaryGaussianSensitivity
