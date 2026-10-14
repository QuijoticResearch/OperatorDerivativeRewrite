import Foundation.PoissonExponentialEntropy

/-! Forward jump Bregman entropy for actual exponential Poisson densities.
This verifies the exponential family, not a general modified log-Sobolev theorem. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.PoissonJumpEntropy
open PoissonDifferenceCore PoissonCoherentVectors PoissonExponentialEntropy

def jumpBregman (ρ : ℕ → ℝ) (n : ℕ) : ℝ :=
  ρ (n+1)*Real.log (ρ (n+1)/ρ n)-ρ (n+1)+ρ n

def jumpEntropyEnergy (rate : ℝ≥0) (ρ : ℕ → ℝ) : ℝ :=
  ∫ n, jumpBregman ρ n ∂((rate : ℝ≥0∞) • poissonLaw rate)

theorem exponential_jumpBregman (θ : ℝ) (n : ℕ) :
    jumpBregman (exponential θ) n=
      (θ*Real.exp θ-Real.exp θ+1)*exponential θ n := by
  have hs : exponential θ (n+1)=Real.exp θ*exponential θ n := by
    simp only [exponential,Nat.cast_add,Nat.cast_one,mul_add,Real.exp_add]
    ring
  have hp : exponential θ n≠0 := ne_of_gt (Real.exp_pos _)
  rw [jumpBregman,hs,mul_div_cancel_right₀ _ hp,Real.log_exp]
  ring

theorem exponential_jump_integrable (rate : ℝ≥0) (θ : ℝ) :
    Integrable (jumpBregman (exponential θ)) ((rate : ℝ≥0∞) • poissonLaw rate) := by
  haveI : IsFiniteMeasure ((rate : ℝ≥0∞) • poissonLaw rate) := ⟨by simp⟩
  have hi := (((exponential_memLp rate θ).smul_measure (by finiteness)).integrable (by norm_num))
    |>.const_mul (θ*Real.exp θ-Real.exp θ+1)
  exact hi.congr (Filter.Eventually.of_forall fun n => (exponential_jumpBregman θ n).symm)

theorem exponential_jump_energy (rate : ℝ≥0) (θ : ℝ) :
    jumpEntropyEnergy rate (exponential θ)=
      (rate : ℝ)*Real.exp ((rate : ℝ)*(Real.exp θ-1))*(θ*Real.exp θ-Real.exp θ+1) := by
  rw [jumpEntropyEnergy]
  simp only [exponential_jumpBregman]
  rw [integral_smul_measure,integral_const_mul,exponential_integral]
  simp
  ring

theorem exponential_square_entropy_eq_jump_energy (rate : ℝ≥0) (θ : ℝ) :
    entropySq (poissonLaw rate) (exponential θ)=
      jumpEntropyEnergy rate (fun n => (exponential θ n)^2) := by
  have he : (fun n => (exponential θ n)^2)=exponential (2*θ) := funext (exponential_square θ)
  rw [he,exponential_entropy,exponential_jump_energy]

theorem exponential_jump_energy_nonneg (rate : ℝ≥0) (θ : ℝ) :
    0 ≤ jumpEntropyEnergy rate (exponential θ) := by
  have hk : 0 ≤ θ*Real.exp θ-Real.exp θ+1 := by
    have hp := InformationTheory.klFun_nonneg (Real.exp_nonneg θ)
    simp only [InformationTheory.klFun,Real.log_exp] at hp
    nlinarith
  rw [exponential_jump_energy]
  exact mul_nonneg (mul_nonneg rate.coe_nonneg (Real.exp_nonneg _)) hk

end OperatorDerivativeRewrite.Foundation.PoissonJumpEntropy
