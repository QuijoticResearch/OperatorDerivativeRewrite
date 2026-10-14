import Foundation.PoissonJumpEntropy
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-! Actual exponential change of measure for Poisson sources. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.PoissonExponentialTilt
open PoissonDifferenceCore PoissonCoherentVectors

def tiltedRate (rate : ℝ≥0) (θ : ℝ) : ℝ≥0 :=
  ⟨(rate : ℝ)*Real.exp θ,mul_nonneg rate.coe_nonneg (Real.exp_pos θ).le⟩

def density (rate : ℝ≥0) (θ : ℝ) (n : ℕ) : ℝ :=
  Real.exp (θ*(n : ℝ)-(rate : ℝ)*(Real.exp θ-1))

def tiltedMeasure (rate : ℝ≥0) (θ : ℝ) : Measure ℕ :=
  (poissonLaw rate).withDensity (fun n => ENNReal.ofReal (density rate θ n))

theorem density_pos (rate : ℝ≥0) (θ : ℝ) (n : ℕ) : 0<density rate θ n := Real.exp_pos _

theorem density_weight (rate : ℝ≥0) (θ : ℝ) (n : ℕ) :
    density rate θ n*poissonWeight rate n=poissonWeight (tiltedRate rate θ) n := by
  have hr : (tiltedRate rate θ : ℝ)=(rate : ℝ)*Real.exp θ := rfl
  simp only [density,poissonWeight,poissonLaw,poissonMeasure_real_singleton]
  rw [hr,mul_pow]
  rw [mul_div_assoc,← mul_assoc,← Real.exp_add,← Real.exp_nat_mul]
  have he : θ*(n : ℝ)-(rate : ℝ)*(Real.exp θ-1)+(-(rate : ℝ))=
      -(rate : ℝ)*Real.exp θ+(n : ℝ)*θ := by ring
  rw [he,Real.exp_add]
  ring

theorem tiltedMeasure_eq_poisson (rate : ℝ≥0) (θ : ℝ) :
    tiltedMeasure rate θ=poissonLaw (tiltedRate rate θ) := by
  apply Measure.ext_of_singleton
  intro n
  rw [tiltedMeasure,withDensity_apply _ (measurableSet_singleton n),lintegral_singleton]
  have hd : 0≤density rate θ n := (Real.exp_pos _).le
  simp only [poissonLaw,poissonMeasure_singleton]
  rw [← ENNReal.ofReal_mul hd]
  have he := density_weight rate θ n
  simp only [poissonWeight,poissonLaw,poissonMeasure_real_singleton] at he
  exact congrArg ENNReal.ofReal he

theorem integral_transfer (rate : ℝ≥0) (θ : ℝ) (g : ℕ → ℝ) :
    (∫ n, g n ∂poissonLaw (tiltedRate rate θ))=
      ∫ n, density rate θ n*g n ∂poissonLaw rate := by
  rw [← tiltedMeasure_eq_poisson,tiltedMeasure,
    integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (Eventually.of_forall fun n => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (density_pos rate θ _).le,
    smul_eq_mul]

theorem density_mean_one (rate : ℝ≥0) (θ : ℝ) :
    (∫ n, density rate θ n ∂poissonLaw rate)=1 := by
  have he := integral_transfer rate θ (fun _ => (1 : ℝ))
  simpa using he.symm

theorem log_density_integrable (rate : ℝ≥0) (θ : ℝ) :
    Integrable (fun n => Real.log (density rate θ n)) (poissonLaw (tiltedRate rate θ)) := by
  have hi := (count_exponential_memLp (tiltedRate rate θ) 0).integrable (by norm_num)
  have hn : Integrable (fun n : ℕ => (n : ℝ)) (poissonLaw (tiltedRate rate θ)) := by
    simpa [exponential] using hi
  have hb := (hn.const_mul θ).sub (integrable_const ((rate : ℝ)*(Real.exp θ-1)))
  exact hb.congr (Eventually.of_forall fun n => by simp [density,Real.log_exp,Pi.sub_apply])

theorem density_log_integrable (rate : ℝ≥0) (θ : ℝ) :
    Integrable (fun n => density rate θ n*Real.log (density rate θ n)) (poissonLaw rate) := by
  have hi := log_density_integrable rate θ
  rw [← tiltedMeasure_eq_poisson,tiltedMeasure,
    integrable_withDensity_iff_integrable_smul' (by fun_prop)
      (Eventually.of_forall fun n => ENNReal.ofReal_lt_top)] at hi
  simpa only [ENNReal.toReal_ofReal (density_pos rate θ _).le,
    smul_eq_mul] using hi

theorem relative_entropy (rate : ℝ≥0) (θ : ℝ) :
    (∫ n, density rate θ n*Real.log (density rate θ n) ∂poissonLaw rate)=
      (rate : ℝ)*(θ*Real.exp θ-Real.exp θ+1) := by
  rw [← integral_transfer]
  simp only [density,Real.log_exp]
  have hi := (count_exponential_memLp (tiltedRate rate θ) 0).integrable (by norm_num)
  have hn : Integrable (fun n : ℕ => (n : ℝ)) (poissonLaw (tiltedRate rate θ)) := by
    simpa [exponential] using hi
  have hm := PoissonExponentialEntropy.count_exponential_integral (tiltedRate rate θ) 0
  have he : (∫ n : ℕ, (n : ℝ) ∂poissonLaw (tiltedRate rate θ))=(tiltedRate rate θ : ℝ) := by
    simpa [exponential] using hm
  rw [integral_sub (hn.const_mul θ) (integrable_const _),integral_const_mul,he]
  simp only [integral_const,probReal_univ,one_smul]
  change θ*((rate : ℝ)*Real.exp θ)-(rate : ℝ)*(Real.exp θ-1)=_
  ring

theorem density_factor (rate : ℝ≥0) (θ : ℝ) (n : ℕ) :
    density rate θ n=Real.exp (-(rate : ℝ)*(Real.exp θ-1))*exponential θ n := by
  rw [density,exponential,← Real.exp_add]
  congr 1
  ring

theorem density_memLp_two (rate : ℝ≥0) (θ : ℝ) :
    MemLp (density rate θ) 2 (poissonLaw rate) := by
  rw [show density rate θ=(fun n => Real.exp (-(rate : ℝ)*(Real.exp θ-1))*exponential θ n)
    from funext (density_factor rate θ)]
  exact (exponential_memLp rate θ).const_mul _

theorem density_succ (rate : ℝ≥0) (θ : ℝ) (n : ℕ) :
    density rate θ (n+1)=Real.exp θ*density rate θ n := by
  rw [density,density,← Real.exp_add]
  push_cast
  congr 1
  ring

theorem density_jumpBregman (rate : ℝ≥0) (θ : ℝ) (n : ℕ) :
    PoissonJumpEntropy.jumpBregman (density rate θ) n=
      (θ*Real.exp θ-Real.exp θ+1)*density rate θ n := by
  rw [PoissonJumpEntropy.jumpBregman,density_succ,
    mul_div_cancel_right₀ _ (ne_of_gt (density_pos rate θ n)),Real.log_exp]
  ring

theorem density_jump_integrable (rate : ℝ≥0) (θ : ℝ) :
    Integrable (PoissonJumpEntropy.jumpBregman (density rate θ)) ((rate : ℝ≥0∞) • poissonLaw rate) := by
  haveI : IsFiniteMeasure ((rate : ℝ≥0∞) • poissonLaw rate) := ⟨by simp⟩
  have hi := (((density_memLp_two rate θ).smul_measure (by finiteness)).integrable (by norm_num))
    |>.const_mul (θ*Real.exp θ-Real.exp θ+1)
  exact hi.congr (Eventually.of_forall fun n => (density_jumpBregman rate θ n).symm)

theorem relative_entropy_eq_jump_energy (rate : ℝ≥0) (θ : ℝ) :
    (∫ n, density rate θ n*Real.log (density rate θ n) ∂poissonLaw rate)=
      PoissonJumpEntropy.jumpEntropyEnergy rate (density rate θ) := by
  rw [relative_entropy,PoissonJumpEntropy.jumpEntropyEnergy]
  simp only [density_jumpBregman]
  rw [integral_smul_measure,integral_const_mul,density_mean_one]
  simp

end OperatorDerivativeRewrite.Foundation.PoissonExponentialTilt
