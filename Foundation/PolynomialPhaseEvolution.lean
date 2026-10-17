import Mathlib.Analysis.Distribution.FourierMultiplier

/-! Actual polynomial-phase evolutions on Schwartz functions and tempered
 distributions. The cubic phase is the Fourier evolution for the Airy branch;
 identification of its differential equation is a separate theorem. No signed
 or probability path-space measure is postulated. -/
noncomputable section
open MeasureTheory FourierTransform
open scoped SchwartzMap Topology
namespace OperatorDerivativeRewrite.Foundation.PolynomialPhaseEvolution
set_option backward.isDefEq.respectTransparency false

def phase (p : ℕ) (t x : ℝ) : ℂ :=
  Complex.exp ((-t*(2*Real.pi*x)^p : ℝ)*Complex.I)

theorem phase_growth (p : ℕ) (t : ℝ) : (phase p t).HasTemperateGrowth := by
  exact Complex.hasTemperateGrowth_exp_mul_I.comp (by fun_prop)

theorem phase_zero (p : ℕ) : phase p 0 = fun _ => 1 := by
  funext x
  simp [phase]

theorem phase_add (p : ℕ) (s t : ℝ) : phase p (s+t) = phase p s * phase p t := by
  funext x
  simp only [phase,Pi.mul_apply]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem phase_norm (p : ℕ) (t x : ℝ) : ‖phase p t x‖ = 1 := by
  simp only [phase,Complex.norm_exp,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,Real.exp_zero]

def schwartzOp (p : ℕ) (t : ℝ) : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  SchwartzMap.fourierMultiplierCLM ℂ (phase p t)

def distributionOp (p : ℕ) (t : ℝ) : 𝓢'(ℝ, ℂ) →L[ℂ] 𝓢'(ℝ, ℂ) :=
  TemperedDistribution.fourierMultiplierCLM ℂ (phase p t)

theorem schwartz_zero (p : ℕ) : schwartzOp p 0 = ContinuousLinearMap.id ℂ _ := by
  simp [schwartzOp,phase_zero]

theorem distribution_zero (p : ℕ) : distributionOp p 0 = ContinuousLinearMap.id ℂ _ := by
  simp [distributionOp,phase_zero]

theorem schwartz_group (p : ℕ) (s t : ℝ) :
    (schwartzOp p s).comp (schwartzOp p t) = schwartzOp p (s+t) := by
  exact (SchwartzMap.fourierMultiplierCLM_compL_fourierMultiplierCLM
    (phase_growth p s) (phase_growth p t)).trans
    (congrArg (SchwartzMap.fourierMultiplierCLM ℂ) (phase_add p s t).symm)

theorem distribution_group (p : ℕ) (s t : ℝ) :
    (distributionOp p s).comp (distributionOp p t) = distributionOp p (s+t) := by
  rw [show s+t=t+s by ring]
  exact (TemperedDistribution.fourierMultiplierCLM_compL_fourierMultiplierCLM
    (phase_growth p t) (phase_growth p s)).trans
    (congrArg (TemperedDistribution.fourierMultiplierCLM ℂ) (phase_add p t s).symm)

theorem schwartz_inverse (p : ℕ) (t : ℝ) :
    (schwartzOp p (-t)).comp (schwartzOp p t) = ContinuousLinearMap.id ℂ _ := by
  rw [schwartz_group,neg_add_cancel,schwartz_zero]

theorem distribution_inverse (p : ℕ) (t : ℝ) :
    (distributionOp p (-t)).comp (distributionOp p t) = ContinuousLinearMap.id ℂ _ := by
  rw [distribution_group,neg_add_cancel,distribution_zero]

def kernel (p : ℕ) (t : ℝ) : 𝓢'(ℝ, ℂ) :=
  distributionOp p t (TemperedDistribution.delta 0)

theorem kernel_zero (p : ℕ) : kernel p 0 = TemperedDistribution.delta (0 : ℝ) := by
  rw [kernel,distribution_zero,ContinuousLinearMap.id_apply]

theorem kernel_propagation (p : ℕ) (s t : ℝ) :
    distributionOp p s (kernel p t) = kernel p (s+t) := by
  exact congrArg (fun L : 𝓢'(ℝ, ℂ) →L[ℂ] 𝓢'(ℝ, ℂ) =>
    L (TemperedDistribution.delta 0)) (distribution_group p s t)

theorem kernel_pairing (p : ℕ) (t : ℝ) (f : 𝓢(ℝ, ℂ)) :
    kernel p t f = (𝓕 (SchwartzMap.smulLeftCLM ℂ (phase p t) (𝓕⁻ f))) 0 := rfl

end OperatorDerivativeRewrite.Foundation.PolynomialPhaseEvolution
