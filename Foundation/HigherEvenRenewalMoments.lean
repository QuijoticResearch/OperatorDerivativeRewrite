import Foundation.FiniteMarkedRenewalMarginals
import Foundation.HigherEvenRenewalProcess
import Foundation.CyclicPolynomialKernel
import Foundation.ComplexRootPoissonQuarticDrift

/-! Actual polynomial moments of the all-even-order renewal realizations. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.HigherEvenRenewalMoments
open FiniteMarkedRenewalMarginals HigherEvenRootInnovation

theorem finite_lower (m : ℕ) [NeZero m] (a : ℝ) (d : ℕ) (hd : d < 2*m) (n : ℕ) (x : ℂ) :
    (∫ ξ, (x+terminal (innovation m a) n ξ)^d
      ∂finiteProbability (CyclicRootProbabilityNoise.probability (2*m)) n) = x^d := by
  induction n generalizing x with
  | zero => simp [terminal]
  | succ n ih =>
    rw [terminal_successor (CyclicRootProbabilityNoise.probability (2*m))
      (innovation m a) n (fun y : ℂ => y^d) x]
    simp_rw [ih]
    change CyclicPolynomialKernel.transition (2*m) ((a : ℂ)*phase m) (fun y => y^d) x = _
    exact CyclicPolynomialKernel.lower_monomial _ _ _ d hd

theorem finite_leading (m : ℕ) [NeZero m] (a : ℝ) (n : ℕ) (x : ℂ) :
    (∫ ξ, (x+terminal (innovation m a) n ξ)^(2*m)
      ∂finiteProbability (CyclicRootProbabilityNoise.probability (2*m)) n) =
      x^(2*m)+(n : ℂ)*(a : ℂ)^(2*m)*(-1 : ℂ)^(m+1) := by
  induction n generalizing x with
  | zero => simp [terminal]
  | succ n ih =>
    rw [terminal_successor (CyclicRootProbabilityNoise.probability (2*m))
      (innovation m a) n (fun y : ℂ => y^(2*m)) x]
    simp_rw [ih]
    rw [integral_add Integrable.of_finite (integrable_const _)]
    have he : (∫ k, (x+innovation m a k)^(2*m) ∂CyclicRootProbabilityNoise.probability (2*m)) =
        x^(2*m)+(a : ℂ)^(2*m)*(-1 : ℂ)^(m+1) := by
      change CyclicPolynomialKernel.transition (2*m) ((a : ℂ)*phase m) (fun y => y^(2*m)) x = _
      rw [CyclicPolynomialKernel.leading_monomial,mul_pow,phase_power]
    rw [he]
    simp only [integral_const,probReal_univ,one_smul]
    push_cast
    ring

theorem power_integrable (m : ℕ) [NeZero m] (a : ℝ) (t : ℝ≥0) (d : ℕ) :
    Integrable (fun ω => HigherEvenRenewalProcess.process m a t ω^d)
      (HigherEvenRenewalProcess.probability m) :=
  process_power_integrable (CyclicRootProbabilityNoise.probability (2*m)) (innovation m a)
    (measurable_of_countable _) |a| (fun k => (HigherEvenRenewalProcess.innovation_norm m a k).le) t d

theorem process_lower (m : ℕ) [NeZero m] (a : ℝ) (t : ℝ≥0) (d : ℕ) (hd0 : 0 < d)
    (hd : d < 2*m) :
    (∫ ω, HigherEvenRenewalProcess.process m a t ω^d ∂HigherEvenRenewalProcess.probability m) = 0 := by
  have hI := process_power_integrable (CyclicRootProbabilityNoise.probability (2*m)) (innovation m a)
    (measurable_of_countable _) |a| (fun k => (HigherEvenRenewalProcess.innovation_norm m a k).le) t d
  change (∫ ω, MarkedRenewalRealization.process (innovation m a) t ω^d
    ∂MarkedRenewalRealization.probability (CyclicRootProbabilityNoise.probability (2*m))) = _
  rw [process_mixture _ _ t (fun y : ℂ => y^d) hI]
  have he (n : ℕ) : (∫ ξ, terminal (innovation m a) n ξ^d
      ∂finiteProbability (CyclicRootProbabilityNoise.probability (2*m)) n) = 0 := by
    simpa only [zero_add,zero_pow (ne_of_gt hd0)] using finite_lower m a d hd n 0
  simp_rw [he]
  simp

theorem process_leading (m : ℕ) [NeZero m] (a : ℝ) (t : ℝ≥0) :
    (∫ ω, HigherEvenRenewalProcess.process m a t ω^(2*m) ∂HigherEvenRenewalProcess.probability m) =
      (t : ℂ)*(a : ℂ)^(2*m)*(-1 : ℂ)^(m+1) := by
  have hI := process_power_integrable (CyclicRootProbabilityNoise.probability (2*m)) (innovation m a)
    (measurable_of_countable _) |a| (fun k => (HigherEvenRenewalProcess.innovation_norm m a k).le) t (2*m)
  change (∫ ω, MarkedRenewalRealization.process (innovation m a) t ω^(2*m)
    ∂MarkedRenewalRealization.probability (CyclicRootProbabilityNoise.probability (2*m))) = _
  rw [process_mixture _ _ t (fun y : ℂ => y^(2*m)) hI]
  have he (n : ℕ) : (∫ ξ, terminal (innovation m a) n ξ^(2*m)
      ∂finiteProbability (CyclicRootProbabilityNoise.probability (2*m)) n) =
      (n : ℂ)*(a : ℂ)^(2*m)*(-1 : ℂ)^(m+1) := by
    have hm := NeZero.pos m
    simpa only [zero_add,zero_pow (by omega : 2*m ≠ 0)] using finite_leading m a n 0
  simp_rw [he]
  rw [integral_mul_const,integral_mul_const,ComplexRootPoissonQuarticDrift.complex_count_integral]

theorem normalized_leading (m : ℕ) [NeZero m] (a : ℝ) (ha : a ≠ 0) (t : ℝ≥0) :
    (∫ ω, HigherEvenRenewalProcess.process m a
        (Real.toNNReal (CyclicPolynomialKernel.rate m a)*t : ℝ≥0) ω^(2*m)
      ∂HigherEvenRenewalProcess.probability m) =
      (t : ℂ)*(Nat.factorial (2*m) : ℂ)*(-1 : ℂ)^(m+1) := by
  rw [process_leading m a (Real.toNNReal (CyclicPolynomialKernel.rate m a)*t)]
  have hr := (CyclicPolynomialKernel.rate_pos m a ha).le
  have hc : ((Real.toNNReal (CyclicPolynomialKernel.rate m a)*t : ℝ≥0) : ℂ) =
      (CyclicPolynomialKernel.rate m a : ℂ)*(t : ℂ) := by
    have he : ((Real.toNNReal (CyclicPolynomialKernel.rate m a)*t : ℝ≥0) : ℝ) =
        CyclicPolynomialKernel.rate m a*(t : ℝ) := by rw [NNReal.coe_mul,Real.coe_toNNReal _ hr]
    simpa only [Complex.ofReal_mul] using congrArg Complex.ofReal he
  have hs : (CyclicPolynomialKernel.rate m a : ℂ)*(a : ℂ)^(2*m) = (Nat.factorial (2*m) : ℂ) := by
    have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha
    simp only [CyclicPolynomialKernel.rate,Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_pow]
    field_simp
  rw [hc]
  calc
    _ = (t : ℂ)*((CyclicPolynomialKernel.rate m a : ℂ)*(a : ℂ)^(2*m))*(-1 : ℂ)^(m+1) := by ring
    _ = _ := by rw [hs]

end OperatorDerivativeRewrite.Foundation.HigherEvenRenewalMoments
