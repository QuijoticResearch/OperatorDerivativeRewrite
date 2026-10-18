import Foundation.CyclicMarkRepresentation
import Foundation.FiniteMarkedRenewalMarginals
import Foundation.CyclicPolynomialKernel
import Foundation.BochnerL2Dominated
import Foundation.HigherEvenRenewalProcess

/-! Positive Hermitian energy of the actual all-even-order probability realizations. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.HigherEvenRenewalEnergy

theorem finite_shift_energy {A : Type*} [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
    (μ : Measure A) [IsProbabilityMeasure μ] (z : A → ℂ) (hz : (∫ k, z k ∂μ) = 0) (x : ℂ) :
    (∫ k, ‖x+z k‖^2 ∂μ) = ‖x‖^2+(∫ k, ‖z k‖^2 ∂μ) := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_add,← integral_complex_ofReal,← integral_complex_ofReal]
  simp_rw [← ComplexRootChannelGram.product_conjugate]
  simp only [map_add,add_mul,mul_add]
  simp_rw [integral_add Integrable.of_finite Integrable.of_finite]
  simp only [integral_const_mul,integral_mul_const,integral_conj,hz,map_zero,mul_zero,
    zero_mul,add_zero,zero_add,integral_const,probReal_univ,one_smul]

theorem innovation_shift_energy (m : ℕ) [NeZero m] (a : ℝ) (x : ℂ) :
    (∫ k, ‖x+HigherEvenRootInnovation.innovation m a k‖^2
      ∂CyclicRootProbabilityNoise.probability (2*m)) = ‖x‖^2+a^2 := by
  have hm : (∫ k, HigherEvenRootInnovation.innovation m a k
      ∂CyclicRootProbabilityNoise.probability (2*m)) = 0 := by
    have hpos := NeZero.pos m
    simpa only [pow_one] using HigherEvenRootInnovation.lower_moment m a 1 (by decide) (by omega)
  rw [finite_shift_energy _ _ hm,HigherEvenRootInnovation.absolute_second]

open FiniteMarkedRenewalMarginals

theorem finite_energy (m : ℕ) [NeZero m] (a : ℝ) (n : ℕ) (x : ℂ) :
    (∫ ξ, ‖x+terminal (HigherEvenRootInnovation.innovation m a) n ξ‖^2
      ∂finiteProbability (CyclicRootProbabilityNoise.probability (2*m)) n) = ‖x‖^2+(n : ℝ)*a^2 := by
  induction n generalizing x with
  | zero => simp [terminal]
  | succ n ih =>
    rw [terminal_successor (CyclicRootProbabilityNoise.probability (2*m))
      (HigherEvenRootInnovation.innovation m a) n (fun y : ℂ => ‖y‖^2) x]
    simp_rw [ih]
    rw [integral_add Integrable.of_finite (integrable_const _),innovation_shift_energy]
    simp only [integral_const,probReal_univ,one_smul]
    push_cast
    ring

theorem process_energy (m : ℕ) [NeZero m] (a : ℝ) (t : ℝ≥0) :
    (∫ ω, ‖HigherEvenRenewalProcess.process m a t ω‖^2 ∂HigherEvenRenewalProcess.probability m) =
      (t : ℝ)*a^2 := by
  have hi := MarkedRenewalRealization.process_square_integrable
    (CyclicRootProbabilityNoise.probability (2*m)) (HigherEvenRootInnovation.innovation m a)
    (measurable_of_countable _) |a| (fun k => (HigherEvenRenewalProcess.innovation_norm m a k).le) t
  change (∫ ω, ‖MarkedRenewalRealization.process (HigherEvenRootInnovation.innovation m a) t ω‖^2
    ∂MarkedRenewalRealization.probability (CyclicRootProbabilityNoise.probability (2*m))) = _
  rw [process_mixture _ _ t (fun y : ℂ => ‖y‖^2) hi]
  have he (n : ℕ) : (∫ ξ, ‖terminal (HigherEvenRootInnovation.innovation m a) n ξ‖^2
      ∂finiteProbability (CyclicRootProbabilityNoise.probability (2*m)) n) = (n : ℝ)*a^2 := by
    simpa only [zero_add,norm_zero,zero_pow (by decide : 2 ≠ 0),zero_add] using finite_energy m a n 0
  simp_rw [he]
  rw [integral_mul_const,PoissonCountMoments.count_integral]

theorem variableL2_norm_square (m : ℕ) [NeZero m] (a : ℝ) (t : ℝ≥0) :
    ‖HigherEvenRenewalProcess.variableL2 m a t‖^2 = (t : ℝ)*a^2 := by
  rw [BochnerL2Dominated.norm_sq_integral]
  calc
    _ = ∫ ω, ‖HigherEvenRenewalProcess.process m a t ω‖^2 ∂HigherEvenRenewalProcess.probability m := by
      apply integral_congr_ae
      filter_upwards [HigherEvenRenewalProcess.variableL2_ae m a t] with ω hω
      rw [hω]
    _ = _ := process_energy m a t

def smallAmplitude (n : ℕ) : ℝ := ((n : ℝ)+1)⁻¹

def acceleratedTime (m n : ℕ) (t : ℝ≥0) : ℝ≥0 :=
  Real.toNNReal (CyclicPolynomialKernel.rate m (smallAmplitude n))*t

def scaledVariable (m : ℕ) [NeZero m] (n : ℕ) (t : ℝ≥0) :
    Lp ℂ 2 (HigherEvenRenewalProcess.probability m) :=
  HigherEvenRenewalProcess.variableL2 m (smallAmplitude n) (acceleratedTime m n t)

theorem scaled_norm_square (m : ℕ) [NeZero m] (n : ℕ) (t : ℝ≥0) :
    ‖scaledVariable m n t‖^2 =
      (t : ℝ)*(Nat.factorial (2*m) : ℝ)*((n : ℝ)+1)^(2*m-2) := by
  rw [scaledVariable,variableL2_norm_square]
  have ha : smallAmplitude n ≠ 0 := by unfold smallAmplitude; positivity
  rw [acceleratedTime,NNReal.coe_mul,Real.coe_toNNReal _ (CyclicPolynomialKernel.rate_pos m _ ha).le]
  have hm := NeZero.pos m
  have hpow : ((n : ℝ)+1)^(2*m) = ((n : ℝ)+1)^(2*m-2)*((n : ℝ)+1)^2 := by
    rw [← pow_add,Nat.sub_add_cancel (by omega : 2 ≤ 2*m)]
  simp only [CyclicPolynomialKernel.rate,smallAmplitude,inv_pow,div_inv_eq_mul]
  rw [hpow]
  have hn : (n : ℝ)+1 ≠ 0 := by positivity
  field_simp

theorem scaled_energy_unbounded (m : ℕ) [NeZero m] (hm : 1 < m) (t : ℝ≥0) (ht : 0 < (t : ℝ)) :
    ¬ ∃ C : ℝ, ∀ n : ℕ, ‖scaledVariable m n t‖^2 ≤ C := by
  rintro ⟨C,hC⟩
  let c : ℝ := (t : ℝ)*(Nat.factorial (2*m) : ℝ)
  have hc : 0 < c := mul_pos ht (by exact_mod_cast Nat.factorial_pos (2*m))
  obtain ⟨n,hn⟩ := exists_nat_gt (C/c)
  have hq : 1 ≤ 2*m-2 := by omega
  have hx : (1 : ℝ) ≤ (n : ℝ)+1 := by linarith [show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n]
  have hp : (n : ℝ)+1 ≤ ((n : ℝ)+1)^(2*m-2) := by
    simpa only [pow_one] using pow_le_pow_right₀ hx hq
  have hb := hC n
  rw [scaled_norm_square] at hb
  have hbound : c*((n : ℝ)+1) ≤ C :=
    le_trans (mul_le_mul_of_nonneg_left hp hc.le) hb
  have hstrict : C < (n : ℝ)*c := (div_lt_iff₀ hc).mp hn
  linarith

theorem no_scaled_L2_limit (m : ℕ) [NeZero m] (hm : 1 < m) (t : ℝ≥0) (ht : 0 < (t : ℝ)) :
    ¬ ∃ Y : Lp ℂ 2 (HigherEvenRenewalProcess.probability m),
      Tendsto (fun n : ℕ => scaledVariable m n t) atTop (𝓝 Y) := by
  rintro ⟨Y,hY⟩
  obtain ⟨C,hC⟩ := (hY.norm.pow 2).cauchySeq.isBounded_range.exists_norm_le
  apply scaled_energy_unbounded m hm t ht
  refine ⟨C,fun n => ?_⟩
  have hn := hC (‖scaledVariable m n t‖^2) ⟨n,rfl⟩
  simpa only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg ‖scaledVariable m n t‖)] using hn

end OperatorDerivativeRewrite.Foundation.HigherEvenRenewalEnergy
