import Foundation.PoissonCoherentVectors
import Foundation.GaussianEntropy

/-! Actual exponential entropy and the obstruction to a Gaussian quadratic LSI. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.PoissonExponentialEntropy
open PoissonDifferenceCore PoissonDifferenceOperators PoissonCoherentVectors PoissonMoments

private theorem exponential_succ (θ : ℝ) (n : ℕ) :
    exponential θ (n+1)=Real.exp θ*exponential θ n := by
  simp only [exponential,Nat.cast_add,Nat.cast_one,mul_add,Real.exp_add]
  ring

theorem weighted_count_exponential_hasSum (rate : ℝ≥0) (θ : ℝ) :
    HasSum (fun n : ℕ => poissonWeight rate n*((n : ℝ)*exponential θ n))
      ((rate : ℝ)*Real.exp θ*Real.exp ((rate : ℝ)*(Real.exp θ-1))) := by
  have hs := (weighted_exponential_hasSum rate θ).mul_left ((rate : ℝ)*Real.exp θ)
  have ht : HasSum (fun n : ℕ => poissonWeight rate (n+1)*(((n+1 : ℕ) : ℝ)*exponential θ (n+1)))
      ((rate : ℝ)*Real.exp θ*Real.exp ((rate : ℝ)*(Real.exp θ-1))) := by
    convert hs using 1
    funext n
    rw [exponential_succ]
    push_cast
    have hp := poisson_weight_succ rate n
    linear_combination (Real.exp θ*exponential θ n)*hp
  have he := (hasSum_nat_add_iff 1
    (f := fun n : ℕ => poissonWeight rate n*((n : ℝ)*exponential θ n))
    (g := (rate : ℝ)*Real.exp θ*Real.exp ((rate : ℝ)*(Real.exp θ-1)))).mp ht
  simpa only [Finset.sum_range_one,Nat.cast_zero,zero_mul,mul_zero,add_zero] using he

theorem count_exponential_integral (rate : ℝ≥0) (θ : ℝ) :
    (∫ n : ℕ, (n : ℝ)*exponential θ n ∂poissonLaw rate)=
      (rate : ℝ)*Real.exp θ*Real.exp ((rate : ℝ)*(Real.exp θ-1)) := by
  rw [integral_eq_weighted_tsum rate _ ((count_exponential_memLp rate θ).integrable (by norm_num))]
  exact (weighted_count_exponential_hasSum rate θ).tsum_eq

theorem exponential_square (θ : ℝ) (n : ℕ) : (exponential θ n)^2=exponential (2*θ) n := by
  simp only [exponential,pow_two,← Real.exp_add]
  congr 1
  ring

theorem exponential_square_log (θ : ℝ) (n : ℕ) :
    (exponential θ n)^2*Real.log ((exponential θ n)^2)=
      (2*θ)*((n : ℝ)*exponential (2*θ) n) := by
  rw [exponential_square]
  simp only [exponential,Real.log_exp]
  ring

theorem exponential_entropy_integrable (rate : ℝ≥0) (θ : ℝ) :
    Integrable (fun n => (exponential θ n)^2*Real.log ((exponential θ n)^2)) (poissonLaw rate) := by
  simpa only [exponential_square_log] using
    ((count_exponential_memLp rate (2*θ)).integrable (by norm_num)).const_mul (2*θ)

theorem exponential_entropy (rate : ℝ≥0) (θ : ℝ) :
    entropySq (poissonLaw rate) (exponential θ)=
      (rate : ℝ)*Real.exp ((rate : ℝ)*(Real.exp (2*θ)-1))*
        (2*θ*Real.exp (2*θ)-Real.exp (2*θ)+1) := by
  unfold entropySq
  have he : (fun n : ℕ => (exponential θ n)^2*Real.log ((exponential θ n)^2))=
      fun n : ℕ => (2*θ)*((n : ℝ)*exponential (2*θ) n) :=
    funext (exponential_square_log θ)
  rw [he]
  simp only [exponential_square]
  rw [integral_const_mul,count_exponential_integral,exponential_integral,Real.log_exp]
  ring

theorem exponential_field_norm_sq (rate : ℝ≥0) (hr : 0 < rate) (θ : ℝ) :
    ‖field rate θ‖^2=(rate : ℝ)*Real.exp ((rate : ℝ)*(Real.exp (2*θ)-1)) := by
  rw [← real_inner_self_eq_norm_sq,L2_inner_eq_integral]
  have he : (fun n : ℕ => inner ℝ (field rate θ n) (field rate θ n))=exponential (2*θ) := by
    funext n
    rw [field_apply rate hr,real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs,exponential_square]
  rw [he,integral_smul_measure,exponential_integral]
  simp

theorem exponential_difference_energy (rate : ℝ≥0) (hr : 0 < rate) (θ : ℝ) :
    ‖(Real.exp θ-1) • field rate θ‖^2=
      (rate : ℝ)*Real.exp ((rate : ℝ)*(Real.exp (2*θ)-1))*(Real.exp θ-1)^2 := by
  rw [norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,exponential_field_norm_sq rate hr θ]
  ring

theorem actual_entropy_counterexample (rate : ℝ≥0) (hr : 0 < rate) (C : ℝ) (hC : 0 ≤ C) :
    ∃ f : ScalarL2 rate, ∃ g : FieldL2 rate,
      (f,g) ∈ (PoissonMaximalOperators.maximalDifference rate hr).graph ∧
        Integrable (fun n => (f n)^2*Real.log ((f n)^2)) (poissonLaw rate) ∧
          C*‖g‖^2 < entropySq (poissonLaw rate) (fun n => f n) := by
  let θ := C+1
  have hθ : 0 < θ := by dsimp [θ]; linarith
  have hf : (fun n => scalar rate θ n) =ᵐ[poissonLaw rate] exponential θ :=
    Eventually.of_forall (scalar_apply rate hr θ)
  refine ⟨scalar rate θ,(Real.exp θ-1) • field rate θ,
    exponential_difference_graph rate hr θ, ?_, ?_⟩
  · exact (exponential_entropy_integrable rate θ).congr
      (hf.symm.fun_comp (fun x : ℝ => x^2*Real.log (x^2)))
  · rw [entropySq_congr hf,exponential_entropy,exponential_difference_energy rate hr θ]
    have he : 1 ≤ Real.exp θ := Real.one_le_exp_iff.mpr hθ.le
    have he2 : Real.exp (2*θ)=(Real.exp θ)^2 := by
      rw [show 2*θ=θ+θ by ring,Real.exp_add,pow_two]
    have hd : (Real.exp θ-1)^2 ≤ Real.exp (2*θ) := by rw [he2]; nlinarith
    have hb : C*(Real.exp θ-1)^2 < 2*θ*Real.exp (2*θ)-Real.exp (2*θ)+1 := by
      have hm := mul_le_mul_of_nonneg_left hd hC
      have hp := Real.exp_pos (2*θ)
      dsimp [θ] at hm hp ⊢
      nlinarith
    have hp : 0 < (rate : ℝ)*Real.exp ((rate : ℝ)*(Real.exp (2*θ)-1)) :=
      mul_pos hr (Real.exp_pos _)
    convert mul_lt_mul_of_pos_left hb hp using 1 <;> ring

theorem no_uniform_quadratic_entropy_bound (rate : ℝ≥0) (hr : 0 < rate) :
    ¬ ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : ScalarL2 rate) (g : FieldL2 rate),
      (f,g) ∈ (PoissonMaximalOperators.maximalDifference rate hr).graph →
        Integrable (fun n => (f n)^2*Real.log ((f n)^2)) (poissonLaw rate) →
          entropySq (poissonLaw rate) (fun n => f n) ≤ C*‖g‖^2 := by
  rintro ⟨C,hC,hbound⟩
  obtain ⟨f,g,hgraph,hint,hfail⟩ := actual_entropy_counterexample rate hr C hC
  exact (not_lt_of_ge (hbound f g hgraph hint)) hfail

end OperatorDerivativeRewrite.Foundation.PoissonExponentialEntropy
