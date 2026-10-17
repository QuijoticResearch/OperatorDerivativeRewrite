import Foundation.ComplexRootContinuousPaths

/-! Positive Hermitian second moments of the actual finite complex root walks. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate
namespace OperatorDerivativeRewrite.Foundation.ComplexRootWalkSecondMoment
open ComplexFourthRootNoise ComplexFourthRootWalk

theorem pair_conjugate_integral (n : ℕ) (a : ℝ) (i j : Fin n) :
    (∫ ω, increment n a i ω * (starRingEnd ℂ) (increment n a j ω) ∂probability n) =
      if i = j then ((2*a^2 : ℝ) : ℂ) else 0 := by
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl]
    have he (ω : Sample n) : increment n a i ω * (starRingEnd ℂ) (increment n a i ω) =
        ((2*a^2 : ℝ) : ℂ) := by
      change noise a (ω i) * (starRingEnd ℂ) (noise a (ω i)) = _
      rw [Complex.mul_conj', ← Complex.ofReal_pow, norm_square]
    simp_rw [he]
    simp
  · rw [if_neg hij]
    have hi := ((increments_independent n a).indepFun hij).comp
      measurable_id Complex.continuous_conj.measurable
    have he := hi.integral_fun_mul_eq_mul_integral
      (measurable_of_countable _).aestronglyMeasurable
      (measurable_of_countable _).aestronglyMeasurable
    simpa only [Function.comp_def, id_eq, increment_mean, zero_mul] using he

theorem terminal_conjugate_integral (n : ℕ) (a : ℝ) :
    (∫ ω, terminal n a ω * (starRingEnd ℂ) (terminal n a ω) ∂probability n) =
      ((2*(n : ℝ)*a^2 : ℝ) : ℂ) := by
  simp only [terminal, map_sum, Finset.sum_mul, Finset.mul_sum]
  rw [integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  simp_rw [integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  simp_rw [pair_conjugate_integral]
  simp [Finset.sum_ite_eq] <;> push_cast <;> ring

theorem terminal_absolute_second (n : ℕ) (a : ℝ) :
    (∫ ω, ‖terminal n a ω‖^2 ∂probability n) = 2*(n : ℝ)*a^2 := by
  have he (ω : Sample n) :
      (terminal n a ω * (starRingEnd ℂ) (terminal n a ω)).re = ‖terminal n a ω‖^2 := by
    rw [Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re]
  calc
    _ = ∫ ω, (terminal n a ω * (starRingEnd ℂ) (terminal n a ω)).re ∂probability n := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun ω => (he ω).symm)
    _ = (∫ ω, terminal n a ω * (starRingEnd ℂ) (terminal n a ω) ∂probability n).re := by
      simpa only [RCLike.re_eq_complex_re] using
        integral_re (μ := probability n)
          (f := fun ω => terminal n a ω * (starRingEnd ℂ) (terminal n a ω)) Integrable.of_finite
    _ = _ := congrArg Complex.re (terminal_conjugate_integral n a)

end OperatorDerivativeRewrite.Foundation.ComplexRootWalkSecondMoment
