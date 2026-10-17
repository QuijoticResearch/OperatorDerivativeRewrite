import Foundation.PoissonEntireMoments

/-! Unbounded continuous observables with geometric growth along the actual finite walks. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.ComplexRootPoissonGrowth
open ComplexRootPoissonLaw ComplexFourthRootWalk

variable (r : ℝ≥0) (a : ℝ) (F : ℂ → ℂ) (hF : Continuous F) (B : ℝ)
  (hB : ∀ n (ω : Sample n), ‖F (terminal n a ω)‖ ≤ B^n)

include hF
theorem walk_integrable (n : ℕ) : Integrable F (ComplexFourthRootWalk.law n a) := by
  rw [ComplexFourthRootWalk.law, integrable_map_measure hF.aestronglyMeasurable
    (terminal_measurable n a).aemeasurable]
  exact Integrable.of_finite

theorem walk_integral (n : ℕ) :
    (∫ z, F z ∂ComplexFourthRootWalk.law n a) =
      ∫ ω, F (terminal n a ω) ∂probability n := by
  rw [ComplexFourthRootWalk.law, integral_map (terminal_measurable n a).aemeasurable
    hF.aestronglyMeasurable]

include hB
theorem walk_norm_integral_bound (n : ℕ) :
    (∫ z, ‖F z‖ ∂ComplexFourthRootWalk.law n a) ≤ B^n := by
  rw [ComplexFourthRootWalk.law, integral_map (terminal_measurable n a).aemeasurable
    hF.norm.aestronglyMeasurable]
  simpa using integral_mono_ae (Integrable.of_finite (f := fun ω : Sample n =>
    ‖F (terminal n a ω)‖)) (integrable_const (μ := probability n) (B^n))
    (Eventually.of_forall (hB n))

theorem growth_integrable : Integrable F (ComplexRootPoissonLaw.law r a) := by
  rw [law_sum]
  apply integrable_sum_measure
  · intro n
    exact (walk_integrable a F hF n).smul_measure ENNReal.ofReal_ne_top
  · apply (PoissonEntireMoments.weighted_real_powers r B).summable.of_nonneg_of_le
    · intro n
      exact integral_nonneg (fun z => norm_nonneg (F z))
    · intro n
      rw [integral_smul_measure, ENNReal.toReal_ofReal (weight_nonneg r n), smul_eq_mul]
      exact mul_le_mul_of_nonneg_left (walk_norm_integral_bound a F hF B hB n)
        (weight_nonneg r n)

theorem count_integrable :
    Integrable (fun n => ∫ z, F z ∂ComplexFourthRootWalk.law n a) (poissonMeasure r) := by
  apply (PoissonEntireMoments.real_powers_integrable r B).mono'
    StronglyMeasurable.of_discrete.aestronglyMeasurable
  exact Eventually.of_forall (fun n => (norm_integral_le_integral_norm _).trans
    (walk_norm_integral_bound a F hF B hB n))

theorem integral_growth :
    (∫ z, F z ∂ComplexRootPoissonLaw.law r a) =
      ∫ n, (∫ ω, F (terminal n a ω) ∂probability n) ∂poissonMeasure r := by
  have hi := growth_integrable r a F hF B hB
  rw [law_sum] at hi
  rw [law_sum, integral_sum_measure hi]
  simp_rw [integral_smul_measure, ENNReal.toReal_ofReal (weight_nonneg r _)]
  have he := integral_poissonMeasure' (count_integrable r a F hF B hB)
  simp_rw [weight, walk_integral a F hF] at he ⊢
  exact he.symm

end OperatorDerivativeRewrite.Foundation.ComplexRootPoissonGrowth
