import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-! Positive second-moment lower tail bounds on genuine finite probability spaces. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace OperatorDerivativeRewrite.Foundation.FiniteProbabilityTailBound

variable {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem finite_memLp (f : Ω → ℝ) (p : ℝ≥0∞) : MemLp f p μ := by
  classical
  apply MemLp.of_bound (measurable_of_countable f).aestronglyMeasurable (∑ x, ‖f x‖)
  exact Eventually.of_forall (fun x => Finset.single_le_sum
    (fun y _ => norm_nonneg (f y)) (Finset.mem_univ x))

theorem integral_mul_square_le (f g : Ω → ℝ) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x) :
    (∫ x, f x*g x ∂μ)^2 ≤ (∫ x, (f x)^2 ∂μ)*(∫ x, (g x)^2 ∂μ) := by
  have he := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Eventually.of_forall hf) (Eventually.of_forall hg)
    (finite_memLp μ f (ENNReal.ofReal 2)) (finite_memLp μ g (ENNReal.ofReal 2))
  simp only [Real.rpow_two] at he
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at he
  have hs := pow_le_pow_left₀ (integral_nonneg (fun x => mul_nonneg (hf x) (hg x))) he 2
  rw [mul_pow, Real.sq_sqrt (integral_nonneg (fun x => sq_nonneg (f x))),
    Real.sq_sqrt (integral_nonneg (fun x => sq_nonneg (g x)))] at hs
  exact hs

theorem mean_tail_square (Y : Ω → ℝ) (hY : ∀ x, 0 ≤ Y x) (b : ℝ) (hb : 0 ≤ b)
    (hbm : b ≤ ∫ x, Y x ∂μ) :
    ((∫ x, Y x ∂μ)-b)^2 ≤ (∫ x, (Y x)^2 ∂μ)*μ.real {x | b < Y x} := by
  classical
  let A : Set Ω := {x | b < Y x}
  let Q : Ω → ℝ := A.indicator 1
  have hQ (x : Ω) : 0 ≤ Q x := by simp only [Q, Set.indicator_apply]; split_ifs <;> norm_num
  have hp (x : Ω) : Y x ≤ b + Y x*Q x := by
    by_cases hx : b < Y x
    · simp [Q, A, hx, hb]
    · simp only [Q, A, Set.indicator_apply, Set.mem_setOf_eq, hx, ite_false, mul_zero, add_zero]
      exact le_of_not_gt hx
  have hm := integral_mono (μ := μ) (Integrable.of_finite (f := Y))
    (Integrable.of_finite (f := fun x => b+Y x*Q x)) hp
  rw [integral_add (integrable_const _) Integrable.of_finite] at hm
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hm
  have hs := integral_mul_square_le μ Y Q hY hQ
  have hQQ : (fun x => (Q x)^2) = Q := by
    funext x
    simp only [Q, Set.indicator_apply]
    split_ifs <;> norm_num
  rw [hQQ, integral_indicator_one (Set.to_countable A).measurableSet] at hs
  exact (pow_le_pow_left₀ (sub_nonneg.mpr hbm) (by linarith :
    (∫ x, Y x ∂μ)-b ≤ ∫ x, Y x*Q x ∂μ) 2).trans hs

end OperatorDerivativeRewrite.Foundation.FiniteProbabilityTailBound
