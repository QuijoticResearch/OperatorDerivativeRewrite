import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-! Positive lower tail inequalities on actual probability spaces with native L2 hypotheses. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace OperatorDerivativeRewrite.Foundation.ProbabilityTailBound
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem integral_mul_square_le (f g : Ω → ℝ) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hf2 : MemLp f 2 μ) (hg2 : MemLp g 2 μ) :
    (∫ x, f x*g x ∂μ)^2 ≤ (∫ x, (f x)^2 ∂μ)*(∫ x, (g x)^2 ∂μ) := by
  have he := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Eventually.of_forall hf) (Eventually.of_forall hg) (by simpa using hf2) (by simpa using hg2)
  simp only [Real.rpow_two] at he
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at he
  have hs := pow_le_pow_left₀ (integral_nonneg (fun x => mul_nonneg (hf x) (hg x))) he 2
  rw [mul_pow, Real.sq_sqrt (integral_nonneg (fun x => sq_nonneg (f x))),
    Real.sq_sqrt (integral_nonneg (fun x => sq_nonneg (g x)))] at hs
  exact hs

theorem mean_tail_square (Y : Ω → ℝ) (hY : Measurable Y) (hY0 : ∀ x, 0 ≤ Y x)
    (hY2 : MemLp Y 2 μ) (b : ℝ) (hb : 0 ≤ b) (hbm : b ≤ ∫ x, Y x ∂μ) :
    ((∫ x, Y x ∂μ)-b)^2 ≤ (∫ x, (Y x)^2 ∂μ)*μ.real {x | b < Y x} := by
  classical
  let A : Set Ω := {x | b < Y x}
  let Q : Ω → ℝ := A.indicator 1
  have hA : MeasurableSet A := measurableSet_lt measurable_const hY
  have hQ (x : Ω) : 0 ≤ Q x := by simp only [Q, Set.indicator_apply]; split_ifs <;> norm_num
  have hQm : Measurable Q := measurable_const.indicator hA
  have hQb (x : Ω) : ‖Q x‖ ≤ 1 := by
    simp only [Q, Set.indicator_apply]
    split_ifs <;> norm_num
  have hQ2 : MemLp Q 2 μ := MemLp.of_bound hQm.aestronglyMeasurable 1
    (Eventually.of_forall hQb)
  have hiY : Integrable Y μ := hY2.integrable (by norm_num)
  have hiYQ : Integrable (fun x => Y x*Q x) μ :=
    hiY.mul_bdd hQm.aestronglyMeasurable (Eventually.of_forall hQb)
  have hp (x : Ω) : Y x ≤ b + Y x*Q x := by
    by_cases hx : b < Y x
    · simp [Q, A, hx, hb]
    · simp only [Q, A, Set.indicator_apply, Set.mem_setOf_eq, hx, ite_false, mul_zero, add_zero]
      exact le_of_not_gt hx
  have hm := integral_mono (μ := μ) hiY ((integrable_const b).add hiYQ) hp
  simp only [Pi.add_apply] at hm
  rw [integral_add (integrable_const _) hiYQ] at hm
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hm
  have hs := integral_mul_square_le μ Y Q hY0 hQ hY2 hQ2
  have hQQ : (fun x => (Q x)^2) = Q := by
    funext x
    simp only [Q, Set.indicator_apply]
    split_ifs <;> norm_num
  rw [hQQ, integral_indicator_one hA] at hs
  exact (pow_le_pow_left₀ (sub_nonneg.mpr hbm) (by linarith :
    (∫ x, Y x ∂μ)-b ≤ ∫ x, Y x*Q x ∂μ) 2).trans hs

end OperatorDerivativeRewrite.Foundation.ProbabilityTailBound
