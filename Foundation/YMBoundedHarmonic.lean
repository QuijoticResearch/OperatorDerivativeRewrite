import Foundation.YMPositivePower

/-! Bounded harmonic uniqueness for the positive-kernel gauge comparison.
The reset inequality is reused verbatim from the verified power construction. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.YMBoundedHarmonic
variable {Ω : Type*} [MeasurableSpace Ω] [Nonempty Ω]
variable (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (k : Ω → Ω → ℝ) (m M : ℝ)
variable (hk : Measurable (Function.uncurry k)) (hm : 0 < m)
variable (hb : ∀ x y,m ≤ k x y ∧ k x y ≤ M)

include hk hm hb in
theorem zero_mean_harmonic (f : Ω → ℝ) (hf : Measurable f) (B : ℝ)
    (hB : ∀ x,|f x| ≤ B) (hfix : ∀ x,YMPositiveKernel.average μ k f x=f x)
    (hzero : (∫ x,f x ∂μ)=0) (x : Ω) : f x=0 := by
  let θ := 1-m/M
  have hM : 0 < M := (hm.trans_le (hb x x).1).trans_le (hb x x).2
  have hmM : m ≤ M := (hb x x).1.trans (hb x x).2
  have hθ0 : 0 ≤ θ := sub_nonneg.mpr ((div_le_one hM).mpr hmM)
  have hθ1 : θ < 1 := by dsimp [θ]; have hp := div_pos hm hM; linarith
  have hdec (n : ℕ) : ∀ y,|f y| ≤ B*θ^n := by
    induction n with
    | zero => simpa using hB
    | succ n ih =>
      intro y
      have he := YMPositivePower.average_reset_range μ k m M hk hm hb f hf
        (-(B*θ^n)) (B*θ^n) (fun z => abs_le.mp (ih z)) y
      rw [hfix,hzero,mul_zero,sub_zero] at he
      apply abs_le.mpr
      constructor
      · calc
          _ = θ*(-(B*θ^n)) := by ring
          _ ≤ f y := he.1
      · calc
          f y ≤ θ*(B*θ^n) := he.2
          _ = _ := by ring
  have hlim : Filter.Tendsto (fun n : ℕ => B*θ^n) Filter.atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_lt_one hθ0 hθ1)
  have he : |f x| ≤ 0 := ge_of_tendsto hlim (Filter.Eventually.of_forall fun n => hdec n x)
  exact abs_eq_zero.mp (le_antisymm he (abs_nonneg _))

include hk hm hb in
theorem bounded_harmonic_constant (f : Ω → ℝ) (hf : Measurable f) (B : ℝ)
    (hB : ∀ x,|f x| ≤ B) (hfix : ∀ x,YMPositiveKernel.average μ k f x=f x) (x : Ω) :
    f x=∫ y,f y ∂μ := by
  let c := ∫ y,f y ∂μ
  have hi : Integrable f μ := Integrable.of_bound hf.aestronglyMeasurable B
    (Filter.Eventually.of_forall fun y => by simpa only [Real.norm_eq_abs] using hB y)
  have hc : |c| ≤ B := by
    have he := integral_mono hi.norm (integrable_const B)
      (fun y => by simpa only [Real.norm_eq_abs] using hB y)
    have hn := norm_integral_le_integral_norm f (μ := μ)
    simpa [c,Real.norm_eq_abs] using hn.trans he
  have hcenter (y : Ω) : |f y-c| ≤ 2*B := by
    exact (abs_sub _ _).trans (by linarith [hB y,hc])
  have hfixed (y : Ω) : YMPositiveKernel.average μ k (fun z => f z-c) y=f y-c := by
    have hd := YMPositiveKernel.density_integrable μ k m M hm
      (fun z => hk.comp measurable_prodMk_left) hb y
    have hp : Integrable (fun z => YMPositiveKernel.rowDensity μ k y z*f z) μ := by
      have hh := hd.bdd_mul hf.aestronglyMeasurable (c := B)
        (Filter.Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs] using hB z)
      simpa only [mul_comm] using hh
    unfold YMPositiveKernel.average
    simp_rw [mul_sub]
    rw [integral_sub hp (hd.mul_const c),integral_mul_const,
      YMPositiveKernel.density_integral μ k m M hm (fun z => hk.comp measurable_prodMk_left) hb y]
    change YMPositiveKernel.average μ k f y-1*c=f y-c
    rw [hfix,one_mul]
  have hz : (∫ y,f y-c ∂μ)=0 := by rw [integral_sub hi (integrable_const c)]; simp [c]
  have he := zero_mean_harmonic μ k m M hk hm hb (fun y => f y-c)
    (hf.sub_const c) (2*B) hcenter hfixed hz x
  linarith

end OperatorDerivativeRewrite.Foundation.YMBoundedHarmonic
