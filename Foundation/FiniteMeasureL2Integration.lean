import Foundation.BochnerL2RepresentativeFubini

/-! Actual scalar integration over a finite parameter measure preserves L2.
The source measure can be any s-finite measure. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.FiniteMeasureL2Integration
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [SFinite ν]

theorem square_integral_le (f : X → ℝ) (hf : MemLp f 2 μ) :
    (∫ x, f x ∂μ)^2 ≤ μ.real Set.univ*(∫ x, (f x)^2 ∂μ) := by
  let F : Lp ℝ 2 μ := hf.toLp f
  let O : Lp ℝ 2 μ := (memLp_const (1 : ℝ)).toLp (fun _ : X => (1 : ℝ))
  have hF : F =ᵐ[μ] f := MemLp.coeFn_toLp hf
  have hO : O =ᵐ[μ] fun _ => (1 : ℝ) := MemLp.coeFn_toLp _
  have hi : inner ℝ O F=∫ x, f x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hF,hO] with x hx ho
    simp [hx,ho]
  have hnO : ‖O‖^2=μ.real Set.univ := by
    rw [← real_inner_self_eq_norm_sq,L2.inner_def]
    have he : (fun x => inner ℝ (O x) (O x)) =ᵐ[μ] fun _ => (1 : ℝ) :=
      hO.mono fun x hx => by simp [hx]
    rw [integral_congr_ae he,integral_const]
    simp
  have hnF : ‖F‖^2=∫ x, (f x)^2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hF] with x hx
    simp only [real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs,hx]
  have hb := abs_real_inner_le_norm O F
  have hs := sq_le_sq₀ (abs_nonneg (inner ℝ O F))
    (mul_nonneg (norm_nonneg O) (norm_nonneg F)) |>.mpr hb
  rw [sq_abs,mul_pow,hnO,hnF,hi] at hs
  exact hs

theorem column_integral_memLp (g : X × Y → ℝ) (hg : MemLp g 2 (μ.prod ν)) :
    MemLp (fun y => ∫ x, g (x,y) ∂μ) 2 ν := by
  have hq : AEStronglyMeasurable (fun y => ∫ x, g (x,y) ∂μ) ν :=
    hg.aestronglyMeasurable.prod_swap.integral_prod_right'
  have hG := hg.integrable_sq
  apply (memLp_two_iff_integrable_sq hq).mpr
  apply (hG.integral_prod_right.const_mul (μ.real Set.univ)).mono'
    ((hq.mul hq).congr (Eventually.of_forall fun y => by simp only [Pi.mul_apply,pow_two]))
  filter_upwards [hg.aestronglyMeasurable.prodMk_right,hG.prod_left_ae] with y hm hy
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact square_integral_le (fun x => g (x,y)) ((memLp_two_iff_integrable_sq hm).mpr hy)

theorem column_integral_energy_le (g : X × Y → ℝ) (hg : MemLp g 2 (μ.prod ν)) :
    (∫ y, (∫ x, g (x,y) ∂μ)^2 ∂ν) ≤ μ.real Set.univ*(∫ z, (g z)^2 ∂μ.prod ν) := by
  have hG := hg.integrable_sq
  have hb := integral_mono_ae (column_integral_memLp g hg).integrable_sq
    (hG.integral_prod_right.const_mul (μ.real Set.univ)) (by
      filter_upwards [hg.aestronglyMeasurable.prodMk_right,hG.prod_left_ae] with y hm hy
      exact square_integral_le (fun x => g (x,y)) ((memLp_two_iff_integrable_sq hm).mpr hy))
  rw [integral_const_mul,← integral_prod_symm (fun z => (g z)^2) hG] at hb
  exact hb

end OperatorDerivativeRewrite.Foundation.FiniteMeasureL2Integration
