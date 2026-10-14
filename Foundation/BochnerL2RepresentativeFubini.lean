import Foundation.BochnerL2Fubini
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

/-! Scalar representative Fubini from integrable L2 sections on finite measures.
No uniform pointwise majorant or independently supplied column L2 class is required. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.BochnerL2RepresentativeFubini
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [IsFiniteMeasure ν]

private def normClass (F : Lp ℝ 2 ν) : Lp ℝ 2 ν :=
  (Lp.memLp F).norm.toLp (fun y => ‖F y‖)

private theorem normClass_ae (F : Lp ℝ 2 ν) : normClass F =ᵐ[ν] fun y => ‖F y‖ :=
  MemLp.coeFn_toLp _

private theorem normClass_norm (F : Lp ℝ 2 ν) : ‖normClass F‖=‖F‖ := by
  rw [normClass,Lp.norm_toLp,eLpNorm_norm _ (Lp.aestronglyMeasurable F)]
  rfl

theorem pairing_norm_integral_le (V F : Lp ℝ 2 ν) :
    (∫ y, ‖inner ℝ (V y) (F y)‖ ∂ν) ≤ ‖V‖*‖F‖ := by
  calc
    _ ≤ ∫ y, ‖V y‖*‖F y‖ ∂ν := by
      apply integral_mono_ae (L2.integrable_inner (𝕜 := ℝ) V F).norm
        ((Lp.memLp V).norm.integrable_mul (Lp.memLp F).norm)
      exact Eventually.of_forall fun y => norm_inner_le_norm _ _
    _ = inner ℝ (normClass V) (normClass F) := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [normClass_ae V,normClass_ae F] with y hV hF
      simp [hV,hF,mul_comm]
    _ ≤ ‖V‖*‖F‖ := by
      simpa only [normClass_norm] using real_inner_le_norm (normClass V) (normClass F)

theorem pairing_integrable_of_slices (v : X → Lp ℝ 2 ν) (hv : Integrable v μ)
    (g : X × Y → ℝ) (hg : AEStronglyMeasurable g (μ.prod ν))
    (hvg : ∀ᵐ x ∂μ, v x =ᵐ[ν] fun y => g (x,y)) (V : Lp ℝ 2 ν) :
    Integrable (fun z => inner ℝ (V z.2) (g z)) (μ.prod ν) := by
  have hm := (Lp.aestronglyMeasurable V).comp_snd.inner (𝕜 := ℝ) hg
  apply (integrable_prod_iff hm).mpr
  constructor
  · filter_upwards [hvg] with x hx
    exact (L2.integrable_inner (𝕜 := ℝ) V (v x)).congr
      (hx.mono fun y hy => congrArg (inner ℝ (V y)) hy)
  · apply (hv.norm.const_mul ‖V‖).mono' hm.norm.integral_prod_right'
    filter_upwards [hvg] with x hx
    rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    calc
      _ = ∫ y, ‖inner ℝ (V y) (v x y)‖ ∂ν := by
        apply integral_congr_ae
        exact hx.symm.mono fun y hy => congrArg (fun z => ‖inner ℝ (V y) z‖) hy
      _ ≤ ‖V‖*‖v x‖ := pairing_norm_integral_le V (v x)

private def oneClass : Lp ℝ 2 ν := (memLp_const (1 : ℝ)).toLp (fun _ : Y => (1 : ℝ))

private theorem oneClass_ae : (oneClass : Lp ℝ 2 ν) =ᵐ[ν] fun _ => (1 : ℝ) :=
  MemLp.coeFn_toLp _

theorem representative_integrable (v : X → Lp ℝ 2 ν) (hv : Integrable v μ)
    (g : X × Y → ℝ) (hg : AEStronglyMeasurable g (μ.prod ν))
    (hvg : ∀ᵐ x ∂μ, v x =ᵐ[ν] fun y => g (x,y)) : Integrable g (μ.prod ν) := by
  apply (pairing_integrable_of_slices v hv g hg hvg oneClass).congr
  have he : ∀ᵐ z : X × Y ∂μ.prod ν, oneClass z.2=(1 : ℝ) :=
    (MeasureTheory.Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae oneClass_ae
  exact he.mono fun z hz => by simp [hz]

theorem integral_coeFn_ae (v : X → Lp ℝ 2 ν) (hv : Integrable v μ)
    (g : X × Y → ℝ) (hg : AEStronglyMeasurable g (μ.prod ν))
    (hvg : ∀ᵐ x ∂μ, v x =ᵐ[ν] fun y => g (x,y)) :
    (∫ x, v x ∂μ) =ᵐ[ν] fun y => ∫ x, g (x,y) ∂μ := by
  let W : Lp ℝ 2 ν := ∫ x, v x ∂μ
  have hG := representative_integrable v hv g hg hvg
  have hW : Integrable (fun y => W y) ν := by
    simpa only [IntegrableOn,Measure.restrict_univ] using
      integrableOn_Lp_of_measure_ne_top (s := Set.univ) W (by norm_num) (by finiteness)
  apply Integrable.ae_eq_of_forall_setIntegral_eq (fun y => W y)
    (fun y => ∫ x, g (x,y) ∂μ) hW hG.integral_prod_right
  intro s hs _
  let V : Lp ℝ 2 ν := indicatorConstLp 2 hs (by finiteness) (1 : ℝ)
  rw [← L2.inner_indicatorConstLp_one hs (by finiteness) W]
  change inner ℝ V (∫ x, v x ∂μ)= _
  rw [← integral_inner hv V]
  calc
    _ = ∫ x, ∫ y, inner ℝ (V y) (g (x,y)) ∂ν ∂μ := by
      apply integral_congr_ae
      filter_upwards [hvg] with x hx
      rw [L2.inner_def]
      exact integral_congr_ae (hx.mono fun y hy => congrArg (inner ℝ (V y)) hy)
    _ = ∫ y, ∫ x, inner ℝ (V y) (g (x,y)) ∂μ ∂ν :=
      integral_integral_swap (pairing_integrable_of_slices v hv g hg hvg V)
    _ = ∫ y, inner ℝ (V y) (∫ x, g (x,y) ∂μ) ∂ν := by
      apply integral_congr_ae
      filter_upwards [hG.prod_left_ae] with y hy
      exact integral_inner hy (V y)
    _ = ∫ y in s, ∫ x, g (x,y) ∂μ ∂ν := by
      rw [← integral_indicator hs]
      apply integral_congr_ae
      filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hs)
        (hμs := by finiteness) (c := (1 : ℝ))] with y hy
      change V y= _ at hy
      by_cases hys : y∈s <;> simp [hy,hys]

theorem column_integral_memLp (v : X → Lp ℝ 2 ν) (hv : Integrable v μ)
    (g : X × Y → ℝ) (hg : AEStronglyMeasurable g (μ.prod ν))
    (hvg : ∀ᵐ x ∂μ, v x =ᵐ[ν] fun y => g (x,y)) :
    MemLp (fun y => ∫ x, g (x,y) ∂μ) 2 ν :=
  (Lp.memLp (∫ x, v x ∂μ)).ae_eq (integral_coeFn_ae v hv g hg hvg)

end OperatorDerivativeRewrite.Foundation.BochnerL2RepresentativeFubini
