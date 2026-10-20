import Foundation.RiemannEvenHorizontalPairing
/-! Exact reflected arithmetic-weight norms for every integer-even order. -/
noncomputable section
open Set Metric Complex MeasureTheory Filter
open scoped ComplexConjugate
namespace OperatorDerivativeRewrite.Foundation.RiemannEvenComplexReflection
open RiemannEvenComplexWeight RiemannEvenHorizontalPairing

theorem reflected_weight_norm (m : ℕ) (t : ℝ) (z q : ℂ) :
    ‖weight m t (-z) (conj q)‖ = ‖weight m t z q‖*Real.exp (2*z.im*q.re) := by
  have hc : ‖weight m t (-z) (conj q)‖ = ‖weight m t (conj z) q‖ := by
    simpa using congrArg norm (weight_conj m t (conj z) q)
  rw [hc]
  have hp : ((t : ℂ)*q^(2*m)+Complex.I*(conj z)*q).re =
      ((t : ℂ)*q^(2*m)+Complex.I*z*q).re+2*z.im*q.re := by
    simp only [Complex.add_re,Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,
      zero_mul,one_mul,zero_sub,neg_mul,Complex.conj_re,Complex.conj_im]
    ring
  unfold weight
  simp only [norm_mul,Complex.norm_exp]
  rw [hp,Real.exp_add]
  ring

theorem reflected_weight_bound (m : ℕ) (t : ℝ) (z q : ℂ) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hz : z.im ≤ -b) (hq : a ≤ q.re) :
    ‖weight m t (-z) (conj q)‖ ≤ ‖weight m t z q‖*Real.exp (-2*b*a) := by
  rw [reflected_weight_norm]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply Real.exp_le_exp.mpr
  have hq0 : 0 ≤ q.re := ha.trans hq
  have h1 := mul_le_mul_of_nonneg_right hz hq0
  have h2 := mul_le_mul_of_nonpos_left hq (by linarith : -b ≤ 0)
  nlinarith

theorem reflected_right_tail_bound (m : ℕ) (t : ℝ) (z v : ℂ) (R a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hz : z.im ≤ -b) (haR : a ≤ v.re+R)
    (hv : |v.im| < Real.pi/8)
    (hmain : IntegrableOn (fun s : ℝ => weight m t z (v+(s : ℂ))) (Ioi R)) :
    IntegrableOn (fun s : ℝ => weight m t (-z) (conj (v+(s : ℂ)))) (Ioi R) ∧
      ‖∫ s : ℝ in Ioi R, weight m t (-z) (conj (v+(s : ℂ)))‖ ≤
        Real.exp (-2*b*a)*(∫ s : ℝ in Ioi R, ‖weight m t z (v+(s : ℂ))‖) := by
  let B := Real.exp (-2*b*a)
  let f := fun s : ℝ => weight m t (-z) (conj (v+(s : ℂ)))
  have hbound (s : ℝ) (hs : s ∈ Ioi R) :
      ‖f s‖ ≤ B*‖weight m t z (v+(s : ℂ))‖ := by
    have hq : a ≤ (v+(s : ℂ)).re := by
      simp only [Complex.add_re,Complex.ofReal_re]
      linarith [show R < s from hs]
    change ‖weight m t (-z) (conj (v+(s : ℂ)))‖ ≤
      Real.exp (-2*b*a)*‖weight m t z (v+(s : ℂ))‖
    exact (reflected_weight_bound m t z (v+(s : ℂ)) a b ha hb hz hq).trans_eq (mul_comm _ _)
  have hfc : Continuous f := by
    apply continuous_iff_continuousAt.mpr
    intro s
    have him : |(conj (v+(s : ℂ))).im| < Real.pi/8 := by
      simpa only [Complex.conj_im,Complex.add_im,Complex.ofReal_im,add_zero,abs_neg] using hv
    exact ContinuousAt.comp (g := weight m t (-z))
      (f := fun u : ℝ => conj (v+(u : ℂ)))
      (weight_analyticAt m t (-z) _ him).continuousAt (by fun_prop)
  have hg : IntegrableOn (fun s : ℝ => B*‖weight m t z (v+(s : ℂ))‖) (Ioi R) :=
    hmain.norm.const_mul B
  have hf : IntegrableOn f (Ioi R) := by
    apply hg.mono' (hfc.continuousOn.aestronglyMeasurable measurableSet_Ioi)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact hbound s hs
  refine ⟨hf,?_⟩
  calc
    ‖∫ s : ℝ in Ioi R, f s‖ ≤ ∫ s : ℝ in Ioi R, ‖f s‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ s : ℝ in Ioi R, B*‖weight m t z (v+(s : ℂ))‖ :=
      setIntegral_mono_on hf.norm hg measurableSet_Ioi hbound
    _ = B*(∫ s : ℝ in Ioi R, ‖weight m t z (v+(s : ℂ))‖) := integral_const_mul _ _

end OperatorDerivativeRewrite.Foundation.RiemannEvenComplexReflection
