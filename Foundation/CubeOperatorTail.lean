import Foundation.CubeNativeL2Domain

/-! Native stationary L2 tail estimates from the actual Wilson kernel envelope. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace OperatorDerivativeRewrite.Foundation.CubeOperatorTail
open CubeTemporalSlab CubeWilsonSlab CubeSlabGround CubeSlabL2 CubeNativeL2Domain
attribute [local irreducible] CubeWilsonSlab.kernel boundaryHaar
variable {beta : ℝ} (d : GroundData beta)
private instance stationary_probability : IsProbabilityMeasure d.stationary := d.stationary_probability

private theorem weighted_abs_integrable (f : State → ℝ) (hf : Measurable f)
    (hm : MemLp f 2 d.stationary) : Integrable (fun U => d.function U*|f U|) boundaryHaar := by
  have h := (weighted_memLp d f hf hm).norm.integrable (by norm_num : (1:ENNReal) ≤ 2)
  simpa only [Real.norm_eq_abs,abs_mul,abs_of_pos (d.function_pos _)] using h

/-- The kernel envelope acts on all native L2 inputs supported in the action tail. -/
theorem transfer_tail_bound (hb : 0 ≤ beta) (eps : ℝ) (f : State → ℝ)
    (hf : Measurable f) (hm : MemLp f 2 d.stationary)
    (hs : ∀ᵐ V ∂boundaryHaar, spatialAction V < eps → f V=0) (U : State) :
    |transfer d f U| ≤ Real.exp (-beta*eps/2)*
      (∫ V,d.function V*|f V| ∂boundaryHaar)/(d.value*d.function U) := by
  have hi := norm_integral_le_of_norm_le
    ((weighted_abs_integrable d f hf hm).const_mul (Real.exp (-beta*eps/2)))
    (f := fun V => kernel beta U V*(d.function V*f V)) ?_
  · rw [integral_const_mul,Real.norm_eq_abs] at hi
    rw [transfer,d.transition_integral,abs_div,abs_of_pos (mul_pos d.value_pos (d.function_pos U))]
    exact div_le_div_of_nonneg_right hi (mul_pos d.value_pos (d.function_pos U)).le
  · filter_upwards [hs] with V hV
    by_cases htail : eps ≤ spatialAction V
    · have hk := CubeLowActionBlock.kernel_spatial_upper beta hb V U
      rw [CubeSlabGauge.kernel_symmetric beta V U] at hk
      have he : Real.exp (-beta*spatialAction V/2) ≤ Real.exp (-beta*eps/2) :=
        Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left htail hb])
      rw [Real.norm_eq_abs,abs_mul,abs_mul,abs_of_pos (kernel_positive beta U V),
        abs_of_pos (d.function_pos V)]
      exact mul_le_mul_of_nonneg_right (hk.trans he)
        (mul_nonneg (d.function_pos V).le (abs_nonneg _))
    · rw [hV (lt_of_not_ge htail)]
      simp

/-- Full native Hilbert-space pairing bound; no bounded-core restriction. -/
theorem pairing_tail_bound (hb : 0 ≤ beta) (eps : ℝ) (f g : StateL2 d)
    (hs : ∀ᵐ V ∂d.stationary, spatialAction V < eps → f V=0) :
    |inner ℝ (operator d f) g| ≤ (Real.exp (-beta*eps/2)/d.value)*‖f‖*‖g‖ := by
  let a := Real.exp (-beta*eps/2)
  let m := ∫ V,d.function V*|f V| ∂boundaryHaar
  have hm : 0 ≤ m := integral_nonneg (fun V => mul_nonneg (d.function_pos V).le (abs_nonneg _))
  have hsup := (CubeNativeL2Domain.ae_iff d _).mp hs
  have hi := norm_integral_le_of_norm_le
    ((weighted_abs_integrable d g (Lp.stronglyMeasurable g).measurable (Lp.memLp g)).const_mul
      (a/d.value*m))
    (f := fun U => d.function U^2*(g U*transfer d f U)) ?_
  · rw [integral_const_mul,Real.norm_eq_abs] at hi
    rw [operator_kernel_pairing,d.stationary_integral,abs_div,abs_of_pos d.normalizer_pos]
    have h1 := div_le_div_of_nonneg_right hi d.normalizer_pos.le
    have hf := weighted_abs_integral_bound d f (Lp.stronglyMeasurable f).measurable (Lp.memLp f)
    have hg := weighted_abs_integral_bound d g (Lp.stronglyMeasurable g).measurable (Lp.memLp g)
    rw [Lp.toLp_coeFn] at hf hg
    have hprod := mul_le_mul hf hg
      (integral_nonneg (fun V => mul_nonneg (d.function_pos V).le (abs_nonneg _)))
      (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
    have hsqrt := Real.sq_sqrt d.normalizer_pos.le
    have h2 : (a/d.value*m*(∫ U,d.function U*|g U| ∂boundaryHaar))/d.normalizer ≤
        (a/d.value)*‖f‖*‖g‖ := by
      apply (div_le_iff₀ d.normalizer_pos).mpr
      have hfactor : Real.sqrt d.normalizer*‖f‖*(Real.sqrt d.normalizer*‖g‖)=
          d.normalizer*‖f‖*‖g‖ := by
        calc
          _ = (Real.sqrt d.normalizer)^2*‖f‖*‖g‖ := by ring
          _ = _ := by rw [hsqrt]
      rw [hfactor] at hprod
      have h := mul_le_mul_of_nonneg_left hprod (div_nonneg (Real.exp_pos (-beta*eps/2)).le d.value_pos.le)
      change (a/d.value)*m*(∫ U,d.function U*|g U| ∂boundaryHaar) ≤ _
      convert h using 1 <;> ring
    exact h1.trans h2
  · filter_upwards with U
    have ht := transfer_tail_bound d hb eps f (Lp.stronglyMeasurable f).measurable
      (Lp.memLp f) hsup U
    have ht' := (le_div_iff₀ (mul_pos d.value_pos (d.function_pos U))).mp ht
    have hh := mul_le_mul_of_nonneg_left ht'
      (div_nonneg (mul_nonneg (d.function_pos U).le (abs_nonneg (g U))) d.value_pos.le)
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (sq_nonneg _),abs_mul]
    dsimp only [a,m]
    convert hh using 1 <;> field_simp [d.value_pos.ne'] <;> ring

/-- Genuine native L2 norm estimate, proved by testing against the actual output. -/
theorem norm_tail_bound (hb : 0 ≤ beta) (eps : ℝ) (f : StateL2 d)
    (hs : ∀ᵐ V ∂d.stationary, spatialAction V < eps → f V=0) :
    ‖operator d f‖ ≤ (Real.exp (-beta*eps/2)/d.value)*‖f‖ := by
  have h := pairing_tail_bound d hb eps f (operator d f) hs
  rw [real_inner_self_eq_norm_sq,abs_of_nonneg (sq_nonneg _)] at h
  have hc := mul_nonneg (div_nonneg (Real.exp_pos (-beta*eps/2)).le d.value_pos.le) (norm_nonneg f)
  nlinarith [norm_nonneg (operator d f)]

end OperatorDerivativeRewrite.Foundation.CubeOperatorTail
