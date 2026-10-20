import Foundation.RiemannEvenWeightedTails

/-! Actual Fourier error controlled by a genuine centered exponential moment.
No convergence or zero-location conclusion is assumed. -/
noncomputable section
open Set MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.RiemannEvenFourierMoment
open RiemannEvenDomain RiemannEvenFlow RiemannEvenWeightedTails

theorem phase_difference_bound (z : ℂ) (u v : ℝ) (hu : 0 ≤ u) :
    ‖Complex.exp (Complex.I*(v : ℂ)*z)-Complex.exp (Complex.I*(u : ℂ)*z)‖ ≤
      Real.exp (u*|z.im|)*‖z‖*|v-u| * Real.exp (‖z‖*|v-u|) := by
  let d : ℂ := Complex.I*((v-u : ℝ) : ℂ)*z
  have hd : ‖d‖ = ‖z‖*|v-u| := by
    simp only [d,norm_mul,Complex.norm_I,Complex.norm_real,Real.norm_eq_abs,one_mul]
    ring
  have herr : ‖Complex.exp d-1‖ ≤ (‖z‖*|v-u|)*Real.exp (‖z‖*|v-u|) := by
    simpa only [Finset.sum_range_one,pow_zero,Nat.factorial_zero,Nat.cast_one,div_one,
      pow_one,hd] using Complex.norm_exp_sub_sum_le_norm_mul_exp d 1
  have heq : Complex.exp (Complex.I*(v : ℂ)*z)-Complex.exp (Complex.I*(u : ℂ)*z) =
      Complex.exp (Complex.I*(u : ℂ)*z)*(Complex.exp d-1) := by
    rw [mul_sub,mul_one,← Complex.exp_add]
    congr 2
    dsimp [d]
    push_cast
    ring
  have hnorm : ‖Complex.exp (Complex.I*(u : ℂ)*z)‖ ≤ Real.exp (u*|z.im|) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simp only [Complex.mul_re,Complex.I_re,Complex.ofReal_re,Complex.I_im,
      Complex.ofReal_im,mul_zero,sub_zero,zero_mul,one_mul,Complex.mul_im,zero_add]
    have hh := mul_le_mul_of_nonneg_left (neg_le_abs z.im) hu
    nlinarith
  rw [heq,norm_mul]
  calc
    _ ≤ Real.exp (u*|z.im|)*((‖z‖*|v-u|)*Real.exp (‖z‖*|v-u|)) :=
      mul_le_mul hnorm herr (norm_nonneg _) (Real.exp_pos _).le
    _ = _ := by ring

theorem actual_jet_moment_error_bound (m : ℕ) (t u : ℝ) (z : ℂ) (hu : 0 ≤ u) :
    ‖jet m 0 t z-(RiemannEvenFlow.flow m t 0)*Complex.exp (Complex.I*(u : ℂ)*z)‖ ≤
      (Real.exp (u*|z.im|)*‖z‖)*
        (∫ v : ℝ in Ici 0, |v-u| * Real.exp (‖z‖*|v-u|) * weighted m 0 t 0 v) := by
  let f : ℝ → ℂ := fun v => (weighted m 0 t 0 v : ℂ)*
    (Complex.exp (Complex.I*(v : ℂ)*z)-Complex.exp (Complex.I*(u : ℂ)*z))
  have hmajor : IntegrableOn (fun v : ℝ => (Real.exp (u*|z.im|)*‖z‖)*
      (|v-u| * Real.exp (‖z‖*|v-u|) * weighted m 0 t 0 v)) (Ici 0) :=
    (actual_centered_exponential_moment_integrable m t u ‖z‖ hu (norm_nonneg z)).const_mul _
  have hpoint : ∀ᵐ v : ℝ ∂RiemannQuarticFlow.halfLine,
      ‖f v‖ ≤ (Real.exp (u*|z.im|)*‖z‖)*
        (|v-u| * Real.exp (‖z‖*|v-u|) * weighted m 0 t 0 v) := by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with v hv
    have hw := (RiemannEvenRealSaddle.weighted_pos m t v hv).le
    dsimp only [f]
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hw]
    have h := mul_le_mul_of_nonneg_left (phase_difference_bound z u v hu) hw
    convert h using 1 <;> ring
  have hb := norm_integral_le_of_norm_le hmajor hpoint
  rw [integral_const_mul] at hb
  have hi : Integrable (fun v : ℝ => (weighted m 0 t 0 v : ℂ)) RiemannQuarticFlow.halfLine :=
    (weighted_integrable m 0 t 0).ofReal
  have hf : (∫ v : ℝ, f v ∂RiemannQuarticFlow.halfLine) =
      jet m 0 t z-(RiemannEvenFlow.flow m t 0)*Complex.exp (Complex.I*(u : ℂ)*z) := by
    simp only [f,mul_sub]
    rw [integral_sub]
    · rw [integral_mul_const,integral_complex_ofReal,← RiemannEvenNormalization.flow_zero_eq_mass]
      simp only [jet,RiemannEvenFlow.integrand,pow_zero,mul_one]
    · have hj := RiemannEvenFlow.integrand_integrable m 0 t z
      change Integrable (fun v : ℝ => (weighted m 0 t 0 v : ℂ)*
        (Complex.I*(v : ℂ))^0*Complex.exp (Complex.I*(v : ℂ)*z)) RiemannQuarticFlow.halfLine at hj
      simpa only [pow_zero,mul_one] using hj
    · exact hi.mul_const _
  rw [hf] at hb
  exact hb

theorem actual_flow_cosine_error_bound (m : ℕ) (t u : ℝ) (z : ℂ) (hu : 0 ≤ u) :
    ‖flow m t z-flow m t 0*Complex.cos ((u : ℂ)*z)‖ ≤
      (Real.exp (u*|z.im|)*‖z‖)*
        (∫ v : ℝ in Ici 0, |v-u| * Real.exp (‖z‖*|v-u|) * weighted m 0 t 0 v) := by
  have hp := actual_jet_moment_error_bound m t u z hu
  have hn := actual_jet_moment_error_bound m t u (-z) hu
  simp only [Complex.neg_im,abs_neg,norm_neg] at hn
  have heq : flow m t z-flow m t 0*Complex.cos ((u : ℂ)*z) =
      ((jet m 0 t z-flow m t 0*Complex.exp (Complex.I*(u : ℂ)*z))+
        (jet m 0 t (-z)-flow m t 0*Complex.exp (Complex.I*(u : ℂ)*(-z))))/2 := by
    rw [show Complex.I*(u : ℂ)*z=((u : ℂ)*z)*Complex.I by ring,
      show Complex.I*(u : ℂ)*(-z)=-((u : ℂ)*z)*Complex.I by ring]
    simp only [flow,Complex.cos]
    ring
  rw [heq,norm_div,Complex.norm_ofNat]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  have h := norm_add_le (jet m 0 t z-flow m t 0*Complex.exp (Complex.I*(u : ℂ)*z))
    (jet m 0 t (-z)-flow m t 0*Complex.exp (Complex.I*(u : ℂ)*(-z)))
  linarith

theorem actual_normalized_cosine_error_bound (m : ℕ) (t u : ℝ) (z : ℂ) (hu : 0 ≤ u) :
    ‖flow m t z/flow m t 0-Complex.cos ((u : ℂ)*z)‖ ≤
      (Real.exp (u*|z.im|)*‖z‖)*
        ((∫ v : ℝ in Ici 0, |v-u| * Real.exp (‖z‖*|v-u|) * weighted m 0 t 0 v)/
          (flow m t 0).re) := by
  have hM := RiemannEvenNormalizedCompact.actual_flow_zero_pos m t
  have hMne : flow m t 0 ≠ 0 := by intro h; rw [h] at hM; simp at hM
  have hnorm : ‖flow m t 0‖ = (flow m t 0).re := by
    rw [RiemannEvenNormalization.flow_zero_eq_mass,Complex.norm_real,Complex.ofReal_re,Real.norm_eq_abs]
    exact abs_of_pos (by simpa only [RiemannEvenNormalization.flow_zero_eq_mass,Complex.ofReal_re] using hM)
  rw [show flow m t z/flow m t 0-Complex.cos ((u : ℂ)*z) =
    (flow m t z-flow m t 0*Complex.cos ((u : ℂ)*z))/flow m t 0 by field_simp,
    norm_div,hnorm]
  have h := div_le_div_of_nonneg_right (actual_flow_cosine_error_bound m t u z hu) hM.le
  simpa only [mul_div_assoc] using h

end OperatorDerivativeRewrite.Foundation.RiemannEvenFourierMoment
