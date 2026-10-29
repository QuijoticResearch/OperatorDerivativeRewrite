import Foundation.CubeOperatorLocalization

/-! Two-sided native L2 compression of the actual Wilson transfer near low action. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace OperatorDerivativeRewrite.Foundation.CubeNativeCompression
open CubeTemporalSlab CubeWilsonSlab CubeSlabGround CubeSlabL2 CubeOperatorLocalization
variable {beta : ℝ} (d : GroundData beta)

/-- The literal action cutoff is self-adjoint in the native stationary space. -/
theorem tailPart_pairing (eps : ℝ) (f g : StateL2 d) :
    inner ℝ (tailPart d eps f) g=inner ℝ f (tailPart d eps g) := by
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [tailPart_coe d eps f,tailPart_coe d eps g] with U hf hg
  rw [hf,hg]
  by_cases h : eps ≤ spatialAction U <;> simp [Set.indicator,h]

/-- Self-adjointness transfers the input-tail bound to the actual output tail. -/
theorem output_tail_bound (hb : 0 ≤ beta) (eps : ℝ) (f : StateL2 d) :
    ‖tailPart d eps (operator d f)‖ ≤ (Real.exp (-beta*eps/2)/d.value)*‖f‖ := by
  let h := tailPart d eps (operator d f)
  let c := Real.exp (-beta*eps/2)/d.value
  have hp : ‖h‖^2 ≤ ‖f‖*(c*‖h‖) := by
    calc
      _ = inner ℝ h h := (real_inner_self_eq_norm_sq h).symm
      _ = inner ℝ f (operator d (tailPart d eps h)) := by
        change inner ℝ (tailPart d eps (operator d f)) h=_
        rw [tailPart_pairing,operator_symmetric]
      _ ≤ ‖f‖*‖operator d (tailPart d eps h)‖ := real_inner_le_norm _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (operator_tailPart_bound d hb eps h) (norm_nonneg f)
  have hc : 0 ≤ c := div_nonneg (Real.exp_pos _).le d.value_pos.le
  change ‖h‖ ≤ c*‖f‖
  by_cases hz : ‖h‖=0
  · rw [hz]
    exact mul_nonneg hc (norm_nonneg f)
  · apply (mul_le_mul_iff_right₀ (lt_of_le_of_ne (norm_nonneg h) (Ne.symm hz))).mp
    convert hp using 1 <;> ring

/-- The complementary low-action component, with no change of the stationary law. -/
def lowPart (eps : ℝ) (f : StateL2 d) : StateL2 d := f-tailPart d eps f

theorem lowPart_norm (eps : ℝ) (f : StateL2 d) : ‖lowPart d eps f‖ ≤ ‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [Lp.coeFn_sub f (tailPart d eps f),tailPart_coe d eps f] with U hs ht
  change (f-tailPart d eps f) U=_ at hs
  change ‖(f-tailPart d eps f) U‖ ≤ _
  simp only [Pi.sub_apply] at hs
  rw [hs,ht]
  by_cases h : eps ≤ spatialAction U <;> simp [Set.indicator,h]

/-- Uniform full-space compression error. This is not a spectral-gap theorem. -/
theorem compression_error (hb : 0 ≤ beta) (eps : ℝ) (f : StateL2 d) :
    ‖operator d f-lowPart d eps (operator d (lowPart d eps f))‖ ≤
      2*(Real.exp (-beta*eps/2)/d.value)*‖f‖ := by
  have he : operator d f-lowPart d eps (operator d (lowPart d eps f))=
      operator d (tailPart d eps f)+tailPart d eps (operator d (lowPart d eps f)) := by
    unfold lowPart
    rw [map_sub]
    abel
  rw [he]
  have h1 := operator_tailPart_bound d hb eps f
  have h2 := output_tail_bound d hb eps (lowPart d eps f)
  have h3 := mul_le_mul_of_nonneg_left (lowPart_norm d eps f)
    (div_nonneg (Real.exp_pos (-beta*eps/2)).le d.value_pos.le)
  have h := norm_add_le (operator d (tailPart d eps f))
    (tailPart d eps (operator d (lowPart d eps f)))
  linarith

end OperatorDerivativeRewrite.Foundation.CubeNativeCompression
