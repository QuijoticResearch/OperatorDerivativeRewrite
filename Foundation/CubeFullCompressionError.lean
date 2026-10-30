import Foundation.CubeCompressedNormLimit

/-! Full-operator control of the original chord-Haar exterior, not only pointwise kernel control. -/
noncomputable section
open MeasureTheory Set
namespace OperatorDerivativeRewrite.Foundation.CubeFullCompressionError
open CubeTemporalSlab CubeWilsonSlab CubeSlabGround CubeAxialSlice CubeHaarSplit CubeChartAction
open CubeChordOperator CubeBoundaryChartL2 CubeBoundaryChartInverse CubeChartCompressedKernel
open CubeBoundaryExterior
attribute [local irreducible] CubeWilsonSlab.kernel

private theorem abs_mean_le_norm (f : ChordL2) : (∫ q,|f q| ∂chordHaar) ≤ ‖f‖ := by
  let a : ChordL2 := (Lp.memLp f).norm.toLp (fun q => ‖f q‖)
  let o : ChordL2 := (memLp_const (1:ℝ)).toLp (fun _ => 1)
  have ha : a =ᵐ[chordHaar] (fun q => ‖f q‖) := MemLp.coeFn_toLp _
  have ho : o =ᵐ[chordHaar] (fun _ => (1:ℝ)) := MemLp.coeFn_toLp _
  have hna : ‖a‖=‖f‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [BochnerL2Dominated.norm_sq_integral,BochnerL2Dominated.norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [ha] with q hq
    rw [hq,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
  have hno : ‖o‖=1 := by
    apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0:ℝ)≤1)).mp
    rw [BochnerL2Dominated.norm_sq_integral]
    calc
      _ = ∫ _ : Chords,(1:ℝ) ∂chordHaar := by
        apply integral_congr_ae
        filter_upwards [ho] with q hq
        simp only [hq,Real.norm_eq_abs,abs_one,one_pow]
      _ = _ := by simp
  have hi : inner ℝ a o=(∫ q,|f q| ∂chordHaar) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [ha,ho] with q hq h1
    rw [hq,h1,Real.inner_apply,mul_one,Real.norm_eq_abs]
  have h := norm_inner_le_norm (𝕜 := ℝ) a o
  rw [hi,hna,hno,mul_one,Real.norm_eq_abs] at h
  exact (le_abs_self _).trans h

private theorem constant_nonnegative : 0 ≤ errorConstant := by
  unfold errorConstant
  exact mul_nonneg (pow_nonneg CubeMatchedGround.temporalConstant_pos.le 7) (by norm_num)

def errorKernel (t : ℝ) (p : Chords × Chords) : ℝ :=
  (chordRegion ×ˢ chordRegion)ᶜ.indicator
    (fun p => kernel (1/t^2) (axialState p.1) (axialState p.2)/t^36) p

theorem errorKernel_measurable (t : ℝ) : Measurable (errorKernel t) :=
  (((kernel_joint_measurable (1/t^2)).comp
    ((CubeChordTransfer.axial_measurable.comp measurable_fst).prodMk
      (CubeChordTransfer.axial_measurable.comp measurable_snd))).div_const (t^36)).indicator
        (chordRegion_measurable.prod chordRegion_measurable).compl

theorem errorKernel_nonnegative (t : ℝ) (ht : 0 < t) (q r : Chords) : 0 ≤ errorKernel t (q,r) := by
  apply Set.indicator_nonneg
  intro p _
  exact div_nonneg (kernel_positive _ _ _).le (pow_pos ht 36).le

theorem errorKernel_bound (t : ℝ) (ht : 0 < t) (h1 : t ≤ 1) (q r : Chords) :
    errorKernel t (q,r) ≤ errorConstant*t := by
  classical
  unfold errorKernel
  by_cases hp : (q,r) ∈ (chordRegion ×ˢ chordRegion)ᶜ
  · rw [Set.indicator_of_mem hp]
    apply outside_kernel_bound t ht h1
    have h : q ∉ chordRegion ∨ r ∉ chordRegion := by
      simpa only [Set.mem_compl_iff,Set.mem_prod,not_and_or] using hp
    rcases h with hq | hr
    · exact Or.inl (by simpa only [region,Set.mem_preimage,reduced_axial] using hq)
    · exact Or.inr (by simpa only [region,Set.mem_preimage,reduced_axial] using hr)
  · rw [Set.indicator_of_notMem hp]
    exact mul_nonneg constant_nonnegative ht.le

def errorRow (t : ℝ) (f : ChordL2) (q : Chords) : ℝ :=
  ∫ r,errorKernel t (q,r)*f r ∂chordHaar

theorem errorRow_integrable (t : ℝ) (ht : 0 < t) (h1 : t ≤ 1) (f : ChordL2) (q : Chords) :
    Integrable (fun r => errorKernel t (q,r)*f r) chordHaar := by
  have hi : Integrable (fun r => |f r|) chordHaar := by
    simpa only [Real.norm_eq_abs] using (Lp.memLp f).norm.integrable (by norm_num : (1:ENNReal)≤2)
  apply (hi.const_mul (errorConstant*t)).mono'
    (((errorKernel_measurable t).comp (measurable_const.prodMk measurable_id)).mul
      (Lp.stronglyMeasurable f).measurable).aestronglyMeasurable
  filter_upwards with r
  change ‖errorKernel t (q,r)*f r‖ ≤ errorConstant*t*|f r|
  rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (errorKernel_nonnegative t ht q r)]
  exact mul_le_mul_of_nonneg_right (errorKernel_bound t ht h1 q r) (abs_nonneg _)

theorem errorRow_bound (t : ℝ) (ht : 0 < t) (h1 : t ≤ 1) (f : ChordL2) (q : Chords) :
    |errorRow t f q| ≤ (errorConstant*t)*‖f‖ := by
  have hi : Integrable (fun r => |f r|) chordHaar := by
    simpa only [Real.norm_eq_abs] using (Lp.memLp f).norm.integrable (by norm_num : (1:ENNReal)≤2)
  have h := norm_integral_le_of_norm_le (hi.const_mul (errorConstant*t))
    (f := fun r => errorKernel t (q,r)*f r) (ae_of_all chordHaar (fun r => by
      rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (errorKernel_nonnegative t ht q r)]
      exact mul_le_mul_of_nonneg_right (errorKernel_bound t ht h1 q r) (abs_nonneg _)))
  rw [integral_const_mul,Real.norm_eq_abs] at h
  exact h.trans (mul_le_mul_of_nonneg_left (abs_mean_le_norm f) (mul_nonneg constant_nonnegative ht.le))

private theorem errorRow_eq (t : ℝ) (ht : 0 < t) (f : ChordL2) (q : Chords) :
    rawChord (beta := 1/t^2) f q/t^36-
      chordRegion.indicator (fun q => rawChord (beta := 1/t^2) (localClass f) q/t^36) q=errorRow t f q := by
  classical
  by_cases hq : q ∈ chordRegion
  · rw [Set.indicator_of_mem hq,← sub_div]
    unfold rawChord errorRow
    rw [← integral_sub (rawChord_integrable f q) (rawChord_integrable (localClass f) q),← integral_div]
    apply integral_congr_ae
    filter_upwards [localClass_coe f] with r hr
    rw [hr]
    by_cases hR : r ∈ chordRegion
    · have hp : (q,r) ∉ (chordRegion ×ˢ chordRegion)ᶜ := fun h => h ⟨hq,hR⟩
      simp only [Set.indicator_of_mem hR,errorKernel,Set.indicator_of_notMem hp,sub_self,zero_div,zero_mul]
    · have hp : (q,r) ∈ (chordRegion ×ˢ chordRegion)ᶜ := fun h => hR h.2
      simp only [Set.indicator_of_notMem hR,errorKernel,Set.indicator_of_mem hp,mul_zero,sub_zero]
      ring
  · rw [Set.indicator_of_notMem hq,sub_zero]
    unfold rawChord errorRow
    rw [← integral_div]
    apply integral_congr_ae
    filter_upwards with r
    have hp : (q,r) ∈ (chordRegion ×ˢ chordRegion)ᶜ := fun h => hq h.1
    simp only [errorKernel,Set.indicator_of_mem hp]
    ring

variable (t : ℝ) (ht : 0 < t) (d : GroundData (1/t^2))

def bare : ChordL2 →L[ℝ] ChordL2 := (d.value/t^36) • chordOperator d
def localOperator : ChordL2 →L[ℝ] ChordL2 := (backward t ht).comp ((compressed t ht d).comp (forward t ht))
def residual : ChordL2 →L[ℝ] ChordL2 := bare t d-localOperator t ht d

theorem local_apply (f : ChordL2) : localOperator t ht d f=
    (d.value/t^36) • localClass (chordOperator d (localClass f)) := by
  simp only [localOperator,compressed,ContinuousLinearMap.comp_apply,ContinuousLinearMap.smul_apply,
    map_smul,backward_forward]

private theorem bare_coe (f : ChordL2) : bare t d f =ᵐ[chordHaar]
    (fun q => rawChord (beta := 1/t^2) f q/t^36) := by
  change (d.value/t^36) • chordOperator d f =ᵐ[chordHaar] _
  filter_upwards [Lp.coeFn_smul (d.value/t^36) (chordOperator d f),chordOperator_coe d f] with q hS hB
  rw [hS]
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [hB]
  field_simp [d.value_pos.ne']

private theorem local_coe (f : ChordL2) : localOperator t ht d f =ᵐ[chordHaar]
    (fun q => chordRegion.indicator (fun q => rawChord (beta := 1/t^2) (localClass f) q/t^36) q) := by
  rw [local_apply]
  filter_upwards [Lp.coeFn_smul (d.value/t^36) (localClass (chordOperator d (localClass f))),
    localClass_coe (chordOperator d (localClass f)),chordOperator_coe d (localClass f)] with q hS hL hB
  rw [hS]
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [hL]
  classical
  by_cases hq : q ∈ chordRegion
  · rw [Set.indicator_of_mem hq,Set.indicator_of_mem hq,hB]
    field_simp [d.value_pos.ne']
  · rw [Set.indicator_of_notMem hq,Set.indicator_of_notMem hq,mul_zero]

/-- Exact residual of the FULL actual operator, including both off-diagonal blocks. -/
theorem residual_coe (f : ChordL2) : residual t ht d f =ᵐ[chordHaar] errorRow t f := by
  filter_upwards [Lp.coeFn_sub (bare t d f) (localOperator t ht d f),bare_coe t d f,local_coe t ht d f]
    with q hS hB hL
  change (bare t d f-localOperator t ht d f) q=_
  rw [hS]
  simp only [Pi.sub_apply]
  rw [hB,hL,errorRow_eq t ht]

theorem residual_norm_bound (h1 : t ≤ 1) : ‖residual t ht d‖ ≤ errorConstant*t := by
  apply (residual t ht d).opNorm_le_bound (mul_nonneg constant_nonnegative ht.le)
  intro f
  have hN := BochnerL2Dominated.norm_sq_integral (residual t ht d f)
  have h := integral_mono_ae (Lp.memLp (residual t ht d f)).norm.integrable_sq
    (integrable_const (((errorConstant*t)*‖f‖)^2)) ?_
  · simp only [integral_const,probReal_univ,smul_eq_mul,one_mul] at h
    rw [← hN] at h
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (mul_nonneg constant_nonnegative ht.le) (norm_nonneg _))).mp h
  · filter_upwards [residual_coe t ht d f] with q hq
    rw [hq,Real.norm_eq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (errorRow_bound t ht h1 f q) 2

end OperatorDerivativeRewrite.Foundation.CubeFullCompressionError
