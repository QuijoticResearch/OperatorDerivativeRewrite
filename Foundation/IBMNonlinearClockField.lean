import Foundation.IBMNonlinearClockColumn

/-! Genuine conditional-source L2 clock-gradient fields for mollified sine
observables. All measurability and fixed-mollifier integrability are proved;
the nonlinear covariance estimate survives genuine clock integration. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMNonlinearClockField
open InfiniteGaussian IBMClockAverageCandidate IBMClockOverlapEnergy IBMConstructedSources
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
attribute [local irreducible] clockPath
  IBMNonlinearClockColumn.column scalarTensor direction
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

def sectionField (n : ℕ) (t : ℝ) (ω : SampleSpace) : GaussianVectorL2 :=
  BrownianSignIntegral.signum (clockPath ω t.toNNReal) •
    scalarTensor (direction t) (IBMNonlinearClockColumn.column n |clockPath ω t.toNNReal|)

theorem section_stronglyMeasurable (n : ℕ) :
    StronglyMeasurable (Function.uncurry (sectionField n)) := by
  have hs : Measurable (fun p : ℝ × SampleSpace =>
      BrownianSignIntegral.signum (clockPath p.2 p.1.toNNReal)) :=
    BrownianSignIntegral.signum_measurable.comp BrownianClockWeightedEnergy.sigma_measurable
  have hd : StronglyMeasurable (fun p : ℝ × SampleSpace => direction p.1) :=
    direction_continuous.stronglyMeasurable.comp_measurable measurable_fst
  have hc : StronglyMeasurable (fun p : ℝ × SampleSpace =>
      IBMNonlinearClockColumn.column n |clockPath p.2 p.1.toNNReal|) :=
    (IBMNonlinearClockColumn.column_stronglyMeasurable n).comp_measurable
      (continuous_abs.measurable.comp BrownianClockWeightedEnergy.sigma_measurable)
  exact hs.stronglyMeasurable.smul
    (scalarTensor_joint_continuous.comp_stronglyMeasurable (hd.prodMk hc))

theorem section_norm_bound (n : ℕ) {C : ℝ} (_hC : 0 ≤ C)
    (hb : ∀ r, ‖IBMNonlinearClockColumn.column n r‖ ≤ C) (t : ℝ) (ω : SampleSpace) :
    ‖sectionField n t ω‖ ≤ C*‖direction t‖ := by
  rw [sectionField,norm_smul,scalarTensor_norm]
  calc
    _ ≤ 1*(C*‖direction t‖) := mul_le_mul (BrownianSignIntegral.signum_bound _)
      (mul_le_mul_of_nonneg_right (hb _) (norm_nonneg _)) (by positivity) zero_le_one
    _ = _ := one_mul _

theorem section_memLp (n : ℕ) (t : ℝ) : MemLp (sectionField n t) 2 gaussianProduct := by
  obtain ⟨C,hC,hb⟩ := IBMNonlinearClockColumn.column_bounded n
  exact MemLp.of_bound ((section_stronglyMeasurable n).comp_measurable
    (measurable_const.prodMk measurable_id)).aestronglyMeasurable (C*‖direction t‖)
      (ae_of_all _ (section_norm_bound n hC hb t))

def field (n : ℕ) (t : ℝ) : IBMClockAverageCandidate.Target :=
  ProductL2Sections.sectionL2 gaussianProduct (Function.uncurry (sectionField n)) t

theorem field_ae (n : ℕ) (t : ℝ) : field n t =ᵐ[gaussianProduct] sectionField n t :=
  ProductL2Sections.sectionL2_coeFn gaussianProduct _ t (section_memLp n t)

theorem field_stronglyMeasurable (n : ℕ) : StronglyMeasurable (field n) :=
  ProductL2Sections.sectionL2_stronglyMeasurable gaussianProduct _ (section_stronglyMeasurable n)

theorem field_norm_bound (n : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ r, ‖IBMNonlinearClockColumn.column n r‖ ≤ C) (t : ℝ) :
    ‖field n t‖ ≤ C*‖direction t‖ := by
  have h := Lp.norm_le_of_ae_bound (f := field n t) (mul_nonneg hC (norm_nonneg _))
    ((field_ae n t).mono fun ω hω => hω ▸ section_norm_bound n hC hb t ω)
  simpa [measureUnivNNReal] using h

theorem field_integrable (n : ℕ) {T : ℝ} (hT : 0 ≤ T) : Integrable (field n) (window T) := by
  obtain ⟨C,hC,hb⟩ := IBMNonlinearClockColumn.column_bounded n
  apply Integrable.of_bound (field_stronglyMeasurable n).aestronglyMeasurable (C*Real.sqrt T)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact (field_norm_bound n hC hb t).trans
    (mul_le_mul_of_nonneg_left (direction_norm_bound hT ht) hC)

theorem section_actual_ae (n : ℕ) (t : ℝ) (ωY : SampleSpace) :
    sectionField n t ωY =ᵐ[gaussianProduct] (fun ωX =>
      (BrownianSignIntegral.signum (clockPath ωY t.toNNReal)*
        Real.cos (mollifiedValue n 0 t.toNNReal (ωX,ωY))*
          mollifiedValue n 1 t.toNNReal (ωX,ωY)) • direction t) := by
  filter_upwards [Lp.coeFn_smul (BrownianSignIntegral.signum (clockPath ωY t.toNNReal))
    (scalarTensor (direction t) (IBMNonlinearClockColumn.column n |clockPath ωY t.toNNReal|)),
    scalarTensor_coeFn (direction t) (IBMNonlinearClockColumn.column n |clockPath ωY t.toNNReal|),
    IBMNonlinearClockColumn.column_actual_ae n |clockPath ωY t.toNNReal|] with ωX hs ht hc
  change (BrownianSignIntegral.signum _ • scalarTensor _ _) ωX = _
  rw [hs,Pi.smul_apply,ht,hc,smul_smul]
  change (BrownianSignIntegral.signum _ *
    (Real.cos (mollifiedValue n 0 t.toNNReal (ωX,ωY))*
      mollifiedValue n 1 t.toNNReal (ωX,ωY))) • _ = _
  rw [mul_assoc]

theorem section_inner_bound (n m : ℕ) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (ω : SampleSpace) :
    ‖inner ℝ (sectionField n s ω) (sectionField m t ω)‖ ≤
      min s t*(IBMFoldedTransitionBound.overlap n m |clockPath ω s.toNNReal|
        |clockPath ω t.toNNReal|+4) := by
  have hmin : 0 ≤ min s t := le_min hs ht
  have hcol := IBMNonlinearClockColumn.column_inner_bound n m
    |clockPath ω s.toNNReal| |clockPath ω t.toNNReal|
  rw [sectionField,sectionField,real_inner_smul_left,inner_smul_right,
    GaussianTimeFieldNorm.scalarTensor_pair_inner,direction_inner hs ht]
  rw [norm_mul,norm_mul,norm_mul,Real.norm_of_nonneg hmin]
  have hsign : ‖BrownianSignIntegral.signum (clockPath ω s.toNNReal)‖*
      ‖BrownianSignIntegral.signum (clockPath ω t.toNNReal)‖ ≤ 1 := by
    exact (mul_le_mul (BrownianSignIntegral.signum_bound _) (BrownianSignIntegral.signum_bound _)
      (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hprod := mul_le_mul hsign hcol (abs_nonneg _) zero_le_one
  have hfinal := mul_le_mul_of_nonneg_right hprod hmin
  simpa only [Real.norm_eq_abs,one_mul,mul_assoc,mul_comm,mul_left_comm] using hfinal

theorem field_inner_bound (n m : ℕ) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    ‖inner ℝ (field n s) (field m t)‖ ≤ min s t*(covariance n m s t+4) := by
  obtain ⟨M,hM0,hM⟩ := IBMFoldedTransitionBound.overlap_bounded n m
  have hc (r : ℝ) : Measurable (fun ω => |clockPath ω r.toNNReal|) :=
    continuous_abs.measurable.comp ((ContinuousMap.measurable_eval _).comp clockPath_measurable)
  have hi : Integrable (fun ω => IBMFoldedTransitionBound.overlap n m
      |clockPath ω s.toNNReal| |clockPath ω t.toNNReal|) gaussianProduct := by
    apply Integrable.of_bound ((IBMFoldedTransitionBound.overlap_continuous n m).measurable.comp
      ((hc s).prodMk (hc t))).aestronglyMeasurable M
    exact ae_of_all _ fun ω => by
      change ‖IBMFoldedTransitionBound.overlap n m |clockPath ω s.toNNReal|
        |clockPath ω t.toNNReal|‖ ≤ M
      rw [Real.norm_of_nonneg (IBMFoldedTransitionBound.overlap_nonneg _ _ _ _)]
      exact hM _ _
  rw [L2_inner_eq_integral]
  calc
    _ ≤ ∫ ω, ‖inner ℝ (field n s ω) (field m t ω)‖ ∂gaussianProduct :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ ω, min s t*(IBMFoldedTransitionBound.overlap n m
        |clockPath ω s.toNNReal| |clockPath ω t.toNNReal|+4) ∂gaussianProduct := by
      apply integral_mono_ae (L2.integrable_inner (𝕜 := ℝ) (field n s) (field m t)).norm
        ((hi.add (integrable_const 4)).const_mul (min s t))
      filter_upwards [field_ae n s,field_ae m t] with ω hn hm
      rw [hn,hm]
      exact section_inner_bound n m hs ht ω
    _ = _ := by rw [integral_const_mul,integral_add hi (integrable_const 4)]; simp [covariance]

end OperatorDerivativeRewrite.Foundation.IBMNonlinearClockField
