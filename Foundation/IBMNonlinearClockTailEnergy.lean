import Foundation.IBMNonlinearClockEnergy
import Foundation.IBMClockTailOverlap

/-! Actual coefficient-valued nonlinear clock fields with bounded spatial tail
masks. Uniform energy comes from the earlier-time weighted clock transition,
including the nonlinear +4 correction and the null time diagonal. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMNonlinearClockTailEnergy
open InfiniteGaussian IBMConstructedSources IBMClockOverlapEnergy IBMFoldedTransitionBound
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

def maskedSection (w : ℝ → ℝ) (n : ℕ) (t : ℝ) (Y : SampleSpace) : GaussianVectorL2 :=
  w (clockPath Y t.toNNReal) • IBMNonlinearClockField.sectionField n t Y

theorem section_stronglyMeasurable (w : ℝ → ℝ) (hw : Measurable w) (n : ℕ) :
    StronglyMeasurable (Function.uncurry (maskedSection w n)) :=
  (hw.comp BrownianClockWeightedEnergy.sigma_measurable).stronglyMeasurable.smul
    (IBMNonlinearClockField.section_stronglyMeasurable n)

theorem section_norm_bound (w : ℝ → ℝ) (h0 : ∀ x, 0 ≤ w x)
    (h1 : ∀ x, w x ≤ 1) (n : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ r, ‖IBMNonlinearClockColumn.column n r‖ ≤ C) (t : ℝ) (Y : SampleSpace) :
    ‖maskedSection w n t Y‖ ≤ C * ‖IBMClockAverageCandidate.direction t‖ := by
  rw [maskedSection,norm_smul,Real.norm_of_nonneg (h0 _)]
  exact (mul_le_mul_of_nonneg_right (h1 _) (norm_nonneg _)).trans
    (by simpa only [one_mul] using IBMNonlinearClockField.section_norm_bound n hC hb t Y)

theorem section_memLp (w : ℝ → ℝ) (hw : Measurable w) (h0 : ∀ x, 0 ≤ w x)
    (h1 : ∀ x, w x ≤ 1) (n : ℕ) (t : ℝ) : MemLp (maskedSection w n t) 2 gaussianProduct := by
  obtain ⟨C,hC,hb⟩ := IBMNonlinearClockColumn.column_bounded n
  exact MemLp.of_bound ((section_stronglyMeasurable w hw n).comp_measurable
    (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      (C * ‖IBMClockAverageCandidate.direction t‖)
      (ae_of_all _ (section_norm_bound w h0 h1 n hC hb t))

def field (w : ℝ → ℝ) (n : ℕ) (t : ℝ) : IBMClockAverageCandidate.Target :=
  ProductL2Sections.sectionL2 gaussianProduct (Function.uncurry (maskedSection w n)) t

theorem field_ae (w : ℝ → ℝ) (hw : Measurable w) (h0 : ∀ x, 0 ≤ w x)
    (h1 : ∀ x, w x ≤ 1) (n : ℕ) (t : ℝ) :
    field w n t =ᵐ[gaussianProduct] maskedSection w n t :=
  ProductL2Sections.sectionL2_coeFn gaussianProduct _ t (section_memLp w hw h0 h1 n t)

theorem field_stronglyMeasurable (w : ℝ → ℝ) (hw : Measurable w) (n : ℕ) :
    StronglyMeasurable (field w n) :=
  ProductL2Sections.sectionL2_stronglyMeasurable gaussianProduct _
    (section_stronglyMeasurable w hw n)

theorem field_integrable (w : ℝ → ℝ) (hw : Measurable w) (h0 : ∀ x, 0 ≤ w x)
    (h1 : ∀ x, w x ≤ 1) (n : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    Integrable (field w n) (window T) := by
  obtain ⟨C,hC,hb⟩ := IBMNonlinearClockColumn.column_bounded n
  apply Integrable.of_bound (field_stronglyMeasurable w hw n).aestronglyMeasurable
    (C * Real.sqrt T)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have hh := Lp.norm_le_of_ae_bound (f := field w n t)
    (mul_nonneg hC (norm_nonneg (IBMClockAverageCandidate.direction t)))
    ((field_ae w hw h0 h1 n t).mono fun Y hY => hY ▸ section_norm_bound w h0 h1 n hC hb t Y)
  have hb' : ‖field w n t‖ ≤ C * ‖IBMClockAverageCandidate.direction t‖ := by
    simpa [measureUnivNNReal] using hh
  exact hb'.trans (mul_le_mul_of_nonneg_left
    (IBMClockAverageCandidate.direction_norm_bound hT ht) hC)

def average (w : ℝ → ℝ) (n : ℕ) (T : ℝ) : IBMClockAverageCandidate.Target :=
  ∫ t, field w n t ∂window T

theorem inner_kernel_integrable (w : ℝ → ℝ) (hw : Measurable w) (h0 : ∀ x, 0 ≤ w x)
    (h1 : ∀ x, w x ≤ 1) (n m : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    Integrable (fun p : ℝ × ℝ => inner ℝ (field w n p.1) (field w m p.2))
      ((window T).prod (window T)) := by
  apply ((field_integrable w hw h0 h1 n hT).norm.mul_prod
    (field_integrable w hw h0 h1 m hT).norm).mono'
    (((field_stronglyMeasurable w hw n).comp_measurable measurable_fst).inner
      ((field_stronglyMeasurable w hw m).comp_measurable measurable_snd)).aestronglyMeasurable
  exact ae_of_all _ fun p => norm_inner_le_norm _ _

theorem average_inner (w : ℝ → ℝ) (hw : Measurable w) (h0 : ∀ x, 0 ≤ w x)
    (h1 : ∀ x, w x ≤ 1) (n m : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    inner ℝ (average w n T) (average w m T) =
      ∫ p : ℝ × ℝ, inner ℝ (field w n p.1) (field w m p.2)
        ∂(window T).prod (window T) := by
  rw [average,average,real_inner_comm,
    ← integral_inner (field_integrable w hw h0 h1 n hT),
    integral_prod _ (inner_kernel_integrable w hw h0 h1 n m hT)]
  apply integral_congr_ae
  exact ae_of_all _ fun s => by
    change inner ℝ (∫ t, field w m t ∂window T) (field w n s) = _
    rw [real_inner_comm,← integral_inner (field_integrable w hw h0 h1 m hT)]

theorem field_inner_ordered_le (w : ℝ → ℝ) (hw : Measurable w) (h0 : ∀ x, 0 ≤ w x)
    {R : ℝ} (hR : 0 < R) (hwR : ∀ x, w x ≤ IBMClockTailOverlap.tail R x)
    (n m : ℕ) {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    ‖inner ℝ (field w n s) (field w m t)‖ ≤
      min s t * ((2 * peak (nndist t s) + 4) * (s / R^2)) := by
  have ht : 0 ≤ t := hs.trans hst.le
  have h1 (x : ℝ) : w x ≤ 1 := (hwR x).trans (IBMClockTailOverlap.tail_le_one R x)
  have hh : s.toNNReal < t.toNNReal := by
    apply NNReal.coe_lt_coe.mp
    simpa only [Real.coe_toNNReal _ hs,Real.coe_toNNReal _ ht] using hst
  have hi := (IBMClockTailOverlap.clock_tail_overlap_integrable n m R s.toNNReal t.toNNReal).add
    ((IBMClockTailOverlap.clock_tail_integrable R s.toNNReal).mul_const 4)
  have hi' : Integrable (fun Y => IBMClockTailOverlap.tail R (clockPath Y s.toNNReal) *
      (overlap n m |clockPath Y s.toNNReal| |clockPath Y t.toNNReal|+4)) gaussianProduct := by
    simp_rw [mul_add]
    exact hi
  rw [L2_inner_eq_integral]
  calc
    _ ≤ ∫ Y, ‖inner ℝ (field w n s Y) (field w m t Y)‖ ∂gaussianProduct :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ Y, min s t * (IBMClockTailOverlap.tail R (clockPath Y s.toNNReal) *
        (overlap n m |clockPath Y s.toNNReal| |clockPath Y t.toNNReal|+4))
          ∂gaussianProduct := by
      apply integral_mono_ae (L2.integrable_inner (𝕜 := ℝ) (field w n s) (field w m t)).norm
        (hi'.const_mul _)
      filter_upwards [field_ae w hw h0 h1 n s,field_ae w hw h0 h1 m t] with Y hn hm
      rw [hn,hm,maskedSection,maskedSection,real_inner_smul_left,inner_smul_right,norm_mul,norm_mul,
        Real.norm_of_nonneg (h0 _),Real.norm_of_nonneg (h0 _)]
      have hb := IBMNonlinearClockField.section_inner_bound n m hs ht Y
      have hp : w (clockPath Y s.toNNReal) * w (clockPath Y t.toNNReal) ≤
          IBMClockTailOverlap.tail R (clockPath Y s.toNNReal) := by
        exact (mul_le_mul (hwR _) (h1 _) (h0 _)
          (IBMClockTailOverlap.tail_nonneg R _)).trans_eq (mul_one _)
      have hmul := mul_le_mul hp hb (norm_nonneg _) (IBMClockTailOverlap.tail_nonneg R _)
      nlinarith [hmul]
    _ = min s t * (∫ Y, IBMClockTailOverlap.tail R (clockPath Y s.toNNReal) *
        (overlap n m |clockPath Y s.toNNReal| |clockPath Y t.toNNReal|+4)
          ∂gaussianProduct) := integral_const_mul _ _
    _ ≤ _ := by
      have h := IBMClockTailOverlap.clock_tail_envelope_le n m hR s.toNNReal t.toNNReal hh
      simp only [Real.coe_toNNReal _ hs,Real.coe_toNNReal _ ht] at h
      exact mul_le_mul_of_nonneg_left h (le_min hs ht)

theorem field_inner_off_diagonal_le (w : ℝ → ℝ) (hw : Measurable w)
    (h0 : ∀ x, 0 ≤ w x) {R : ℝ} (hR : 0 < R)
    (hwR : ∀ x, w x ≤ IBMClockTailOverlap.tail R x) (n m : ℕ) {T s t : ℝ}
    (hs : s ∈ Ioc 0 T) (ht : t ∈ Ioc 0 T) (hne : s ≠ t) :
    ‖inner ℝ (field w n s) (field w m t)‖ ≤
      (T^2/R^2) * (2*peak 1*timeKernel T s t+4) := by
  have hmin : 0 ≤ min s t := le_min hs.1.le ht.1.le
  have hmax : min s t ≤ T := (min_le_left _ _).trans hs.2
  have hT : 0 ≤ T := hs.1.le.trans hs.2
  have hR2 : 0 < R^2 := sq_pos_of_pos hR
  have hscale (a : ℝ) (ha : 0 ≤ a) (haT : a ≤ T) : min s t * a / R^2 ≤ T^2/R^2 := by
    apply div_le_div_of_nonneg_right _ hR2.le
    nlinarith [mul_le_mul hmax haT ha hT]
  rw [timeKernel_off_diagonal hs ht hne]
  rcases lt_or_gt_of_ne hne with hst | hts
  · have h := field_inner_ordered_le w hw h0 hR hwR n m hs.1.le hst
    rw [peak_nndist] at h
    have hk : 0 ≤ 2*peak 1*|t-s|^(-(1/2:ℝ))+4 :=
      add_nonneg (mul_nonneg (mul_nonneg (by norm_num) (peak_nonneg 1))
        (Real.rpow_nonneg (abs_nonneg _) _)) (by norm_num)
    have hh := mul_le_mul_of_nonneg_right (hscale s hs.1.le hs.2) hk
    apply h.trans
    convert hh using 1
    ring
  · rw [real_inner_comm]
    have h := field_inner_ordered_le w hw h0 hR hwR m n ht.1.le hts
    rw [peak_nndist,abs_sub_comm,min_comm] at h
    have hk : 0 ≤ 2*peak 1*|t-s|^(-(1/2:ℝ))+4 :=
      add_nonneg (mul_nonneg (mul_nonneg (by norm_num) (peak_nonneg 1))
        (Real.rpow_nonneg (abs_nonneg _) _)) (by norm_num)
    have hh := mul_le_mul_of_nonneg_right (hscale t ht.1.le ht.2) hk
    apply h.trans
    convert hh using 1
    ring

theorem average_uniform_tail_energy (w : ℝ → ℝ) (hw : Measurable w)
    (h0 : ∀ x, 0 ≤ w x) {R : ℝ} (hR : 0 < R)
    (hwR : ∀ x, w x ≤ IBMClockTailOverlap.tail R x) (n : ℕ)
    {T : ℝ} (hT : 0 ≤ T) :
    ‖average w n T‖^2 ≤ (T/R^2) * (8*peak 1*T^2*Real.sqrt T+4*T^3) := by
  have h1 (x : ℝ) : w x ≤ 1 := (hwR x).trans (IBMClockTailOverlap.tail_le_one R x)
  have hi : Integrable (fun p : ℝ × ℝ => 2*peak 1*timeKernel T p.1 p.2+4)
      ((window T).prod (window T)) :=
    ((timeKernel_integrable hT).const_mul _).add (integrable_const 4)
  rw [← real_inner_self_eq_norm_sq,average_inner w hw h0 h1 n n hT]
  calc
    _ ≤ ∫ p : ℝ × ℝ, (T^2/R^2)*(2*peak 1*timeKernel T p.1 p.2+4)
        ∂(window T).prod (window T) := by
      apply integral_mono_ae (inner_kernel_integrable w hw h0 h1 n n hT) (hi.const_mul _)
      filter_upwards [window_pair_mem T,window_off_diagonal T] with p hp hne
      exact (le_abs_self _).trans
        (field_inner_off_diagonal_le w hw h0 hR hwR n n hp.1 hp.2 hne)
    _ = (T^2/R^2)*((2*peak 1)*(∫ p : ℝ × ℝ, timeKernel T p.1 p.2
        ∂(window T).prod (window T))+4*T^2) := by
      rw [integral_const_mul,integral_add ((timeKernel_integrable hT).const_mul _)
        (integrable_const 4),integral_const_mul,integral_const]
      have hm : ((window T).prod (window T)).real univ = T*T := by
        simpa only [univ_prod_univ,IBMNonlinearClockEnergy.window_mass hT] using
          (measureReal_prod_prod (μ := window T) (ν := window T) univ univ)
      simp only [smul_eq_mul,hm]
      ring
    _ ≤ (T^2/R^2)*((2*peak 1)*(4*T*Real.sqrt T)+4*T^2) := by
      gcongr
      · exact mul_nonneg (by norm_num) (peak_nonneg 1)
      · exact timeKernel_integral_bound hT
    _ = _ := by ring

end OperatorDerivativeRewrite.Foundation.IBMNonlinearClockTailEnergy
