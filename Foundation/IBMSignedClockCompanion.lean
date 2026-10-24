import Foundation.IBMRawTemporalKernel
import Foundation.BrownianSignIntegral

/-! Actual signed-clock companion and a positive finite-energy transfer.
The companion is an ambient joint-law variable, not asserted IBM-observable. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.IBMSignedClockCompanion
open InfiniteGaussian IBMTimeAveragedObservable IBMRandomTimeHilbert GaussianTimeProcess
open BrownianSignIntegral IBMRawTemporalKernel IBMFoldedClockAbsolute GaussianAbsoluteMoments
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
attribute [local irreducible] IBMConstructedSources.ibmValue IBMConstructedSources.clockPath
  GaussianTimeProcess.process

def source (t : ℝ≥0) (Y : SampleSpace) : GaussianL2 :=
  signum (process t Y) • randomSourceClass t Y

theorem source_memLp (t : ℝ≥0) : MemLp (source t) 2 gaussianProduct := by
  have hm : StronglyMeasurable (source t) :=
    (signum_measurable.comp (process_stronglyMeasurable t).measurable).stronglyMeasurable.smul
      (randomSourceClass_stronglyMeasurable t)
  apply (randomSourceClass_memLp t).mono hm.aestronglyMeasurable
  apply ae_of_all
  intro Y
  change ‖signum (process t Y) • randomSourceClass t Y‖ ≤ ‖randomSourceClass t Y‖
  rw [norm_smul]
  exact (mul_le_mul_of_nonneg_right (signum_bound _) (norm_nonneg _)).trans_eq (one_mul _)

def sourceL2 (t : ℝ≥0) : ValueSpace := (source_memLp t).toLp (source t)

theorem sourceL2_ae (t : ℝ≥0) : sourceL2 t =ᵐ[gaussianProduct] source t :=
  MemLp.coeFn_toLp _

def observed (t : ℝ≥0) : JointL2 := jointRealization (sourceL2 t)

theorem observed_actual (t : ℝ≥0) : observed t =ᵐ[IBMSourceLaws.jointMeasure]
    fun p => signum (IBMConstructedSources.clockPath p.2 t) *
      IBMConstructedSources.ibmValue t p := by
  apply jointRealization_ae_of_sections
  · have hc : Measurable (fun p : IBMSourceLaws.JointSample =>
        IBMConstructedSources.clockPath p.2 t) :=
      ((ContinuousMap.measurable_eval t).comp IBMConstructedSources.clockPath_measurable).comp
        measurable_snd
    have hp : Measurable (fun p : IBMSourceLaws.JointSample => (t,p)) :=
      measurable_const.prodMk measurable_id
    have hb : Measurable (fun p : IBMSourceLaws.JointSample =>
        IBMConstructedSources.ibmValue t p) := by
      simpa only [Function.comp_def] using IBMConstructedSources.ibmValue_jointly_measurable.comp hp
    exact (signum_measurable.comp hc).mul hb
  · filter_upwards [sourceL2_ae t,IBMUnmollifiedSourceDerivative.actual_section_ae t,
      IBMConstructedSources.clockPath_coordinate_ae t] with Y hY ha hc
    rw [hY]
    filter_upwards [ha,Lp.coeFn_smul (signum (process t Y)) (randomSourceClass t Y)]
      with X hX hsm
    change (signum (process t Y) • randomSourceClass t Y) X = _
    simp only [hsm,Pi.smul_apply,smul_eq_mul,hX,hc]

theorem signed_min_identity (x y : ℝ) :
    signum x * signum y * min |x| |y| = (|x+y|-|x-y|)/2 := by
  by_cases hx0 : x=0
  · subst x
    simp [signum_zero]
  by_cases hy0 : y=0
  · subst y
    simp [signum_zero]
  have h := min_absolute_identity x y
  rcases lt_or_gt_of_ne hx0 with hx | hx <;> rcases lt_or_gt_of_ne hy0 with hy | hy
  · have hsx : signum x = -1 := by simp [signum,hx,not_lt_of_gt hx]
    have hsy : signum y = -1 := by simp [signum,hy,not_lt_of_gt hy]
    rw [hsx,hsy,abs_of_neg hx,abs_of_neg hy,abs_of_neg (add_neg hx hy)] at *
    linarith
  · have hsx : signum x = -1 := by simp [signum,hx,not_lt_of_gt hx]
    have hsy : signum y = 1 := by simp [signum,hy]
    rw [hsx,hsy,abs_of_neg hx,abs_of_pos hy,abs_of_neg (by linarith : x-y<0)] at *
    linarith
  · have hsx : signum x = 1 := by simp [signum,hx]
    have hsy : signum y = -1 := by simp [signum,hy,not_lt_of_gt hy]
    rw [hsx,hsy,abs_of_pos hx,abs_of_neg hy,abs_of_pos (by linarith : 0<x-y)] at *
    linarith
  · have hsx : signum x = 1 := by simp [signum,hx]
    have hsy : signum y = 1 := by simp [signum,hy]
    rw [hsx,hsy,abs_of_pos hx,abs_of_pos hy,abs_of_pos (add_pos hx hy)] at *
    linarith

def companionKernel (s t : ℝ≥0) : ℝ :=
  standardMoment 1 * (Real.sqrt ((s:ℝ)+t+2*min (s:ℝ) t)-Real.sqrt |(t:ℝ)-s|)/2

theorem actual_inner (s t : ℝ≥0) :
    inner ℝ (observed s) (observed t) = companionKernel s t := by
  change inner ℝ (jointRealization (sourceL2 s)) (jointRealization (sourceL2 t)) = _
  rw [jointRealization.inner_map_map,L2_inner_eq_integral]
  have he : (∫ Y, inner ℝ (sourceL2 s Y) (sourceL2 t Y) ∂gaussianProduct) =
      ∫ Y, (|process s Y+process t Y|-|process s Y-process t Y|)/2 ∂gaussianProduct := by
    apply integral_congr_ae
    filter_upwards [sourceL2_ae s,sourceL2_ae t] with Y hs ht
    rw [hs,ht]
    change inner ℝ (signum (process s Y) • IBMContinuousScenery.sourceScenery |process s Y|)
      (signum (process t Y) • IBMContinuousScenery.sourceScenery |process t Y|) = _
    rw [real_inner_smul_left,real_inner_smul_right,source_inner (abs_nonneg _) (abs_nonneg _)]
    rw [← signed_min_identity]
    ring
  rw [he,integral_div]
  have hs : Integrable (process s) gaussianProduct :=
    (process_memLp s 1 (by simp)).integrable (by simp)
  have ht : Integrable (process t) gaussianProduct :=
    (process_memLp t 1 (by simp)).integrable (by simp)
  have hi := integral_sub (hs.add ht).abs (hs.sub ht).abs
  simp only [Pi.add_apply,Pi.sub_apply] at hi
  rw [hi,clock_sum_absolute,clock_sub_absolute]
  unfold companionKernel
  ring

theorem kernel_split (s t : ℝ≥0) : kernel s t + companionKernel s t = 2*quarterKernel s t := by
  unfold kernel companionKernel quarterKernel
  ring

theorem energy_split {ι : Type*} (A : Finset ι) (a : ι → ℝ) (τ : ι → ℝ≥0) :
    ‖∑ i ∈ A, a i • IBMDeterministicRangeObstruction.observed (τ i)‖^2 +
      ‖∑ i ∈ A, a i • observed (τ i)‖^2 =
        2 * ∑ i ∈ A, ∑ j ∈ A, a i*a j*quarterKernel (τ i) (τ j) := by
  rw [IBMRawTemporalKernel.finite_energy,← real_inner_self_eq_norm_sq]
  simp only [sum_inner,inner_sum,real_inner_smul_left,real_inner_smul_right,actual_inner]
  have hsym (s t : ℝ≥0) : companionKernel t s = companionKernel s t :=
    (actual_inner t s).symm.trans ((real_inner_comm _ _).trans (actual_inner s t))
  rw [← Finset.sum_add_distrib]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [hsym]
  calc
    _ = a i*a j*(kernel (τ i) (τ j)+companionKernel (τ i) (τ j)) := by ring
    _ = _ := by rw [kernel_split]; ring

theorem finite_energy_bound {ι : Type*} (A : Finset ι) (a : ι → ℝ) (τ : ι → ℝ≥0) :
    ‖∑ i ∈ A, a i • IBMDeterministicRangeObstruction.observed (τ i)‖^2 ≤
      2 * ∑ i ∈ A, ∑ j ∈ A, a i*a j*quarterKernel (τ i) (τ j) := by
  have h := energy_split A a τ
  nlinarith [sq_nonneg ‖∑ i ∈ A, a i • observed (τ i)‖]

end OperatorDerivativeRewrite.Foundation.IBMSignedClockCompanion
