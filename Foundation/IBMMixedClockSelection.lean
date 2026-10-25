import Foundation.IBMRawGridMixedObservable

/-! Smaller-radius selection for actual mixed clock covariation.
The selector may depend on both observations; convergence uses literal L1
errors, not an unjustified two-observation conditional projection. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMMixedClockSelection
open InfiniteGaussian GaussianTimeProcess GaussianBrownianQuadraticVariation
open IBMClippedClockCrossing IBMClippedClockCovariation IBMObservedClockCap
open IBMObservedClockOccupation IBMObservedClockBracket IBMTerminalBracketWeights

def select (R S : ℝ≥0) (f g : SampleSpace → ℝ) (Y : SampleSpace) : ℝ :=
  if |process R Y| ≤ |process S Y| then f Y else g Y

theorem select_integrable (R S : ℝ≥0) {f g : SampleSpace → ℝ}
    (hf : Integrable f gaussianProduct) (hg : Integrable g gaussianProduct) :
    Integrable (select R S f g) gaussianProduct := by
  have hm : MeasurableSet {Y | |process R Y| ≤ |process S Y|} := by
    simpa only [Real.norm_eq_abs] using measurableSet_le
      (process_stronglyMeasurable R).measurable.norm
      (process_stronglyMeasurable S).measurable.norm
  change Integrable ({Y | |process R Y| ≤ |process S Y|}.piecewise f g) gaussianProduct
  exact Integrable.piecewise hm hf.integrableOn hg.integrableOn

def selectedSum (H R S : ℝ≥0) (N : ℕ) : SampleSpace → ℝ :=
  select R S (cappedSum H R N) (cappedSum H S N)

def selectedOccupation (H R S : ℝ≥0) : SampleSpace → ℝ :=
  select R S (occupation H R) (occupation H S)

theorem selectedSum_integrable (H R S : ℝ≥0) (N : ℕ) :
    Integrable (selectedSum H R S N) gaussianProduct :=
  select_integrable R S (cappedSum_integrable H R N) (cappedSum_integrable H S N)

theorem selectedOccupation_integrable (H R S : ℝ≥0) :
    Integrable (selectedOccupation H R S) gaussianProduct :=
  select_integrable R S ((occupation_memLp H R).integrable (by norm_num))
    ((occupation_memLp H S).integrable (by norm_num))

theorem selection_error_bound (H R S : ℝ≥0) (N : ℕ) (Y : SampleSpace) :
    |selectedSum H R S N Y-selectedOccupation H R S Y| ≤
      |cappedSum H R N Y-occupation H R Y|+|cappedSum H S N Y-occupation H S Y| := by
  unfold selectedSum selectedOccupation select
  split_ifs <;> linarith [abs_nonneg (cappedSum H R N Y-occupation H R Y),
    abs_nonneg (cappedSum H S N Y-occupation H S Y)]

theorem selected_absolute_error_tendsto (H R S : ℝ≥0) (hH : 0 < H) :
    Tendsto (fun N => ∫ Y, |selectedSum H R S N Y-selectedOccupation H R S Y|
      ∂gaussianProduct) atTop (𝓝 0) := by
  have h := (IBMAllObservationLimits.actual_absolute_error_tendsto_all H R hH).add
    (IBMAllObservationLimits.actual_absolute_error_tendsto_all H S hH)
  simp only [zero_add] at h
  apply squeeze_zero (fun N => integral_nonneg fun Y => abs_nonneg _) _ h
  intro N
  have he := integral_add ((cappedSum_integrable H R N).sub
    ((occupation_memLp H R).integrable (by norm_num))).abs
    ((cappedSum_integrable H S N).sub
    ((occupation_memLp H S).integrable (by norm_num))).abs
  simp only [Pi.sub_apply] at he
  rw [← he]
  exact integral_mono ((selectedSum_integrable H R S N).sub
    (selectedOccupation_integrable H R S)).abs
    (((cappedSum_integrable H R N).sub ((occupation_memLp H R).integrable (by norm_num))).abs.add
      ((cappedSum_integrable H S N).sub ((occupation_memLp H S).integrable (by norm_num))).abs)
    (selection_error_bound H R S N)

def mixedSum (H R S : ℝ≥0) (N : ℕ) (Y : SampleSpace) : ℝ :=
  ∑ i : Fin (N+1),
    (cap (process R Y) (process (uniformTime H N i.succ) Y)-
      cap (process R Y) (process (uniformTime H N i.castSucc) Y))*
    (cap (process S Y) (process (uniformTime H N i.succ) Y)-
      cap (process S Y) (process (uniformTime H N i.castSucc) Y))

theorem mixed_difference_sum (H R S : ℝ≥0) (N : ℕ) (Y : SampleSpace) :
    mixedSum H R S N Y-selectedSum H R S N Y =
      ∑ i : Fin (N+1), mixedError (process R Y) (process S Y)
        (process (uniformTime H N i.castSucc) Y) (process (uniformTime H N i.succ) Y) := by
  unfold mixedSum mixedError
  rw [Finset.sum_sub_distrib]
  congr 1
  unfold selectedSum select cappedSum
  simp only [cap_min_radius]
  split_ifs <;> rfl

theorem mixed_difference_bound (δ : ℝ) (H R S : ℝ≥0) (N : ℕ) (Y : SampleSpace) :
    |mixedSum H R S N Y-selectedSum H R S N Y| ≤
      2*(weightedValue (outerBand δ) H R N Y+weightedValue (outerBand δ) H S N Y+
        IBMClippedClockTail.value δ H N Y) := by
  rw [mixed_difference_sum]
  calc
    _ ≤ ∑ i : Fin (N+1), |mixedError (process R Y) (process S Y)
        (process (uniformTime H N i.castSucc) Y) (process (uniformTime H N i.succ) Y)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin (N+1), 2*(process (uniformTime H N i.succ) Y-
        process (uniformTime H N i.castSucc) Y)^2 *
        (outerBand δ (process (uniformTime H N i.castSucc) Y,process R Y)+
          outerBand δ (process (uniformTime H N i.castSucc) Y,process S Y)+
            (if δ < |process (uniformTime H N i.succ) Y-process (uniformTime H N i.castSucc) Y|
              then 1 else 0)) :=
      Finset.sum_le_sum fun i _ => mixedError_crossing_bound _ _ _ _ _
    _ = _ := by
      unfold weightedValue IBMClippedClockTail.value
      rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      unfold IBMClippedClockTail.cell
      split_ifs <;> ring

theorem mixedSum_measurable (H R S : ℝ≥0) (N : ℕ) :
    Measurable (mixedSum H R S N) := by
  unfold mixedSum cap
  apply Finset.measurable_sum
  intro i hi
  have hp (t : ℝ≥0) : Measurable (fun Y => |process t Y|) := by
    simpa only [Real.norm_eq_abs] using (process_stronglyMeasurable t).measurable.norm
  exact (((hp _).min (hp _)).sub ((hp _).min (hp _))).mul
    (((hp _).min (hp _)).sub ((hp _).min (hp _)))

theorem mixedSum_bound (H R S : ℝ≥0) (N : ℕ) (Y : SampleSpace) :
    |mixedSum H R S N Y| ≤ cappedSum H R N Y+cappedSum H S N Y := by
  unfold mixedSum cappedSum
  rw [← Finset.sum_add_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  generalize cap (process R Y) (process (uniformTime H N i.succ) Y)-
    cap (process R Y) (process (uniformTime H N i.castSucc) Y) = a
  generalize cap (process S Y) (process (uniformTime H N i.succ) Y)-
    cap (process S Y) (process (uniformTime H N i.castSucc) Y) = b
  apply abs_le.mpr
  constructor <;> nlinarith [sq_nonneg (a+b),sq_nonneg (a-b),sq_nonneg a,sq_nonneg b]

theorem mixedSum_integrable (H R S : ℝ≥0) (N : ℕ) :
    Integrable (mixedSum H R S N) gaussianProduct := by
  apply ((cappedSum_integrable H R N).add (cappedSum_integrable H S N)).mono'
    (mixedSum_measurable H R S N).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun Y => by
    simpa only [Real.norm_eq_abs,Pi.add_apply] using mixedSum_bound H R S N Y

theorem mixed_difference_mean_bound (δ : ℝ) (H R S : ℝ≥0) (N : ℕ) :
    (∫ Y, |mixedSum H R S N Y-selectedSum H R S N Y| ∂gaussianProduct) ≤
      2*((∫ Y, weightedValue (outerBand δ) H R N Y ∂gaussianProduct)+
        (∫ Y, weightedValue (outerBand δ) H S N Y ∂gaussianProduct)+
          ∫ Y, IBMClippedClockTail.value δ H N Y ∂gaussianProduct) := by
  have hr := (weightedValue_memLp _ (outerBand_measurable δ) (outerBand_bound δ) H R N).integrable (by norm_num)
  have hs := (weightedValue_memLp _ (outerBand_measurable δ) (outerBand_bound δ) H S N).integrable (by norm_num)
  have ht := IBMClippedClockTail.value_integrable δ H N
  calc
    _ ≤ ∫ Y, 2*(weightedValue (outerBand δ) H R N Y+weightedValue (outerBand δ) H S N Y+
        IBMClippedClockTail.value δ H N Y) ∂gaussianProduct :=
      integral_mono ((mixedSum_integrable H R S N).sub (selectedSum_integrable H R S N)).abs
        (((hr.add hs).add ht).const_mul 2) (mixed_difference_bound δ H R S N)
    _ = _ := by
      rw [integral_const_mul]
      have he := integral_add (hr.add hs) ht
      simp only [Pi.add_apply] at he
      rw [he,integral_add hr hs]

theorem mixed_difference_absolute_tendsto (H R S : ℝ≥0) (hH : 0 < H) :
    Tendsto (fun N => ∫ Y, |mixedSum H R S N Y-selectedSum H R S N Y|
      ∂gaussianProduct) atTop (𝓝 0) := by
  have h := ((IBMAllObservationLimits.outer_weighted_mean_tendsto_all H R hH
    IBMClippedClockTail.width IBMClippedClockTail.width_tendsto).add
    (IBMAllObservationLimits.outer_weighted_mean_tendsto_all H S hH
      IBMClippedClockTail.width IBMClippedClockTail.width_tendsto)).add
        (IBMClippedClockTail.width_mean_tendsto H)
  have hm := h.const_mul 2
  simp only [zero_add,mul_zero] at hm
  exact squeeze_zero (fun N => integral_nonneg fun Y => abs_nonneg _)
    (fun N => mixed_difference_mean_bound (IBMClippedClockTail.width N) H R S N) hm

theorem mixed_absolute_error_tendsto (H R S : ℝ≥0) (hH : 0 < H) :
    Tendsto (fun N => ∫ Y, |mixedSum H R S N Y-selectedOccupation H R S Y|
      ∂gaussianProduct) atTop (𝓝 0) := by
  have h := (mixed_difference_absolute_tendsto H R S hH).add
    (selected_absolute_error_tendsto H R S hH)
  simp only [zero_add] at h
  apply squeeze_zero (fun N => integral_nonneg fun Y => abs_nonneg _) _ h
  intro N
  have hf := ((mixedSum_integrable H R S N).sub (selectedSum_integrable H R S N)).abs
  have hg := ((selectedSum_integrable H R S N).sub (selectedOccupation_integrable H R S)).abs
  have he := integral_add hf hg
  simp only [Pi.sub_apply] at he
  rw [← he]
  exact integral_mono ((mixedSum_integrable H R S N).sub
    (selectedOccupation_integrable H R S)).abs (hf.add hg) fun Y =>
      abs_sub_le _ _ _

end OperatorDerivativeRewrite.Foundation.IBMMixedClockSelection
