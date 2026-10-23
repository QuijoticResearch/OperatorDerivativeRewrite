import Foundation.IBMFullPredictableIntegral
import Foundation.IBMObservableHorizonLimit

/-! Literal predictable time truncation intertwines the original actual stochastic
integral with observed projections. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMPredictableTimeCutoff
open IBMTimeAveragedObservable IBMPredictableRectangles IBMPredictableLpDictionary
open IBMPredictableFiniteIntegral IBMObservedTerminalMartingale IBMGermPredictableStep
open IBMJointPredictableEnergyMeasure IBMIntrinsicRightGerm IBMRightGermFiltration
set_option backward.isDefEq.respectTransparency false
local instance : MeasurableSpace Space := IBMNaturalFiltrationObstruction.naturalFiltration.predictable

def timeSet (t : ℝ≥0) : Set Space := rect 0 t univ

theorem timeSet_measurable (t : ℝ≥0) : MeasurableSet (timeSet t) :=
  rect_predictable 0 t univ MeasurableSet.univ

def cut (F : JointL2) (t : ℝ≥0) (H : PredictableL2 F) : PredictableL2 F :=
  ((Lp.memLp H).indicator (timeSet_measurable t)).toLp _

theorem cut_ae (F : JointL2) (t : ℝ≥0) (H : PredictableL2 F) :
    cut F t H =ᵐ[predictableMeasure F] (timeSet t).indicator H :=
  ((Lp.memLp H).indicator (timeSet_measurable t)).coeFn_toLp

def cutLinear (F : JointL2) (t : ℝ≥0) : PredictableL2 F →ₗ[ℝ] PredictableL2 F where
  toFun := cut F t
  map_add' H K := by
    apply Lp.ext
    filter_upwards [cut_ae F t (H+K), cut_ae F t H, cut_ae F t K,
      Lp.coeFn_add H K, Lp.coeFn_add (cut F t H) (cut F t K)] with p hc hh hk hs hadd
    rw [hc, hadd, Pi.add_apply, hh, hk]
    by_cases hp : p ∈ timeSet t
    · simp only [indicator_of_mem hp]; exact hs
    · simp only [indicator_of_notMem hp, zero_add]
  map_smul' a H := by
    apply Lp.ext
    filter_upwards [cut_ae F t (a • H), cut_ae F t H,
      Lp.coeFn_smul a H, Lp.coeFn_smul a (cut F t H)] with p hc hh hs hadd
    change cut F t (a • H) p = (a • cut F t H) p
    rw [hc, hadd, Pi.smul_apply, hh]
    by_cases hp : p ∈ timeSet t
    · simpa only [indicator_of_mem hp, Pi.smul_apply] using hs
    · simp only [indicator_of_notMem hp, smul_zero]

theorem cut_norm (F : JointL2) (t : ℝ≥0) (H : PredictableL2 F) : ‖cut F t H‖ ≤ ‖H‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [cut_ae F t H] with p hp
  rw [hp]
  by_cases h : p ∈ timeSet t
  · simp only [indicator_of_mem h, le_refl]
  · simp only [indicator_of_notMem h, norm_zero, norm_nonneg]

def cutoff (F : JointL2) (t : ℝ≥0) : PredictableL2 F →L[ℝ] PredictableL2 F :=
  (cutLinear F t).mkContinuous 1 (fun H => by
    change ‖cut F t H‖ ≤ 1*‖H‖
    simpa only [one_mul] using cut_norm F t H)

theorem cutoff_ae (F : JointL2) (t : ℝ≥0) (H : PredictableL2 F) :
    cutoff F t H =ᵐ[predictableMeasure F] (timeSet t).indicator H := cut_ae F t H

theorem project_channel_min (F : JointL2) (t b : ℝ≥0) :
    (rightPast t).starProjection (channelClass F b) = channelClass F (min t b) := by
  by_cases h : t ≤ b
  · rw [min_eq_left h]; exact project_channel F h
  · have hb : b ≤ t := le_of_not_ge h
    rw [min_eq_right hb]
    exact Submodule.starProjection_eq_self_iff.mpr
      (rightPast_mono hb (Submodule.starProjection_apply_mem _ _))

def cutIndex (t : ℝ≥0) (d : Index) : Index :=
  ⟨(left d, max (left d) (min (right d) t), event d), le_max_left _ _, event_measurable d⟩

theorem basisProcess_cut (t : ℝ≥0) (d : Index) :
    basisProcess (cutIndex t d) = (timeSet t).indicator (basisProcess d) := by
  funext p
  have he : rect (left d) (max (left d) (min (right d) t)) (event d) =
      timeSet t ∩ rect (left d) (right d) (event d) := by
    ext ⟨r,ω⟩
    simp only [rect, timeSet, mem_inter_iff, mem_prod, mem_Ioc, mem_univ, and_true]
    constructor
    · rintro ⟨⟨ha, hb⟩, hω⟩
      have hr : r ≤ min (right d) t := (le_max_iff.mp hb).resolve_left (not_le_of_gt ha)
      exact ⟨⟨(zero_le : 0 ≤ left d).trans_lt ha, hr.trans (min_le_right _ _)⟩,
        ⟨ha, hr.trans (min_le_left _ _)⟩, hω⟩
    · rintro ⟨⟨_, ht⟩, ⟨ha, hb⟩, hω⟩
      exact ⟨⟨ha, (le_min hb ht).trans (le_max_right _ _)⟩, hω⟩
  change (rect (left d) (max (left d) (min (right d) t)) (event d)).indicator (fun _ => 1) p = _
  rw [he]
  by_cases hp : p ∈ timeSet t <;> by_cases hq : p ∈ rect (left d) (right d) (event d) <;>
    simp [Set.indicator, basisProcess, hp, hq]

theorem basisIntegral_cut (F : JointL2) (t : ℝ≥0) (d : Index) :
    basisIntegral F (cutIndex t d) = (rightPast t).starProjection (basisIntegral F d) := by
  let W := IBMWeightedTerminalEnergy.weightedTerminal F (left d)
    (IBMWeightedTerminalEnergy.eventCoefficient (left d) (event d) (event_measurable d))
  change channelClass W (max (left d) (min (right d) t)) - channelClass W (left d) =
    (rightPast t).starProjection (channelClass W (right d) - channelClass W (left d))
  rw [map_sub, project_channel_min, project_channel_min]
  by_cases ht : t ≤ left d
  · have htb := ht.trans (ordered d)
    rw [min_eq_right htb, max_eq_left ht, min_eq_left htb, min_eq_left ht]
    simp only [sub_self]
  · have hat : left d ≤ t := le_of_not_ge ht
    rw [max_eq_right (le_min (ordered d) hat), min_eq_right hat, min_comm t (right d)]



def cutPresentation (t : ℝ≥0) : (Index →₀ ℝ) →ₗ[ℝ] (Index →₀ ℝ) :=
  Finsupp.linearCombination ℝ (fun d => Finsupp.single (cutIndex t d) 1)

theorem cutoff_dictionary (F : JointL2) (t : ℝ≥0) (l : Index →₀ ℝ) :
    cutoff F t (dictionary F l) = dictionary F (cutPresentation t l) := by
  classical
  induction l using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add l k hl hk => simp only [map_add, hl, hk]
  | single d a =>
    have he : cutPresentation t (Finsupp.single d a) = Finsupp.single (cutIndex t d) a := by
      simp only [cutPresentation, Finsupp.linearCombination_single, Finsupp.smul_single,
        smul_eq_mul, mul_one]
    rw [he]
    apply Lp.ext
    filter_upwards [cutoff_ae F t (dictionary F (Finsupp.single d a)),
      dictionary_ae F (Finsupp.single d a), dictionary_ae F (Finsupp.single (cutIndex t d) a)]
      with p hc hd he
    rw [hc, he]
    by_cases hp : p ∈ timeSet t
    · rw [indicator_of_mem hp, hd]
      simp only [processLinear, Finsupp.linearCombination_single, Pi.smul_apply,
        basisProcess_cut, indicator_of_mem hp]
    · rw [indicator_of_notMem hp]
      simp only [processLinear, Finsupp.linearCombination_single, Pi.smul_apply,
        basisProcess_cut, indicator_of_notMem hp, smul_zero]

theorem cutPresentation_integral (F : JointL2) (t : ℝ≥0) (l : Index →₀ ℝ) :
    integralLinear F (cutPresentation t l) = (rightPast t).starProjection (integralLinear F l) := by
  classical
  induction l using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add l k hl hk => simp only [map_add, hl, hk]
  | single d a =>
    simp only [cutPresentation, integralLinear, Finsupp.linearCombination_single,
      Finsupp.smul_single, smul_eq_mul, mul_one, basisIntegral_cut, map_smul]

theorem integral_cutoff (F : JointL2) (t : ℝ≥0) (H : PredictableL2 F) :
    IBMFullPredictableIntegral.integral F (cutoff F t H) =
      (rightPast t).starProjection (IBMFullPredictableIntegral.integral F H) := by
  have he := (IBMPredictableDictionaryDensity.dictionary_dense F).equalizer
    ((IBMFullPredictableIntegral.integral F).continuous.comp (cutoff F t).continuous)
    ((rightPast t).starProjection.continuous.comp (IBMFullPredictableIntegral.integral F).continuous)
    (show (fun H => IBMFullPredictableIntegral.integral F (cutoff F t H)) ∘ dictionary F =
      (fun H => (rightPast t).starProjection (IBMFullPredictableIntegral.integral F H)) ∘ dictionary F from by
        funext l
        simp only [Function.comp_apply, cutoff_dictionary,
          IBMFullPredictableIntegral.integral_dictionary, cutPresentation_integral])
  exact congrFun he H

theorem cutoff_comp (F : JointL2) (s t : ℝ≥0) (H : PredictableL2 F) :
    cutoff F s (cutoff F t H) = cutoff F (min s t) H := by
  apply Lp.ext
  filter_upwards [cutoff_ae F s (cutoff F t H), cutoff_ae F t H, cutoff_ae F (min s t) H]
    with p hs ht hm
  rw [hs, hm]
  by_cases hp : p ∈ timeSet s
  · rw [indicator_of_mem hp, ht]
    by_cases hq : p ∈ timeSet t
    · have hh : p ∈ timeSet (min s t) := ⟨⟨hp.1.1, le_min hp.1.2 hq.1.2⟩, mem_univ _⟩
      rw [indicator_of_mem hq, indicator_of_mem hh]
    · have hh : p ∉ timeSet (min s t) := fun h => hq ⟨⟨h.1.1, h.1.2.trans (min_le_right _ _)⟩, mem_univ _⟩
      rw [indicator_of_notMem hq, indicator_of_notMem hh]
  · have hh : p ∉ timeSet (min s t) := fun h => hp ⟨⟨h.1.1, h.1.2.trans (min_le_left _ _)⟩, mem_univ _⟩
    rw [indicator_of_notMem hp, indicator_of_notMem hh]

theorem cutoff_zero (F : JointL2) (H : PredictableL2 F) : cutoff F 0 H = 0 := by
  apply Lp.ext
  filter_upwards [cutoff_ae F 0 H, Lp.coeFn_zero ℝ 2 (predictableMeasure F)] with p hp hz
  rw [hp, hz]
  simp only [timeSet, rect, Ioc_self, empty_prod, indicator_empty, Pi.zero_apply]

theorem integral_cutoff_projection (F : JointL2) (s t : ℝ≥0) (hst : s ≤ t) (H : PredictableL2 F) :
    (rightPast s).starProjection (IBMFullPredictableIntegral.integral F (cutoff F t H)) =
      IBMFullPredictableIntegral.integral F (cutoff F s H) := by
  rw [← integral_cutoff, cutoff_comp, min_eq_left hst]

theorem integral_cutoff_measurable (F : JointL2) (t : ℝ≥0) (H : PredictableL2 F) :
    StronglyMeasurable[IBMRightGermFiltration.germFiltration t]
      (IBMFullPredictableIntegral.integral F (cutoff F t H) : IBMSourceLaws.JointSample → ℝ) := by
  rw [integral_cutoff]
  exact (IBMRightGermFiltration.representative_measurable t _
    (Submodule.starProjection_apply_mem _ _)).stronglyMeasurable

theorem integral_cutoff_martingale (F : JointL2) (H : PredictableL2 F) :
    Martingale (fun t => (IBMFullPredictableIntegral.integral F (cutoff F t H) :
      IBMSourceLaws.JointSample → ℝ)) IBMRightGermFiltration.germFiltration IBMSourceLaws.jointMeasure := by
  have he : (fun t => (IBMFullPredictableIntegral.integral F (cutoff F t H) :
      IBMSourceLaws.JointSample → ℝ)) = channel (IBMFullPredictableIntegral.integral F H) := by
    funext t
    rw [integral_cutoff]
    rfl
  rw [he]
  exact channel_martingale _



theorem cutoff_right_continuous (F : JointL2) (H : PredictableL2 F) (t : ℝ≥0) :
    ContinuousWithinAt (fun s => cutoff F s H) (Ici t) t := by
  apply (IBMFullPredictableIntegral.integral F).isometry.tendsto_nhds_iff.mpr
  have hc := channel_right_continuous (IBMFullPredictableIntegral.integral F H) t
  change Tendsto (fun s => (rightPast s).starProjection (IBMFullPredictableIntegral.integral F H))
    (𝓝[Ici t] t) (𝓝 ((rightPast t).starProjection (IBMFullPredictableIntegral.integral F H))) at hc
  simpa only [Function.comp_def, integral_cutoff] using hc

theorem cutoff_horizon_limit (F : JointL2) (H : PredictableL2 F) :
    Tendsto (fun n : ℕ => cutoff F n H) atTop (𝓝 H) := by
  apply (IBMFullPredictableIntegral.integral F).isometry.tendsto_nhds_iff.mpr
  simpa only [Function.comp_def, integral_cutoff] using
    IBMObservableHorizonLimit.right_projection_tendsto
      (⟨IBMFullPredictableIntegral.integral F H,
        IBMPredictableIntegralObservable.integral_mem_intrinsic F H⟩ : IntrinsicSpace)

theorem cutoff_increment_energy (F : JointL2) (H : PredictableL2 F)
    {s t : ℝ≥0} (hst : s ≤ t) :
    ‖cutoff F t H‖^2-‖cutoff F s H‖^2 = ‖cutoff F t H-cutoff F s H‖^2 := by
  rw [← (IBMFullPredictableIntegral.integral F).norm_map (cutoff F t H),
    ← (IBMFullPredictableIntegral.integral F).norm_map (cutoff F s H),
    ← (IBMFullPredictableIntegral.integral F).norm_map (cutoff F t H-cutoff F s H), map_sub,
    integral_cutoff, integral_cutoff]
  exact IBMTerminalEnergyMeasure.increment_energy (IBMFullPredictableIntegral.integral F H) hst

end OperatorDerivativeRewrite.Foundation.IBMPredictableTimeCutoff
