import Foundation.IBMCompletedPredictableMultiplier
import Foundation.MultiplierCore

/-! Actual random predictable rectangle pull-out for every original channel input. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMPredictableRectanglePullout
open IBMTimeAveragedObservable IBMPredictableRectangles IBMPredictableFiniteIntegral
open IBMPredictableLpDictionary IBMJointPredictableMultiplier IBMCompletedPredictableMultiplier
open IBMObservedTerminalMartingale IBMIntrinsicRightGerm
local instance : MeasurableSpace Space := IBMNaturalFiltrationObstruction.naturalFiltration.predictable
set_option backward.isDefEq.respectTransparency false

def sampleMask (A : Set IBMSourceLaws.JointSample) (hA : MeasurableSet A) : JointL2 →L[ℝ] JointL2 :=
  boundedMultiplier (A.indicator (fun _ => (1 : ℝ))) ((memLp_top_const 1).indicator hA)

theorem sampleMask_ae (A : Set IBMSourceLaws.JointSample) (hA : MeasurableSet A) (Y : JointL2) :
    sampleMask A hA Y =ᵐ[IBMSourceLaws.jointMeasure] A.indicator (Y : IBMSourceLaws.JointSample → ℝ) := by
  filter_upwards [boundedMultiplier_coeFn (A.indicator (fun _ => (1 : ℝ)))
    ((memLp_top_const 1).indicator hA) Y] with ω hω
  change sampleMask A hA Y ω = _ at hω ⊢
  rw [hω]
  by_cases h : ω ∈ A <;> simp [Set.indicator, h]

def futureSet (s : ℝ≥0) (A : Set IBMSourceLaws.JointSample) : Set Space := Ioi s ×ˢ A

theorem futureSet_measurable (s : ℝ≥0) (A : Set IBMSourceLaws.JointSample)
    (hA : MeasurableSet[IBMNaturalFiltrationObstruction.naturalFiltration s] A) :
    MeasurableSet (futureSet s A) := measurableSet_predictable_Ioi_prod hA

def futureMultiplier (s : ℝ≥0) (A : Set IBMSourceLaws.JointSample)
    (hA : MeasurableSet[IBMNaturalFiltrationObstruction.naturalFiltration s] A) : BoundedPredictable :=
  indicator (futureSet s A) (futureSet_measurable s A hA)

def tailIndex (s : ℝ≥0) (d : Index) : Index :=
  ⟨(max (left d) s, max (max (left d) s) (right d), event d), le_max_left _ _,
    (IBMNaturalFiltrationObstruction.naturalFiltration.mono (le_max_left _ _)) _ (event_measurable d)⟩

def localizedIndex (s : ℝ≥0) (A : Set IBMSourceLaws.JointSample)
    (hA : MeasurableSet[IBMNaturalFiltrationObstruction.naturalFiltration s] A) (d : Index) : Index :=
  ⟨(max (left d) s, max (max (left d) s) (right d), A ∩ event d), le_max_left _ _,
    ((IBMNaturalFiltrationObstruction.naturalFiltration.mono (le_max_right _ _)) _ hA).inter
      ((IBMNaturalFiltrationObstruction.naturalFiltration.mono (le_max_left _ _)) _ (event_measurable d))⟩

theorem tail_rect (s : ℝ≥0) (d : Index) :
    rect (max (left d) s) (max (max (left d) s) (right d)) (event d) =
      futureSet s univ ∩ rect (left d) (right d) (event d) := by
  ext ⟨r,ω⟩
  simp only [rect,futureSet,mem_inter_iff,mem_prod,mem_Ioc,mem_Ioi,mem_univ,and_true,max_lt_iff]
  constructor
  · rintro ⟨⟨⟨ha,hs⟩,hb⟩,hω⟩
    have hr : r ≤ right d := (le_max_iff.mp hb).resolve_left (not_le_of_gt (max_lt ha hs))
    exact ⟨hs,⟨ha,hr⟩,hω⟩
  · rintro ⟨hs,⟨ha,hb⟩,hω⟩
    exact ⟨⟨⟨ha,hs⟩,hb.trans (le_max_right _ _)⟩,hω⟩

theorem tail_process (s : ℝ≥0) (d : Index) :
    basisProcess (tailIndex s d) = basisProcess d-
      (IBMPredictableTimeCutoff.timeSet s).indicator (basisProcess d) := by
  funext p
  have he := tail_rect s d
  change (rect (max (left d) s) (max (max (left d) s) (right d)) (event d)).indicator
    (fun _ => (1 : ℝ)) p = _
  rw [he]
  by_cases hp : p ∈ rect (left d) (right d) (event d)
  · have hpos : 0 < p.1 := (zero_le : 0 ≤ left d).trans_lt hp.1.1
    by_cases hs : p.1 ≤ s
    · have htime : p ∈ IBMPredictableTimeCutoff.timeSet s := ⟨⟨hpos,hs⟩,mem_univ _⟩
      have hfuture : p ∉ futureSet s univ := fun h => (not_lt_of_ge hs) h.1
      simp [basisProcess, Set.indicator, hp, htime, hfuture]
    · have hfuture : p ∈ futureSet s univ := ⟨lt_of_not_ge hs,mem_univ _⟩
      have htime : p ∉ IBMPredictableTimeCutoff.timeSet s := fun h => hs h.1.2
      simp [basisProcess, Set.indicator, hp, htime, hfuture]
  · simp [basisProcess, Set.indicator, hp]

theorem localized_process (s : ℝ≥0) (A : Set IBMSourceLaws.JointSample)
    (hA : MeasurableSet[IBMNaturalFiltrationObstruction.naturalFiltration s] A) (d : Index) :
    basisProcess (localizedIndex s A hA d) = (futureMultiplier s A hA).function * basisProcess d := by
  funext p
  have he : rect (max (left d) s) (max (max (left d) s) (right d)) (A ∩ event d) =
      futureSet s A ∩ rect (left d) (right d) (event d) := by
    ext ⟨r,ω⟩
    simp only [rect,futureSet,mem_inter_iff,mem_prod,mem_Ioc,mem_Ioi,max_lt_iff]
    constructor
    · rintro ⟨⟨⟨ha,hs⟩,hb⟩,hA,hB⟩
      have hr : r ≤ right d := (le_max_iff.mp hb).resolve_left (not_le_of_gt (max_lt ha hs))
      exact ⟨⟨hs,hA⟩,⟨ha,hr⟩,hB⟩
    · rintro ⟨⟨hs,hA⟩,⟨ha,hb⟩,hB⟩
      exact ⟨⟨⟨ha,hs⟩,hb.trans (le_max_right _ _)⟩,hA,hB⟩
  change (rect (max (left d) s) (max (max (left d) s) (right d)) (A ∩ event d)).indicator
    (fun _ => (1 : ℝ)) p = _
  rw [he]
  by_cases hp : p ∈ futureSet s A <;> by_cases hq : p ∈ rect (left d) (right d) (event d) <;>
    simp [futureMultiplier,IBMCompletedPredictableMultiplier.indicator,basisProcess,Set.indicator,hp,hq]

def cell (F : JointL2) (d : Index) : PredictableL2 F := dictionary F (Finsupp.single d 1)

theorem cell_ae (F : JointL2) (d : Index) :
    cell F d =ᵐ[IBMJointPredictableEnergyMeasure.predictableMeasure F] basisProcess d := by
  simpa only [cell,processLinear,Finsupp.linearCombination_single,one_smul] using
    dictionary_ae F (Finsupp.single d 1)

theorem cell_integral (F : JointL2) (d : Index) :
    IBMFullPredictableIntegral.integral F (cell F d) = basisIntegral F d := by
  rw [cell,IBMFullPredictableIntegral.integral_dictionary]
  simp only [integralLinear,Finsupp.linearCombination_single,one_smul]

theorem cell_tail (F : JointL2) (s : ℝ≥0) (d : Index) :
    cell F (tailIndex s d) = cell F d-IBMPredictableTimeCutoff.cutoff F s (cell F d) := by
  apply Lp.ext
  filter_upwards [cell_ae F (tailIndex s d), cell_ae F d,
    IBMPredictableTimeCutoff.cutoff_ae F s (cell F d),
    Lp.coeFn_sub (cell F d) (IBMPredictableTimeCutoff.cutoff F s (cell F d))] with p ht hd hc hs
  rw [ht,hs,Pi.sub_apply,hc,hd]
  have he := congrFun (tail_process s d) p
  change basisProcess (tailIndex s d) p = basisProcess d p-
    (IBMPredictableTimeCutoff.timeSet s).indicator (cell F d) p
  by_cases hp : p ∈ IBMPredictableTimeCutoff.timeSet s
  · simpa only [Pi.sub_apply,indicator_of_mem hp,hd] using he
  · simpa only [Pi.sub_apply,indicator_of_notMem hp] using he

theorem cell_localized (F : JointL2) (s : ℝ≥0) (A : Set IBMSourceLaws.JointSample)
    (hA : MeasurableSet[IBMNaturalFiltrationObstruction.naturalFiltration s] A) (d : Index) :
    multiplier (futureMultiplier s A hA) F (cell F d) = cell F (localizedIndex s A hA d) := by
  apply Lp.ext
  filter_upwards [multiplier_ae (futureMultiplier s A hA) F (cell F d),cell_ae F d,
    cell_ae F (localizedIndex s A hA d)] with p hg hd hl
  rw [hg,hl,Pi.mul_apply,hd]
  exact (congrFun (localized_process s A hA d) p).symm



theorem localized_integral (F : JointL2) (s : ℝ≥0) (A : Set IBMSourceLaws.JointSample)
    (hA : MeasurableSet[IBMNaturalFiltrationObstruction.naturalFiltration s] A) (d : Index) :
    basisIntegral F (localizedIndex s A hA d) =
      sampleMask A (IBMNaturalFiltrationObstruction.naturalFiltration.le s _ hA)
        (basisIntegral F (tailIndex s d)) := by
  have hl := IBMGermPredictableStep.stepClass_ae F (ordered (localizedIndex s A hA d))
    (IBMWeightedTerminalEnergy.eventCoefficient _ _ (event_measurable (localizedIndex s A hA d)))
  have ht := IBMGermPredictableStep.stepClass_ae F (ordered (tailIndex s d))
    (IBMWeightedTerminalEnergy.eventCoefficient _ _ (event_measurable (tailIndex s d)))
  change basisIntegral F (localizedIndex s A hA d) =ᵐ[IBMSourceLaws.jointMeasure]
    (fun ω => (A ∩ event d).indicator (fun _ => (1 : ℝ)) ω *
      (channel F (max (max (left d) s) (right d)) ω-channel F (max (left d) s) ω)) at hl
  change basisIntegral F (tailIndex s d) =ᵐ[IBMSourceLaws.jointMeasure]
    (fun ω => (event d).indicator (fun _ => (1 : ℝ)) ω *
      (channel F (max (max (left d) s) (right d)) ω-channel F (max (left d) s) ω)) at ht
  apply Lp.ext
  filter_upwards [hl,ht,sampleMask_ae A (IBMNaturalFiltrationObstruction.naturalFiltration.le s _ hA)
    (basisIntegral F (tailIndex s d))] with ω hl ht hm
  rw [hl,hm]
  by_cases ha : ω ∈ A <;> by_cases hb : ω ∈ event d <;>
    simp [Set.indicator,ha,hb,ht]

theorem cell_future_integral (F : JointL2) (s : ℝ≥0) (A : Set IBMSourceLaws.JointSample)
    (hA : MeasurableSet[IBMNaturalFiltrationObstruction.naturalFiltration s] A) (d : Index) :
    IBMFullPredictableIntegral.integral F (multiplier (futureMultiplier s A hA) F (cell F d)) =
      sampleMask A (IBMNaturalFiltrationObstruction.naturalFiltration.le s _ hA)
        (IBMFullPredictableIntegral.integral F (cell F d)-
          channelClass (IBMFullPredictableIntegral.integral F (cell F d)) s) := by
  rw [cell_localized,cell_integral,localized_integral,← cell_integral F (tailIndex s d),cell_tail,
    map_sub,IBMPredictableTimeCutoff.integral_cutoff]
  rfl

theorem future_integral (F : JointL2) (s : ℝ≥0) (A : Set IBMSourceLaws.JointSample)
    (hA : MeasurableSet[IBMNaturalFiltrationObstruction.naturalFiltration s] A) (H : PredictableL2 F) :
    IBMFullPredictableIntegral.integral F (multiplier (futureMultiplier s A hA) F H) =
      sampleMask A (IBMNaturalFiltrationObstruction.naturalFiltration.le s _ hA)
        (IBMFullPredictableIntegral.integral F H-channelClass (IBMFullPredictableIntegral.integral F H) s) := by
  let L : PredictableL2 F →L[ℝ] JointL2 :=
    (IBMFullPredictableIntegral.integral F).toContinuousLinearMap.comp (multiplier (futureMultiplier s A hA) F)
  let R : PredictableL2 F →L[ℝ] JointL2 :=
    (sampleMask A (IBMNaturalFiltrationObstruction.naturalFiltration.le s _ hA)).comp
      ((ContinuousLinearMap.id ℝ JointL2-(rightPast s).starProjection).comp
        (IBMFullPredictableIntegral.integral F).toContinuousLinearMap)
  have he : L.toLinearMap.comp (dictionary F) = R.toLinearMap.comp (dictionary F) := by
    apply Finsupp.lhom_ext'
    intro d
    apply LinearMap.ext
    intro a
    have hc : dictionary F (Finsupp.single d a) = a • cell F d := by
      rw [show Finsupp.single d a = a • Finsupp.single d 1 by simp]
      rw [map_smul]
      rfl
    change L (dictionary F (Finsupp.single d a)) = R (dictionary F (Finsupp.single d a))
    rw [hc,map_smul,map_smul]
    exact congrArg (fun v : JointL2 => a • v) (cell_future_integral F s A hA d)
  have hLR : (L : PredictableL2 F → JointL2) = R :=
    (IBMPredictableDictionaryDensity.dictionary_dense F).equalizer L.continuous R.continuous
      (funext fun l => DFunLike.congr_fun he l)
  exact congrFun hLR H



def rectangleMultiplier (s t : ℝ≥0) (A : Set IBMSourceLaws.JointSample)
    (hA : MeasurableSet[IBMNaturalFiltrationObstruction.naturalFiltration s] A) : BoundedPredictable :=
  IBMCompletedPredictableMultiplier.indicator (rect s t A) (rect_predictable s t A hA)

theorem rectangle_multiplier_split (F : JointL2) {s t : ℝ≥0} (hst : s ≤ t)
    (A : Set IBMSourceLaws.JointSample)
    (hA : MeasurableSet[IBMNaturalFiltrationObstruction.naturalFiltration s] A) (H : PredictableL2 F) :
    multiplier (rectangleMultiplier s t A hA) F H =
      multiplier (futureMultiplier s A hA) F H-
        multiplier (futureMultiplier t A ((IBMNaturalFiltrationObstruction.naturalFiltration.mono hst) _ hA)) F H := by
  apply Lp.ext
  filter_upwards [multiplier_ae (rectangleMultiplier s t A hA) F H,
    multiplier_ae (futureMultiplier s A hA) F H,
    multiplier_ae (futureMultiplier t A ((IBMNaturalFiltrationObstruction.naturalFiltration.mono hst) _ hA)) F H,
    Lp.coeFn_sub (multiplier (futureMultiplier s A hA) F H)
      (multiplier (futureMultiplier t A ((IBMNaturalFiltrationObstruction.naturalFiltration.mono hst) _ hA)) F H)]
    with p hr hs ht hsub
  rw [hr,hsub,Pi.sub_apply,hs,ht]
  by_cases ha : p.2 ∈ A
  · by_cases hs : s < p.1
    · by_cases ht : p.1 ≤ t
      · have hnt : ¬ t < p.1 := not_lt_of_ge ht
        simp [rectangleMultiplier,futureMultiplier,IBMCompletedPredictableMultiplier.indicator,
          rect,futureSet,Set.indicator,ha,hs,ht,hnt]
      · have htr : t < p.1 := lt_of_not_ge ht
        simp [rectangleMultiplier,futureMultiplier,IBMCompletedPredictableMultiplier.indicator,
          rect,futureSet,Set.indicator,ha,hs,ht,htr]
    · have hnt : ¬ t < p.1 := fun h => hs (hst.trans_lt h)
      simp [rectangleMultiplier,futureMultiplier,IBMCompletedPredictableMultiplier.indicator,
        rect,futureSet,Set.indicator,ha,hs,hnt]
  · simp [rectangleMultiplier,futureMultiplier,IBMCompletedPredictableMultiplier.indicator,
      rect,futureSet,Set.indicator,ha]

def stepOutput (s t : ℝ≥0) (A : Set IBMSourceLaws.JointSample)
    (hA : MeasurableSet[IBMNaturalFiltrationObstruction.naturalFiltration s] A) : JointL2 →L[ℝ] JointL2 :=
  (sampleMask A (IBMNaturalFiltrationObstruction.naturalFiltration.le s _ hA)).comp
    ((rightPast t).starProjection-(rightPast s).starProjection)

theorem stepOutput_ae (s t : ℝ≥0) (A : Set IBMSourceLaws.JointSample)
    (hA : MeasurableSet[IBMNaturalFiltrationObstruction.naturalFiltration s] A) (Y : JointL2) :
    stepOutput s t A hA Y =ᵐ[IBMSourceLaws.jointMeasure]
      (fun ω => A.indicator (fun _ => (1 : ℝ)) ω*(channel Y t ω-channel Y s ω)) := by
  have hm := sampleMask_ae A (IBMNaturalFiltrationObstruction.naturalFiltration.le s _ hA)
    (channelClass Y t-channelClass Y s)
  change stepOutput s t A hA Y =ᵐ[IBMSourceLaws.jointMeasure] _ at hm
  filter_upwards [hm,Lp.coeFn_sub (channelClass Y t) (channelClass Y s)] with ω hm hs
  rw [hm]
  by_cases ha : ω ∈ A
  · simp only [indicator_of_mem ha,one_mul]
    exact hs
  · simp only [indicator_of_notMem ha,zero_mul]

theorem stepOutput_eq_stepClass (F : JointL2) {s t : ℝ≥0} (hst : s ≤ t)
    (A : Set IBMSourceLaws.JointSample)
    (hA : MeasurableSet[IBMNaturalFiltrationObstruction.naturalFiltration s] A) :
    stepOutput s t A hA F = IBMGermPredictableStep.stepClass F s t
      (IBMWeightedTerminalEnergy.eventCoefficient s A hA) := by
  apply Lp.ext
  exact (stepOutput_ae s t A hA F).trans (IBMGermPredictableStep.stepClass_ae F hst
    (IBMWeightedTerminalEnergy.eventCoefficient s A hA)).symm

theorem rectangle_integral (F : JointL2) {s t : ℝ≥0} (hst : s ≤ t)
    (A : Set IBMSourceLaws.JointSample)
    (hA : MeasurableSet[IBMNaturalFiltrationObstruction.naturalFiltration s] A) (H : PredictableL2 F) :
    IBMFullPredictableIntegral.integral F (multiplier (rectangleMultiplier s t A hA) F H) =
      stepOutput s t A hA (IBMFullPredictableIntegral.integral F H) := by
  rw [rectangle_multiplier_split F hst,map_sub,future_integral,future_integral,← map_sub]
  change sampleMask A (IBMNaturalFiltrationObstruction.naturalFiltration.le s _ hA)
    (IBMFullPredictableIntegral.integral F H-channelClass (IBMFullPredictableIntegral.integral F H) s-
      (IBMFullPredictableIntegral.integral F H-channelClass (IBMFullPredictableIntegral.integral F H) t)) =
    sampleMask A (IBMNaturalFiltrationObstruction.naturalFiltration.le s _ hA)
      (channelClass (IBMFullPredictableIntegral.integral F H) t-
        channelClass (IBMFullPredictableIntegral.integral F H) s)
  congr 1
  abel

end OperatorDerivativeRewrite.Foundation.IBMPredictableRectanglePullout
