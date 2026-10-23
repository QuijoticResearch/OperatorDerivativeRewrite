import Foundation.IBMPredictableRectanglePullout

/-! Actual completed random-rectangle identities and full original L2
stochastic integration lift through the genuine joint-energy completion. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology DirectSum
namespace OperatorDerivativeRewrite.Foundation.IBMCompletedStochasticAssociativity
open IBMTimeAveragedObservable IBMPredictableRectangles IBMPredictableFiniteIntegral
open IBMPredictableLpDictionary IBMMultichannelCompletion
open IBMCompletedPredictableMultiplier IBMPredictableRectanglePullout
attribute [local instance] componentAdd componentGroup componentModule componentZeroDec
set_option backward.isDefEq.respectTransparency false
local instance : MeasurableSpace Space := IBMNaturalFiltrationObstruction.naturalFiltration.predictable
variable {ι : Type*} [DecidableEq ι] (F : ι → JointL2)

theorem completed_rectangle {s t : ℝ≥0} (hst : s ≤ t) (A : Set IBMSourceLaws.JointSample)
    (hA : MeasurableSet[IBMNaturalFiltrationObstruction.naturalFiltration s] A) (z : Completed F) :
    completedIntegral F (operator F (rectangleMultiplier s t A hA) z) =
      stepOutput s t A hA (completedIntegral F z) := by
  let L : Completed F →L[ℝ] JointL2 :=
    (completedIntegral F).toContinuousLinearMap.comp (operator F (rectangleMultiplier s t A hA))
  let R : Completed F →L[ℝ] JointL2 :=
    (stepOutput s t A hA).comp (completedIntegral F).toContinuousLinearMap
  have hr : L.toLinearMap.comp (embed F) = R.toLinearMap.comp (embed F) := by
    apply DirectSum.linearMap_ext
    intro i
    apply LinearMap.ext
    intro H
    change completedIntegral F (operator F (rectangleMultiplier s t A hA)
      (embed F (DirectSum.lof ℝ ι _ i H))) =
      stepOutput s t A hA (completedIntegral F (embed F (DirectSum.lof ℝ ι _ i H)))
    rw [operator_single,completedIntegral_embed,rawIntegral_single,
      completedIntegral_embed,rawIntegral_single,rectangle_integral (F i) hst]
  have he := (embed_dense F).equalizer L.continuous R.continuous
    (funext fun u => DFunLike.congr_fun hr u)
  exact congrFun he z

theorem completed_rectangle_ae {s t : ℝ≥0} (hst : s ≤ t) (A : Set IBMSourceLaws.JointSample)
    (hA : MeasurableSet[IBMNaturalFiltrationObstruction.naturalFiltration s] A) (z : Completed F) :
    completedIntegral F (operator F (rectangleMultiplier s t A hA) z) =ᵐ[IBMSourceLaws.jointMeasure]
      (fun ω => A.indicator (fun _ => (1 : ℝ)) ω*
        (IBMObservedTerminalMartingale.channel (completedIntegral F z) t ω-
          IBMObservedTerminalMartingale.channel (completedIntegral F z) s ω)) := by
  rw [completed_rectangle F hst]
  exact stepOutput_ae s t A hA _

def finiteAction : (Index →₀ ℝ) →ₗ[ℝ] (Completed F →L[ℝ] Completed F) :=
  Finsupp.linearCombination ℝ (fun d =>
    operator F (rectangleMultiplier (left d) (right d) (event d) (event_measurable d)))

def finiteInput (z : Completed F) : (Index →₀ ℝ) →ₗ[ℝ] Completed F :=
  (ContinuousLinearMap.apply ℝ (Completed F) z).toLinearMap.comp (finiteAction F)

theorem finiteInput_single (z : Completed F) (d : Index) (a : ℝ) :
    finiteInput F z (Finsupp.single d a) =
      a • operator F (rectangleMultiplier (left d) (right d) (event d) (event_measurable d)) z := by
  simp only [finiteInput,LinearMap.comp_apply,finiteAction,Finsupp.linearCombination_single]
  rfl

theorem finiteInput_actual (z : Completed F) (l : Index →₀ ℝ) :
    completedIntegral F (finiteInput F z l) = integralLinear (completedIntegral F z) l := by
  classical
  induction l using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add l k hl hk => simp only [map_add,hl,hk]
  | single d a =>
    rw [finiteInput_single,map_smul,completed_rectangle F (ordered d),
      stepOutput_eq_stepClass _ (ordered d)]
    simp only [integralLinear,Finsupp.linearCombination_single,basisIntegral]

theorem finiteInput_norm (z : Completed F) (l : Index →₀ ℝ) :
    ‖finiteInput F z l‖ = ‖dictionary (completedIntegral F z) l‖ := by
  rw [← (completedIntegral F).norm_map,finiteInput_actual]
  exact dictionary_norm _ l

def nestedIntegral (z : Completed F) : PredictableL2 (completedIntegral F z) →ₗᵢ[ℝ] Completed F :=
  (finiteInput F z).extendOfIsometry
    (IBMPredictableDictionaryDensity.dictionary_dense (completedIntegral F z)) (finiteInput_norm F z)

theorem nested_dictionary (z : Completed F) (l : Index →₀ ℝ) :
    nestedIntegral F z (dictionary (completedIntegral F z) l) = finiteInput F z l :=
  LinearMap.extendOfIsometry_eq _ _ _ l

theorem nested_actual (z : Completed F) (H : PredictableL2 (completedIntegral F z)) :
    completedIntegral F (nestedIntegral F z H) =
      IBMFullPredictableIntegral.integral (completedIntegral F z) H := by
  have he := (IBMPredictableDictionaryDensity.dictionary_dense (completedIntegral F z)).equalizer
    ((completedIntegral F).continuous.comp (nestedIntegral F z).continuous)
    (IBMFullPredictableIntegral.integral (completedIntegral F z)).continuous
    (show (fun H => completedIntegral F (nestedIntegral F z H)) ∘ dictionary (completedIntegral F z) =
      IBMFullPredictableIntegral.integral (completedIntegral F z) ∘ dictionary (completedIntegral F z) from by
        funext l
        simp only [Function.comp_apply,nested_dictionary,finiteInput_actual,
          IBMFullPredictableIntegral.integral_dictionary])
  exact congrFun he H

theorem nested_norm (z : Completed F) (H : PredictableL2 (completedIntegral F z)) :
    ‖nestedIntegral F z H‖ = ‖H‖ := (nestedIntegral F z).norm_map H

theorem nested_unique (z : Completed F)
    (T : PredictableL2 (completedIntegral F z) →ₗᵢ[ℝ] Completed F)
    (hT : ∀ l, T (dictionary (completedIntegral F z) l) = finiteInput F z l) :
    T = nestedIntegral F z := by
  symm
  apply LinearMap.extendOfIsometry_unique (finiteInput F z)
    (IBMPredictableDictionaryDensity.dictionary_dense (completedIntegral F z)) (finiteInput_norm F z) T
  exact LinearMap.ext hT

theorem nested_limit {α : Type*} (z : Completed F) {l : Filter α}
    (a : α → (Index →₀ ℝ)) (H : PredictableL2 (completedIntegral F z))
    (ha : Tendsto (fun n => dictionary (completedIntegral F z) (a n)) l (𝓝 H)) :
    Tendsto (fun n => finiteInput F z (a n)) l (𝓝 (nestedIntegral F z H)) ∧
    Tendsto (fun n => integralLinear (completedIntegral F z) (a n)) l
      (𝓝 (completedIntegral F (nestedIntegral F z H))) := by
  have hi : Tendsto (fun n => finiteInput F z (a n)) l (𝓝 (nestedIntegral F z H)) := by
    simpa only [Function.comp_def,nested_dictionary] using
      (nestedIntegral F z).continuous.continuousAt.tendsto.comp ha
  refine ⟨hi,?_⟩
  simpa only [Function.comp_def,finiteInput_actual] using
    (completedIntegral F).continuous.continuousAt.tendsto.comp hi



theorem stochastic_range_stable (Y : JointL2)
    (hY : Y ∈ LinearMap.range (completedIntegral F).toLinearMap) (H : PredictableL2 Y) :
    IBMFullPredictableIntegral.integral Y H ∈ LinearMap.range (completedIntegral F).toLinearMap := by
  obtain ⟨z,rfl⟩ := hY
  exact ⟨nestedIntegral F z H,nested_actual F z H⟩

end OperatorDerivativeRewrite.Foundation.IBMCompletedStochasticAssociativity
