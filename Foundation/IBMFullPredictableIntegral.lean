import Foundation.IBMPredictableDictionaryDensity

/-! A genuine integral on ALL L2 of the actual raw-predictable energy measure. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMFullPredictableIntegral
open IBMPredictableRectangles IBMPredictableFiniteIntegral IBMPredictableRingContent
open IBMPredictableLpDictionary IBMPredictableDictionaryDensity
open IBMJointPredictableEnergyMeasure IBMTimeAveragedObservable
set_option backward.isDefEq.respectTransparency false
local instance : MeasurableSpace Space := IBMNaturalFiltrationObstruction.naturalFiltration.predictable
local instance (F : JointL2) : IsFiniteMeasure (predictableMeasure F) := finite_measure F

def integral (F : JointL2) : PredictableL2 F →ₗᵢ[ℝ] JointL2 :=
  (integralLinear F).extendOfIsometry (dictionary_dense F) (dictionary_norm F)

theorem integral_dictionary (F : JointL2) (l : Index →₀ ℝ) :
    integral F (dictionary F l) = integralLinear F l :=
  LinearMap.extendOfIsometry_eq _ _ _ _

theorem integral_dictionary_ae (F : JointL2) (l : Index →₀ ℝ) :
    integral F (dictionary F l) =ᵐ[IBMSourceLaws.jointMeasure] fun ω =>
      ∑ d ∈ l.support, (l d * (IBMWeightedTerminalEnergy.eventCoefficient
        (left d) (event d) (event_measurable d)).function ω) *
        (IBMObservedTerminalMartingale.channel F (right d) ω -
          IBMObservedTerminalMartingale.channel F (left d) ω) := by
  rw [integral_dictionary]
  exact integralLinear_ae F l

theorem integral_indicator (F : JointL2) {E : Set Space} (hE : E ∈ elementaryRing) :
    integral F (indicatorConstLp 2 (elementary_predictable hE) (measure_ne_top _ _) (1 : ℝ)) =
      ringIntegral F E := by
  obtain ⟨l, hl⟩ := ring_indicator_mem hE
  have he : dictionary F l =
      indicatorConstLp 2 (elementary_predictable hE) (measure_ne_top _ _) (1 : ℝ) := by
    apply Lp.ext
    have hd := dictionary_ae F l
    rw [hl] at hd
    exact hd.trans indicatorConstLp_coeFn.symm
  rw [← he, integral_dictionary]
  have hp : indicatorClass E = ⟨processLinear l, ⟨l, rfl⟩⟩ := by
    apply Subtype.ext
    rw [indicatorClass_value hE]
    exact hl.symm
  rw [ringIntegral, hp, integral_process]

theorem integral_norm (F : JointL2) (H : PredictableL2 F) : ‖integral F H‖ = ‖H‖ :=
  (integral F).norm_map H

theorem integral_inner (F : JointL2) (H K : PredictableL2 F) :
    inner ℝ (integral F H) (integral F K) = inner ℝ H K :=
  (integral F).inner_map_map H K

theorem actual_integral_energy (F : JointL2) (H : PredictableL2 F) :
    (∫ ω, (integral F H ω) ^ 2 ∂IBMSourceLaws.jointMeasure) =
      ∫ p, H p ^ 2 ∂predictableMeasure F := by
  have hi := integral_inner F H H
  rw [L2.inner_def, L2.inner_def] at hi
  simpa only [Real.inner_apply, pow_two] using hi

theorem integral_limit {α : Type*} (F : JointL2) {l : Filter α}
    (a : α → (Index →₀ ℝ)) (H : PredictableL2 F)
    (ha : Tendsto (fun n => dictionary F (a n)) l (𝓝 H)) :
    Tendsto (fun n => integralLinear F (a n)) l (𝓝 (integral F H)) := by
  simpa only [Function.comp_def, integral_dictionary] using
    (integral F).continuous.continuousAt.tendsto.comp ha

theorem integral_unique (F : JointL2) (J : PredictableL2 F →ₗᵢ[ℝ] JointL2)
    (hJ : ∀ a, J (dictionary F a) = integralLinear F a) : J = integral F := by
  symm
  apply LinearMap.extendOfIsometry_unique (integralLinear F) (dictionary_dense F) (dictionary_norm F) J
  exact LinearMap.ext hJ

theorem exists_actual_approximation (F : JointL2) (H : PredictableL2 F) :
    ∃ a : ℕ → (Index →₀ ℝ),
      Tendsto (fun n => dictionary F (a n)) atTop (𝓝 H) ∧
      Tendsto (fun n => integralLinear F (a n)) atTop (𝓝 (integral F H)) := by
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.mp (dictionary_dense F H)
  choose a ha using hu
  have he : (fun n => dictionary F (a n)) = u := funext ha
  have ht : Tendsto (fun n => dictionary F (a n)) atTop (𝓝 H) := he ▸ hlim
  exact ⟨a, ht, integral_limit F a H ht⟩

end OperatorDerivativeRewrite.Foundation.IBMFullPredictableIntegral
