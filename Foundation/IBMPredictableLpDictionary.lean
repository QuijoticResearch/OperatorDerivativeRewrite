import Foundation.IBMPredictableFiniteIsometry

/-! The finite dictionary in the actual predictable L2 space, with its true norm. -/
noncomputable section
open MeasureTheory Set
open scoped NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.IBMPredictableLpDictionary
open IBMPredictableRectangles IBMPredictableFiniteIntegral IBMPredictableRingContent
open IBMJointPredictableEnergyMeasure IBMPredictableFiniteIsometry IBMTimeAveragedObservable
set_option backward.isDefEq.respectTransparency false
local instance : MeasurableSpace Space := IBMNaturalFiltrationObstruction.naturalFiltration.predictable
local instance (F : JointL2) : IsFiniteMeasure (predictableMeasure F) := finite_measure F

abbrev PredictableL2 (F : JointL2) := Lp ℝ 2 (predictableMeasure F)

def dictionary (F : JointL2) : (Index →₀ ℝ) →ₗ[ℝ] PredictableL2 F where
  toFun l := (process_memLp F l).toLp (processLinear l)
  map_add' l k := by simpa only [map_add] using (process_memLp F l).toLp_add (process_memLp F k)
  map_smul' a l := by
    simpa only [map_smul, RingHom.id_apply] using (process_memLp F l).toLp_const_smul a

theorem dictionary_ae (F : JointL2) (l : Index →₀ ℝ) :
    dictionary F l =ᵐ[predictableMeasure F] processLinear l :=
  (process_memLp F l).coeFn_toLp

theorem dictionary_inner (F : JointL2) (l k : Index →₀ ℝ) :
    inner ℝ (integralLinear F l) (integralLinear F k) =
      inner ℝ (dictionary F l) (dictionary F k) := by
  rw [finite_cross_integral, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [dictionary_ae F l, dictionary_ae F k] with p hl hk
  rw [hl, hk, Real.inner_apply, mul_comm]

theorem dictionary_norm (F : JointL2) (l : Index →₀ ℝ) :
    ‖integralLinear F l‖ = ‖dictionary F l‖ := by
  have h := dictionary_inner F l l
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg (integralLinear F l), norm_nonneg (dictionary F l)]

theorem dictionary_eq_iff (F : JointL2) (l k : Index →₀ ℝ) :
    dictionary F l = dictionary F k ↔ processLinear l =ᵐ[predictableMeasure F] processLinear k :=
  (process_memLp F l).toLp_eq_toLp_iff (process_memLp F k)

theorem stochastic_eq_iff (F : JointL2) (l k : Index →₀ ℝ) :
    integralLinear F l = integralLinear F k ↔
      processLinear l =ᵐ[predictableMeasure F] processLinear k := by
  rw [← dictionary_eq_iff]
  have hn := dictionary_norm F (l-k)
  rw [map_sub, map_sub] at hn
  constructor
  · intro h
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    rw [← hn, h, sub_self, norm_zero]
  · intro h
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    rw [hn, h, sub_self, norm_zero]

theorem indicator_in_range (F : JointL2) {E : Set Space} (hE : E ∈ elementaryRing) :
    indicatorConstLp 2 (elementary_predictable hE) (measure_ne_top _ _) (1 : ℝ) ∈
      LinearMap.range (dictionary F) := by
  obtain ⟨l, hl⟩ := ring_indicator_mem hE
  refine ⟨l, Lp.ext ?_⟩
  have hi : (indicatorConstLp 2 (elementary_predictable hE) (measure_ne_top _ _) (1 : ℝ) :
      PredictableL2 F) =ᵐ[predictableMeasure F] E.indicator (fun _ => 1) :=
    indicatorConstLp_coeFn
  have hd := dictionary_ae F l
  rw [hl] at hd
  exact hd.trans hi.symm

end OperatorDerivativeRewrite.Foundation.IBMPredictableLpDictionary
