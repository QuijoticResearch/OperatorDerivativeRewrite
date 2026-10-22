import Foundation.IBMPredictableSimpleCoefficient
import Foundation.BochnerL2Approximation

/-! Actual bounded coefficient approximation in both stochastic L2 topologies. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMPredictableBoundedApproximation
open IBMPredictableRectangles IBMPredictableCoefficientLift IBMPredictableLpDictionary
open IBMJointPredictableEnergyMeasure IBMTimeAveragedObservable IBMNaturalFiltrationObstruction
open IBMWeightedTerminalEnergy IBMObservedTerminalMartingale IBMGermPredictableStep
open IBMIntrinsicMartingaleStep (Coefficient)
set_option backward.isDefEq.respectTransparency false
local instance : MeasurableSpace Space := naturalFiltration.predictable
local instance (F : JointL2) : IsFiniteMeasure (predictableMeasure F) := finite_measure F

def cap {s : ℝ≥0} (a : Coefficient s) : ℝ := max a.bound 0

theorem cap_nonneg {s : ℝ≥0} (a : Coefficient s) : 0 ≤ cap a := le_max_right _ _

def approximation {s : ℝ≥0} (a : Coefficient s) (n : ℕ) : Coefficient s where
  function := a.adapted.approxBounded (cap a) n
  adapted := (a.adapted.approxBounded (cap a) n).stronglyMeasurable
  bound := cap a
  bounded := ae_of_all _ (a.adapted.norm_approxBounded_le (cap_nonneg a) n)

theorem approximation_bound {s : ℝ≥0} (a : Coefficient s) (n : ℕ)
    (ω : IBMSourceLaws.JointSample) : ‖(approximation a n).function ω‖ ≤ cap a :=
  a.adapted.norm_approxBounded_le (cap_nonneg a) n ω

theorem original_bound {s : ℝ≥0} (a : Coefficient s) :
    ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, ‖a.function ω‖ ≤ cap a :=
  a.bounded.mono fun _ h => h.trans (le_max_left _ _)

theorem original_approximation {s : ℝ≥0} (a : Coefficient s) :
    ∀ᵐ ω ∂IBMSourceLaws.jointMeasure,
      Tendsto (fun n => (approximation a n).function ω) atTop (𝓝 (a.function ω)) :=
  a.adapted.tendsto_approxBounded_ae (original_bound a)

theorem lifted_bound (F : JointL2) {s t : ℝ≥0} (hst : s ≤ t) (a : Coefficient s) :
    ∀ᵐ p ∂predictableMeasure F, p.1 ∈ Ioc s t → ‖a.function p.2‖ ≤ cap a := by
  have hm : MeasurableSet[naturalFiltration s] {ω | ‖a.function ω‖ ≤ cap a} := by
    let : MeasurableSpace IBMSourceLaws.JointSample := naturalFiltration s
    exact measurableSet_le a.adapted.measurable.norm measurable_const
  exact ae_lift F hst _ hm (original_bound a)

theorem coefficientLp_approximation (F : JointL2) {s t : ℝ≥0} (hst : s ≤ t)
    (a : Coefficient s) :
    Tendsto (fun n => coefficientLp F hst (approximation a n)) atTop
      (𝓝 (coefficientLp F hst a)) := by
  let b : PredictableL2 F := (memLp_const (cap a)).toLp (fun _ => cap a)
  have hb : b =ᵐ[predictableMeasure F] (fun _ => cap a) := (memLp_const (cap a)).coeFn_toLp
  apply BochnerL2Approximation.tendsto_of_dominated _ _ b
  · intro n
    filter_upwards [coefficientLp_ae F hst (approximation a n), hb] with p hp hbp
    rw [hp, hbp, Real.norm_of_nonneg (cap_nonneg a)]
    by_cases hr : p.1 ∈ Ioc s t
    · simpa only [lift, indicator_of_mem hr] using approximation_bound a n p.2
    · simp only [lift, indicator_of_notMem hr, norm_zero]
      exact cap_nonneg a
  · filter_upwards [coefficientLp_ae F hst a, hb, lifted_bound F hst a] with p hp hbp hbound
    rw [hp, hbp, Real.norm_of_nonneg (cap_nonneg a)]
    by_cases hr : p.1 ∈ Ioc s t
    · simpa only [lift, indicator_of_mem hr] using hbound hr
    · simp only [lift, indicator_of_notMem hr, norm_zero]
      exact cap_nonneg a
  · have hn := ae_all_iff.mpr fun n => coefficientLp_ae F hst (approximation a n)
    filter_upwards [hn, coefficientLp_ae F hst a, lifted_bound F hst a] with p hp hlim hbound
    simp only [hp, hlim]
    by_cases hr : p.1 ∈ Ioc s t
    · simpa only [lift, indicator_of_mem hr, approximation] using
        a.adapted.tendsto_approxBounded_of_norm_le (hbound hr)
    · simp only [lift, indicator_of_notMem hr]
      exact tendsto_const_nhds

theorem stepClass_approximation (F : JointL2) {s t : ℝ≥0} (hst : s ≤ t)
    (a : Coefficient s) :
    Tendsto (fun n => stepClass F s t (approximation a n)) atTop (𝓝 (stepClass F s t a)) := by
  let b : JointL2 := cap a • (channelClass F t - channelClass F s)
  have hb : b =ᵐ[IBMSourceLaws.jointMeasure]
      (fun ω => cap a * (channel F t ω - channel F s ω)) := by
    filter_upwards [Lp.coeFn_smul (cap a) (channelClass F t - channelClass F s),
      Lp.coeFn_sub (channelClass F t) (channelClass F s)] with ω hs hd
    rw [show b ω = _ from hs, Pi.smul_apply, smul_eq_mul, hd]
    rfl
  apply BochnerL2Approximation.tendsto_of_dominated _ _ b
  · intro n
    filter_upwards [stepClass_ae F hst (approximation a n), hb] with ω hs hbp
    rw [hs, hbp, norm_mul, norm_mul, Real.norm_of_nonneg (cap_nonneg a)]
    exact mul_le_mul_of_nonneg_right (approximation_bound a n ω) (norm_nonneg _)
  · filter_upwards [stepClass_ae F hst a, hb, original_bound a] with ω hs hbp hbound
    rw [hs, hbp, norm_mul, norm_mul, Real.norm_of_nonneg (cap_nonneg a)]
    exact mul_le_mul_of_nonneg_right hbound (norm_nonneg _)
  · have hn := ae_all_iff.mpr fun n => stepClass_ae F hst (approximation a n)
    filter_upwards [hn, stepClass_ae F hst a, original_approximation a] with ω hn hs ht
    simp only [hn, hs]
    exact ht.mul_const _

theorem integral_identification (F : JointL2) {s t : ℝ≥0} (hst : s ≤ t)
    (a : Coefficient s) :
    IBMFullPredictableIntegral.integral F (coefficientLp F hst a) = stepClass F s t a := by
  have hnew := (IBMFullPredictableIntegral.integral F).continuous.continuousAt.tendsto.comp
    (coefficientLp_approximation F hst a)
  have he n := IBMPredictableSimpleCoefficient.simple_integral_identification F hst
    (approximation a n) (a.adapted.approxBounded (cap a) n) rfl
  have hold := stepClass_approximation F hst a
  exact tendsto_nhds_unique (by simpa only [Function.comp_def, he] using hnew) hold

theorem coefficient_energy (F : JointL2) {s t : ℝ≥0} (hst : s ≤ t) (a : Coefficient s) :
    (∫ p, lift s t a.function p ^ 2 ∂predictableMeasure F) =
      ∫ ω, a.function ω ^ 2 * (channel F t ω - channel F s ω) ^ 2
        ∂IBMSourceLaws.jointMeasure := by
  calc
    (∫ p, lift s t a.function p ^ 2 ∂predictableMeasure F) = ‖coefficientLp F hst a‖ ^ 2 := by
      rw [BochnerL2Dominated.norm_sq_integral]
      apply integral_congr_ae
      filter_upwards [coefficientLp_ae F hst a] with p hp
      rw [hp, Real.norm_eq_abs, sq_abs]
    _ = ‖stepClass F s t a‖ ^ 2 := by
      rw [← IBMFullPredictableIntegral.integral_norm F (coefficientLp F hst a),
        integral_identification]
    _ = _ := step_energy F hst a

end OperatorDerivativeRewrite.Foundation.IBMPredictableBoundedApproximation
