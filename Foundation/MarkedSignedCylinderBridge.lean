import Foundation.MarkedTwoTimeHeatLimit
import Foundation.HigherHeatCylinderFourier

/-! Actual complex-process joint laws and their holomorphic bridge to signed heat cylinders. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.MarkedSignedCylinderBridge
open MarkedRootRenewalProcess (StateSample probability)
open MarkedRenewalMartingale MarkedHolomorphicExponential
open ComplexRootHeatTransformLimit

def jointLaw (a : ℝ) (s t : ℝ≥0) : Measure (ℂ × ℂ) :=
  probability.map (fun ω => (process a s ω,process a t ω))

instance jointLaw_isProbability (a : ℝ) (s t : ℝ≥0) : IsProbabilityMeasure (jointLaw a s t) where
  measure_univ := by
    rw [jointLaw,Measure.map_apply ((process_measurable a s).prodMk (process_measurable a t))
      MeasurableSet.univ,Set.preimage_univ,measure_univ]

theorem jointLaw_transform (a η ξ : ℝ) (s t : ℝ≥0) (hst : s ≤ t) :
    (∫ z : ℂ × ℂ, Complex.exp (Complex.I*(η : ℂ)*z.1)*
      Complex.exp (Complex.I*(ξ : ℂ)*z.2) ∂jointLaw a s t) =
      Complex.exp ((s : ℂ)*symbol a (η+ξ)+((t-s : ℝ≥0) : ℂ)*symbol a ξ) := by
  have hm : Measurable (fun z : ℂ × ℂ => Complex.exp (Complex.I*(η : ℂ)*z.1)*
      Complex.exp (Complex.I*(ξ : ℂ)*z.2)) := by fun_prop
  rw [jointLaw,integral_map ((process_measurable a s).prodMk
    (process_measurable a t)).aemeasurable hm.aestronglyMeasurable]
  exact MarkedTwoTimeHolomorphicTransform.two_time_transform a η ξ s t hst

def signedFourier (s h : ℝ≥0) (hs : 0 < s) (hh : 0 < h) (η ξ : ℝ) : ℂ :=
  HigherHeatCylinderFourier.cylinderFourier 2 (by decide) ![s,h]
    (by intro j; fin_cases j <;> simp_all) (HigherHeatCylinderFourier.cumulativeMatrix 2) ![η,ξ]

theorem signedFourier_eq (s h : ℝ≥0) (hs : 0 < s) (hh : 0 < h) (η ξ : ℝ) :
    signedFourier s h hs hh η ξ = HigherHeatL2.symbol 2 s (η+ξ)*HigherHeatL2.symbol 2 h ξ := by
  unfold signedFourier
  rw [HigherHeatCylinderFourier.positionFourier_eq]
  norm_num [Fin.prod_univ_succ,Fin.sum_univ_succ,Finset.sum_filter]

theorem actual_to_signed_cylinder_limit (s h : ℝ≥0) (hs : 0 < s) (hh : 0 < h) (η ξ : ℝ) :
    Tendsto (fun n : ℕ => ∫ ω,
      phase (amplitude 1 n) (2*Real.pi*η) ((n : ℝ≥0)*s) ω*
      phase (amplitude 1 n) (2*Real.pi*ξ) ((n : ℝ≥0)*(s+h)) ω ∂probability) atTop
      (𝓝 (signedFourier s h hs hh η ξ)) := by
  rw [signedFourier_eq]
  simpa only [add_tsub_cancel_left] using
    MarkedTwoTimeHeatLimit.rate_scaled_operator_two_time_limit s (s+h)
      (le_add_of_nonneg_right (zero_le : 0 ≤ h)) η ξ

end OperatorDerivativeRewrite.Foundation.MarkedSignedCylinderBridge
