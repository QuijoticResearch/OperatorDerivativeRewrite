import Foundation.IBMTemporalCovarianceObstruction
import Mathlib.Probability.Martingale.Basic
import Foundation.StickyNaturalMartingales

/-! Actual IBM is not a martingale in its own natural filtration: its genuine
L2 conditional projection at time one does not equal the previous value. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMNaturalFiltrationObstruction
open InfiniteGaussian IBMTimeAveragedObservable IBMTemporalCovarianceObstruction
set_option backward.isDefEq.respectTransparency false

theorem point_stronglyMeasurable (t : ℝ≥0) :
    StronglyMeasurable (IBMConstructedSources.ibmValue t) :=
  (IBMConstructedSources.ibmValue_jointly_measurable.comp
    (measurable_const.prodMk measurable_id)).stronglyMeasurable

def naturalFiltration : Filtration ℝ≥0
    (inferInstance : MeasurableSpace IBMSourceLaws.JointSample) :=
  Filtration.natural IBMConstructedSources.ibmValue point_stronglyMeasurable

theorem point_stronglyAdapted :
    StronglyAdapted naturalFiltration IBMConstructedSources.ibmValue :=
  Filtration.stronglyAdapted_natural point_stronglyMeasurable

def past (t : ℝ≥0) : Submodule ℝ JointL2 :=
  lpMeas ℝ ℝ (naturalFiltration t) 2 IBMSourceLaws.jointMeasure

theorem past_closed (t : ℝ≥0) : IsClosed (past t : Set JointL2) := by
  change IsClosed {f : JointL2 | AEStronglyMeasurable[naturalFiltration t]
    f IBMSourceLaws.jointMeasure}
  exact isClosed_aestronglyMeasurable (naturalFiltration.le t)

theorem previous_mem_past : (intrinsicCurve 1 : JointL2) ∈ past 1 := by
  change AEStronglyMeasurable[naturalFiltration 1]
    (intrinsicCurve 1 : JointL2) IBMSourceLaws.jointMeasure
  exact (point_stronglyAdapted 1).aestronglyMeasurable.congr (joint_point_actual_ae 1).symm

theorem conditional_L2_ne_previous :
    (condExpL2 ℝ ℝ (naturalFiltration.le 1) (intrinsicCurve 2 : JointL2) : JointL2) ≠
      (intrinsicCurve 1 : JointL2) := by
  let : CompleteSpace (past 1) := (past_closed 1).completeSpace_coe
  change (past 1).starProjection (intrinsicCurve 2 : JointL2) ≠ (intrinsicCurve 1 : JointL2)
  exact past_projection_ne_previous (past 1) previous_mem_past

theorem conditional_expectation_ne_previous :
    ¬ (IBMSourceLaws.jointMeasure[IBMConstructedSources.ibmValue 2 | naturalFiltration 1]
      =ᵐ[IBMSourceLaws.jointMeasure] IBMConstructedSources.ibmValue 1) := by
  intro h
  have he := (Lp.memLp (intrinsicCurve 2 : JointL2)).condExpL2_ae_eq_condExp
    (𝕜 := ℝ) (naturalFiltration.le 1)
  have hce : (condExpL2 ℝ ℝ (naturalFiltration.le 1) (intrinsicCurve 2 : JointL2) : JointL2)
      =ᵐ[IBMSourceLaws.jointMeasure]
        IBMSourceLaws.jointMeasure[(intrinsicCurve 2 : JointL2) | naturalFiltration 1] := by
    simpa only [Lp.toLp_coeFn] using he
  apply conditional_L2_ne_previous
  apply Lp.ext
  exact hce.trans ((condExp_congr_ae (joint_point_actual_ae 2)).trans
    (h.trans (joint_point_actual_ae 1).symm))

theorem actual_not_martingale :
    ¬ Martingale IBMConstructedSources.ibmValue naturalFiltration IBMSourceLaws.jointMeasure := by
  intro h
  exact conditional_expectation_ne_previous
    (h.condExp_ae_eq (show (1 : ℝ≥0) ≤ 2 by norm_num))

/-- No larger filtration can make the actual uncorrected IBM a martingale.
The existing sticky-process filtration-shrinking lemma supplies the transfer. -/
theorem no_martingale_filtration
    (ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace IBMSourceLaws.JointSample)) :
    ¬ Martingale IBMConstructedSources.ibmValue ℱ IBMSourceLaws.jointMeasure := by
  intro h
  have hle (t : ℝ≥0) : naturalFiltration t ≤ ℱ t := by
    change (⨆ s ≤ t, MeasurableSpace.comap (IBMConstructedSources.ibmValue s) inferInstance) ≤ ℱ t
    exact iSup₂_le fun s hst =>
      (h.stronglyAdapted s).measurable.comap_le.trans (ℱ.mono hst)
  exact actual_not_martingale (StickyNaturalMartingales.shrink IBMSourceLaws.jointMeasure
    naturalFiltration ℱ hle IBMConstructedSources.ibmValue h point_stronglyAdapted)

end OperatorDerivativeRewrite.Foundation.IBMNaturalFiltrationObstruction
