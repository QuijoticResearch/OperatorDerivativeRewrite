import Foundation.PeriodicLocalEnergy
import Foundation.PeriodicCurvatureVariance
import Foundation.PeriodicQuarticCurvature
/-! A native counterexample to global variance control by only the restricted
low-action cap energy. The explicit bounded continuous physical cutoff has
positive actual stationary variance and zero restricted local increments.
No failure of a spectral gap for the full operator is asserted. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace OperatorDerivativeRewrite.Foundation.PeriodicLocalEnergyObstruction
open PeriodicTemporalSlab PeriodicWilsonSlab PeriodicSlabGround PeriodicSlabL2
open PeriodicLocalEnergy PeriodicKineticCapLower
attribute [local irreducible] spatialAction boundaryHaar

def cutoff (β K : ℝ) (U : State) : ℝ := max 0 (β*spatialAction U-(2*K+27648))

theorem cutoff_continuous (β K : ℝ) : Continuous (cutoff β K) :=
  continuous_const.max ((continuous_const.mul PeriodicLowActionBlock.spatial_continuous).sub continuous_const)

theorem cutoff_gauge (β K : ℝ) (a : Gauge) (U : State) :
    cutoff β K (PeriodicSlabGauge.gaugeAction a U)=cutoff β K U := by
  unfold cutoff
  rw [PeriodicSlabGauge.spatial_action_invariant]

theorem cutoff_bounds (β K : ℝ) (hb : 0 ≤ β) (hK : 0 ≤ K) (U : State) :
    0 ≤ cutoff β K U ∧ cutoff β K U ≤ 384*β := by
  constructor
  · exact le_max_left _ _
  · apply max_le (by positivity)
    have hs := mul_le_mul_of_nonneg_left (spatial_action_bounds U).2 hb
    nlinarith

theorem cutoff_memLp {β : ℝ} (g : GroundData β) (K : ℝ) (hb : 0 ≤ β) (hK : 0 ≤ K) :
    MemLp (cutoff β K) 2 g.stationary := by
  let : IsProbabilityMeasure g.stationary := g.stationary_probability
  apply MemLp.of_bound (cutoff_continuous β K).measurable.aestronglyMeasurable (384*β)
  filter_upwards with U
  rw [Real.norm_eq_abs,abs_of_nonneg (cutoff_bounds β K hb hK U).1]
  exact (cutoff_bounds β K hb hK U).2

theorem cutoff_anchor_zero (t : ℝ) (ht : 0 < t) (K : ℝ) (hK : 0 ≤ K)
    (U : State) (hU : (1/t^2)*spatialAction U ≤ K) :
    capIncrement t (cutoff (1/t^2) K) U=0 := by
  have hscale : (1/t^2)*t^2=1 := by field_simp
  have hbase : cutoff (1/t^2) K U=0 := by
    unfold cutoff
    exact max_eq_left (by linarith)
  unfold capIncrement
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem (capBox_measurable t)] with h hh
  have hs := mul_le_mul_of_nonneg_left (PeriodicLocalGroundHarnack.cap_spatial_upper U h t ht.le hh)
    (show (0:ℝ) ≤ 1/t^2 by positivity)
  have hv : cutoff (1/t^2) K (U*h)=0 := by
    unfold cutoff
    apply max_eq_left
    nlinarith
  rw [hv,hbase]
  norm_num

private instance boundary_open : boundaryHaar.IsOpenPosMeasure := by unfold boundaryHaar; infer_instance

theorem cutoff_variance_pos {β : ℝ} (g : GroundData β) (K : ℝ) (hb : 0 ≤ β) (hK : 0 ≤ K)
    (hhigh : 2*K+27648 < 128*β) : 0 < variance (cutoff β K) g.stationary := by
  let : IsProbabilityMeasure g.stationary := g.stationary_probability
  by_contra hn
  have hz : variance (cutoff β K) g.stationary=0 :=
    le_antisymm (le_of_not_gt hn) (variance_nonneg _ _)
  have hae := ae_eq_integral_of_variance_eq_zero (cutoff_memLp g K hb hK) hz
  have hh := (PeriodicCurvatureVariance.stationary_ae_iff g _).mp hae
  have heq := Measure.eq_of_ae_eq hh (cutoff_continuous β K) continuous_const
  have h0 := congrFun heq (1 : State)
  have h1 := congrFun heq (PeriodicQuarticCurvature.field (Real.pi/2))
  have hs : spatialAction (1 : State)=0 := by
    simp [spatialAction,spatialWord,SU2OpenLinkGaugeObstruction.halfTrace_one]
  have he : spatialAction (PeriodicQuarticCurvature.field (Real.pi/2))=128 := by
    rw [PeriodicQuarticCurvature.spatial_action,Real.sin_pi_div_two]
    norm_num
  have hf0 : cutoff β K (1 : State)=0 := by
    unfold cutoff
    rw [hs,mul_zero]
    exact max_eq_left (by linarith)
  have hf1 : 0 < cutoff β K (PeriodicQuarticCurvature.field (Real.pi/2)) := by
    unfold cutoff
    rw [he]
    exact lt_max_of_lt_right (by linarith)
  rw [hf0] at h0
  rw [h1,h0.symm] at hf1
  linarith

theorem cutoff_local_zero (t : ℝ) (ht : 0 < t) (g : GroundData (1/t^2)) (K : ℝ) (hK : 0 ≤ K) :
    (∫ U in {U | (1/t^2)*spatialAction U ≤ K},capIncrement t (cutoff (1/t^2) K) U ∂g.stationary)=0 := by
  have hA : MeasurableSet {U : State | (1/t^2)*spatialAction U ≤ K} :=
    measurableSet_le (spatial_action_measurable.const_mul (1/t^2)) measurable_const
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem hA] with U hU
  exact cutoff_anchor_zero t ht K hK U hU

/-- No finite scalar controls the actual native variance of every bounded
continuous physical observable using only the restricted local functional.
This does not assert failure of a spectral gap for the full operator. -/
theorem no_restricted_poincare (t : ℝ) (ht : 0 < t) (g : GroundData (1/t^2)) (K : ℝ) (hK : 0 ≤ K)
    (hhigh : 2*K+27648 < 128*(1/t^2)) (C : ℝ) :
    ¬ variance (cutoff (1/t^2) K) g.stationary ≤
      C*((∫ U in {U | (1/t^2)*spatialAction U ≤ K},capIncrement t (cutoff (1/t^2) K) U ∂g.stationary)/
        boundaryHaar.real (capBox t)) := by
  rw [cutoff_local_zero t ht g K hK,zero_div,mul_zero]
  exact not_le_of_gt (cutoff_variance_pos g K (by positivity) hK hhigh)

end OperatorDerivativeRewrite.Foundation.PeriodicLocalEnergyObstruction
