import Foundation.IBMCompactVarianceGeometry
import Foundation.IBMDilatedMollifier

/-! Genuine variance and covariance limits for every positive-width family.
The slope convergence is asserted away from zero, as needed for occupation arguments. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.IBMDilatedVarianceGeometry
open InfiniteGaussian IBMContinuousScenery IBMCompactVarianceGeometry IBMDilatedMollifier
set_option backward.isDefEq.respectTransparency false

theorem covariance_bracket {ρ : ℝ → ℝ} (hc : HasCompactSupport ρ)
    (hρ : ContDiff ℝ 2 ρ) (hmass : (∫ z, ρ z) = 1) (x : ℝ) :
    ‖wholeLineScenery (deriv ρ) x‖^2 + inner ℝ (wholeLineScenery ρ x)
      (wholeLineScenery (deriv (deriv ρ)) x) = ρ x := by
  have h1 := variance_second hc hρ.continuous hmass x
  have h2 := wholeLineVariance_second_deriv ρ hc hρ x
  linarith

theorem variance_lipschitz {ρ : ℝ → ℝ} (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 2 ρ)
    (hpos : ∀ x, 0 ≤ ρ x) (hmass : (∫ z, ρ z) = 1) : LipschitzWith 1 (wholeLineVariance ρ) :=
  lipschitzWith_of_nnnorm_deriv_le ((variance_C2 hc hρ).differentiable (by norm_num))
    (fun x => show ‖deriv (wholeLineVariance ρ) x‖ ≤ (1 : ℝ) from
      slope_bound hc hρ.continuous hpos hmass x)

theorem variance_tendsto {ι : Type*} {l : Filter ι} {ε : ι → ℝ}
    (hε : ∀ i, 0 < ε i) (hlim : Tendsto ε l (𝓝 0)) {ρ : ℝ → ℝ}
    (hc : HasCompactSupport ρ) (hρ : Continuous ρ)
    (hpos : ∀ x, 0 ≤ ρ x) (hmass : (∫ z, ρ z) = 1) (x : ℝ) :
    Tendsto (fun i => wholeLineVariance (dilate ρ (ε i)) x) l (𝓝 |x|) := by
  have h := (scenery_tendsto hε hlim hρ hc hpos hmass x).norm.pow 2
  simpa only [wholeLineVariance,IBMRandomTimeHilbert.sourceScenery_norm_sq] using h

theorem slope_tendsto_nonzero {ι : Type*} {l : Filter ι} {ε : ι → ℝ}
    (hε : ∀ i, 0 < ε i) (hlim : Tendsto ε l (𝓝 0)) {ρ : ℝ → ℝ}
    (hc : HasCompactSupport ρ) (hρ : Continuous ρ) (hmass : (∫ z, ρ z) = 1)
    (x : ℝ) (hx : x ≠ 0) :
    Tendsto (fun i => deriv (wholeLineVariance (dilate ρ (ε i))) x) l
      (𝓝 (BrownianSignIntegral.signum x)) := by
  obtain ⟨R0,hR0⟩ := hc.isBounded.exists_norm_le
  let R := max R0 0
  have hs (z : ℝ) (hz : ρ z ≠ 0) : |z| ≤ R := by
    have hb : |z| ≤ R0 := by simpa only [Real.norm_eq_abs] using hR0 z (subset_tsupport ρ hz)
    exact hb.trans (le_max_left _ _)
  have hr : Tendsto (fun i => ε i*R) l (𝓝 0) := by simpa only [zero_mul] using hlim.mul_const R
  apply tendsto_const_nhds.congr'
  filter_upwards [hr.eventually (eventually_lt_nhds (abs_pos.mpr hx))] with i hi
  have hm := (dilate_integral ρ (hε i)).trans hmass
  have hcont : Continuous (dilate ρ (ε i)) := continuous_const.mul (hρ.comp (continuous_id.div_const _))
  have hsup (z : ℝ) (hz : dilate ρ (ε i) z ≠ 0) : |z| ≤ ε i*R := dilate_support hs (hε i) hz
  rcases lt_or_gt_of_ne hx with hn | hp
  · rw [abs_of_neg hn] at hi
    rw [slope_negative_bulk (dilate_compact hc (hε i).ne') hcont hm hsup (by linarith)]
    simp [BrownianSignIntegral.signum,hn,not_lt_of_gt hn]
  · rw [abs_of_pos hp] at hi
    rw [slope_positive_bulk (dilate_compact hc (hε i).ne') hcont hm hsup hi]
    simp [BrownianSignIntegral.signum,hp]

end OperatorDerivativeRewrite.Foundation.IBMDilatedVarianceGeometry
